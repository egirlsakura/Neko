import os
import re
import time
import sqlite3
import html as html_module
import asyncio
import random
import logging
from collections import deque
from urllib.parse import quote

import aiohttp
import discord
from discord import app_commands
from discord.ext import commands
import yt_dlp
from dotenv import load_dotenv

load_dotenv()

TOKEN = os.getenv("DISCORD_TOKEN")
MAX_QUEUE = 100             # máximo de faixas na fila
MAX_PLAYLIST_TRACKS = 100   # máximo carregado de uma playlist por link
MAX_SAVED_TRACKS = 200      # máximo de faixas em uma playlist salva

# Banco das playlists criadas pelo bot (SQLite, arquivo local).
DB_PATH = os.getenv("PLAYLIST_DB", "playlists.db")

# Opcional: necessário só para playlists/álbuns do Spotify.
# Crie um app em https://developer.spotify.com/dashboard
SPOTIFY_CLIENT_ID = os.getenv("SPOTIFY_CLIENT_ID")
SPOTIFY_CLIENT_SECRET = os.getenv("SPOTIFY_CLIENT_SECRET")

# Opcional: arquivo de cookies do YouTube (formato Netscape).
# Só é usado se o arquivo existir. Útil quando o YouTube pede
# "Sign in to confirm you're not a bot" (comum em VPS/servidores).
COOKIES_FILE = os.getenv("YTDLP_COOKIES", "cookies.txt")

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("Neko")

intents = discord.Intents.default()
bot = commands.Bot(command_prefix="!", intents=intents)

YDL_OPTIONS = {
    "format": "bestaudio/best",
    "noplaylist": True,
    "quiet": True,
    "no_warnings": True,
    "default_search": "ytsearch",
    "socket_timeout": 15,
    "retries": 3,
}

# Cookies via variável de ambiente (ideal para Secrets do GitHub,
# Codespaces, Railway etc.): cole o conteúdo do cookies.txt em
# YOUTUBE_COOKIES e o bot cria o arquivo ao iniciar.
COOKIES_ENV = os.getenv("YOUTUBE_COOKIES")
if COOKIES_ENV and not os.path.isfile(COOKIES_FILE):
    with open(COOKIES_FILE, "w", encoding="utf-8") as cookie_file:
        cookie_file.write(COOKIES_ENV)

if os.path.isfile(COOKIES_FILE):
    YDL_OPTIONS["cookiefile"] = COOKIES_FILE
    log.info("Usando cookies de %s", COOKIES_FILE)

# Opcional: proxy residencial/HTTP para contornar bloqueio de IP.
PROXY = os.getenv("YTDLP_PROXY")
if PROXY:
    YDL_OPTIONS["proxy"] = PROXY
    log.info("Usando proxy para o yt-dlp.")

FFMPEG_OPTIONS = {
    "before_options": (
        "-reconnect 1 -reconnect_streamed 1 "
        "-reconnect_delay_max 5"
    ),
    "options": "-vn",
}

# Imagens aceitas nos comandos de avatar e banner.
IMAGE_TYPES = {"image/png", "image/jpeg", "image/gif", "image/webp"}
MAX_IMAGE_BYTES = 10 * 1024 * 1024  # 10 MB


class Track:
    """Uma faixa da fila.

    Se `url` (stream) ainda não existe, a faixa é "preguiçosa":
    o áudio só é buscado na hora de tocar (ensure_stream). Isso
    permite carregar playlists grandes sem esperar cada música.
    """

    def __init__(self, data, requester):
        self.title = data.get("title") or "Faixa desconhecida"
        self.url = (
            data.get("webpage_url")
            or data.get("original_url")
            or ""
        )
        self.stream = data.get("url")
        # Link ou texto usado para (re)buscar a faixa depois.
        self.query = data.get("query") or self.url or self.title
        self.duration = data.get("duration") or 0
        self.artist = (
            data.get("uploader")
            or data.get("artist")
            or "Artista desconhecido"
        )
        self.thumbnail = data.get("thumbnail")
        self.requester = requester

    async def ensure_stream(self):
        if self.stream:
            return

        resolved = await resolve_track(self.query, self.requester)
        self.stream = resolved.stream
        self.title = resolved.title
        self.url = resolved.url
        self.duration = resolved.duration
        self.artist = resolved.artist
        self.thumbnail = resolved.thumbnail


class MusicPlayer:
    def __init__(self):
        self.queue = deque()
        self.current = None
        self.voice = None
        self.channel = None
        self.panel = None
        self.volume = 0.5
        self.loop = False
        self.shuffle = False
        self.autoplay = False
        self.lock = asyncio.Lock()


players = {}


def get_player(guild_id):
    if guild_id not in players:
        players[guild_id] = MusicPlayer()
    return players[guild_id]


def format_time(seconds):
    seconds = int(seconds or 0)
    minutes, secs = divmod(seconds, 60)
    hours, minutes = divmod(minutes, 60)

    if hours:
        return f"{hours}:{minutes:02}:{secs:02}"
    return f"{minutes}:{secs:02}"


async def extract_info(query):
    loop = asyncio.get_running_loop()

    def extract():
        with yt_dlp.YoutubeDL(YDL_OPTIONS) as ydl:
            info = ydl.extract_info(query, download=False)

            if info and "entries" in info:
                info = next(
                    (item for item in info["entries"] if item),
                    None,
                )

            if not info or not info.get("url"):
                raise ValueError("Nenhum áudio reproduzível encontrado.")

            return info

    return await loop.run_in_executor(None, extract)


async def search_text(text, skip_youtube=False):
    """Busca por texto: tenta YouTube e, se falhar, SoundCloud."""
    yt_error = None

    if not skip_youtube:
        try:
            return await extract_info(f"ytsearch1:{text}")
        except Exception as error:
            yt_error = error
            log.warning(
                "Busca no YouTube falhou (%s). Tentando SoundCloud...",
                clean_error(error),
            )

    try:
        return await extract_info(f"scsearch1:{text}")
    except Exception as sc_error:
        log.error(
            "Busca no SoundCloud falhou: %s",
            clean_error(sc_error),
        )
        # Mantém o erro do YouTube, que explica melhor o motivo.
        if yt_error:
            raise yt_error from sc_error
        raise


def clean_error(error):
    """Remove códigos de cor e deixa a mensagem do yt-dlp legível."""
    text = re.sub(r"\x1b\[[0-9;]*m", "", str(error))
    return text.replace("ERROR: ", "").strip()


def friendly_reason(error):
    """Traduz os erros mais comuns do yt-dlp para o usuário."""
    text = clean_error(error).lower()

    if "not a bot" in text or "sign in" in text:
        return (
            "O YouTube bloqueou o servidor do bot "
            "(pede login/cookies)."
        )
    if "javascript runtime" in text or "deno" in text:
        return (
            "Falta o Deno (runtime JavaScript) para o yt-dlp "
            "acessar o YouTube."
        )
    if "requested format is not available" in text:
        return "Nenhum formato de áudio disponível (yt-dlp desatualizado?)."
    if "private" in text or "unavailable" in text:
        return "O vídeo está privado ou indisponível."
    return None


def clean_spotify_title(title):
    """Converte o og:title do Spotify em algo bom para buscar."""
    title = re.sub(r"\s*\|\s*Spotify\s*$", "", title, flags=re.I)
    title = re.sub(
        r"\s*-\s*(song|single|album|ep)"
        r"( and lyrics)?\s*(by|from)\s*",
        " ",
        title,
        flags=re.I,
    )
    return re.sub(r"\s+", " ", title).strip()


YOUTUBE_RE = re.compile(r"(youtube\.com|youtu\.be)", re.I)

# Links que são, por si só, uma playlist/álbum inteiro.
PLAYLIST_URL_RE = re.compile(
    r"(youtube\.com/playlist\?"
    r"|soundcloud\.com/[^/\s]+/sets/"
    r"|open\.spotify\.com/(?:[\w-]+/)?(?:playlist|album)/)",
    re.I,
)


def is_playlist_url(url):
    return bool(PLAYLIST_URL_RE.search(url))


async def youtube_oembed_title(url):
    """Pega o título de um vídeo do YouTube sem passar pelo bloqueio."""
    api = (
        "https://www.youtube.com/oembed?format=json&url="
        + quote(url, safe="")
    )
    async with aiohttp.ClientSession() as session:
        async with session.get(
            api,
            timeout=aiohttp.ClientTimeout(total=10),
            headers={"User-Agent": "Mozilla/5.0"},
        ) as response:
            if response.status != 200:
                raise ValueError("Não consegui ler os dados do vídeo.")
            data = await response.json()

    title = data.get("title")
    if not title:
        raise ValueError("Não consegui identificar a música.")
    return title


def clean_video_title(title):
    """Remove '(Official Video)', '[Lyrics]' etc. do título."""
    title = re.sub(
        r"\s*[\(\[][^\)\]]*"
        r"(official|video|audio|lyrics?|clipe|hd|4k)"
        r"[^\)\]]*[\)\]]",
        "",
        title,
        flags=re.I,
    )
    return re.sub(r"\s+", " ", title).strip()


async def resolve_track(query, requester):
    is_link = query.startswith(("http://", "https://"))

    # Busca por texto: YouTube primeiro, SoundCloud como reserva.
    if not is_link:
        try:
            info = await search_text(query)
            return Track(info, requester)
        except Exception as search_error:
            log.error(
                "Busca por texto falhou para %r: %s",
                query,
                clean_error(search_error),
            )
            raise ValueError(
                friendly_reason(search_error)
                or "Não encontrei uma versão reproduzível dessa música."
            ) from search_error

    # Links compatíveis são tentados diretamente.
    try:
        info = await extract_info(query)
        return Track(info, requester)
    except Exception as original_error:
        log.error(
            "yt-dlp falhou para %r: %s",
            query,
            clean_error(original_error),
        )

        reason = friendly_reason(original_error)

        try:
            # Link do YouTube bloqueado: pega o título pelo oEmbed
            # e procura a música no SoundCloud.
            if YOUTUBE_RE.search(query):
                title = clean_video_title(
                    await youtube_oembed_title(query)
                )
                log.info(
                    "YouTube bloqueado; buscando %r no SoundCloud",
                    title,
                )
                info = await search_text(title, skip_youtube=True)
                return Track(info, requester)

            # Link de outra plataforma (ex.: Spotify): lê o título
            # da página e procura uma versão reproduzível.
            async with aiohttp.ClientSession() as session:
                async with session.get(
                    query,
                    timeout=aiohttp.ClientTimeout(total=10),
                    headers={"User-Agent": "Mozilla/5.0"},
                ) as response:
                    if response.status >= 400:
                        raise ValueError("Não foi possível abrir o link.")
                    page = await response.text(errors="ignore")

            match = re.search(
                r'<meta[^>]+property=["\']og:title["\']'
                r'[^>]+content=["\']([^"\']+)',
                page,
                re.I,
            )

            if not match:
                match = re.search(
                    r'<meta[^>]+content=["\']([^"\']+)'
                    r'["\'][^>]+property=["\']og:title["\']',
                    page,
                    re.I,
                )

            if not match:
                raise ValueError("Não consegui identificar a música.")

            title = html_module.unescape(match.group(1))

            if "spotify.com" in query:
                title = clean_spotify_title(title)

            desc = re.search(
                r'<meta[^>]+property=["\']og:description["\']'
                r'[^>]+content=["\']([^"\']+)',
                page,
                re.I,
            )
            if desc and "spotify.com" in query:
                artist = html_module.unescape(desc.group(1))
                artist = artist.split("·")[0].strip()
                if artist and artist.lower() not in title.lower():
                    title = f"{artist} {title}"

            log.info("Fallback: buscando %r", title)
            info = await search_text(title)
            return Track(info, requester)

        except Exception as fallback_error:
            log.error(
                "Fallback falhou para %r: %s",
                query,
                clean_error(fallback_error),
            )
            raise ValueError(
                reason
                or (
                    "Não consegui reproduzir esse link. "
                    "Tente /play com o nome da música."
                )
            ) from fallback_error


# ---------------------------------------------------------------
# Playlists por link (YouTube, SoundCloud, Spotify)
# ---------------------------------------------------------------

_spotify_token = {"value": None, "expires": 0}


async def spotify_token():
    now = time.time()
    if (
        _spotify_token["value"]
        and now < _spotify_token["expires"] - 30
    ):
        return _spotify_token["value"]

    async with aiohttp.ClientSession() as session:
        async with session.post(
            "https://accounts.spotify.com/api/token",
            data={"grant_type": "client_credentials"},
            auth=aiohttp.BasicAuth(
                SPOTIFY_CLIENT_ID,
                SPOTIFY_CLIENT_SECRET,
            ),
            timeout=aiohttp.ClientTimeout(total=15),
        ) as response:
            if response.status != 200:
                raise ValueError(
                    "Não consegui autenticar no Spotify. "
                    "Confira o Client ID e o Client Secret."
                )
            data = await response.json()

    _spotify_token["value"] = data["access_token"]
    _spotify_token["expires"] = now + int(data.get("expires_in", 3600))
    return _spotify_token["value"]


async def expand_spotify(url, requester):
    if not (SPOTIFY_CLIENT_ID and SPOTIFY_CLIENT_SECRET):
        raise ValueError(
            "Para playlists e álbuns do Spotify, configure "
            "SPOTIFY_CLIENT_ID e SPOTIFY_CLIENT_SECRET nas variáveis "
            "do bot (https://developer.spotify.com/dashboard)."
        )

    match = re.search(
        r"spotify\.com/(?:[\w-]+/)?(playlist|album)/([A-Za-z0-9]+)",
        url,
    )
    if not match:
        raise ValueError("Link do Spotify não reconhecido.")

    kind, spotify_id = match.groups()
    headers = {"Authorization": f"Bearer {await spotify_token()}"}
    api = (
        f"https://api.spotify.com/v1/{kind}s/{spotify_id}/tracks"
        "?limit=50"
    )

    tracks = []

    async with aiohttp.ClientSession() as session:
        while api and len(tracks) < MAX_PLAYLIST_TRACKS:
            async with session.get(
                api,
                headers=headers,
                timeout=aiohttp.ClientTimeout(total=15),
            ) as response:
                if response.status in (403, 404):
                    raise ValueError(
                        "O Spotify não liberou essa playlist "
                        "(pode ser privada ou restrita)."
                    )
                if response.status != 200:
                    raise ValueError(
                        f"Erro ao consultar o Spotify "
                        f"({response.status})."
                    )
                data = await response.json()

            for item in data.get("items", []):
                track = item.get("track") if kind == "playlist" else item
                if not track or not track.get("name"):
                    continue

                artist = (track.get("artists") or [{}])[0].get("name", "")
                text = f"{artist} {track['name']}".strip()
                tracks.append(
                    Track(
                        {
                            "title": text,
                            "query": text,
                            "uploader": artist,
                            "duration": (
                                (track.get("duration_ms") or 0) // 1000
                            ),
                        },
                        requester,
                    )
                )

            api = data.get("next")

    if not tracks:
        raise ValueError("Nenhuma faixa encontrada nessa playlist.")

    label = "Playlist do Spotify" if kind == "playlist" else "Álbum do Spotify"
    return tracks[:MAX_PLAYLIST_TRACKS], label


async def expand_playlist(url, requester):
    """Transforma um link de playlist em faixas (carregadas depois)."""
    if "spotify.com" in url:
        return await expand_spotify(url, requester)

    is_youtube = bool(YOUTUBE_RE.search(url))

    if is_youtube:
        match = re.search(r"[?&]list=([\w-]+)", url)
        if match:
            url = f"https://www.youtube.com/playlist?list={match.group(1)}"

    loop = asyncio.get_running_loop()

    def extract():
        options = {
            **YDL_OPTIONS,
            "noplaylist": False,
            "extract_flat": "in_playlist",
            "playlistend": MAX_PLAYLIST_TRACKS,
        }
        with yt_dlp.YoutubeDL(options) as ydl:
            return ydl.extract_info(url, download=False)

    info = await loop.run_in_executor(None, extract)
    entries = [entry for entry in (info or {}).get("entries") or [] if entry]

    tracks = []
    for entry in entries:
        title = entry.get("title") or "Faixa"
        if title.startswith("[") and (
            "private" in title.lower() or "deleted" in title.lower()
        ):
            continue

        link = entry.get("url") or entry.get("webpage_url")
        if not link or not link.startswith("http"):
            if is_youtube and entry.get("id"):
                link = f"https://www.youtube.com/watch?v={entry['id']}"
            else:
                continue

        tracks.append(
            Track(
                {
                    "title": title,
                    "webpage_url": link,
                    "query": link,
                    "duration": entry.get("duration"),
                    "uploader": (
                        entry.get("uploader") or entry.get("channel")
                    ),
                },
                requester,
            )
        )

    if not tracks:
        raise ValueError("Nenhuma faixa encontrada nessa playlist.")

    return tracks[:MAX_PLAYLIST_TRACKS], (info or {}).get("title")


async def tracks_from_lines(lines, requester):
    """Lê vários links/nomes (um por linha) e devolve as faixas."""
    tracks = []
    notes = []

    for raw in lines:
        line = raw.strip()
        if not line:
            continue

        if line.startswith(("http://", "https://")):
            if is_playlist_url(line):
                try:
                    found, _ = await expand_playlist(line, requester)
                    tracks.extend(found)
                except Exception as error:
                    notes.append(
                        f"{line[:50]}: "
                        f"{(friendly_reason(error) or clean_error(error))[:100]}"
                    )
            else:
                tracks.append(
                    Track({"title": line[:80], "query": line}, requester)
                )
        else:
            tracks.append(
                Track({"title": line[:80], "query": line}, requester)
            )

        if len(tracks) >= MAX_QUEUE:
            break

    return tracks, notes


def add_tracks(player, tracks):
    """Coloca faixas na fila respeitando o limite. Retorna (ok, fora)."""
    free = max(MAX_QUEUE - len(player.queue), 0)
    accepted = tracks[:free]
    player.queue.extend(accepted)
    return len(accepted), len(tracks) - len(accepted)


async def kick(player):
    """Começa a tocar se estiver parado e atualiza o painel."""
    await play_next(player)
    await update_panel(player)


async def add_playlist_link(interaction, player, link):
    try:
        tracks, title = await expand_playlist(link, interaction.user)
    except Exception as error:
        log.error(
            "Falha ao carregar playlist %r: %s",
            link,
            clean_error(error),
        )
        reason = friendly_reason(error) or clean_error(error)[:250]
        await interaction.followup.send(
            f"Não consegui carregar a playlist: {reason}"
        )
        return

    added, skipped = add_tracks(player, tracks)

    message = f"📃 **{title or 'Playlist'}**: {added} faixas adicionadas à fila."
    if skipped:
        message += (
            f" ({skipped} ficaram de fora: limite de {MAX_QUEUE} na fila.)"
        )

    await interaction.followup.send(message)
    await kick(player)


def track_query(track):
    return track.query or track.url or track.title


# ---------------------------------------------------------------
# Playlists salvas pelo bot (SQLite)
# ---------------------------------------------------------------

def db():
    con = sqlite3.connect(DB_PATH)
    con.execute(
        "CREATE TABLE IF NOT EXISTS playlists ("
        "id INTEGER PRIMARY KEY AUTOINCREMENT, "
        "guild_id INTEGER NOT NULL, "
        "name TEXT NOT NULL COLLATE NOCASE, "
        "owner_id INTEGER NOT NULL, "
        "UNIQUE(guild_id, name))"
    )
    con.execute(
        "CREATE TABLE IF NOT EXISTS playlist_items ("
        "playlist_id INTEGER NOT NULL, "
        "position INTEGER NOT NULL, "
        "title TEXT, "
        "query TEXT NOT NULL)"
    )
    return con


def add_to_playlist(guild_id, name, owner_id, items):
    """Cria a playlist (ou adiciona nela). Retorna (criada, total, novas)."""
    con = db()
    try:
        row = con.execute(
            "SELECT id FROM playlists WHERE guild_id=? AND name=?",
            (guild_id, name),
        ).fetchone()

        created = row is None
        if created:
            cursor = con.execute(
                "INSERT INTO playlists (guild_id, name, owner_id) "
                "VALUES (?, ?, ?)",
                (guild_id, name, owner_id),
            )
            playlist_id = cursor.lastrowid
        else:
            playlist_id = row[0]

        last = con.execute(
            "SELECT COALESCE(MAX(position), 0) FROM playlist_items "
            "WHERE playlist_id=?",
            (playlist_id,),
        ).fetchone()[0]
        count = con.execute(
            "SELECT COUNT(*) FROM playlist_items WHERE playlist_id=?",
            (playlist_id,),
        ).fetchone()[0]

        items = items[: max(MAX_SAVED_TRACKS - count, 0)]

        for index, (title, query) in enumerate(items, 1):
            con.execute(
                "INSERT INTO playlist_items "
                "(playlist_id, position, title, query) "
                "VALUES (?, ?, ?, ?)",
                (playlist_id, last + index, title, query),
            )

        con.commit()
        return created, count + len(items), len(items)
    finally:
        con.close()


def get_playlist(guild_id, name):
    con = db()
    try:
        return con.execute(
            "SELECT id, name, owner_id FROM playlists "
            "WHERE guild_id=? AND name=?",
            (guild_id, name),
        ).fetchone()
    finally:
        con.close()


def get_items(playlist_id):
    con = db()
    try:
        return con.execute(
            "SELECT title, query FROM playlist_items "
            "WHERE playlist_id=? ORDER BY position",
            (playlist_id,),
        ).fetchall()
    finally:
        con.close()


def list_playlists(guild_id):
    con = db()
    try:
        return con.execute(
            "SELECT p.name, COUNT(i.playlist_id), p.owner_id "
            "FROM playlists p "
            "LEFT JOIN playlist_items i ON i.playlist_id = p.id "
            "WHERE p.guild_id=? GROUP BY p.id ORDER BY p.name",
            (guild_id,),
        ).fetchall()
    finally:
        con.close()


def remove_playlist_item(playlist_id, number):
    """Remove a faixa de número `number` (1, 2, 3...). Retorna o título."""
    con = db()
    try:
        rows = con.execute(
            "SELECT rowid, title FROM playlist_items "
            "WHERE playlist_id=? ORDER BY position",
            (playlist_id,),
        ).fetchall()

        if not 1 <= number <= len(rows):
            return None

        con.execute(
            "DELETE FROM playlist_items WHERE rowid=?",
            (rows[number - 1][0],),
        )
        con.commit()
        return rows[number - 1][1]
    finally:
        con.close()


def delete_playlist(playlist_id):
    con = db()
    try:
        con.execute(
            "DELETE FROM playlist_items WHERE playlist_id=?",
            (playlist_id,),
        )
        con.execute("DELETE FROM playlists WHERE id=?", (playlist_id,))
        con.commit()
    finally:
        con.close()


def can_manage(interaction, owner_id):
    """Quem criou a playlist ou quem tem 'Gerenciar Servidor'."""
    perms = getattr(interaction.user, "guild_permissions", None)
    return interaction.user.id == owner_id or bool(
        perms and perms.manage_guild
    )


def saved_message(name, created, total, added):
    action = "criada" if created else "atualizada"
    if added == 0:
        return (
            f"Playlist **{name}** {action}, mas nenhuma faixa foi "
            f"adicionada (limite de {MAX_SAVED_TRACKS} faixas)."
        )
    return (
        f"✅ Playlist **{name}** {action}: +{added} faixas "
        f"(total: {total})."
    )


# ---------------------------------------------------------------
# Painel e reprodução
# ---------------------------------------------------------------

def make_embed(player):
    embed = discord.Embed(
        title="🐱 NEKO MUSIC",
        color=discord.Color.from_rgb(119, 86, 255),
    )

    if player.current:
        track = player.current
        title = discord.utils.escape_markdown(track.title)

        if track.url:
            embed.description = f"🎵 **[{title}]({track.url})**"
        else:
            embed.description = f"🎵 **{title}**"

        embed.add_field(
            name="🎤 Artista",
            value=track.artist[:100],
            inline=True,
        )
        embed.add_field(
            name="⏱️ Duração",
            value=format_time(track.duration),
            inline=True,
        )
        embed.add_field(
            name="👤 Pedido por",
            value=track.requester.mention,
            inline=True,
        )

        if track.thumbnail:
            embed.set_thumbnail(url=track.thumbnail)
    else:
        embed.description = "Nenhuma música está tocando."

    embed.set_footer(
        text=(
            f"Volume: {int(player.volume * 100)}% | "
            f"Loop: {'Ligado' if player.loop else 'Desligado'} | "
            f"Fila: {len(player.queue)}"
        )
    )

    return embed


async def update_panel(player):
    if not player.channel:
        return

    view = MusicPanel(player)
    embed = make_embed(player)

    try:
        if player.panel:
            await player.panel.edit(embed=embed, view=view)
        else:
            player.panel = await player.channel.send(
                embed=embed,
                view=view,
            )
    except discord.HTTPException:
        player.panel = None


async def play_next(player):
    async with player.lock:
        while True:
            if not player.voice or not player.voice.is_connected():
                return

            if player.voice.is_playing() or player.voice.is_paused():
                return

            if player.loop and player.current:
                track = player.current
            elif player.queue:
                track = player.queue.popleft()
                player.current = track
            else:
                player.current = None
                await update_panel(player)
                return

            try:
                # Faixas de playlist são resolvidas só agora.
                await track.ensure_stream()
                break
            except Exception as error:
                log.error(
                    "Não consegui carregar %r: %s",
                    track.title,
                    clean_error(error),
                )
                player.current = None

                if player.channel:
                    reason = (
                        friendly_reason(error) or clean_error(error)
                    )[:200]
                    try:
                        await player.channel.send(
                            f"⚠️ Pulei **{track.title[:80]}**: {reason}"
                        )
                    except discord.HTTPException:
                        pass

        source = discord.PCMVolumeTransformer(
            discord.FFmpegPCMAudio(
                track.stream,
                **FFMPEG_OPTIONS,
            ),
            volume=player.volume,
        )

        def after_play(error):
            if error:
                log.error("Erro na reprodução: %s", error)

            asyncio.run_coroutine_threadsafe(
                play_next(player),
                bot.loop,
            )

        player.voice.play(source, after=after_play)
        await update_panel(player)


async def connect_voice(interaction):
    if not interaction.user.voice:
        await interaction.followup.send(
            "Entre em um canal de voz primeiro.",
            ephemeral=True,
        )
        return None

    player = get_player(interaction.guild_id)
    channel = interaction.user.voice.channel

    if player.voice and player.voice.is_connected():
        if player.voice.channel != channel:
            await player.voice.move_to(channel)
    else:
        player.voice = await channel.connect()

    player.channel = interaction.channel
    return player


# ---------------------------------------------------------------
# Janelas (modais) para vários links e para salvar playlists
# ---------------------------------------------------------------

class MultiAddModal(discord.ui.Modal, title="Adicionar várias músicas"):
    linhas = discord.ui.TextInput(
        label="Um link ou nome de música por linha",
        style=discord.TextStyle.paragraph,
        placeholder=(
            "https://youtu.be/...\n"
            "https://soundcloud.com/...\n"
            "nome da música\n"
            "(também aceita link de playlist)"
        ),
        max_length=4000,
        required=True,
    )

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(thinking=True, ephemeral=True)

        player = await connect_voice(interaction)
        if not player:
            return

        tracks, notes = await tracks_from_lines(
            str(self.linhas).splitlines(),
            interaction.user,
        )

        if not tracks:
            await interaction.followup.send(
                "Não encontrei nenhum link ou nome válido.",
                ephemeral=True,
            )
            return

        added, skipped = add_tracks(player, tracks)

        message = f"➕ {added} faixas adicionadas à fila."
        if skipped:
            message += f" ({skipped} ficaram de fora: fila cheia.)"
        if notes:
            message += "\n⚠️ " + "\n⚠️ ".join(notes[:5])

        await interaction.followup.send(message[:1900], ephemeral=True)
        await kick(player)


class SaveQueueModal(discord.ui.Modal, title="Salvar fila como playlist"):
    nome = discord.ui.TextInput(
        label="Nome da playlist",
        max_length=50,
        required=True,
    )

    def __init__(self, player):
        super().__init__()
        self.player = player

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)

        tracks = (
            [self.player.current] if self.player.current else []
        ) + list(self.player.queue)

        if not tracks:
            await interaction.followup.send(
                "Não há músicas para salvar.",
                ephemeral=True,
            )
            return

        items = [(t.title, track_query(t)) for t in tracks]
        name = str(self.nome).strip()

        created, total, added = add_to_playlist(
            interaction.guild_id,
            name,
            interaction.user.id,
            items,
        )
        await interaction.followup.send(
            saved_message(name, created, total, added),
            ephemeral=True,
        )


class CreateListModal(discord.ui.Modal, title="Criar / adicionar à playlist"):
    linhas = discord.ui.TextInput(
        label="Um link ou nome de música por linha",
        style=discord.TextStyle.paragraph,
        placeholder=(
            "https://youtu.be/...\n"
            "nome da música\n"
            "(também aceita link de playlist)"
        ),
        max_length=4000,
        required=True,
    )

    def __init__(self, nome):
        super().__init__()
        self.nome = nome

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)

        tracks, notes = await tracks_from_lines(
            str(self.linhas).splitlines(),
            interaction.user,
        )

        if not tracks:
            await interaction.followup.send(
                "Não encontrei nenhum link ou nome válido.",
                ephemeral=True,
            )
            return

        items = [(t.title, track_query(t)) for t in tracks]
        created, total, added = add_to_playlist(
            interaction.guild_id,
            self.nome,
            interaction.user.id,
            items,
        )

        message = saved_message(self.nome, created, total, added)
        if notes:
            message += "\n⚠️ " + "\n⚠️ ".join(notes[:5])

        await interaction.followup.send(message[:1900], ephemeral=True)


class MusicPanel(discord.ui.View):
    def __init__(self, player):
        super().__init__(timeout=None)
        self.player = player

    @discord.ui.button(
        label="🔉 Volume -",
        style=discord.ButtonStyle.secondary,
        row=0,
    )
    async def volume_down(self, interaction, button):
        p = self.player
        p.volume = max(0.0, p.volume - 0.1)

        if p.voice and p.voice.source:
            p.voice.source.volume = p.volume

        await interaction.response.send_message(
            f"Volume: {int(p.volume * 100)}%",
            ephemeral=True,
        )
        await update_panel(p)

    @discord.ui.button(
        label="⏮ Anterior",
        style=discord.ButtonStyle.secondary,
        row=0,
    )
    async def previous(self, interaction, button):
        p = self.player

        if p.current:
            p.queue.appendleft(p.current)
            if p.voice:
                p.voice.stop()

        await interaction.response.send_message(
            "Voltando à faixa anterior disponível.",
            ephemeral=True,
        )

    @discord.ui.button(
        label="⏯ Pausar/Continuar",
        style=discord.ButtonStyle.primary,
        row=0,
    )
    async def pause(self, interaction, button):
        p = self.player

        if not p.voice:
            await interaction.response.send_message(
                "O bot não está conectado.",
                ephemeral=True,
            )
            return

        if p.voice.is_playing():
            p.voice.pause()
            message = "Reprodução pausada."
        elif p.voice.is_paused():
            p.voice.resume()
            message = "Reprodução retomada."
        else:
            message = "Nenhuma música está tocando."

        await interaction.response.send_message(
            message,
            ephemeral=True,
        )

    @discord.ui.button(
        label="⏭ Pular",
        style=discord.ButtonStyle.secondary,
        row=0,
    )
    async def skip(self, interaction, button):
        p = self.player

        if p.voice and (
            p.voice.is_playing() or p.voice.is_paused()
        ):
            p.voice.stop()
            message = "Pulando faixa."
        else:
            message = "Nenhuma música está tocando."

        await interaction.response.send_message(
            message,
            ephemeral=True,
        )

    @discord.ui.button(
        label="🔊 Volume +",
        style=discord.ButtonStyle.secondary,
        row=0,
    )
    async def volume_up(self, interaction, button):
        p = self.player
        p.volume = min(1.0, p.volume + 0.1)

        if p.voice and p.voice.source:
            p.voice.source.volume = p.volume

        await interaction.response.send_message(
            f"Volume: {int(p.volume * 100)}%",
            ephemeral=True,
        )
        await update_panel(p)

    @discord.ui.button(
        label="🔀 Embaralhar",
        style=discord.ButtonStyle.secondary,
        row=1,
    )
    async def shuffle(self, interaction, button):
        p = self.player
        p.shuffle = not p.shuffle

        if p.shuffle:
            tracks = list(p.queue)
            random.shuffle(tracks)
            p.queue = deque(tracks)

        await interaction.response.send_message(
            f"Embaralhamento {'ativado' if p.shuffle else 'desativado'}.",
            ephemeral=True,
        )
        await update_panel(p)

    @discord.ui.button(
        label="🔁 Repetir",
        style=discord.ButtonStyle.secondary,
        row=1,
    )
    async def repeat(self, interaction, button):
        p = self.player
        p.loop = not p.loop

        await interaction.response.send_message(
            f"Repetição {'ativada' if p.loop else 'desativada'}.",
            ephemeral=True,
        )
        await update_panel(p)

    @discord.ui.button(
        label="⏹ Parar",
        style=discord.ButtonStyle.danger,
        row=1,
    )
    async def stop_music(self, interaction, button):
        p = self.player
        p.queue.clear()
        p.loop = False
        p.current = None

        if p.voice:
            p.voice.stop()

        await interaction.response.send_message(
            "Reprodução parada e fila limpa.",
            ephemeral=True,
        )
        await update_panel(p)

    @discord.ui.button(
        label="▶ AutoPlay",
        style=discord.ButtonStyle.secondary,
        row=1,
    )
    async def autoplay(self, interaction, button):
        p = self.player
        p.autoplay = not p.autoplay

        await interaction.response.send_message(
            f"AutoPlay {'ativado' if p.autoplay else 'desativado'}. "
            "A busca automática de recomendações ainda precisa "
            "de uma fonte específica.",
            ephemeral=True,
        )

    @discord.ui.button(
        label="📃 Fila",
        style=discord.ButtonStyle.secondary,
        row=1,
    )
    async def show_queue(self, interaction, button):
        p = self.player

        if not p.queue:
            message = "A fila está vazia."
        else:
            message = "\n".join(
                f"{i}. {track.title[:80]} "
                f"({format_time(track.duration)})"
                for i, track in enumerate(
                    list(p.queue)[:15], 1
                )
            )

        await interaction.response.send_message(
            message[:1900],
            ephemeral=True,
        )

    @discord.ui.button(
        label="🗑 Limpar fila",
        style=discord.ButtonStyle.danger,
        row=2,
    )
    async def clear_queue(self, interaction, button):
        p = self.player
        removed = len(p.queue)
        p.queue.clear()

        await interaction.response.send_message(
            f"Fila limpa ({removed} faixas removidas). "
            "A música atual continua tocando.",
            ephemeral=True,
        )
        await update_panel(p)

    @discord.ui.button(
        label="➕ Adicionar várias",
        style=discord.ButtonStyle.success,
        row=2,
    )
    async def add_many(self, interaction, button):
        await interaction.response.send_modal(MultiAddModal())

    @discord.ui.button(
        label="💾 Salvar fila",
        style=discord.ButtonStyle.secondary,
        row=2,
    )
    async def save_queue(self, interaction, button):
        await interaction.response.send_modal(
            SaveQueueModal(self.player)
        )


@bot.event
async def on_ready():
    try:
        synced = await bot.tree.sync()
        log.info("Neko conectado: %s", bot.user)
        log.info("%s comandos sincronizados.", len(synced))
        log.info("yt-dlp versão: %s", yt_dlp.version.__version__)
    except Exception:
        log.exception("Erro ao sincronizar comandos.")


@bot.tree.command(
    name="play",
    description="Toca uma música pelo nome ou link.",
)
@app_commands.describe(busca="Nome da música ou link")
async def play(interaction: discord.Interaction, busca: str):
    await interaction.response.defer(thinking=True)

    player = await connect_voice(interaction)
    if not player:
        return

    # Link de playlist inteira: carrega todas as faixas.
    if is_playlist_url(busca):
        await add_playlist_link(interaction, player, busca)
        return

    try:
        track = await resolve_track(busca, interaction.user)
    except Exception as error:
        await interaction.followup.send(
            f"Não consegui encontrar a música: {str(error)[:300]}"
        )
        return

    if player.current or (
        player.voice and (
            player.voice.is_playing()
            or player.voice.is_paused()
        )
    ):
        if len(player.queue) >= MAX_QUEUE:
            await interaction.followup.send(
                "A fila atingiu o limite."
            )
            return

        player.queue.append(track)
        await interaction.followup.send(
            f"➕ Adicionada à fila: **{track.title}**"
        )
        await update_panel(player)
    else:
        player.queue.append(track)
        await interaction.followup.send(
            f"🎵 Preparando: **{track.title}**"
        )
        await play_next(player)


@bot.tree.command(
    name="playlist",
    description="Adiciona uma playlist inteira por link.",
)
@app_commands.describe(
    link="Link da playlist (YouTube, SoundCloud ou Spotify)"
)
async def playlist_link_command(
    interaction: discord.Interaction,
    link: str,
):
    await interaction.response.defer(thinking=True)

    if not link.startswith(("http://", "https://")):
        await interaction.followup.send(
            "Envie o link completo da playlist (começando com https://)."
        )
        return

    player = await connect_voice(interaction)
    if not player:
        return

    await add_playlist_link(interaction, player, link)


@bot.tree.command(
    name="adicionar_varios",
    description="Adiciona vários links ou nomes de uma vez.",
)
async def add_many_command(interaction: discord.Interaction):
    await interaction.response.send_modal(MultiAddModal())


@bot.tree.command(
    name="limpar",
    description="Limpa a fila (a música atual continua).",
)
async def clear_command(interaction: discord.Interaction):
    p = get_player(interaction.guild_id)
    removed = len(p.queue)
    p.queue.clear()

    await interaction.response.send_message(
        f"Fila limpa ({removed} faixas removidas)."
    )
    await update_panel(p)


@bot.tree.command(
    name="painel",
    description="Envia o painel de música.",
)
async def panel_command(interaction: discord.Interaction):
    player = get_player(interaction.guild_id)
    player.channel = interaction.channel

    await interaction.response.defer(ephemeral=True)
    await update_panel(player)
    await interaction.followup.send(
        "Painel atualizado.",
        ephemeral=True,
    )


@bot.tree.command(
    name="fila",
    description="Mostra a fila de músicas.",
)
async def queue_command(interaction: discord.Interaction):
    p = get_player(interaction.guild_id)

    if not p.queue:
        await interaction.response.send_message(
            "A fila está vazia.",
            ephemeral=True,
        )
        return

    text = "\n".join(
        f"{i}. {track.title[:80]}"
        for i, track in enumerate(list(p.queue)[:20], 1)
    )

    await interaction.response.send_message(
        text[:1900],
        ephemeral=True,
    )


@bot.tree.command(name="pular", description="Pula a música atual.")
async def skip_command(interaction: discord.Interaction):
    p = get_player(interaction.guild_id)

    if p.voice and (
        p.voice.is_playing() or p.voice.is_paused()
    ):
        p.voice.stop()
        await interaction.response.send_message("Faixa pulada.")
    else:
        await interaction.response.send_message(
            "Nenhuma música está tocando.",
            ephemeral=True,
        )


@bot.tree.command(
    name="parar",
    description="Para a música e limpa a fila.",
)
async def stop_command(interaction: discord.Interaction):
    p = get_player(interaction.guild_id)
    p.queue.clear()
    p.current = None
    p.loop = False

    if p.voice:
        p.voice.stop()

    await interaction.response.send_message(
        "Reprodução parada e fila limpa."
    )
    await update_panel(p)


@bot.tree.command(
    name="sair",
    description="Desconecta do canal de voz.",
)
async def leave_command(interaction: discord.Interaction):
    p = get_player(interaction.guild_id)

    if p.voice and p.voice.is_connected():
        await p.voice.disconnect()

    p.voice = None
    p.current = None
    p.queue.clear()

    await interaction.response.send_message(
        "Neko saiu do canal de voz."
    )


@bot.tree.command(
    name="letra",
    description="Pesquisa a letra da música atual ou de outra faixa.",
)
@app_commands.describe(
    musica="Nome da música. Deixe vazio para a faixa atual."
)
async def lyrics_command(
    interaction: discord.Interaction,
    musica: str = None,
):
    await interaction.response.defer(thinking=True)

    if not musica:
        p = get_player(interaction.guild_id)
        if not p.current:
            await interaction.followup.send(
                "Não há música atual. Informe o nome da faixa."
            )
            return
        musica = p.current.title

    url = f"https://lrclib.net/api/search?q={quote(musica)}"

    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(
                url,
                timeout=aiohttp.ClientTimeout(total=15),
            ) as response:
                if response.status != 200:
                    raise ValueError("Serviço de letras indisponível.")
                results = await response.json()

        item = next(
            (result for result in results
             if result.get("plainLyrics")),
            None,
        )

        if not item:
            await interaction.followup.send(
                "Não encontrei uma letra disponível para essa faixa."
            )
            return

        lyrics = item["plainLyrics"]
        heading = (
            f"**{item.get('trackName', musica)}**"
            f" • {item.get('artistName', 'Artista desconhecido')}\n"
        )

        # Discord limita cada mensagem a 2000 caracteres.
        await interaction.followup.send(
            heading + lyrics[:1900]
        )

    except Exception:
        await interaction.followup.send(
            "Não consegui consultar as letras neste momento."
        )


# ---------------------------------------------------------------
# Playlists criadas pelo bot: /lista ...
# ---------------------------------------------------------------

lista = app_commands.Group(
    name="lista",
    description="Playlists salvas do servidor.",
    guild_only=True,
)
bot.tree.add_command(lista)


async def playlist_name_autocomplete(
    interaction: discord.Interaction,
    current: str,
):
    rows = list_playlists(interaction.guild_id)
    return [
        app_commands.Choice(name=name, value=name)
        for name, _, _ in rows
        if current.lower() in name.lower()
    ][:25]


@lista.command(
    name="criar",
    description="Cria uma playlist ou adiciona faixas a uma existente.",
)
@app_commands.describe(nome="Nome da playlist")
async def lista_create(
    interaction: discord.Interaction,
    nome: str,
):
    nome = nome.strip()[:50]
    if not nome:
        await interaction.response.send_message(
            "Informe um nome para a playlist.",
            ephemeral=True,
        )
        return

    await interaction.response.send_modal(CreateListModal(nome))


@lista_create.autocomplete("nome")
async def lista_create_autocomplete(interaction, current):
    return await playlist_name_autocomplete(interaction, current)


@lista.command(
    name="salvar_fila",
    description="Salva a fila atual como playlist.",
)
@app_commands.describe(nome="Nome da playlist")
async def lista_save_queue(
    interaction: discord.Interaction,
    nome: str,
):
    p = get_player(interaction.guild_id)
    tracks = ([p.current] if p.current else []) + list(p.queue)

    if not tracks:
        await interaction.response.send_message(
            "Não há músicas para salvar.",
            ephemeral=True,
        )
        return

    nome = nome.strip()[:50]
    items = [(t.title, track_query(t)) for t in tracks]
    created, total, added = add_to_playlist(
        interaction.guild_id,
        nome,
        interaction.user.id,
        items,
    )

    await interaction.response.send_message(
        saved_message(nome, created, total, added),
        ephemeral=True,
    )


@lista_save_queue.autocomplete("nome")
async def lista_save_autocomplete(interaction, current):
    return await playlist_name_autocomplete(interaction, current)


@lista.command(
    name="tocar",
    description="Coloca uma playlist salva na fila.",
)
@app_commands.describe(
    nome="Nome da playlist",
    embaralhar="Embaralhar as faixas antes de adicionar",
)
async def lista_play(
    interaction: discord.Interaction,
    nome: str,
    embaralhar: bool = False,
):
    await interaction.response.defer(thinking=True)

    playlist = get_playlist(interaction.guild_id, nome)
    if not playlist:
        await interaction.followup.send(
            f"Não encontrei a playlist **{nome}**. "
            "Veja as existentes com `/lista ver`."
        )
        return

    items = get_items(playlist[0])
    if not items:
        await interaction.followup.send("Essa playlist está vazia.")
        return

    player = await connect_voice(interaction)
    if not player:
        return

    tracks = [
        Track({"title": title, "query": query}, interaction.user)
        for title, query in items
    ]
    if embaralhar:
        random.shuffle(tracks)

    added, skipped = add_tracks(player, tracks)

    message = f"📃 **{playlist[1]}**: {added} faixas adicionadas à fila."
    if skipped:
        message += f" ({skipped} ficaram de fora: fila cheia.)"

    await interaction.followup.send(message)
    await kick(player)


@lista_play.autocomplete("nome")
async def lista_play_autocomplete(interaction, current):
    return await playlist_name_autocomplete(interaction, current)


@lista.command(
    name="ver",
    description="Mostra as playlists salvas ou as faixas de uma.",
)
@app_commands.describe(
    nome="Nome da playlist (deixe vazio para listar todas)"
)
async def lista_view(
    interaction: discord.Interaction,
    nome: str = None,
):
    if not nome:
        rows = list_playlists(interaction.guild_id)
        if not rows:
            await interaction.response.send_message(
                "Nenhuma playlist salva. Crie com `/lista criar`.",
                ephemeral=True,
            )
            return

        text = "\n".join(
            f"• **{name}** ({count} faixas)"
            for name, count, _ in rows
        )
        await interaction.response.send_message(
            text[:1900],
            ephemeral=True,
        )
        return

    playlist = get_playlist(interaction.guild_id, nome)
    if not playlist:
        await interaction.response.send_message(
            f"Não encontrei a playlist **{nome}**.",
            ephemeral=True,
        )
        return

    items = get_items(playlist[0])
    if not items:
        await interaction.response.send_message(
            "Essa playlist está vazia.",
            ephemeral=True,
        )
        return

    text = f"**{playlist[1]}** ({len(items)} faixas)\n" + "\n".join(
        f"{i}. {(title or query)[:80]}"
        for i, (title, query) in enumerate(items[:25], 1)
    )
    if len(items) > 25:
        text += f"\n... e mais {len(items) - 25}."

    await interaction.response.send_message(
        text[:1900],
        ephemeral=True,
    )


@lista_view.autocomplete("nome")
async def lista_view_autocomplete(interaction, current):
    return await playlist_name_autocomplete(interaction, current)


@lista.command(
    name="remover_faixa",
    description="Remove uma faixa de uma playlist salva.",
)
@app_commands.describe(
    nome="Nome da playlist",
    numero="Número da faixa (veja em /lista ver)",
)
async def lista_remove_track(
    interaction: discord.Interaction,
    nome: str,
    numero: int,
):
    playlist = get_playlist(interaction.guild_id, nome)
    if not playlist:
        await interaction.response.send_message(
            f"Não encontrei a playlist **{nome}**.",
            ephemeral=True,
        )
        return

    if not can_manage(interaction, playlist[2]):
        await interaction.response.send_message(
            "Só quem criou a playlist (ou quem tem Gerenciar "
            "Servidor) pode remover faixas.",
            ephemeral=True,
        )
        return

    removed = remove_playlist_item(playlist[0], numero)
    if removed is None:
        await interaction.response.send_message(
            "Número de faixa inválido.",
            ephemeral=True,
        )
        return

    await interaction.response.send_message(
        f"🗑 Removida: **{(removed or 'faixa')[:80]}**",
        ephemeral=True,
    )


@lista_remove_track.autocomplete("nome")
async def lista_remove_track_autocomplete(interaction, current):
    return await playlist_name_autocomplete(interaction, current)


@lista.command(
    name="apagar",
    description="Apaga uma playlist salva inteira.",
)
@app_commands.describe(nome="Nome da playlist")
async def lista_delete(
    interaction: discord.Interaction,
    nome: str,
):
    playlist = get_playlist(interaction.guild_id, nome)
    if not playlist:
        await interaction.response.send_message(
            f"Não encontrei a playlist **{nome}**.",
            ephemeral=True,
        )
        return

    if not can_manage(interaction, playlist[2]):
        await interaction.response.send_message(
            "Só quem criou a playlist (ou quem tem Gerenciar "
            "Servidor) pode apagá-la.",
            ephemeral=True,
        )
        return

    delete_playlist(playlist[0])
    await interaction.response.send_message(
        f"🗑 Playlist **{playlist[1]}** apagada.",
        ephemeral=True,
    )


@lista_delete.autocomplete("nome")
async def lista_delete_autocomplete(interaction, current):
    return await playlist_name_autocomplete(interaction, current)


# ---------------------------------------------------------------
# Perfil do bot: avatar e banner (somente o dono do bot)
# ---------------------------------------------------------------

async def owner_only(interaction):
    """Libera o comando apenas para o dono do bot."""
    if await bot.is_owner(interaction.user):
        return True

    await interaction.response.send_message(
        "Apenas o dono do bot pode usar este comando.",
        ephemeral=True,
    )
    return False


async def get_image_bytes(arquivo, link):
    """Lê a imagem/GIF enviada como anexo ou baixada de um link."""
    if arquivo:
        kind = (arquivo.content_type or "").split(";")[0].lower()
        if kind not in IMAGE_TYPES:
            raise ValueError("Envie uma imagem PNG, JPG, GIF ou WEBP.")
        if arquivo.size > MAX_IMAGE_BYTES:
            raise ValueError("A imagem passa de 10 MB.")
        return await arquivo.read()

    if link:
        if not link.startswith(("http://", "https://")):
            raise ValueError(
                "O link precisa começar com http:// ou https://."
            )

        async with aiohttp.ClientSession() as session:
            async with session.get(
                link,
                timeout=aiohttp.ClientTimeout(total=15),
                headers={"User-Agent": "Mozilla/5.0"},
            ) as response:
                if response.status != 200:
                    raise ValueError(
                        "Não consegui baixar a imagem desse link."
                    )

                kind = (
                    response.headers.get("Content-Type", "")
                    .split(";")[0]
                    .lower()
                )
                if kind not in IMAGE_TYPES:
                    raise ValueError(
                        "O link não aponta direto para uma imagem "
                        "PNG, JPG, GIF ou WEBP."
                    )

                data = await response.content.read(MAX_IMAGE_BYTES + 1)
                if len(data) > MAX_IMAGE_BYTES:
                    raise ValueError("A imagem passa de 10 MB.")
                return data

    raise ValueError(
        "Envie uma imagem/GIF no campo `arquivo` ou informe um `link`."
    )


async def update_profile(interaction, field, value, success_message):
    """Aplica a mudança no perfil do bot e responde ao dono."""
    try:
        await bot.user.edit(**{field: value})
    except TypeError:
        message = (
            "Sua versão do discord.py não suporta essa alteração. "
            "Atualize com: pip install -U discord.py"
        )
    except discord.HTTPException as error:
        text = error.text or str(error)
        log.error(
            "Falha ao alterar %s (status %s, código %s): %s",
            field,
            error.status,
            error.code,
            text,
        )

        if error.status == 429 or "too fast" in text.lower():
            message = (
                "O Discord limitou as mudanças de perfil. "
                "Aguarde um pouco e tente de novo.\n"
                f"Resposta do Discord: {text[:200]}"
            )
        else:
            message = f"O Discord recusou a alteração: {text[:300]}"
    else:
        message = success_message

    await interaction.followup.send(message, ephemeral=True)


@bot.tree.command(
    name="avatar_definir",
    description="Define a foto/GIF de avatar do bot (só o dono).",
)
@app_commands.describe(
    arquivo="Imagem ou GIF para o avatar",
    link="Ou link direto para a imagem/GIF",
)
async def avatar_set_command(
    interaction: discord.Interaction,
    arquivo: discord.Attachment = None,
    link: str = None,
):
    if not await owner_only(interaction):
        return

    await interaction.response.defer(ephemeral=True)

    try:
        data = await get_image_bytes(arquivo, link)
    except Exception as error:
        await interaction.followup.send(str(error)[:300], ephemeral=True)
        return

    await update_profile(
        interaction,
        "avatar",
        data,
        "✅ Avatar atualizado.",
    )


@bot.tree.command(
    name="avatar_remover",
    description="Remove o avatar do bot (só o dono).",
)
async def avatar_remove_command(interaction: discord.Interaction):
    if not await owner_only(interaction):
        return

    await interaction.response.defer(ephemeral=True)
    await update_profile(
        interaction,
        "avatar",
        None,
        "✅ Avatar removido.",
    )


@bot.tree.command(
    name="banner_definir",
    description="Define a foto/GIF do banner do perfil do bot (só o dono).",
)
@app_commands.describe(
    arquivo="Imagem ou GIF para o banner",
    link="Ou link direto para a imagem/GIF",
)
async def banner_set_command(
    interaction: discord.Interaction,
    arquivo: discord.Attachment = None,
    link: str = None,
):
    if not await owner_only(interaction):
        return

    await interaction.response.defer(ephemeral=True)

    try:
        data = await get_image_bytes(arquivo, link)
    except Exception as error:
        await interaction.followup.send(str(error)[:300], ephemeral=True)
        return

    await update_profile(
        interaction,
        "banner",
        data,
        "✅ Banner atualizado.",
    )


@bot.tree.command(
    name="banner_remover",
    description="Remove o banner do perfil do bot (só o dono).",
)
async def banner_remove_command(interaction: discord.Interaction):
    if not await owner_only(interaction):
        return

    await interaction.response.defer(ephemeral=True)
    await update_profile(
        interaction,
        "banner",
        None,
        "✅ Banner removido.",
    )


@bot.tree.command(
    name="ajuda",
    description="Mostra os comandos do Neko.",
)
async def help_command(interaction: discord.Interaction):
    embed = discord.Embed(
        title="🐱 Neko • Ajuda",
        description=(
            "**Música**\n"
            "`/play busca` • Uma música por nome ou link\n"
            "`/playlist link` • Playlist inteira por link\n"
            "`/adicionar_varios` • Vários links/nomes de uma vez\n"
            "`/painel` • Mostra o painel com botões\n"
            "`/fila` • Mostra a fila\n"
            "`/limpar` • Limpa a fila\n"
            "`/pular` • Avança a faixa\n"
            "`/parar` • Para e limpa tudo\n"
            "`/sair` • Desconecta do canal\n"
            "`/letra [musica]` • Pesquisa letras\n"
            "\n**Playlists salvas**\n"
            "`/lista criar nome` • Cria ou adiciona faixas\n"
            "`/lista salvar_fila nome` • Salva a fila atual\n"
            "`/lista tocar nome` • Toca uma playlist salva\n"
            "`/lista ver [nome]` • Lista playlists ou faixas\n"
            "`/lista remover_faixa nome numero` • Tira uma faixa\n"
            "`/lista apagar nome` • Apaga a playlist\n"
            "\n**Somente o dono do bot**\n"
            "`/avatar_definir` • Define o avatar (foto/GIF)\n"
            "`/avatar_remover` • Remove o avatar\n"
            "`/banner_definir` • Define o banner (foto/GIF)\n"
            "`/banner_remover` • Remove o banner\n"
        ),
        color=discord.Color.from_rgb(119, 86, 255),
    )

    await interaction.response.send_message(
        embed=embed,
        ephemeral=True,
    )


if not TOKEN:
    raise RuntimeError(
        "Configure a variável de ambiente DISCORD_TOKEN."
    )

bot.run(TOKEN)
