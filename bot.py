import os
import re
import json
import time
import base64
import sqlite3
import html as html_module
import asyncio
import random
import logging
import unicodedata
from collections import deque
from urllib.parse import quote

import aiohttp
import discord
from discord import app_commands
from discord.ext import commands
import yt_dlp
from dotenv import load_dotenv

try:
    # Já vem instalado junto com o yt-dlp; usado só para ler a duração.
    from mutagen import File as MutagenFile
except ImportError:
    MutagenFile = None

load_dotenv()

TOKEN = os.getenv("DISCORD_TOKEN")
MAX_QUEUE = 100             # máximo de faixas na fila
MAX_PLAYLIST_TRACKS = 100   # máximo carregado de uma playlist por link
MAX_SAVED_TRACKS = 200      # máximo de faixas em uma playlist salva
MAX_BLOCKS = 10             # máximo de playlists no rodízio
MAX_CONSECUTIVE_FAILURES = 10  # para de tentar após tantas falhas seguidas
SOUNDCLOUD_TRIES = 4        # quantos resultados do SoundCloud testar

# Banco das playlists criadas pelo bot (SQLite, arquivo local).
DB_PATH = os.getenv("PLAYLIST_DB", "playlists.db")

# Pasta dos arquivos de música (enviados com /musica_adicionar).
# Por padrão usa /data/musicas quando a pasta /data existe (costuma
# ser persistente em hospedagens); senão, "musicas" ao lado do bot.py.
MUSIC_DIR = os.getenv("MUSIC_DIR") or (
    "/data/musicas"
    if os.path.isdir("/data") and os.access("/data", os.W_OK)
    else "musicas"
)
AUDIO_EXTS = (".mp3", ".ogg", ".wav", ".flac", ".m4a", ".opus", ".aac")
MAX_AUDIO_BYTES = 100 * 1024 * 1024  # 100 MB por arquivo

# Opcional: usado só para ÁLBUNS do Spotify (pela API oficial).
# Playlists do Spotify são lidas pela página pública e não precisam
# destas credenciais.
SPOTIFY_CLIENT_ID = os.getenv("SPOTIFY_CLIENT_ID")
SPOTIFY_CLIENT_SECRET = os.getenv("SPOTIFY_CLIENT_SECRET")

# Opcional: arquivo de cookies do YouTube (formato Netscape).
# Só é usado se o arquivo existir. Útil quando o YouTube pede
# "Sign in to confirm you're not a bot" (comum em VPS/servidores).
COOKIES_FILE = os.getenv("YTDLP_COOKIES", "cookies.txt")

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("Neko")

try:
    os.makedirs(MUSIC_DIR, exist_ok=True)
    log.info("Pasta de músicas: %s", MUSIC_DIR)
except OSError:
    log.warning("Não consegui criar a pasta de músicas: %s", MUSIC_DIR)

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
# YOUTUBE_COOKIES e o bot recria o arquivo a cada inicialização.
COOKIES_ENV = os.getenv("YOUTUBE_COOKIES")
if COOKIES_ENV:
    with open(COOKIES_FILE, "w", encoding="utf-8") as cookie_file:
        cookie_file.write(COOKIES_ENV.strip() + "\n")

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

# Arquivos locais não usam as opções de reconexão de rede.
FFMPEG_LOCAL_OPTIONS = {"options": "-vn"}

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
        # Preenchido quando a faixa vem do rodízio de playlists.
        self.block_id = data.get("block_id")
        # True quando é um arquivo da pasta de músicas.
        self.local = bool(data.get("local"))

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
        self.local = resolved.local


class PlaylistBlock:
    """Uma playlist do rodízio (adicionada com /playduspika)."""

    def __init__(self, block_id, link, title, requester, items):
        self.id = block_id
        self.link = link
        self.title = title or "Playlist"
        self.requester = requester
        # Lista de dicts: title, query, uploader, duration.
        self.items = items


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

        # Rodízio de playlists (separado da fila normal).
        self.blocks = []
        self.block_index = 0
        self.block_pos = 0
        self.block_counter = 0
        self.rotation_loop = True


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


# ---------------------------------------------------------------
# Arquivos de música locais
# ---------------------------------------------------------------

def list_local_files():
    """Nomes dos arquivos de áudio da pasta de músicas."""
    if not os.path.isdir(MUSIC_DIR):
        return []

    return sorted(
        name
        for name in os.listdir(MUSIC_DIR)
        if name.lower().endswith(AUDIO_EXTS)
        and len(name) <= 100
        and os.path.isfile(os.path.join(MUSIC_DIR, name))
    )


def safe_music_path(name):
    """Caminho seguro de um arquivo da pasta de músicas."""
    base = os.path.realpath(MUSIC_DIR)
    path = os.path.realpath(os.path.join(base, os.path.basename(name)))

    if (
        not path.startswith(base + os.sep)
        or not path.lower().endswith(AUDIO_EXTS)
        or not os.path.isfile(path)
    ):
        raise ValueError("Arquivo não encontrado na pasta de músicas.")

    return path


def safe_filename(filename):
    """Nome de arquivo limpo, sem pastas nem símbolos estranhos."""
    stem, ext = os.path.splitext(os.path.basename(filename))
    stem = re.sub(r"[^\w\s().,'&+-]", "_", stem).strip()[:80] or "musica"
    return stem + ext.lower()


def local_duration(path):
    """Duração do arquivo em segundos (0 se não conseguir ler)."""
    if MutagenFile is None:
        return 0

    try:
        audio = MutagenFile(path)
        return int(audio.info.length) if audio and audio.info else 0
    except Exception:
        return 0


def local_track(name, requester):
    path = safe_music_path(name)
    filename = os.path.basename(path)

    return Track(
        {
            "title": os.path.splitext(filename)[0],
            "url": path,
            "query": f"local:{filename}",
            "uploader": "Arquivo local",
            "duration": local_duration(path),
            "local": True,
        },
        requester,
    )


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


async def extract_flat_entries(query, limit):
    """Lista os resultados de uma busca sem abrir cada um."""
    loop = asyncio.get_running_loop()

    def extract():
        options = {
            **YDL_OPTIONS,
            "extract_flat": True,
            "playlistend": limit,
        }
        with yt_dlp.YoutubeDL(options) as ydl:
            info = ydl.extract_info(query, download=False)
        return [
            entry
            for entry in (info or {}).get("entries") or []
            if entry
        ]

    return await loop.run_in_executor(None, extract)


async def search_soundcloud(text):
    """Procura no SoundCloud e usa o primeiro resultado que tocar.

    Alguns resultados são protegidos (DRM) ou indisponíveis; nesses
    casos o bot passa para o próximo em vez de desistir.
    """
    entries = await extract_flat_entries(
        f"scsearch{SOUNDCLOUD_TRIES}:{text}",
        SOUNDCLOUD_TRIES,
    )

    last_error = None
    for entry in entries:
        link = entry.get("url") or entry.get("webpage_url")
        if not link:
            continue

        try:
            return await extract_info(link)
        except Exception as error:
            last_error = error
            log.warning(
                "SoundCloud: pulei um resultado (%s)",
                clean_error(error)[:120],
            )

    if last_error:
        raise last_error
    raise ValueError("Nenhum áudio reproduzível encontrado.")


NOISE_WORDS = {
    "official", "oficial", "music", "video", "mv", "audio", "lyrics",
    "lyric", "clipe", "hd", "4k", "full", "version",
}


def simplify_query(text):
    """Versão mais simples da busca: sem feat., símbolos e palavras
    como 'Official Music Video'."""
    text = re.sub(r"[\(\[].*?[\)\]]", " ", text)
    text = re.sub(r"\b(feat|ft|featuring)\b\.?.*", " ", text, flags=re.I)
    text = re.sub(r"[^\w\s'-]", " ", text)
    words = [w for w in text.split() if w.lower() not in NOISE_WORDS]
    return " ".join(words)


def query_variants(text):
    """Buscas a tentar no SoundCloud, da mais exata à mais simples."""
    simple = simplify_query(text)
    variants = [text, simple]

    words = simple.split()
    if len(words) > 3:
        variants.append(" ".join(words[:3]))

    seen = set()
    result = []
    for variant in variants:
        key = variant.lower().strip()
        if key and key not in seen:
            seen.add(key)
            result.append(variant.strip())
    return result


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

    # SoundCloud: da busca original até uma versão simplificada.
    queries = query_variants(text)

    sc_error = None
    for query in queries:
        try:
            return await search_soundcloud(query)
        except Exception as error:
            sc_error = error
            log.warning(
                "SoundCloud não achou %r: %s",
                query,
                clean_error(error),
            )

    blocked = skip_youtube or (
        yt_error is not None
        and "YouTube bloqueou" in (friendly_reason(yt_error) or "")
    )

    if blocked:
        raise ValueError(
            "Não achei essa música no SoundCloud e o YouTube "
            "bloqueou o servidor do bot (pede login/cookies)."
        ) from sc_error

    if yt_error:
        raise yt_error from sc_error
    raise sc_error


def clean_error(error):
    """Remove códigos de cor e deixa a mensagem do yt-dlp legível."""
    text = re.sub(r"\x1b\[[0-9;]*m", "", str(error))
    return text.replace("ERROR: ", "").strip()


def friendly_reason(error):
    """Traduz os erros mais comuns do yt-dlp para o usuário."""
    text = clean_error(error).lower()

    # Mensagem que o próprio bot já montou.
    if text.startswith("não achei") or text.startswith("arquivo não"):
        return clean_error(error)

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


def looks_like_playlist(url):
    """Link de playlist, ou link do YouTube que traz ?list=."""
    return is_playlist_url(url) or bool(re.search(r"[?&]list=", url))


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
    # Arquivo da pasta de músicas (guardado como "local:nome.mp3").
    if query.startswith("local:"):
        return local_track(query[len("local:"):], requester)

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
                friendly_reason(fallback_error)
                or reason
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
    """Token da API oficial do Spotify (usado só para álbuns)."""
    now = time.time()
    if (
        _spotify_token["value"]
        and now < _spotify_token["expires"] - 30
    ):
        return _spotify_token["value"]

    credentials = base64.b64encode(
        f"{SPOTIFY_CLIENT_ID}:{SPOTIFY_CLIENT_SECRET}".encode()
    ).decode()

    async with aiohttp.ClientSession() as session:
        async with session.post(
            "https://accounts.spotify.com/api/token",
            data={"grant_type": "client_credentials"},
            headers={"Authorization": f"Basic {credentials}"},
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


def find_list_by_key(node, key):
    """Procura, em qualquer nível de um JSON, uma lista com esse nome."""
    if isinstance(node, dict):
        value = node.get(key)
        if isinstance(value, list):
            return value
        for child in node.values():
            found = find_list_by_key(child, key)
            if found is not None:
                return found
    elif isinstance(node, list):
        for child in node:
            found = find_list_by_key(child, key)
            if found is not None:
                return found
    return None


async def spotify_public_playlist(spotify_id, requester):
    """Lê as faixas de uma playlist PÚBLICA pela página de incorporação.

    Não usa a API oficial (que, desde fevereiro de 2026, só entrega
    playlists do próprio usuário logado). É um método não oficial e
    pode parar de funcionar se o Spotify mudar a página.
    """
    url = f"https://open.spotify.com/embed/playlist/{spotify_id}"

    async with aiohttp.ClientSession() as session:
        async with session.get(
            url,
            timeout=aiohttp.ClientTimeout(total=15),
            headers={"User-Agent": "Mozilla/5.0"},
        ) as response:
            if response.status != 200:
                raise ValueError(
                    f"Página da playlist indisponível ({response.status})."
                )
            page = await response.text(errors="ignore")

    match = re.search(
        r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>',
        page,
        re.S,
    )
    if not match:
        raise ValueError("Formato da página do Spotify não reconhecido.")

    data = json.loads(match.group(1))
    entries = find_list_by_key(data, "trackList")
    if not entries:
        raise ValueError("Nenhuma faixa encontrada na página.")

    tracks = []
    for entry in entries:
        name = (entry.get("title") or "").strip()
        if not name:
            continue

        artist = re.sub(r"\s+", " ", entry.get("subtitle") or "").strip()
        text = f"{artist} {name}".strip()

        tracks.append(
            Track(
                {
                    "title": text,
                    "query": text,
                    "uploader": artist,
                    "duration": int(entry.get("duration") or 0) // 1000,
                },
                requester,
            )
        )

    return tracks[:MAX_PLAYLIST_TRACKS]


async def expand_spotify(url, requester):
    match = re.search(
        r"spotify\.com/(?:[\w-]+/)?(playlist|album)/([A-Za-z0-9]+)",
        url,
    )
    if not match:
        raise ValueError("Link do Spotify não reconhecido.")

    kind, spotify_id = match.groups()

    # Playlists: página pública (a API oficial não serve para bots).
    if kind == "playlist":
        try:
            tracks = await spotify_public_playlist(spotify_id, requester)
        except Exception as error:
            log.error(
                "Leitura da playlist do Spotify falhou: %s",
                clean_error(error),
            )
            raise ValueError(
                "Não consegui ler essa playlist do Spotify. Ela precisa "
                "ser pública. Como alternativa, copie os links das "
                "faixas e use /adicionar_varios."
            ) from error

        if not tracks:
            raise ValueError("Nenhuma faixa encontrada nessa playlist.")
        return tracks, "Playlist do Spotify"

    # Álbuns: API oficial (precisa de Client ID e Client Secret).
    if not (SPOTIFY_CLIENT_ID and SPOTIFY_CLIENT_SECRET):
        raise ValueError(
            "Para álbuns do Spotify, configure SPOTIFY_CLIENT_ID e "
            "SPOTIFY_CLIENT_SECRET nas variáveis do bot."
        )

    headers = {"Authorization": f"Bearer {await spotify_token()}"}
    api = f"https://api.spotify.com/v1/albums/{spotify_id}/tracks?limit=50"

    tracks = []

    async with aiohttp.ClientSession() as session:
        while api and len(tracks) < MAX_PLAYLIST_TRACKS:
            async with session.get(
                api,
                headers=headers,
                timeout=aiohttp.ClientTimeout(total=15),
            ) as response:
                if response.status != 200:
                    body = (await response.text())[:200]
                    log.error(
                        "Spotify álbum falhou (%s): %s",
                        response.status,
                        body,
                    )
                    raise ValueError(
                        f"O Spotify não liberou esse álbum "
                        f"({response.status})."
                    )
                data = await response.json()

            for item in data.get("items", []):
                if not item or not item.get("name"):
                    continue

                artist = (item.get("artists") or [{}])[0].get("name", "")
                text = f"{artist} {item['name']}".strip()
                tracks.append(
                    Track(
                        {
                            "title": text,
                            "query": text,
                            "uploader": artist,
                            "duration": (
                                (item.get("duration_ms") or 0) // 1000
                            ),
                        },
                        requester,
                    )
                )

            api = data.get("next")

    if not tracks:
        raise ValueError("Nenhuma faixa encontrada nesse álbum.")

    return tracks[:MAX_PLAYLIST_TRACKS], "Álbum do Spotify"


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
# Rodízio de playlists (uma playlist depois da outra)
# ---------------------------------------------------------------

def tracks_to_items(tracks):
    """Guarda só os dados da faixa; o áudio é buscado na hora de tocar."""
    return [
        {
            "title": track.title,
            "query": track.query,
            "uploader": track.artist,
            "duration": track.duration,
        }
        for track in tracks
    ]


def add_block(player, link, title, requester, tracks):
    player.block_counter += 1
    block = PlaylistBlock(
        player.block_counter,
        link,
        title,
        requester,
        tracks_to_items(tracks),
    )
    player.blocks.append(block)
    return block


def remove_block(player, block_id):
    """Remove uma playlist do rodízio, ajustando a posição atual."""
    for index, block in enumerate(player.blocks):
        if block.id == block_id:
            del player.blocks[index]

            if index < player.block_index:
                player.block_index -= 1
            elif index == player.block_index:
                player.block_pos = 0

            return block
    return None


def clear_rotation(player):
    player.blocks.clear()
    player.block_index = 0
    player.block_pos = 0


def next_rotation_track(player):
    """Próxima faixa do rodízio, ou None se não houver mais."""
    if not player.blocks:
        return None

    wrapped = False

    while True:
        if player.block_index >= len(player.blocks):
            if not player.rotation_loop or wrapped:
                return None
            player.block_index = 0
            player.block_pos = 0
            wrapped = True

        block = player.blocks[player.block_index]

        if player.block_pos < len(block.items):
            data = dict(block.items[player.block_pos])
            data["block_id"] = block.id
            player.block_pos += 1
            return Track(data, block.requester)

        # Acabou esta playlist: passa para a próxima.
        player.block_index += 1
        player.block_pos = 0


def can_edit_block(interaction, block):
    """Quem adicionou a playlist ou quem tem 'Gerenciar Servidor'."""
    perms = getattr(interaction.user, "guild_permissions", None)
    return block.requester.id == interaction.user.id or bool(
        perms and perms.manage_guild
    )


def blocks_embed(player, selected=None):
    embed = discord.Embed(
        title="📋 Playlists do rodízio",
        color=discord.Color.from_rgb(119, 86, 255),
    )

    if not player.blocks:
        embed.description = (
            "Nenhuma playlist no rodízio.\n"
            "Adicione com `/playduspika`."
        )
    else:
        playing_id = (
            getattr(player.current, "block_id", None)
            if player.current
            else None
        )

        lines = []
        for number, block in enumerate(player.blocks, 1):
            marker = "👉 " if block.id == selected else ""
            title = discord.utils.escape_markdown(block.title)[:60]
            line = (
                f"{marker}**{number}.** [{title}](<{block.link}>) "
                f"— {len(block.items)} faixas • {block.requester.mention}"
            )
            if block.id == playing_id:
                line += "\n      ▶ tocando agora"
            lines.append(line)

        embed.description = "\n".join(lines)[:4000]

    embed.set_footer(
        text=(
            "Depois da última playlist: "
            + (
                "volta para a primeira"
                if player.rotation_loop
                else "para de tocar o rodízio"
            )
        )
    )

    return embed


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

    footer = (
        f"Volume: {int(player.volume * 100)}% | "
        f"Loop: {'Ligado' if player.loop else 'Desligado'} | "
        f"Fila: {len(player.queue)}"
    )
    if player.blocks:
        footer += f" | Playlists: {len(player.blocks)}"

    embed.set_footer(text=footer)

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
        failures = 0

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
                # Fila normal vazia: segue o rodízio de playlists.
                track = next_rotation_track(player)
                if track is None:
                    player.current = None
                    await update_panel(player)
                    return
                player.current = track

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
                failures += 1

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

                if failures >= MAX_CONSECUTIVE_FAILURES:
                    if player.channel:
                        try:
                            await player.channel.send(
                                "⚠️ Muitas faixas seguidas falharam, "
                                "então parei por aqui. Tente de novo "
                                "com /play."
                            )
                        except discord.HTTPException:
                            pass
                    await update_panel(player)
                    return

        ffmpeg_options = (
            FFMPEG_LOCAL_OPTIONS if track.local else FFMPEG_OPTIONS
        )

        source = discord.PCMVolumeTransformer(
            discord.FFmpegPCMAudio(
                track.stream,
                **ffmpeg_options,
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
# Janelas (modais) para vários links, salvar e substituir playlists
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


class ReplaceModal(discord.ui.Modal, title="Substituir playlist"):
    link = discord.ui.TextInput(
        label="Link da nova playlist",
        placeholder="https://...",
        max_length=500,
        required=True,
    )

    def __init__(self, player, block_id):
        super().__init__()
        self.player = player
        self.block_id = block_id

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)

        block = next(
            (b for b in self.player.blocks if b.id == self.block_id),
            None,
        )
        if not block:
            await interaction.followup.send(
                "Essa playlist já foi removida do rodízio.",
                ephemeral=True,
            )
            return

        link = str(self.link).strip()
        if not link.startswith(("http://", "https://")) or (
            not looks_like_playlist(link)
        ):
            await interaction.followup.send(
                "Esse link não parece ser de uma playlist.",
                ephemeral=True,
            )
            return

        try:
            tracks, title = await expand_playlist(link, interaction.user)
        except Exception as error:
            log.error(
                "Falha ao substituir playlist %r: %s",
                link,
                clean_error(error),
            )
            reason = friendly_reason(error) or clean_error(error)[:250]
            await interaction.followup.send(
                f"Não consegui carregar a nova playlist: {reason}",
                ephemeral=True,
            )
            return

        block.link = link
        block.title = title or "Playlist"
        block.items = tracks_to_items(tracks)
        block.requester = interaction.user

        # Se era a playlist da vez, a nova começa do início
        # (a música atual termina normalmente).
        if (
            block in self.player.blocks
            and self.player.blocks.index(block) == self.player.block_index
        ):
            self.player.block_pos = 0

        try:
            await interaction.edit_original_response(
                embed=blocks_embed(self.player, block.id),
                view=RotationView(self.player, block.id),
            )
        except discord.HTTPException:
            pass

        await interaction.followup.send(
            f"🔄 Playlist substituída por **{block.title}** "
            f"({len(block.items)} faixas).",
            ephemeral=True,
        )
        await update_panel(self.player)


class RotationView(discord.ui.View):
    """Lista das playlists do rodízio, com remover/substituir."""

    def __init__(self, player, selected=None):
        super().__init__(timeout=300)
        self.player = player
        self.selected = selected

        if player.blocks:
            options = [
                discord.SelectOption(
                    label=f"{number}. {block.title}"[:100],
                    value=str(block.id),
                    default=(block.id == selected),
                )
                for number, block in enumerate(player.blocks, 1)
            ]
            select = discord.ui.Select(
                placeholder="Escolha uma playlist...",
                options=options,
                row=0,
            )
            select.callback = self.on_select
            self.add_item(select)

    def get_block(self):
        for block in self.player.blocks:
            if block.id == self.selected:
                return block
        return None

    async def on_select(self, interaction: discord.Interaction):
        selected = int(interaction.data["values"][0])
        await interaction.response.edit_message(
            embed=blocks_embed(self.player, selected),
            view=RotationView(self.player, selected),
        )

    @discord.ui.button(
        label="🗑 Remover",
        style=discord.ButtonStyle.danger,
        row=1,
    )
    async def remove_selected(self, interaction, button):
        block = self.get_block()
        if not block:
            await interaction.response.send_message(
                "Escolha uma playlist na lista primeiro.",
                ephemeral=True,
            )
            return

        if not can_edit_block(interaction, block):
            await interaction.response.send_message(
                "Só quem adicionou a playlist (ou quem tem Gerenciar "
                "Servidor) pode remover.",
                ephemeral=True,
            )
            return

        remove_block(self.player, block.id)

        await interaction.response.edit_message(
            embed=blocks_embed(self.player),
            view=RotationView(self.player),
        )
        await update_panel(self.player)

    @discord.ui.button(
        label="🔄 Substituir",
        style=discord.ButtonStyle.primary,
        row=1,
    )
    async def replace_selected(self, interaction, button):
        block = self.get_block()
        if not block:
            await interaction.response.send_message(
                "Escolha uma playlist na lista primeiro.",
                ephemeral=True,
            )
            return

        if not can_edit_block(interaction, block):
            await interaction.response.send_message(
                "Só quem adicionou a playlist (ou quem tem Gerenciar "
                "Servidor) pode substituir.",
                ephemeral=True,
            )
            return

        await interaction.response.send_modal(
            ReplaceModal(self.player, block.id)
        )

    @discord.ui.button(
        label="🔁 Rodízio",
        style=discord.ButtonStyle.secondary,
        row=1,
    )
    async def toggle_rotation(self, interaction, button):
        self.player.rotation_loop = not self.player.rotation_loop

        await interaction.response.edit_message(
            embed=blocks_embed(self.player, self.selected),
            view=RotationView(self.player, self.selected),
        )

    @discord.ui.button(
        label="🔃 Atualizar",
        style=discord.ButtonStyle.secondary,
        row=1,
    )
    async def refresh_list(self, interaction, button):
        await interaction.response.edit_message(
            embed=blocks_embed(self.player, self.selected),
            view=RotationView(self.player, self.selected),
        )


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
        clear_rotation(p)
        p.loop = False
        p.current = None

        if p.voice:
            p.voice.stop()

        await interaction.response.send_message(
            "Reprodução parada, fila e rodízio limpos.",
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
            "A música atual e o rodízio de playlists continuam.",
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

    @discord.ui.button(
        label="📋 Playlists",
        style=discord.ButtonStyle.primary,
        row=2,
    )
    async def show_rotation(self, interaction, button):
        await interaction.response.send_message(
            embed=blocks_embed(self.player),
            view=RotationView(self.player),
            ephemeral=True,
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
    name="playduspika",
    description="Adiciona uma playlist ao rodízio (uma toca depois da outra).",
)
@app_commands.describe(
    link="Link da playlist (YouTube, SoundCloud ou Spotify)"
)
async def rotation_add_command(
    interaction: discord.Interaction,
    link: str,
):
    await interaction.response.defer(thinking=True)

    link = link.strip()
    if not link.startswith(("http://", "https://")):
        await interaction.followup.send(
            "Envie o link completo da playlist (começando com https://)."
        )
        return

    if not looks_like_playlist(link):
        await interaction.followup.send(
            "Esse link não parece ser de uma playlist. "
            "Para uma música só, use `/play`."
        )
        return

    player = await connect_voice(interaction)
    if not player:
        return

    if len(player.blocks) >= MAX_BLOCKS:
        await interaction.followup.send(
            f"O rodízio já tem {MAX_BLOCKS} playlists. Remova alguma "
            "em `/playduspika_lista` para adicionar outra."
        )
        return

    try:
        tracks, title = await expand_playlist(link, interaction.user)
    except Exception as error:
        log.error(
            "Falha ao carregar playlist do rodízio %r: %s",
            link,
            clean_error(error),
        )
        reason = friendly_reason(error) or clean_error(error)[:250]
        await interaction.followup.send(
            f"Não consegui carregar a playlist: {reason}"
        )
        return

    block = add_block(player, link, title, interaction.user, tracks)
    position = len(player.blocks)

    message = (
        f"📋 **{block.title}** entrou no rodízio como playlist nº "
        f"{position} ({len(block.items)} faixas)."
    )
    if position > 1:
        message += " Ela toca quando a anterior terminar."

    await interaction.followup.send(message)
    await kick(player)


@bot.tree.command(
    name="playduspika_lista",
    description="Mostra as playlists do rodízio e permite remover/substituir.",
)
async def rotation_list_command(interaction: discord.Interaction):
    player = get_player(interaction.guild_id)

    await interaction.response.send_message(
        embed=blocks_embed(player),
        view=RotationView(player),
        ephemeral=True,
    )


@bot.tree.command(
    name="adicionar_varios",
    description="Adiciona vários links ou nomes de uma vez.",
)
async def add_many_command(interaction: discord.Interaction):
    await interaction.response.send_modal(MultiAddModal())


@bot.tree.command(
    name="limpar",
    description="Limpa a fila (a música atual e o rodízio continuam).",
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
    description="Para a música e limpa a fila e o rodízio.",
)
async def stop_command(interaction: discord.Interaction):
    p = get_player(interaction.guild_id)
    p.queue.clear()
    clear_rotation(p)
    p.current = None
    p.loop = False

    if p.voice:
        p.voice.stop()

    await interaction.response.send_message(
        "Reprodução parada, fila e rodízio limpos."
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
    clear_rotation(p)

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
# Músicas locais: /musica, /musica_todas, /musica_lista ...
# ---------------------------------------------------------------

async def local_file_autocomplete(
    interaction: discord.Interaction,
    current: str,
):
    return [
        app_commands.Choice(name=name, value=name)
        for name in list_local_files()
        if current.lower() in name.lower()
    ][:25]


@bot.tree.command(
    name="musica",
    description="Toca um arquivo de música da pasta do bot.",
)
@app_commands.describe(nome="Nome do arquivo (comece a digitar)")
async def local_play_command(
    interaction: discord.Interaction,
    nome: str,
):
    await interaction.response.defer(thinking=True)

    try:
        track = local_track(nome, interaction.user)
    except ValueError as error:
        await interaction.followup.send(
            f"{error} Veja os nomes com `/musica_lista`."
        )
        return

    player = await connect_voice(interaction)
    if not player:
        return

    added, _ = add_tracks(player, [track])
    if not added:
        await interaction.followup.send("A fila atingiu o limite.")
        return

    await interaction.followup.send(
        f"🎵 Adicionada à fila: **{track.title}**"
    )
    await kick(player)


@local_play_command.autocomplete("nome")
async def local_play_autocomplete(interaction, current):
    return await local_file_autocomplete(interaction, current)


@bot.tree.command(
    name="musica_todas",
    description="Coloca todos os arquivos da pasta de músicas na fila.",
)
@app_commands.describe(embaralhar="Embaralhar antes de adicionar")
async def local_all_command(
    interaction: discord.Interaction,
    embaralhar: bool = False,
):
    await interaction.response.defer(thinking=True)

    files = list_local_files()
    if not files:
        await interaction.followup.send(
            "A pasta de músicas está vazia. O dono pode enviar "
            "arquivos com `/musica_adicionar`."
        )
        return

    player = await connect_voice(interaction)
    if not player:
        return

    tracks = [
        Track(
            {
                "title": os.path.splitext(name)[0],
                "query": f"local:{name}",
                "uploader": "Arquivo local",
            },
            interaction.user,
        )
        for name in files
    ]
    if embaralhar:
        random.shuffle(tracks)

    added, skipped = add_tracks(player, tracks)

    message = f"📁 {added} músicas da pasta adicionadas à fila."
    if skipped:
        message += f" ({skipped} ficaram de fora: fila cheia.)"

    await interaction.followup.send(message)
    await kick(player)


@bot.tree.command(
    name="musica_lista",
    description="Lista os arquivos da pasta de músicas.",
)
async def local_list_command(interaction: discord.Interaction):
    files = list_local_files()

    if not files:
        await interaction.response.send_message(
            "A pasta de músicas está vazia. O dono pode enviar "
            "arquivos com `/musica_adicionar`.",
            ephemeral=True,
        )
        return

    lines = [f"{i}. {name}" for i, name in enumerate(files, 1)]
    text = f"**{len(files)} arquivos**\n" + "\n".join(lines)
    if len(text) > 1900:
        text = text[:1900].rsplit("\n", 1)[0] + "\n..."

    await interaction.response.send_message(text, ephemeral=True)


@bot.tree.command(
    name="musica_adicionar",
    description="Adiciona até 10 arquivos de áudio à pasta do Neko.",
)
@app_commands.describe(
    arquivo1="Primeiro arquivo de áudio",
    arquivo2="Segundo arquivo de áudio (opcional)",
    arquivo3="Terceiro arquivo de áudio (opcional)",
    arquivo4="Quarto arquivo de áudio (opcional)",
    arquivo5="Quinto arquivo de áudio (opcional)",
    arquivo6="Sexto arquivo de áudio (opcional)",
    arquivo7="Sétimo arquivo de áudio (opcional)",
    arquivo8="Oitavo arquivo de áudio (opcional)",
    arquivo9="Nono arquivo de áudio (opcional)",
    arquivo10="Décimo arquivo de áudio (opcional)",
)
async def local_add_command(
    interaction: discord.Interaction,
    arquivo1: discord.Attachment,
    arquivo2: discord.Attachment = None,
    arquivo3: discord.Attachment = None,
    arquivo4: discord.Attachment = None,
    arquivo5: discord.Attachment = None,
    arquivo6: discord.Attachment = None,
    arquivo7: discord.Attachment = None,
    arquivo8: discord.Attachment = None,
    arquivo9: discord.Attachment = None,
    arquivo10: discord.Attachment = None,
):
    """Permite que qualquer membro envie até 10 músicas por comando."""
    await interaction.response.defer(ephemeral=True, thinking=True)
    attachments = [item for item in (
        arquivo1, arquivo2, arquivo3, arquivo4, arquivo5,
        arquivo6, arquivo7, arquivo8, arquivo9, arquivo10,
    ) if item is not None]

    if not attachments:
        await interaction.followup.send(
            "Anexe pelo menos um arquivo de áudio.", ephemeral=True
        )
        return

    try:
        os.makedirs(MUSIC_DIR, exist_ok=True)
    except OSError as error:
        log.error("Não consegui criar a pasta de músicas: %s", error)
        await interaction.followup.send(
            "Não consegui acessar a pasta de músicas da hospedagem.",
            ephemeral=True,
        )
        return

    added, skipped = [], []
    for attachment in attachments:
        name = safe_filename(attachment.filename)
        if not name.lower().endswith(AUDIO_EXTS):
            skipped.append(f"{attachment.filename}: formato não aceito")
            continue
        if attachment.size > MAX_AUDIO_BYTES:
            skipped.append(f"{attachment.filename}: passa de 100 MB")
            continue

        path = os.path.join(MUSIC_DIR, name)
        if os.path.exists(path):
            # Evita sobrescrever arquivos já existentes; cria nome alternativo.
            stem, ext = os.path.splitext(name)
            counter = 2
            while os.path.exists(path):
                suffix = f" ({counter})"
                path = os.path.join(MUSIC_DIR, f"{stem[:80-len(suffix)]}{suffix}{ext}")
                counter += 1
            name = os.path.basename(path)

        try:
            await attachment.save(path)
            added.append(name)
        except Exception as error:
            log.error("Falha ao salvar %s: %s", name, error)
            skipped.append(f"{attachment.filename}: falha ao salvar")
            try:
                if os.path.exists(path) and os.path.getsize(path) == 0:
                    os.remove(path)
            except OSError:
                pass

    lines = []
    if added:
        lines.append(f"✅ **{len(added)} arquivo(s) adicionado(s):**")
        lines.extend(f"• {name}" for name in added[:15])
        if len(added) > 15:
            lines.append(f"• ... e mais {len(added) - 15} arquivo(s)")
    if skipped:
        lines.append(f"⚠️ **{len(skipped)} arquivo(s) não foram adicionados:**")
        lines.extend(f"• {reason}" for reason in skipped[:10])
    if added:
        lines.append("Use `/musica` para tocar uma faixa ou `/musica_lista` para ver os arquivos.")
        lines.append("Envie apenas músicas que você tem direito de usar.")
    await interaction.followup.send("\n".join(lines)[:1900], ephemeral=True)


def normalize_music_label(value):
    """Normaliza nomes para comparação, aceitando título com ou sem extensão."""
    value = os.path.basename(value.strip().strip("\"'`"))
    value = unicodedata.normalize("NFKC", value).casefold().strip()
    # Só remove uma extensão de áudio conhecida no final do texto.
    for ext in AUDIO_EXTS:
        if value.endswith(ext):
            value = value[:-len(ext)]
            break
    # Espaços repetidos e diferenças entre espaços não afetam a comparação.
    return re.sub(r"\s+", " ", value).strip()


@bot.tree.command(
    name="musica_remover",
    description="Remove arquivos por posição ou nome (só o dono).",
)
@app_commands.describe(
    nomes="Posições (1, 2) e/ou títulos com ou sem extensão, separados por vírgula"
)
async def local_remove_command(
    interaction: discord.Interaction,
    nomes: str,
):
    if not await owner_only(interaction):
        return

    # A numeração usa exatamente a mesma ordem alfabética de /musica_lista.
    files = list_local_files()
    if not files:
        await interaction.response.send_message(
            "A pasta de músicas está vazia.", ephemeral=True
        )
        return

    requested = [
        item.strip().strip("\"'`")
        for item in re.split(r"[,;\n]+", nomes)
        if item.strip()
    ]
    if not requested:
        await interaction.response.send_message(
            "Informe posições ou nomes. Exemplo: `1, 3, Gurenge`.",
            ephemeral=True,
        )
        return

    # Índices por nome completo e por título sem extensão.
    by_label = {}
    for filename in files:
        by_label.setdefault(normalize_music_label(filename), []).append(filename)

    targets, failed, seen = [], [], set()
    for item in requested:
        match = None
        if item.isdecimal():
            position = int(item)
            if 1 <= position <= len(files):
                match = files[position - 1]
            else:
                failed.append(f"posição {position} (a lista tem {len(files)} música(s))")
                continue
        else:
            key = normalize_music_label(item)
            matches = by_label.get(key, [])
            if len(matches) == 1:
                match = matches[0]
            elif len(matches) > 1:
                failed.append(f"{item[:80]} (há títulos repetidos; informe o nome completo com extensão)")
                continue

        if match is None:
            failed.append(item[:100])
            continue
        key = match.casefold()
        if key not in seen:
            seen.add(key)
            targets.append(match)

    removed = []
    for filename in targets:
        try:
            os.remove(safe_music_path(filename))
            removed.append(filename)
        except (ValueError, OSError):
            failed.append(filename[:100])

    lines = []
    if removed:
        lines.append(f"🗑 **{len(removed)} arquivo(s) removido(s):**")
        lines.extend(f"• {filename}" for filename in removed[:15])
        if len(removed) > 15:
            lines.append(f"• ... e mais {len(removed) - 15} arquivo(s)")
    if failed:
        lines.append(f"⚠️ **{len(failed)} item(ns) não encontrado(s) ou não removido(s):**")
        lines.extend(f"• {item}" for item in failed[:10])
    await interaction.response.send_message(
        "\n".join(lines)[:1900] or "Nenhum arquivo foi removido.",
        ephemeral=True,
    )


@bot.tree.command(
    name="musica_limpar",
    description="Apaga todos os arquivos de música baixados (só o dono).",
)
@app_commands.describe(confirmar="Marque como verdadeiro para confirmar a exclusão de todos os arquivos")
async def local_clear_command(
    interaction: discord.Interaction,
    confirmar: bool = False,
):
    if not await owner_only(interaction):
        return

    files = list_local_files()
    if not files:
        await interaction.response.send_message(
            "A pasta de músicas já está vazia.", ephemeral=True
        )
        return

    if not confirmar:
        await interaction.response.send_message(
            f"⚠️ Há **{len(files)} arquivo(s)** na pasta. Para apagar todos, execute `/musica_limpar` novamente com `confirmar: verdadeiro`.",
            ephemeral=True,
        )
        return

    removed, failed = [], []
    for filename in files:
        try:
            os.remove(safe_music_path(filename))
            removed.append(filename)
        except (ValueError, OSError):
            failed.append(filename)

    message = f"🧹 Foram apagados **{len(removed)} de {len(files)}** arquivo(s) de música."
    if failed:
        message += "\nNão consegui apagar: " + ", ".join(failed[:10])
    await interaction.response.send_message(message[:1900], ephemeral=True)

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
    """Atualiza avatar/banner e trata limites do Discord."""
    if bot.user is None:
        await interaction.followup.send(
            "O Neko ainda não está conectado ao Discord.",
            ephemeral=True,
        )
        return

    try:
        await bot.user.edit(**{field: value})

    except TypeError:
        await interaction.followup.send(
            "A versão do discord.py pode estar desatualizada. "
            "Atualize com: pip install -U discord.py e reinicie o Neko.",
            ephemeral=True,
        )

    except discord.HTTPException as error:
        resposta = error.text or str(error)
        log.error(
            "Falha ao alterar %s: status=%s, código=%s, resposta=%s",
            field,
            error.status,
            error.code,
            resposta,
        )

        if error.status == 429 or "too fast" in resposta.lower():
            mensagem = (
                f"O Discord limitou a alteração de {field}. "
                "Não tente novamente repetidamente. Aguarde o limite "
                "ser liberado e tente uma vez."
            )
        else:
            mensagem = (
                f"O Discord recusou a alteração de {field}: "
                f"{resposta[:250]}"
            )

        await interaction.followup.send(mensagem, ephemeral=True)

    else:
        await interaction.followup.send(
            success_message,
            ephemeral=True,
        )


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
            "`/parar` • Para e limpa fila e rodízio\n"
            "`/sair` • Desconecta do canal\n"
            "`/letra [musica]` • Pesquisa letras\n"
            "\n**Arquivos de música**\n"
            "`/musica nome` • Toca um arquivo da pasta\n"
            "`/musica_todas` • Toca todos os arquivos (opção de embaralhar)\n"
            "`/musica_lista` • Lista os arquivos\n"
            "\n**Rodízio de playlists**\n"
            "`/playduspika link` • Entra na sequência de playlists\n"
            "`/playduspika_lista` • Vê, remove ou substitui playlists\n"
            "\n**Playlists salvas**\n"
            "`/lista criar nome` • Cria ou adiciona faixas\n"
            "`/lista salvar_fila nome` • Salva a fila atual\n"
            "`/lista tocar nome` • Toca uma playlist salva\n"
            "`/lista ver [nome]` • Lista playlists ou faixas\n"
            "`/lista remover_faixa nome numero` • Tira uma faixa\n"
            "`/lista apagar nome` • Apaga a playlist\n"
            "\n**Gerenciamento de arquivos**\n"
            "`/musica_adicionar` • Qualquer membro pode enviar até 10 arquivos por vez\n"
            "`/musica_remover nomes` • Remove por posição ou nome, com/sem extensão (só o dono)\n"
            "`/musica_limpar confirmar` • Apaga todos os arquivos de música (só o dono)\n"
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
