import os
import re
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
MAX_QUEUE = 100

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


class Track:
    def __init__(self, data, requester):
        self.title = data.get("title", "Faixa desconhecida")
        self.url = (
            data.get("webpage_url")
            or data.get("original_url")
            or ""
        )
        self.stream = data["url"]
        self.duration = data.get("duration") or 0
        self.artist = (
            data.get("uploader")
            or data.get("artist")
            or "Artista desconhecido"
        )
        self.thumbnail = data.get("thumbnail")
        self.requester = requester


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


def make_embed(player):
    embed = discord.Embed(
        title="🐱 NEKO MUSIC",
        color=discord.Color.from_rgb(119, 86, 255),
    )

    if player.current:
        track = player.current

        embed.description = (
            f"🎵 **[{discord.utils.escape_markdown(track.title)}]"
            f"({track.url})**"
        )
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
    async def stop(self, interaction, button):
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
        label="📃 Playlist",
        style=discord.ButtonStyle.secondary,
        row=1,
    )
    async def playlist(self, interaction, button):
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


@bot.tree.command(
    name="ajuda",
    description="Mostra os comandos do Neko.",
)
async def help_command(interaction: discord.Interaction):
    embed = discord.Embed(
        title="🐱 Neko • Ajuda",
        description=(
            "`/play busca` • Reproduz por nome ou link\n"
            "`/painel` • Mostra o painel\n"
            "`/fila` • Mostra a fila\n"
            "`/pular` • Avança a faixa\n"
            "`/parar` • Para e limpa a fila\n"
            "`/sair` • Desconecta do canal\n"
            "`/letra [musica]` • Pesquisa letras\n"
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
