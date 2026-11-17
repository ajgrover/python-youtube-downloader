"""Download YouTube videos with a Tkinter queue and a yt-dlp backend."""

import json
import os
import signal
import subprocess
import queue
import re
import shutil
import sys
import tempfile
import threading
import tkinter as tk
import urllib.parse
import urllib.request
from pathlib import Path
from tkinter import font as tkfont, ttk
from typing import Any, cast

import yt_dlp
from tqdm import tqdm
from yt_dlp.utils import DownloadCancelled, DownloadError


# Application configuration
DOWNLOAD_PATH = Path.home() / "Downloads"
QUALITY_CHOICES = ["720p", "1080p", "Highest Quality"]
HIGHEST_CHOICES = {"Highest Quality", "Highest Possible"}  # Backward compatibility

# Validation and error messages
YOUTUBE_URL = re.compile(
    r"^(https?://)?(www\.|m\.|music\.)?(youtube\.com|youtu\.be|youtube-nocookie\.com)/",
    re.IGNORECASE,
)
INVALID_MARKERS = (
    "video unavailable",
    "private video",
    "has been removed",
    "incorrect youtube id",
    "not a valid url",
    "unsupported url",
    "does not exist",
    "this video is not available",
    "account associated with this video has been terminated",
    "members-only",
    "confirm your age",  # Existing behavior: classify this message as invalid.
)

# GUI appearance
GREY = "#8a8a8a"
BLUE = "#1d9bf0"
RED = "#d93025"
OUTPUT_BG = "#ececec"

STATUS_DISPLAY = {
    "blank": ("", GREY),
    "valid": ("✓", GREY),
    "queued": ("✓✓", GREY),
    "done": ("✓✓", BLUE),
    "failed": ("✓✓", RED),
}
LOG_NAV_KEYS = {
    "Left", "Right", "Up", "Down", "Home", "End", "Prior", "Next",
    "Shift_L", "Shift_R", "Control_L", "Control_R", "Meta_L", "Meta_R",
    "Command", "Alt_L", "Alt_R",
}


# ---------------------------------------------------------------------------
# Shared utility functions
# ---------------------------------------------------------------------------


def safe_filename(name):
    """Remove characters that are invalid in macOS filenames."""
    return re.sub(r'[/:\x00-\x1f\x7f]', "-", name).strip()


def needs_vpn_change(error):
    """Identify errors for which the application suggests changing VPN location."""
    name = type(error).__name__
    text = str(error)
    lowered = text.lower()
    return (
        "BotDetection" in name
        or "detected as a bot" in lowered
        or "not a bot" in lowered
        or "UNEXPECTED_EOF_WHILE_READING" in text
    )


def wheel_units(event):
    """Convert a mouse wheel event into scroll units for any platform."""
    if getattr(event, "num", None) == 4:
        return -1
    if getattr(event, "num", None) == 5:
        return 1
    if sys.platform == "darwin":
        return -event.delta
    return -int(event.delta / 120)


# ---------------------------------------------------------------------------
# yt-dlp logging and download progress
# ---------------------------------------------------------------------------


class SilentLogger:
    """Swallow yt-dlp's own console output; we print our own messages."""

    def debug(self, msg):
        pass

    def info(self, msg):
        pass

    def warning(self, msg):
        pass

    def error(self, msg):
        pass


class DownloadLogger(SilentLogger):
    """Display retry warnings in active progress-bar descriptions."""

    def __init__(self, bars: dict[str, tqdm]):
        self.bars = bars
        self.retry_count = 0

    def warning(self, msg):
        lowered = msg.lower()
        if "retry" in lowered or "got error" in lowered:
            self.retry_count += 1
            for bar in self.bars.values():
                if bar is None:
                    continue
                label = bar.desc.split(" (Retrying")[0]
                bar.set_description(f"{label} (Retrying {self.retry_count}/10)")


class _DownloadProgress:
    """Track yt-dlp downloads and FFmpeg's actual merging progress.

    FFmpeg writes progress snapshots to a per-download temporary file. Reading
    that file does not interfere with yt-dlp's subprocess or other threads.
    """

    def __init__(self, log=None, cancel_event=None):
        self.log = log
        self.cancel_event = cancel_event
        self.bars: dict[str, tqdm] = {}
        self.duration: float | None = None
        self.merge_bar = None
        self.merge_progress_file = None
        self._merge_stop = threading.Event()
        self._merge_thread = None
        self._merge_lock = threading.Lock()
        self._merge_position = 0.0
        self._merge_cancel_sent = False

    def check_cancelled(self):
        if self.cancel_event is not None and self.cancel_event.is_set():
            raise DownloadCancelled("Cancelled by user")

    def _bar(self, **kwargs):
        if self.log is not None:
            kwargs["file"] = self.log
        return tqdm(**kwargs)

    def progress_hook(self, data):
        self.check_cancelled()
        key = data.get("filename")
        info = data.get("info_dict") or {}

        if data["status"] == "downloading":
            bar = self.bars.get(key)
            if bar is None:
                label = "Audio" if info.get("vcodec") == "none" else "Video"
                total = data.get("total_bytes") or data.get("total_bytes_estimate")
                bar = self._bar(
                    total=total, unit="B", unit_scale=True,
                    unit_divisor=1024, desc=label,
                )
                self.bars[key] = bar
            downloaded = data.get("downloaded_bytes") or 0
            bar.update(downloaded - bar.n)

        elif data["status"] == "finished":
            bar = self.bars.pop(key, None)
            if bar is not None:
                if bar.total and bar.n < bar.total:
                    bar.update(bar.total - bar.n)
                bar.close()

    @staticmethod
    def _parse_progress(contents):
        """Read FFmpeg's most recent out_time value (microseconds or HH:MM:SS)."""
        for line in reversed(contents.splitlines()):
            if line.startswith(("out_time_us=", "out_time_ms=")):
                try:
                    return max(0.0, int(line.split("=", 1)[1]) / 1_000_000)
                except ValueError:
                    continue
            if line.startswith("out_time="):
                try:
                    hours, minutes, seconds = line.partition("=")[2].split(":")
                    return max(0.0, int(hours) * 3600 + int(minutes) * 60 + float(seconds))
                except ValueError:
                    continue
        return None

    def _interrupt_merger(self):
        """Stop only the FFmpeg child using this download's unique progress file.

        yt-dlp runs its FFmpeg merger as a child process. Its progress hooks
        can't interrupt FFmpeg mid-merge, so identify this particular child by
        the temporary progress-file argument instead of signalling other
        FFmpeg processes or the whole application.
        """
        if self.merge_progress_file is None:
            return
        try:
            result = subprocess.run(
                ["ps", "-ww", "-axo", "pid=,ppid=,command="],
                capture_output=True, text=True, check=True, timeout=3,
            )
        except (OSError, subprocess.SubprocessError):
            return

        for line in result.stdout.splitlines():
            fields = line.strip().split(None, 2)
            if len(fields) != 3:
                continue
            pid_str, ppid_str, command = fields
            if not (pid_str.isdecimal() and ppid_str.isdecimal()):
                continue
            if int(ppid_str) != os.getpid():
                continue
            if "ffmpeg" not in command.lower() or str(self.merge_progress_file) not in command:
                continue
            try:
                os.kill(int(pid_str), signal.SIGTERM)
            except (OSError, ProcessLookupError):
                pass

    def _watch_merge(self):
        while not self._merge_stop.wait(0.2):
            if (self.cancel_event is not None and self.cancel_event.is_set()
                    and not self._merge_cancel_sent):
                self._merge_cancel_sent = True
                self._interrupt_merger()
            try:
                assert self.merge_progress_file is not None
                data = self.merge_progress_file.read_text(errors="replace")
            except OSError:
                continue
            seconds = self._parse_progress(data)
            if seconds is None:
                continue
            with self._merge_lock:
                if self.merge_bar is None:
                    break
                # FFmpeg time can go just past the reported video duration.
                upper = self.merge_bar.total
                position = min(seconds, upper) if upper else seconds
                if position > self._merge_position:
                    self.merge_bar.update(position - self._merge_position)
                    self._merge_position = position

    def _stop_merge(self, completed):
        self._merge_stop.set()
        if self._merge_thread is not None:
            self._merge_thread.join(timeout=1)
            self._merge_thread = None
        with self._merge_lock:
            if self.merge_bar is not None:
                if completed and self.merge_bar.total and self.merge_bar.n < self.merge_bar.total:
                    self.merge_bar.update(self.merge_bar.total - self.merge_bar.n)
                self.merge_bar.close()
                self.merge_bar = None

    def postprocessor_hook(self, data):
        self.check_cancelled()
        if data.get("postprocessor") != "Merger":
            return
        if data["status"] == "started":
            self._merge_stop.clear()
            self._merge_position = 0.0
            self._merge_cancel_sent = False
            with self._merge_lock:
                self.merge_bar = self._bar(
                    total=self.duration, unit="s", desc="Merging",
                )
            self._merge_thread = threading.Thread(target=self._watch_merge, daemon=True)
            self._merge_thread.start()
        elif data["status"] == "finished":
            self._stop_merge(completed=True)

    def close(self):
        """Release remaining bars after cancellation or errors."""
        self._stop_merge(completed=False)
        for bar in self.bars.values():
            bar.close()
        self.bars.clear()


# ---------------------------------------------------------------------------
# Video download and title lookup
# ---------------------------------------------------------------------------


def _format_selector(quality):
    """Preserve exact MP4 choices; allow every format for highest quality."""
    if quality in HIGHEST_CHOICES or quality is None:
        # yt-dlp chooses any best video/audio combination, with a single-file
        # fallback when separate streams are unavailable.
        return "bestvideo+bestaudio/best"
    height = int(quality.rstrip("p"))
    return f"bestvideo[height={height}][ext=mp4]+bestaudio[ext=m4a]"


def _video_metadata(info):
    """Use the selected *video* stream; never use the audio stream's FPS."""
    formats = info.get("requested_formats") or [info]
    video = next((fmt for fmt in formats if fmt.get("vcodec") != "none"), None)
    video = video or info

    height = video.get("height") or info.get("height")
    if not height:
        for fmt in (video, info):
            description = str(fmt.get("resolution") or fmt.get("format_note") or "")
            match = re.search(r"(?:\d+x)?(\d{3,4})(?:p\d+)?(?:\D|$)", description)
            if match:
                height = int(match.group(1))
                break
    try:
        height = int(height) if height else None
    except (ValueError, TypeError):
        height = None

    resolution = f"{height}p" if height else "unknown resolution"
    fps = video.get("fps") or info.get("fps")
    fps_display = f"{fps} fps" if fps else "unknown fps"
    return resolution, fps_display


def _download_options(format_selector, output_path, temp_dir, logger, progress, quality):
    """Configure one download without changing any global output streams."""
    progress.merge_progress_file = Path(temp_dir) / "ffmpeg-progress.txt"
    # All highest-quality stream types are eligible. Let yt-dlp select the
    # compatible destination container (MP4, WebM or MKV).
    merge_format = None if quality in HIGHEST_CHOICES or quality is None else "mp4"
    merger_args = [
        "-stats_period", "0.2", "-progress", str(progress.merge_progress_file),
    ]
    if merge_format == "mp4":
        merger_args += ["-movflags", "+faststart"]
    return {
        "format": format_selector,
        "merge_output_format": merge_format,
        "postprocessor_args": {"merger": merger_args},
        "paths": {"home": str(output_path), "temp": temp_dir},
        "overwrites": True,
        "noplaylist": True,
        "quiet": True,
        "no_warnings": True,
        "noprogress": True,
        "logger": logger,
        "progress_hooks": [progress.progress_hook],
        "postprocessor_hooks": [progress.postprocessor_hook],
        "socket_timeout": 60,
        "retries": 10,
        "fragment_retries": 10,
        "file_access_retries": 3,
    }

def _ffmpeg_location():
    """Prefer the bundled FFmpeg/FFprobe pair; use PATH only in development."""
    resources = os.environ.get("RESOURCEPATH")  # Provided by py2app.
    folders = []
    if hasattr(sys, "_MEIPASS"):
        folders.append(Path(sys._MEIPASS) / "bin")
    if resources:
        folders.append(Path(resources) / "bin")
    if getattr(sys, "frozen", False):
        folders.append(Path(sys.executable).resolve().parent.parent / "Resources" / "bin")
    folders.append(Path(__file__).resolve().parent / "vendor" / "bin")

    for folder in folders:
        if all((folder / name).is_file() and os.access(folder / name, os.X_OK)
               for name in ("ffmpeg", "ffprobe")):
            return str(folder)

    if resources or getattr(sys, "frozen", False):
        raise RuntimeError(
            "This app was packaged without working FFmpeg and FFprobe executables. "
            "Please obtain a corrected app build from its developer."
        )
    if shutil.which("ffmpeg") and shutil.which("ffprobe"):
        return None  # Let yt-dlp discover both on PATH while developing.
    raise RuntimeError(
        "FFmpeg and FFprobe are required. For a standalone app, place executable "
        "macOS binaries in vendor/bin/ before building with py2app."
    )

def _write_log(log, message):
    """Send worker output directly to its own queue, or to the terminal."""
    if log is None:
        print(message)
    else:
        log.write(message + "\n")


def download_video(url, quality=None, output_path=DOWNLOAD_PATH, *, log=None, cancel_event=None):
    """Download the selected video, reporting directly to the supplied log."""
    output_path = Path(output_path)
    output_path.mkdir(parents=True, exist_ok=True)

    ffmpeg_location = _ffmpeg_location()

    format_selector = _format_selector(quality)
    progress = _DownloadProgress(log, cancel_event)
    logger = DownloadLogger(progress.bars)
    progress.check_cancelled()

    try:
        with tempfile.TemporaryDirectory() as temp_dir:
            options = _download_options(
                format_selector, output_path, temp_dir, logger, progress, quality
            )
            if ffmpeg_location is not None:
                options["ffmpeg_location"] = ffmpeg_location
            with yt_dlp.YoutubeDL(cast(Any, options)) as ydl:
                progress.check_cancelled()
                try:
                    info = ydl.extract_info(url, download=False)
                except DownloadError as error:
                    if "requested format is not available" in str(error).lower():
                        raise ValueError(f"No suitable video stream found: {url}") from error
                    raise
                progress.check_cancelled()

                title_text = info.get("title") or "(Untitled)"
                author = info.get("channel") or info.get("uploader") or "Unknown"
                resolution, fps = _video_metadata(info)
                _write_log(log, f"\nDownloading: {title_text}")
                stream_kind = (
                    "separate streams" if len(tuple(info.get("requested_formats") or ())) > 1
                    else "single stream"
                )
                _write_log(log, f"Selected: {resolution} ({fps}, {stream_kind})")
                try:
                    duration = info.get("duration")
                    progress.duration = float(duration) if duration is not None else None
                except (TypeError, ValueError):
                    progress.duration = None

                # Both metadata components are cleaned, and the actual chosen
                # video height (rather than the quality menu label) is named.
                name = f"{safe_filename(title_text)} ({safe_filename(author)}) [{resolution}]"
                extension = info.get("ext") or "mp4"
                # Preserve faststart optimization when the highest-quality
                # selection still produces MP4; omit it for WebM/MKV.
                if quality in HIGHEST_CHOICES or quality is None:
                    if extension == "mp4":
                        existing_args = cast(
                            dict[str, list[str]],
                            ydl.params.get("postprocessor_args") or {},
                        )
                        ydl.params["postprocessor_args"] = {
                            **existing_args,
                            "merger": [
                                *(existing_args.get("merger") or ()),
                                "-movflags",
                                "+faststart",
                            ],
                        }

                final_path = output_path / f"{name}.{extension}"
                ydl.params["outtmpl"] = {
                    "default": name.replace("%", "%%") + ".%(ext)s"
                }
                result = ydl.process_ie_result(info, download=True)
                # A yt-dlp merger may choose a different extension after
                # processing metadata; this reflects the final file format.
                processed_info = result if isinstance(result, dict) else info
                extension = processed_info.get("ext") or info.get("ext") or extension
                final_path = output_path / f"{name}.{extension}"
    finally:
        progress.close()

    _write_log(log, f"Saved: {final_path}")
    return final_path


def fetch_title_oembed(url, timeout=8):
    """Fast title lookup via YouTube's public oEmbed endpoint.

    Returns the title, or None on any failure (caller falls back to yt-dlp).
    """
    try:
        endpoint = (
            "https://www.youtube.com/oembed?format=json&url="
            + urllib.parse.quote(url, safe="")
        )
        request = urllib.request.Request(
            endpoint, headers={"User-Agent": "Mozilla/5.0"}
        )
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return json.load(response).get("title") or None
    except Exception:
        return None


def fetch_title(url):
    """Look up a video title.

    Tries the fast oEmbed endpoint first, then falls back to yt-dlp (which
    also covers videos with embedding disabled and gives a reliable
    valid/invalid answer).

    Returns the title, or None if the link is invalid / unavailable.
    Other errors (e.g. no internet) propagate so they aren't mislabeled invalid.
    """
    if not YOUTUBE_URL.match(url.strip()):
        return None

    title = fetch_title_oembed(url)
    if title:
        return title

    options = {
        "noplaylist": True,
        "quiet": True,
        "no_warnings": True,
        "logger": SilentLogger(),
        "skip_download": True,
    }
    try:
        with yt_dlp.YoutubeDL(cast(Any, options)) as ydl:
            # process=False skips format selection, which makes this much quicker.
            info = ydl.extract_info(url, download=False, process=False)
    except DownloadError as error:
        message = str(error).lower()
        if any(marker in message for marker in INVALID_MARKERS):
            return None
        raise
    return (info or {}).get("title") or "(Untitled)"


# ---------------------------------------------------------------------------
# GUI helpers and widgets
# ---------------------------------------------------------------------------


class QueueWriter:
    """File-like object that forwards everything written to a queue."""

    def __init__(self, q):
        self.q = q

    def write(self, text):
        if text:
            self.q.put(text)
        return len(text)

    def flush(self):
        pass

    def isatty(self):
        return False


class Dropdown(ttk.OptionMenu):
    """Native menu-backed selector with a compact, non-selectable label."""

    def __init__(self, parent, variable, values):
        super().__init__(parent, variable, variable.get(), *values)
        font_name = ttk.Style(self).lookup("TMenubutton", "font") or "TkDefaultFont"
        menu_font = tkfont.Font(root=self, font=font_name)
        digit_width = max(menu_font.measure("0"), 1)
        text_width = max(menu_font.measure(value) for value in values)
        self.configure(width=(text_width + digit_width - 1) // digit_width)
        # Aqua owns its menu highlight; other platforms honor these colors.
        self["menu"].configure(activebackground="#dcdcdc", activeforeground="black")

    def set_enabled(self, enabled):
        self.configure(state="normal" if enabled else "disabled")


class Row:
    """One table row: status, link, quality, title."""

    def __init__(self):
        self.url_var = tk.StringVar()
        self.quality_var = tk.StringVar(value=QUALITY_CHOICES[0])
        self.title_var = tk.StringVar()
        self.status = "blank"
        self.check = "idle"
        self.after_id = None

        self.status_label: ttk.Label | None = None
        self.entry: ttk.Entry | None = None
        self.dropdown: Dropdown | None = None
        self.title_label: tk.Label | None = None

    def widgets(self):
        return (self.status_label, self.entry, self.dropdown, self.title_label)


class DownloaderApp:
    """Manage the Tkinter UI, title checks, and the queued download worker."""

    def __init__(self, root):
        self.root = root
        root.title("YouTube Downloader")
        root.geometry("920x640")
        root.minsize(700, 480)

        self.rows = []
        self.log_queue = queue.Queue()
        self.ui_queue = queue.Queue()  # callbacks posted from worker threads
        self.carriage_return = False
        self.running = False
        self.cancel_event = threading.Event()
        self.all_quality_var = tk.StringVar(value=QUALITY_CHOICES[0])

        main = ttk.Frame(root, padding=12)
        main.pack(fill="both", expand=True)
        main.columnconfigure(0, weight=1)
        main.rowconfigure(1, weight=2)
        main.rowconfigure(4, weight=3)

        self._build_header(main)
        self._build_table(main)
        self._build_download_button(main)
        self._build_log(main)
        self._bind_global_events()

        self.add_row()
        self._align_header_columns()
        self.root.after(50, self.poll_queues)

    def _build_header(self, main):
        self.header = ttk.Frame(main)
        header = self.header
        # The 1px pad matches the table frame's border.
        header.grid(row=0, column=0, sticky="ew", padx=(1, 0))
        self.configure_columns(header)
        bold = ("Helvetica", 12, "bold")
        for column, label, padding in (
            (0, "Status", 0),
            (1, "YouTube Video Link", (4, 8)),
            (2, "Quality", (0, 8)),
            (3, "Video Title", (0, 4)),
        ):
            ttk.Label(
                header, text=label, font=bold,
                anchor="center" if column == 0 else "w",
            ).grid(
                row=0, column=column,
                sticky="ew" if column == 0 else "w", padx=padding,
            )

    def _build_table(self, main):
        self.table_frame = ttk.Frame(main, relief="sunken", borderwidth=1)
        self.table_frame.grid(row=1, column=0, sticky="nsew", pady=(2, 0))
        self.table_frame.columnconfigure(0, weight=1)
        self.table_frame.rowconfigure(0, weight=1)

        self.canvas = tk.Canvas(
            self.table_frame, highlightthickness=0, yscrollincrement=24
        )
        self.scrollbar = ttk.Scrollbar(
            self.table_frame, orient="vertical", command=self.canvas.yview
        )
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.scrollbar.grid(row=0, column=1, sticky="ns")

        self.table = ttk.Frame(self.canvas)
        self.configure_columns(self.table)
        self.table_window = self.canvas.create_window(
            (0, 0), window=self.table, anchor="nw"
        )
        self.table.bind("<Configure>", self.update_scrollregion)
        self.canvas.bind("<Configure>", self.on_canvas_configure)

    def _build_download_button(self, main):
        # The toolbar remains full-width when its controls are swapped.
        # Left-side bulk controls; Download centered in the right third.
        self.toolbar = ttk.Frame(main, height=40)
        self.toolbar.grid(row=2, column=0, sticky="ew", pady=10)
        self.toolbar.grid_propagate(False)
        self.toolbar.bind("<Configure>", self._position_bulk_controls)

        self.bulk_controls = ttk.Frame(self.toolbar)
        self.set_all_button = ttk.Button(
            self.bulk_controls, text="Set all to:", command=self.set_all_quality
        )
        self.set_all_button.grid(row=0, column=0, padx=(0, 5))
        self.all_quality_dropdown = Dropdown(
            self.bulk_controls, self.all_quality_var, QUALITY_CHOICES
        )
        self.all_quality_dropdown.grid(row=0, column=1, pady=(2.4, 0))

        self.download_button = ttk.Button(
            self.toolbar, text="Download", command=self.start_download
        )
        # Keep the native macOS button appearance; Aqua does not support
        # changing a standard ttk button's background color reliably.
        self.cancel_button = ttk.Button(
            self.toolbar, text="Cancel", command=self.cancel_download
        )
        self._show_download_button()

    def _build_log(self, main):
        # Copying and selection are allowed, but text editing is blocked.
        ttk.Label(main, text="Log", font=("Helvetica", 12, "bold")).grid(
            row=3, column=0, sticky="w"
        )
        log_frame = ttk.Frame(main)
        log_frame.grid(row=4, column=0, sticky="nsew")
        log_frame.columnconfigure(0, weight=1)
        log_frame.rowconfigure(0, weight=1)

        self.log = tk.Text(
            log_frame,
            wrap="none",
            font=("Menlo", 11),
            height=10,
            insertwidth=0,  # hide the text cursor
        )
        log_scroll = ttk.Scrollbar(
            log_frame, orient="vertical", command=self.log.yview
        )
        self.log.configure(yscrollcommand=log_scroll.set)
        self.log.grid(row=0, column=0, sticky="nsew")
        log_scroll.grid(row=0, column=1, sticky="ns")

        self.log.bind("<Key>", self.on_log_key)
        for sequence in (
            "<<Paste>>", "<<Cut>>", "<<Clear>>", "<<PasteSelection>>",
            "<<Undo>>", "<<Redo>>",
        ):
            self.log.bind(sequence, lambda e: "break")
        self.log.bind("<MouseWheel>", self.on_log_wheel)
        self.log.bind("<Button-4>", self.on_log_wheel)
        self.log.bind("<Button-5>", self.on_log_wheel)

    def _bind_global_events(self):
        # Clicking elsewhere clears focus; scrolling over the table scrolls it.
        self.root.bind_all("<Button-1>", self.on_global_click, add="+")
        self.root.bind_all("<MouseWheel>", self.on_mousewheel, add="+")
        self.root.bind_all("<Button-4>", self.on_mousewheel, add="+")
        self.root.bind_all("<Button-5>", self.on_mousewheel, add="+")

    def _align_header_columns(self):
        # The quality column matches its row selector, not toolbar controls.
        self.root.update_idletasks()
        quality_width = self.rows[0].dropdown.winfo_reqwidth() + 8
        for frame in (self.header, self.table):
            frame.columnconfigure(2, minsize=quality_width)
        self.header.columnconfigure(4, minsize=self.scrollbar.winfo_reqwidth() + 1)

    @staticmethod
    def configure_columns(frame):
        """Shared column layout for the header and the table."""
        frame.columnconfigure(0, minsize=56)
        frame.columnconfigure(1, weight=1, uniform="wide")
        frame.columnconfigure(3, weight=1, uniform="wide")

    def update_scrollregion(self, _event=None):
        """Keep the region at least as tall as the view so you can't scroll above the top."""
        content = self.table.winfo_reqheight()
        view = self.canvas.winfo_height()
        self.canvas.configure(
            scrollregion=(0, 0, self.canvas.winfo_width(), max(content, view))
        )
        if content <= view:
            self.canvas.yview_moveto(0)

    def on_canvas_configure(self, event):
        self.canvas.itemconfigure(self.table_window, width=event.width)
        self.update_scrollregion()

    @staticmethod
    def is_within(widget, ancestor):
        while widget is not None:
            if widget is ancestor:
                return True
            widget = widget.master
        return False

    def on_global_click(self, event):
        widget = event.widget
        if not isinstance(widget, tk.Misc):
            return

        if widget.winfo_toplevel() is not self.root:
            return
        if isinstance(widget, (ttk.Entry, tk.Entry, tk.Text)):
            return
        self.root.focus_set()

    def on_mousewheel(self, event):
        widget = event.widget
        if not isinstance(widget, tk.Misc):
            return
        if not self.is_within(widget, self.table_frame):
            return
        units = wheel_units(event)
        top, bottom = self.canvas.yview()
        # Only scroll when there's more content in that direction.
        if (units < 0 and top > 0.0) or (units > 0 and bottom < 1.0):
            self.canvas.yview_scroll(units, "units")
        return "break"

    def on_log_wheel(self, event):
        self.log.yview_scroll(wheel_units(event), "units")
        return "break"

    def on_log_key(self, event):
        """Block all edits in the log while still allowing navigation, select-all and copy."""
        if event.keysym in LOG_NAV_KEYS:
            return None
        # Control (0x4) or Command (0x8 on macOS) combined with C or A.
        if event.state & 0x4 or (sys.platform == "darwin" and event.state & 0x8):
            if event.keysym.lower() in ("c", "a"):
                return None
        return "break"

    def add_row(self):
        index = len(self.rows)
        row = Row()
        self._create_row_widgets(row, index)

        self.rows.append(row)
        row.url_var.trace_add("write", lambda *_: self.on_url_changed(row))
        if index == 0:
            assert row.entry is not None
            row.entry.focus_set()

    def _create_row_widgets(self, row, index):
        row.status_label = ttk.Label(
            self.table, text="", width=4, anchor="center",
            font=("Helvetica", 13, "bold"),
        )
        row.status_label.grid(row=index, column=0, sticky="ew", pady=2)

        row.entry = ttk.Entry(self.table, textvariable=row.url_var)
        row.entry.grid(row=index, column=1, sticky="ew", padx=(4, 8), pady=2)
        row.entry.bind("<FocusOut>", lambda e, w=row.entry: w.selection_clear())

        row.dropdown = Dropdown(self.table, row.quality_var, QUALITY_CHOICES)
        row.dropdown.grid(row=index, column=2, sticky="w", padx=(0, 8), pady=2)

        # Output-only box: a plain light-grey label (not selectable, not focusable).
        row.title_label = tk.Label(
            self.table, textvariable=row.title_var,
            anchor="w", bg=OUTPUT_BG, fg="black",
            padx=6, pady=3, width=1,
            highlightthickness=1, highlightbackground="#d4d4d4",
            takefocus=0,
        )
        row.title_label.grid(row=index, column=3, sticky="ew", padx=(0, 4), pady=2)


    def prune_row(self, row):
        """Remove a row that is empty, unless it's the single blank row at the end."""
        if row not in self.rows or self.running:
            return
        if row.url_var.get().strip() or row is self.rows[-1]:
            return

        index = self.rows.index(row)
        had_focus = self.root.focus_get() is row.entry

        if row.after_id is not None:
            self.root.after_cancel(row.after_id)
            row.after_id = None
        self.rows.remove(row)
        for widget in row.widgets():
            widget.destroy()

        for new_index, remaining in enumerate(self.rows):
            for widget in remaining.widgets():
                widget.grid_configure(row=new_index)

        if had_focus and self.rows:
            self.rows[min(index, len(self.rows) - 1)].entry.focus_set()

    def set_status(self, row, status):
        if row not in self.rows:
            return
        row.status = status
        text, color = STATUS_DISPLAY[status]
        row.status_label.configure(text=text, foreground=color)

    def set_title(self, row, text, invalid=False):
        row.title_var.set(text)
        row.title_label.configure(fg=RED if invalid else "black")

    def on_url_changed(self, row):
        if row not in self.rows:
            return
        if row.after_id is not None:
            self.root.after_cancel(row.after_id)
            row.after_id = None

        url = row.url_var.get().strip()
        row.check = "pending" if url else "idle"
        self.set_status(row, "blank")
        self.set_title(row, "")

        if url:
            # Debounce so we don't check on every keystroke.
            row.after_id = self.root.after(600, lambda: self.start_check(row, url))
        else:
            # Prune once the current edit finishes (so select-all + paste still works).
            self.root.after_idle(lambda: self.prune_row(row))

        # When the last row gets text, add a fresh empty row below it.
        if row is self.rows[-1] and url:
            self.add_row()
            self.root.after(20, lambda: self.canvas.yview_moveto(1.0))

    def start_check(self, row, url):
        row.after_id = None

        def work():
            try:
                title = fetch_title(url)
                error = None
            except Exception as exc:
                if needs_vpn_change(exc):
                    self.log_queue.put("Tip: Change VPN Location.\n")

                title, error = None, exc
            self.ui_queue.put(lambda: self.finish_check(row, url, title, error))

        threading.Thread(target=work, daemon=True).start()

    def finish_check(self, row, url, title, error):
        if row not in self.rows or row.url_var.get().strip() != url:
            return  # row removed or link changed while checking; ignore stale result

        if error is not None:
            row.check = "error"
            self.set_title(row, "Could not check link", invalid=True)
        elif title is None:
            row.check = "invalid"
            self.set_title(row, "Invalid", invalid=True)
        else:
            row.check = "valid"
            self.set_title(row, title)
            if row.status == "blank":
                self.set_status(row, "valid")

    def set_all_quality(self):
        """Apply the selected header quality to every row in one operation."""
        if self.running:
            return
        choice = self.all_quality_var.get()
        for row in self.rows:
            row.quality_var.set(choice)

    def set_inputs_enabled(self, enabled):
        self.set_all_button.configure(state="normal" if enabled else "disabled")
        self.all_quality_dropdown.set_enabled(enabled)
        for row in self.rows:
            row.entry.configure(state="normal" if enabled else "disabled")
            row.dropdown.set_enabled(enabled)
        if not enabled:
            self.root.focus_set()

    def append_log(self, text):
        """Append text, emulating terminal handling of \\r (tqdm progress bars)."""
        for part in re.split(r"(\r|\n)", text):
            if not part:
                continue
            if part == "\r":
                self.carriage_return = True
            elif part == "\n":
                self.carriage_return = False
                self.log.insert("end", "\n")
            else:
                if self.carriage_return:
                    self.log.delete("end-1c linestart", "end-1c")
                    self.carriage_return = False
                self.log.insert("end", part)
        self.log.see("end")

    def poll_queues(self):
        chunks = []
        try:
            while True:
                chunks.append(self.log_queue.get_nowait())
        except queue.Empty:
            pass
        if chunks:
            self.append_log("".join(chunks))

        try:
            while True:
                callback = self.ui_queue.get_nowait()
                callback()
        except queue.Empty:
            pass

        self.root.after(50, self.poll_queues)

    def _collect_jobs(self):
        """Completed blue-check rows never re-enter the download queue."""
        jobs = []
        for row in self.rows:
            if row.check == "valid" and row.status in ("valid", "failed"):
                choice = row.quality_var.get()
                quality = None if choice in HIGHEST_CHOICES else choice
                jobs.append((row, row.url_var.get().strip(), quality))
        return jobs

    def _position_bulk_controls(self, _event=None):
        if self.bulk_controls.winfo_manager() == "place":
            center = max(self.toolbar.winfo_width() / 3.6,
                         self.bulk_controls.winfo_reqwidth() / 2)
            self.bulk_controls.place_configure(relx=0, x=round(center))

    def _show_cancel_button(self):
        self.bulk_controls.place_forget()
        self.download_button.place_forget()
        self.cancel_button.place(relx=0.5, rely=0.5, anchor="center")

    def _show_download_button(self, ready=True):
        self.cancel_button.place_forget()
        self.bulk_controls.place(rely=0.5, y=2, anchor="center")
        self._position_bulk_controls()
        self.download_button.configure(state="normal" if ready else "disabled")
        self.download_button.place(relx=4.1 / 6, rely=0.5, anchor="center")

    def start_download(self):
        if self.running:
            return
        if any(row.check == "pending" for row in self.rows):
            self.append_log("Still checking some links, try again in a moment.\n")
            return

        jobs = self._collect_jobs()
        if not jobs:
            self.append_log("No new valid links to download.\n")
            return

        self.running = True
        self.cancel_event.clear()
        self._show_cancel_button()
        self.set_inputs_enabled(False)
        prior_statuses = {row: row.status for row, _url, _quality in jobs}
        for row, _url, _quality in jobs:
            self.set_status(row, "queued")

        thread = threading.Thread(
            target=self.run_jobs, args=(jobs, prior_statuses), daemon=True
        )
        thread.start()

    def cancel_download(self):
        if not self.running or self.cancel_event.is_set():
            return
        self.cancel_event.set()
        # Restore the toolbar immediately; don't permit another run until
        # the active worker actually exits and releases its download resources.
        self._show_download_button(ready=False)
        self.append_log("\nCancelling download...\n")

    def run_jobs(self, jobs, prior_statuses):
        """Run in one worker; send text to the UI without replacing sys.stdout."""
        writer = QueueWriter(self.log_queue)
        cancelled = False
        try:
            for row, url, quality in jobs:
                if self.cancel_event.is_set():
                    cancelled = True
                    break
                try:
                    download_video(
                        url, quality, DOWNLOAD_PATH,
                        log=writer, cancel_event=self.cancel_event,
                    )
                except DownloadCancelled:
                    cancelled = True
                    break
                except Exception as error:
                    if self.cancel_event.is_set():
                        cancelled = True
                        break
                    _write_log(writer, f"\nFailed: {url}\n{type(error).__name__}: {error}")
                    if needs_vpn_change(error):
                        _write_log(writer, "Tip: Change VPN Location.")
                    self.ui_queue.put(lambda r=row: self.set_status(r, "failed"))
                else:
                    self.ui_queue.put(lambda r=row: self.set_status(r, "done"))
            if self.cancel_event.is_set():
                cancelled = True
            _write_log(writer, "\nCancelled." if cancelled else "\nAll done.")
        finally:
            self.ui_queue.put(
                lambda: self.finish_download(jobs, prior_statuses)
            )

    def finish_download(self, jobs=None, prior_statuses=None):
        # Restore unstarted/interrupted rows to their previous retryable state.
        for row, _url, _quality in jobs or ():
            if row.status == "queued":
                assert prior_statuses is not None
                self.set_status(row, prior_statuses.get(row, "valid"))
        self.running = False
        self._show_download_button()
        self.set_inputs_enabled(True)


if __name__ == "__main__":
    # A frozen macOS app is also the Python executable for spawned workers.
    # Divert multiprocessing helpers before creating a second Tk window.
    from multiprocessing import freeze_support

    freeze_support()
    root = tk.Tk()
    DownloaderApp(root)
    root.mainloop()


