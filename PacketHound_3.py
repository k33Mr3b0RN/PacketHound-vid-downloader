#!/usr/bin/env python3
"""
PacketHound Vid Downloader (yt-dlp based)  v3.0
- Supports YouTube and 1000+ sites via yt-dlp
- Custom headers / cookies for restricted or login-required sites
- Automatic dependency installation (including ffmpeg)
- Subtitles, audio only, thumbnails, metadata, batch mode
- Live stream recording, battery/charging detection, bandwidth forecasting
-- NEW in v2.0 --
- Clipboard watcher: auto-detects video URLs copied to clipboard
- Download stats dashboard: per-session counters, speed tracking, top sources
- Parallel/concurrent downloads with configurable worker count
- Download scheduling: set a time window (e.g. 02:00-06:00)
- Post-download webhooks: ping a URL when a download finishes
- Archive mode: skip already-downloaded URLs using yt-dlp's --download-archive
- Notification sounds on download complete/fail (cross-platform)
- Playlist metadata save: dump playlist JSON alongside downloads
-- NEW in v3.0 --
- Universal terminal compatibility: iOS (a-Shell, iSH, Pythonista, Carnets),
  Android (Termux, AIDE, Pydroid 3), Windows (cmd, PowerShell, Windows Terminal),
  macOS (Terminal.app, iTerm2, Alacritty), Linux (any)
- Adaptive UI: auto-detects terminal width, color support, and Unicode capability;
  gracefully degrades on restricted environments (no ANSI, narrow screens, no emoji)
- Image Upscaler: upscale any local image using Real-ESRGAN (GPU/CPU) or Pillow
  fallback; resolutions from 240p up to 8K (7680×4320) with per-preset controls
"""

import subprocess
import sys
import os
import json
import shutil
import time
import traceback
import re
import tempfile
from datetime import datetime
import threading
import queue as _queue
import urllib.parse
import urllib.request
import socket
import hashlib

# ======================================================================
# CROSS-PLATFORM TERMINAL COMPATIBILITY  (v3.0)
# Detects the runtime environment and configures safe defaults for:
#   - iOS:     a-Shell, iSH, Pythonista, Carnets
#   - Android: Termux, Pydroid 3, AIDE
#   - Windows: cmd.exe, PowerShell, Windows Terminal, Cygwin, MSYS2
#   - macOS:   Terminal.app, iTerm2, Alacritty, Hyper
#   - Linux:   xterm, GNOME Terminal, Konsole, Kitty, etc.
# ======================================================================

def _detect_terminal_env():
    """Return a dict of terminal capability flags for the current platform."""
    env = {}

    # ── Platform ──────────────────────────────────────────────────────
    env["is_windows"]  = sys.platform == "win32"
    env["is_macos"]    = sys.platform == "darwin"
    env["is_linux"]    = sys.platform.startswith("linux")
    env["is_ios"]      = False
    env["is_android"]  = False

    # iOS detection: a-Shell sets SHELL=/bin/sh and has no standard /proc;
    # iSH (Alpine on iOS) has /proc but is_linux is True and PREFIX is absent.
    # Most reliable heuristic: check for a-Shell's unique env vars.
    _ashell_marker = os.environ.get("ASHELL_VERSION") or os.path.exists(
        os.path.expanduser("~/Documents/.ashell"))
    _ish_marker    = os.path.exists("/proc/ish")
    _ios_python    = os.environ.get("PYTHONISTA_CONSOLE") or os.environ.get(
        "CARNETS_APP")
    if _ashell_marker or _ish_marker or _ios_python:
        env["is_ios"] = True

    # Android / Termux detection
    _termux_prefix = os.environ.get("PREFIX", "")
    _termux_home   = os.environ.get("TERMUX_VERSION") or (
        "/data/data/com.termux" in _termux_prefix)
    _pydroid       = os.environ.get("ANDROID_DATA") and not _termux_home
    if _termux_home or _pydroid or os.environ.get("TERMUX_VERSION"):
        env["is_android"] = True

    # ── Terminal dimensions ────────────────────────────────────────────
    try:
        _sz = shutil.get_terminal_size(fallback=(80, 24))
        env["term_cols"] = _sz.columns
        env["term_rows"] = _sz.lines
    except Exception:
        env["term_cols"] = 80
        env["term_rows"] = 24
    env["is_narrow"] = env["term_cols"] < 60   # e.g. iPhone in portrait

    # ── Colour / ANSI support ──────────────────────────────────────────
    # TERM=dumb, NO_COLOR, or Windows without VIRTUAL_TERMINAL_PROCESSING
    # all mean: no ANSI escape codes.
    _no_color    = os.environ.get("NO_COLOR")          # https://no-color.org
    _term        = os.environ.get("TERM", "")
    _colorterm   = os.environ.get("COLORTERM", "")
    _wt_session  = os.environ.get("WT_SESSION")         # Windows Terminal
    _force_color = os.environ.get("FORCE_COLOR")

    if _force_color:
        env["color_support"] = True
    elif _no_color or _term == "dumb":
        env["color_support"] = False
    elif env["is_windows"]:
        # Windows ≥ 10 1511: enable VT processing via ctypes
        _vt_ok = False
        try:
            import ctypes
            kernel32 = ctypes.windll.kernel32
            # ENABLE_VIRTUAL_TERMINAL_PROCESSING = 0x0004
            handle = kernel32.GetStdHandle(-11)     # STD_OUTPUT_HANDLE
            mode   = ctypes.c_ulong()
            if kernel32.GetConsoleMode(handle, ctypes.byref(mode)):
                kernel32.SetConsoleMode(handle, mode.value | 0x0004)
                _vt_ok = True
        except Exception:
            pass
        env["color_support"] = _vt_ok or bool(_wt_session) or bool(_colorterm)
    else:
        # Unix: color if connected to a tty and TERM isn't dumb/unknown
        env["color_support"] = (
            hasattr(sys.stdout, "isatty") and sys.stdout.isatty()
            and _term not in ("", "dumb", "unknown")
        )

    # ── Unicode / emoji support ────────────────────────────────────────
    # Windows cmd.exe (cp850/cp1252) and some SSH sessions lack full Unicode.
    # Force UTF-8 output on platforms that support it.
    _encoding = getattr(sys.stdout, "encoding", "") or ""
    env["utf8_support"] = _encoding.lower().replace("-", "") in (
        "utf8", "utf-8", "") or env["is_ios"] or env["is_android"]

    # On Windows try to switch console to UTF-8 (code page 65001)
    if env["is_windows"]:
        try:
            import ctypes
            ctypes.windll.kernel32.SetConsoleOutputCP(65001)
            ctypes.windll.kernel32.SetConsoleCP(65001)
            env["utf8_support"] = True
        except Exception:
            pass
        # Also set Python's stdout/stderr to UTF-8
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")  # type: ignore
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")  # type: ignore
        except Exception:
            pass

    # Emoji: conservative — only on known-good terminals
    _emoji_ok = (
        env["utf8_support"] and (
            env["is_ios"] or env["is_android"] or env["is_macos"]
            or bool(_wt_session) or bool(_colorterm)
            or "xterm" in _term or "256color" in _term
            or "kitty" in _term or "iterm" in _term.lower()
        )
    )
    env["emoji_support"] = _emoji_ok

    return env

TERM_ENV = _detect_terminal_env()

def _e(emoji_str, fallback_str=""):
    """Return emoji_str if the terminal supports it, else fallback_str."""
    return emoji_str if TERM_ENV.get("emoji_support") else fallback_str

def _safe_clear():
    """Clear the screen in a cross-platform, safe way."""
    if TERM_ENV.get("color_support"):
        os.system("cls" if TERM_ENV["is_windows"] else "clear")
    else:
        # No ANSI: just print blank lines so the terminal looks clean
        print("\n" * 4)

def _safe_print(msg, **kwargs):
    """Print with safe encoding fallback (replaces unencodable chars)."""
    try:
        print(msg, **kwargs)
    except UnicodeEncodeError:
        # Strip all non-ASCII as last resort
        safe = msg.encode("ascii", errors="replace").decode("ascii")
        print(safe, **kwargs)

# ── Windows: ensure input() can handle Unicode paste ──────────────────
if TERM_ENV["is_windows"]:
    try:
        import msvcrt
        # Switch stdin to Unicode mode
        import ctypes
        ctypes.windll.kernel32.SetConsoleCP(65001)
    except Exception:
        pass

# ----------------------------------------------------------------------
# Auto-install Python packages (rich, yt-dlp)
# ----------------------------------------------------------------------
RICH_AVAILABLE = False

def auto_install(package, display_name, pip_name=None):
    if pip_name is None:
        pip_name = package
    try:
        __import__(package)
        return True
    except ImportError:
        print(f"📦 Installing {display_name}...")
        try:
            subprocess.run([sys.executable, "-m", "pip", "install", "--quiet", pip_name],
                           check=True, capture_output=True)
            __import__(package)
            print(f"✅ {display_name} installed successfully.")
            return True
        except Exception as e:
            print(f"❌ Failed to install {display_name}: {e}")
            print(f"   Please install manually: pip install {pip_name}")
            return False

# Install rich
if auto_install("rich", "rich"):
    RICH_AVAILABLE = True
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    from rich.progress import Progress, SpinnerColumn, TextColumn
    from rich import box
    from rich.live import Live
    from rich.table import Table as RichTable
    # Override Rich's built-in magenta/cyan prompt theme with blue/white.
    # Rich uses named theme styles "prompt.choices" (default: magenta) and
    # "prompt.default" (default: cyan). Overriding the Console theme is the
    # correct approach — no make_prompt subclass needed.
    from rich.theme import Theme
    from rich.text import Text
    from rich.style import Style
    from rich.prompt import Prompt as _BasePrompt, Confirm as _BaseConfirm

    _blue_white_theme = Theme({
        "prompt":          "white",
        "prompt.choices":  "bold blue",
        "prompt.default":  "white",
        "prompt.invalid":  "bold white",
    })
    # Respect the terminal detection: disable color if the terminal can't handle it
    console = Console(
        theme=_blue_white_theme,
        highlight=False,
        force_terminal=TERM_ENV.get("color_support", True),
        no_color=not TERM_ENV.get("color_support", True),
    )

    # Belt-and-suspenders: also override make_prompt so older Rich versions
    # that don't resolve theme names inside Text.append() still get the right
    # colours. Uses Style objects directly — never goes through markup parsing.
    _S_BLUE  = Style(color="blue", bold=True)
    _S_WHITE = Style(color="white")
    _S_DIM   = Style(dim=True)

    class Prompt(_BasePrompt):
        def render_default(self, default) -> Text:
            return Text(f"({default})", style=_S_WHITE)

        def make_prompt(self, default) -> Text:
            t = self.prompt.copy()
            t.end = ""
            if self.show_choices and self.choices:
                t.append(" [" + "/".join(self.choices) + "]", style=_S_BLUE)
            if (default is not ... and self.show_default
                    and isinstance(default, (str, self.response_type))):
                t.append(" ", style=_S_WHITE)
                t.append(self.render_default(default))
            t.append(": ", style=_S_WHITE)
            return t

    class Confirm(_BaseConfirm):
        def render_default(self, default) -> Text:
            d = "y" if default else "n"
            return Text(f"({d})", style=_S_WHITE)

        def make_prompt(self, default) -> Text:
            t = self.prompt.copy()
            t.end = ""
            t.append(" [y/n]", style=_S_BLUE)
            if default is not None:
                t.append(" ", style=_S_WHITE)
                t.append(self.render_default(default))
            t.append(": ", style=_S_WHITE)
            return t
else:
    # Fallback dummy implementations
    class DummyConsole:
        def print(self, *args, **kwargs):
            # Strip Rich markup tags like [bold blue] for plain terminals
            text = " ".join(str(a) for a in args)
            text = re.sub(r"\[/?[a-zA-Z0-9 _#,;]+\]", "", text)
            _safe_print(text)
        def clear(self):
            _safe_clear()
    console = DummyConsole()

    class Prompt:
        @staticmethod
        def ask(prompt, default="", choices=None):
            while True:
                result = input(f"{prompt} [{default}]: ").strip() or default
                if choices is None or result in choices:
                    return result
                print(f"Invalid choice. Please choose from: {', '.join(choices)}")
    class Confirm:
        @staticmethod
        def ask(prompt, default=True):
            return input(f"{prompt} (y/n): ").lower().startswith('y')
    class Panel:
        def __init__(self, *args, **kwargs):
            self._text = str(args[0]) if args else ""
        def __str__(self):
            return self._text
        @staticmethod
        def fit(*args, **kwargs):
            return str(args[0]) if args else ""
    class Progress:
        def __enter__(self): return self
        def __exit__(self, *args): pass
        def add_task(self, *args, **kwargs): pass
    class SpinnerColumn: pass
    class TextColumn: pass
    box = None

# Install yt-dlp
# FIX 1 (Critical): Guard the import so a pip failure produces a clear message
# instead of an unhandled ModuleNotFoundError that crashes the whole script.
if not auto_install("yt_dlp", "yt-dlp", pip_name="yt-dlp"):
    print("❌ yt-dlp is required and could not be installed automatically.")
    print("   Please run: pip install yt-dlp  and then restart the script.")
    sys.exit(1)
try:
    import yt_dlp
except ImportError:
    print("❌ yt-dlp installation succeeded but the module cannot be imported.")
    print("   Try restarting the script, or run: pip install --force-reinstall yt-dlp")
    sys.exit(1)

# Install optional but important yt-dlp dependencies
#
# curl-cffi version notes:
#   - curl-cffi 0.1.5 is confirmed compatible with a-Shell's bundled cffi 1.17.1
#   - curl-cffi >= 0.8 requires cffi >= 2.0.0, which breaks a-Shell's backend
#   - On a-Shell (iOS) we install 0.1.5 directly — no conflict, no skip needed
#   - On other platforms we also pin to 0.1.5 for consistency, unless a newer
#     compatible version is already present
#
def _install_curl_cffi():
    # Check if a compatible version is already installed
    try:
        import curl_cffi as _cc
        ver = tuple(int(x) for x in getattr(_cc, '__version__', '0.0.0').split('.')[:3])
        if ver == (0, 1, 5):
            return  # Already on the confirmed-good version
        if ver >= (0, 8, 0):
            # Version >= 0.8 requires cffi >= 2.0.0; check if cffi matches
            import cffi as _cffi
            cffi_ver = tuple(int(x) for x in _cffi.__version__.split('.')[:2])
            if cffi_ver >= (2, 0):
                return  # cffi 2.x present and matches — all good on desktop
            # Mismatch (e.g. a-Shell cffi 1.17.1): downgrade to known-good version
            print("⚠️  curl-cffi is too new for your cffi version. Downgrading to 0.1.5 ...")
            subprocess.run(
                [sys.executable, "-m", "pip", "install", "--quiet", "curl_cffi==0.1.5"],
                check=True, capture_output=True
            )
            print("✅ curl-cffi downgraded to 0.1.5.")
            return
        # Any other older version — leave it alone
        return
    except ImportError:
        pass  # Not installed yet — fall through to fresh install

    # Fresh install: pin to 0.1.5 (confirmed compatible with cffi 1.x including a-Shell)
    auto_install("curl_cffi", "curl-cffi 0.1.5 (browser impersonation)", pip_name="curl_cffi==0.1.5")

_install_curl_cffi()
auto_install("brotli",    "brotli (compressed response support)",               pip_name="brotli")
auto_install("websockets","websockets (live stream support)",                    pip_name="websockets")

# ----------------------------------------------------------------------
# Auto-install ffmpeg (platform specific)
# ----------------------------------------------------------------------
def auto_install_ffmpeg():
    """Try to install ffmpeg using the system package manager."""
    # First check if ffmpeg already works
    try:
        subprocess.run(["ffmpeg", "-version"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        return True
    except Exception:
        pass

    print("\n⚠️  ffmpeg is not installed.")
    print("   ffmpeg is required for merging video/audio, embedding thumbnails, and many other features.")
    if not Confirm.ask("   Would you like me to try installing ffmpeg automatically?", default=True):
        print("   Continuing without ffmpeg – some features may fail.\n")
        return False

    system = sys.platform
    try:
        if system == "win32":
            # Windows: try Chocolatey first, then winget, then give manual instructions
            if shutil.which("choco"):
                print("   Installing ffmpeg via Chocolatey...")
                subprocess.run(["choco", "install", "ffmpeg", "-y"], check=True)
            elif shutil.which("winget"):
                print("   Installing ffmpeg via winget...")
                subprocess.run(["winget", "install", "FFmpeg", "-h", "--accept-package-agreements"], check=True)
            else:
                print("   No supported package manager found (Chocolatey or winget).")
                print("   Please download ffmpeg from https://ffmpeg.org/download.html and add it to PATH.")
                return False
        elif system == "darwin":
            # macOS / iOS (a-Shell)
            if shutil.which("brew"):
                print("   Installing ffmpeg via Homebrew...")
                subprocess.run(["brew", "install", "ffmpeg"], check=True)
            elif shutil.which("pkg"):
                # a-Shell on iOS
                print("   Installing ffmpeg via pkg (a-Shell)...")
                subprocess.run(["pkg", "install", "-y", "ffmpeg"], check=True)
            else:
                print("   No supported package manager found (Homebrew or pkg).")
                print("   Please install ffmpeg manually from https://ffmpeg.org/download.html")
                return False
        elif "linux" in system:
            # Linux / Termux / iSH (Alpine on iOS) / a-Shell
            if shutil.which("apt-get") or shutil.which("apt"):
                _apt = shutil.which("apt-get") or "apt"
                print(f"   Installing ffmpeg via apt...")
                # Termux doesn't use sudo; iSH Alpine also doesn't need it
                _use_sudo = not TERM_ENV.get("is_android") and not TERM_ENV.get("is_ios")
                if _use_sudo:
                    subprocess.run(["sudo", _apt, "update"], check=False)
                    subprocess.run(["sudo", _apt, "install", "-y", "ffmpeg"], check=True)
                else:
                    subprocess.run([_apt, "update"], check=False)
                    subprocess.run([_apt, "install", "-y", "ffmpeg"], check=True)
            elif shutil.which("pkg"):
                # Termux or a-Shell Alpine
                print("   Installing ffmpeg via pkg (Termux/a-Shell)...")
                subprocess.run(["pkg", "install", "-y", "ffmpeg"], check=True)
            elif shutil.which("apk"):
                print("   Installing ffmpeg via apk (Alpine/iSH)...")
                subprocess.run(["apk", "add", "ffmpeg"], check=True)
            elif shutil.which("pacman"):
                print("   Installing ffmpeg via pacman...")
                subprocess.run(["sudo", "pacman", "-S", "--noconfirm", "ffmpeg"], check=True)
            elif shutil.which("dnf"):
                print("   Installing ffmpeg via dnf...")
                subprocess.run(["sudo", "dnf", "install", "-y", "ffmpeg"], check=True)
            else:
                print("   No known package manager found. Please install ffmpeg manually.")
                return False
        else:
            print(f"   Unsupported platform: {system}. Please install ffmpeg manually.")
            return False

        # Verify installation
        subprocess.run(["ffmpeg", "-version"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        print("✅ ffmpeg installed successfully.\n")
        return True
    except Exception as e:
        print(f"   Failed to install ffmpeg: {e}")
        print("   Please install ffmpeg manually from https://ffmpeg.org/download.html\n")
        return False

# Run ffmpeg auto-install after Python packages are ready
auto_install_ffmpeg()

# ----------------------------------------------------------------------
# Configuration
# ----------------------------------------------------------------------
CONFIG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".ytdownloader_config.json")
# FIX W2: persist the queue to disk so "save for later" actually works across restarts.
QUEUE_FILE  = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".ytdownloader_queue.json")
DEFAULT_CONFIG = {
    "output_dir": os.getcwd(),
    "fps_pref": None,
    "quality_preset": "4",
    "speed_limit": None,
    "embed_thumbnail": True,
    "embed_metadata": True,
    "subtitles_lang": "en",
    "auto_retry": 3,
    "audio_only": False,
    "audio_format": "mp3",
    "cookies_file": None,
    "custom_headers_enabled": False,
    "custom_headers": {},
    "referer": None,
    "user_agent": None,
    "format_opt": "bestvideo[ext=mp4]+bestaudio[ext=m4a]/bestvideo+bestaudio/best",
    "battery_threshold": 20,
    "enable_smart_sleep": True,
    "live_record_duration": 0,
    "impersonate_target": "auto",
    "proxy": None,
    "sponsorblock_enabled": False,
    "sponsorblock_action": "remove",
    "sponsorblock_categories": ["sponsor", "intro", "outro", "selfpromo", "interaction"],
    # --- v2.0 additions ---
    "clipboard_watcher_enabled": False,
    "clipboard_poll_interval": 1.5,
    "clipboard_auto_queue": False,
    "parallel_downloads": 1,
    "schedule_enabled": False,
    "schedule_start": "02:00",
    "schedule_end": "06:00",
    "webhook_url": None,
    "webhook_on_success": True,
    "webhook_on_failure": True,
    "archive_file": None,
    "notify_sound": True,
    "save_playlist_metadata": False,
}

def load_config():
    # FIX W1: wrap JSON parse so a corrupt config falls back to defaults
    # instead of crashing on startup.
    config = DEFAULT_CONFIG.copy()
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, 'r') as f:
                file_config = json.load(f)
                config.update(file_config)
        except (json.JSONDecodeError, IOError) as e:
            print(f"\u26a0\ufe0f  Config file is corrupt ({e}). Using defaults.")
            backup = CONFIG_FILE + ".corrupt"
            try:
                shutil.copy2(CONFIG_FILE, backup)
                print(f"   Corrupt config backed up to: {backup}")
            except Exception:
                pass
    if not isinstance(config.get('custom_headers'), dict):
        config['custom_headers'] = {}
    config['output_dir'] = os.path.expanduser(config['output_dir']) if config['output_dir'] else os.getcwd()
    return config

def save_config(config):
    # FIX W1: atomic write — write to .tmp then rename so a crash mid-write
    # never leaves a corrupt/empty config file.
    tmp_path = CONFIG_FILE + ".tmp"
    try:
        with open(tmp_path, 'w') as f:
            json.dump(config, f, indent=2)
        os.replace(tmp_path, CONFIG_FILE)
    except Exception as e:
        console.print(f"[bold white]Failed to save config: {e}[/bold white]")
        try:
            os.remove(tmp_path)
        except Exception:
            pass

config = load_config()

# ----------------------------------------------------------------------
# Download history management (robust with fallback)
# ----------------------------------------------------------------------
HISTORY_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "download_history.json")
HISTORY_FALLBACK_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "download_history_fallback.txt")

def load_history():
    """Load download history from JSON file. Returns empty list on any error."""
    if not os.path.exists(HISTORY_FILE):
        return []
    try:
        with open(HISTORY_FILE, 'r') as f:
            data = json.load(f)
            if isinstance(data, list):
                # Basic validation: each item must have required keys
                for item in data:
                    if not isinstance(item, dict) or 'url' not in item:
                        raise ValueError("Corrupted history entry")
                return data
            else:
                return []
    except (json.JSONDecodeError, ValueError, IOError) as e:
        console.print(f"[bold white]⚠️ History file is corrupted: {e}[/bold white]")
        # Try to load from fallback text file
        try:
            if os.path.exists(HISTORY_FALLBACK_FILE):
                with open(HISTORY_FALLBACK_FILE, 'r') as f:
                    lines = f.readlines()
                fallback_history = []
                for line in lines:
                    parts = line.strip().split('|')
                    if len(parts) >= 4:
                        fallback_history.append({
                            'url': parts[0],
                            'title': parts[1],
                            'output_path': parts[2],
                            'extractor': parts[3],
                            'timestamp': parts[4] if len(parts) > 4 else '?'
                        })
                console.print("[blue]Recovered history from fallback file.[/blue]")
                return fallback_history
        except Exception:
            pass
        # Backup corrupt file
        backup_file = HISTORY_FILE + ".corrupt"
        try:
            shutil.copy2(HISTORY_FILE, backup_file)
            console.print(f"[white]Backup saved to {backup_file}[/white]")
        except Exception:
            pass
        try:
            os.remove(HISTORY_FILE)
            console.print("[blue]Corrupt history file removed. Starting fresh.[/blue]")
        except Exception:
            console.print("[bold white]Could not remove corrupt file. Please delete it manually.[/bold white]")
        return []
    except Exception as e:
        console.print(f"[bold white]Unexpected error reading history: {e}[/bold white]")
        return []

def save_history(history):
    """Save download history to JSON file + fallback text file."""
    # Ensure history is a list of dicts with required keys
    if not isinstance(history, list):
        history = []
    # Remove duplicates (keep latest)
    unique = {}
    for item in history:
        if isinstance(item, dict) and 'url' in item:
            unique[item['url']] = item
    history = list(unique.values())
    # Save as JSON
    try:
        with open(HISTORY_FILE, 'w') as f:
            json.dump(history, f, indent=2)
    except Exception as e:
        console.print(f"[bold white]Failed to save JSON history: {e}[/bold white]")
    # Also save as simple text fallback
    try:
        with open(HISTORY_FALLBACK_FILE, 'w') as f:
            for item in history:
                line = f"{item.get('url','')}|{item.get('title','')}|{item.get('output_path','')}|{item.get('extractor','')}|{item.get('timestamp','')}\n"
                f.write(line)
    except Exception:
        pass

def add_to_history(url, title, output_path, extractor):
    """Add a downloaded video to history, avoiding duplicates."""
    try:
        history = load_history()
        # Remove any existing entry with same URL
        history = [h for h in history if h.get('url') != url]
        history.append({
            'url': url,
            'title': title,
            'output_path': output_path,
            'extractor': extractor,
            'timestamp': datetime.now().isoformat()
        })
        save_history(history)
    except Exception as e:
        console.print(f"[bold white]Failed to add to history: {e}[/bold white]")

def is_already_downloaded(url):
    history = load_history()
    return any(h.get('url') == url for h in history)

def show_history():
    """Interactive history viewer: search/filter entries and optionally re-download."""
    history = load_history()
    if not history:
        console.print("[white]No download history yet.[/white]")
        input("Press Enter to continue...")
        return

    # Work on a reversed copy so newest entries are shown first
    working = list(reversed(history))

    while True:
        _safe_clear()
        console.print(Panel.fit("[bold blue]📜 Download History[/bold blue]", border_style="blue"))
        console.print(f"[blue]{len(working)} of {len(history)} entries shown.[/blue]  "
                      "[dim]s=search  c=clear filter  r=re-download  q=back[/dim]\n")

        # Two-line layout per entry — works on any terminal width.
        #   Line 1:  [#] Title
        #   Line 2:      Date  ·  Source
        if RICH_AVAILABLE:
            for i, h in enumerate(working[:30], 1):
                title = h.get('title') or 'Unknown'
                date  = (h.get('timestamp') or '?')[:19]
                ext   = h.get('extractor') or '?'
                console.print(f"[dim]{i:>3}.[/dim] [white]{title}[/white]")
                console.print(f"     [blue]{date}[/blue]  [dim white]{ext}[/dim white]")
            if len(working) > 30:
                console.print(f"[dim]  … and {len(working)-30} more (use search to narrow results)[/dim]")
        else:
            for i, h in enumerate(working[:30], 1):
                title = h.get('title') or 'Unknown'
                date  = (h.get('timestamp') or '?')[:19]
                ext   = h.get('extractor') or '?'
                print(f"  {i:>3}. {title}")
                print(f"       {date}  {ext}")
            if len(working) > 30:
                print(f"       … and {len(working)-30} more")

        action = Prompt.ask("\nAction", default="q").strip().lower()

        # ---- search / filter ----
        if action in ('s', 'search'):
            query = Prompt.ask("Search (title / source / date fragment)").strip().lower()
            if query:
                working = [
                    h for h in reversed(history)
                    if query in h.get('title', '').lower()
                    or query in h.get('extractor', '').lower()
                    or query in (h.get('timestamp', '')[:10]).lower()
                    or query in h.get('url', '').lower()
                ]
                if not working:
                    console.print(f"[white]No results for '{query}'.[/white]")
                    time.sleep(1.2)
                    working = list(reversed(history))   # reset so loop continues

        # ---- clear filter ----
        elif action in ('c', 'clear'):
            working = list(reversed(history))

        # ---- re-download ----
        elif action in ('r', 're-download', 'redownload'):
            if not working:
                console.print("[white]Nothing to re-download.[/white]")
                time.sleep(1)
                continue
            raw = Prompt.ask("Enter entry number to re-download (or 'q' to cancel)", default="q")
            if raw.strip().lower() in ('q', 'quit', ''):
                continue
            try:
                idx = int(raw.strip()) - 1
                if idx < 0 or idx >= len(working):
                    raise IndexError
            except (ValueError, IndexError):
                console.print("[bold white]Invalid number.[/bold white]")
                time.sleep(1)
                continue

            entry = working[idx]
            url   = entry.get('url', '')
            title = entry.get('title', 'Unknown')
            if not url:
                console.print("[bold white]No URL stored for this entry.[/bold white]")
                time.sleep(1)
                continue

            console.print(f"\n[bold blue]Re-downloading:[/bold blue] {title}")
            console.print(f"[dim]{url}[/dim]")
            if Confirm.ask("Proceed?", default=True):
                _safe_clear()
                download_single_video(url)
                input("Press Enter to return to history...")

        # ---- back / quit ----
        elif action in ('q', 'quit', 'back', ''):
            break

        else:
            console.print("[white]Unknown action. Use s / c / r / q.[/white]")
            time.sleep(0.8)

def clear_history():
    """Clear all download history after confirmation."""
    if Confirm.ask("Are you sure you want to clear ALL download history?", default=False):
        try:
            if os.path.exists(HISTORY_FILE):
                os.remove(HISTORY_FILE)
            if os.path.exists(HISTORY_FALLBACK_FILE):
                os.remove(HISTORY_FALLBACK_FILE)
            console.print("[blue]Download history cleared.[/blue]")
        except Exception as e:
            console.print(f"[bold white]Failed to clear history: {e}[/bold white]")
    else:
        console.print("[white]Clear cancelled.[/white]")
    input("Press Enter to continue...")

# ----------------------------------------------------------------------
# History export (Feature: export to CSV or HTML)
# a-Shell note: no desktop notification, no webbrowser module → we just
# print the output path so the user can open it with 'open <file>' or
# share it via the Files app.
# ----------------------------------------------------------------------
def export_history():
    """Export download history to CSV or a self-contained HTML file."""
    history = load_history()
    if not history:
        console.print("[white]No download history to export.[/white]")
        input("Press Enter to continue...")
        return

    console.print(Panel.fit("[bold blue]Export Download History[/bold blue]", border_style="blue"))
    console.print(f"[blue]{len(history)} entries found.[/blue]\n")
    fmt = Prompt.ask("Export format", choices=["csv", "html"], default="csv")

    out_dir = os.path.expanduser(config.get('output_dir', os.getcwd()))
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_path = os.path.join(out_dir, f"download_history_{timestamp}.{fmt}")

    try:
        if fmt == "csv":
            _export_history_csv(history, out_path)
        else:
            _export_history_html(history, out_path)
        console.print(f"\n[bold blue]✅ Exported to:[/bold blue] {out_path}")
        console.print("[white]On a-Shell you can open it with: open <filename>[/white]")
    except Exception as e:
        console.print(f"[bold white]Export failed: {e}[/bold white]")
        traceback.print_exc()
    input("Press Enter to continue...")

def _export_history_csv(history, path):
    """Write history to a UTF-8 CSV file (no external deps)."""
    import csv
    fieldnames = ['timestamp', 'title', 'extractor', 'url', 'output_path']
    with open(path, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction='ignore')
        writer.writeheader()
        for item in history:
            writer.writerow({k: item.get(k, '') for k in fieldnames})

def _export_history_html(history, path):
    """Write history to a self-contained, styled HTML file (no external deps)."""
    # FIX 4 (Critical): full HTML escaping on ALL fields.
    # Old code: only escaped & < > in title; extractor missed < > ; URL only
    # escaped quotes — a javascript: URL in href or a <script> in extractor
    # would execute as XSS when the file was opened in a browser.
    def _he(s):
        """Full HTML-escape a string."""
        return (str(s)
                .replace('&', '&amp;')
                .replace('<', '&lt;')
                .replace('>', '&gt;')
                .replace('"', '&quot;')
                .replace("'", '&#39;'))

    def _safe_href(url):
        """Return the URL only if it uses a safe scheme; otherwise return #."""
        if re.match(r'^https?://', url, re.IGNORECASE):
            return _he(url)
        return '#'

    rows = ""
    for i, item in enumerate(reversed(history), 1):
        ts    = item.get('timestamp', '')[:19] if item.get('timestamp') else ''
        title = _he(item.get('title', 'Unknown'))
        ext   = _he(item.get('extractor', '?'))
        url   = item.get('url', '')
        href  = _safe_href(url)
        row_class = 'even' if i % 2 == 0 else 'odd'
        rows += (
            f'<tr class="{row_class}">'
            f'<td>{i}</td>'
            f'<td>{ts}</td>'
            f'<td><a href="{href}" target="_blank" rel="noopener noreferrer">{title}</a></td>'
            f'<td>{ext}</td>'
            '</tr>\n'
        )
    generated = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Download History</title>
<style>
  body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
         background: #0f0f0f; color: #e0e0e0; margin: 0; padding: 20px; }}
  h1   {{ color: #4a9eff; margin-bottom: 4px; }}
  p.meta {{ color: #666; font-size: 0.85em; margin-top: 0; margin-bottom: 20px; }}
  table {{ width: 100%; border-collapse: collapse; font-size: 0.92em; }}
  th   {{ background: #1a1a2e; color: #4a9eff; padding: 10px 12px;
          text-align: left; border-bottom: 2px solid #333; }}
  td   {{ padding: 8px 12px; border-bottom: 1px solid #222; vertical-align: top; }}
  tr.odd  {{ background: #141414; }}
  tr.even {{ background: #181818; }}
  tr:hover td {{ background: #1e2a3a; }}
  a    {{ color: #6bbeff; text-decoration: none; }}
  a:hover {{ text-decoration: underline; }}
  td:first-child {{ color: #555; font-size: 0.85em; width: 40px; }}
  td:nth-child(2) {{ white-space: nowrap; color: #aaa; font-size: 0.85em; width: 160px; }}
  td:last-child {{ color: #888; font-size: 0.85em; width: 100px; }}
</style>
</head>
<body>
<h1>📜 Download History</h1>
<p class="meta">{len(history)} entries &mdash; generated {generated} by PacketHound Vid Downloader</p>
<table>
<thead><tr><th>#</th><th>Date</th><th>Title</th><th>Source</th></tr></thead>
<tbody>
{rows}
</tbody>
</table>
</body>
</html>"""
    with open(path, 'w', encoding='utf-8') as f:
        f.write(html)

# ----------------------------------------------------------------------
# Cross-platform battery & charging detection (Feature 12)
# Supports: macOS (ioreg), Linux/Termux (/sys), Windows (WMIC), iOS (a-Shell stub)
# ----------------------------------------------------------------------
def get_battery_status():
    """Returns (percentage, is_charging). Falls back to (100, True) if undetectable."""
    platform = sys.platform

    # --- macOS: use ioreg ---
    if platform == "darwin" and shutil.which("ioreg"):
        try:
            output = subprocess.check_output(["ioreg", "-r", "-k", "BatteryPercent"], text=True, stderr=subprocess.DEVNULL)
            match = re.search(r'"BatteryPercent"\s*=\s*(\d+)', output)
            percent = int(match.group(1)) if match else 100
            charging_output = subprocess.check_output(["ioreg", "-r", "-k", "IsCharging"], text=True, stderr=subprocess.DEVNULL)
            is_charging = bool(re.search(r'"IsCharging"\s*=\s*(1|Yes)', charging_output))
            return percent, is_charging
        except Exception:
            pass

    # --- Linux / Termux / Android: read /sys/class/power_supply ---
    if platform.startswith("linux"):
        try:
            # Find the first battery device
            ps_path = "/sys/class/power_supply"
            if os.path.isdir(ps_path):
                for entry in os.listdir(ps_path):
                    bat_path = os.path.join(ps_path, entry)
                    cap_file = os.path.join(bat_path, "capacity")
                    status_file = os.path.join(bat_path, "status")
                    type_file = os.path.join(bat_path, "type")
                    # Only use Battery-type entries
                    if os.path.exists(type_file):
                        with open(type_file) as f:
                            if f.read().strip().lower() != "battery":
                                continue
                    if os.path.exists(cap_file) and os.path.exists(status_file):
                        with open(cap_file) as f:
                            percent = int(f.read().strip())
                        with open(status_file) as f:
                            status = f.read().strip().lower()
                        is_charging = status in ("charging", "full")
                        return percent, is_charging
        except Exception:
            pass

    # --- Windows: use PowerShell (preferred) then fall back to WMIC ---
    # FIX N4: WMIC was deprecated in Win 10 21H1 and removed from some Win 11
    # builds. Use PowerShell Get-WmiObject which works on all supported Windows
    # versions. Fall back to wmic for older systems.
    if platform == "win32":
        # Try PowerShell first
        try:
            ps_cmd = (
                "Get-WmiObject Win32_Battery | "
                "Select-Object -First 1 EstimatedChargeRemaining,BatteryStatus | "
                "ConvertTo-Json"
            )
            out = subprocess.check_output(
                ["powershell", "-NoProfile", "-NonInteractive", "-Command", ps_cmd],
                text=True, stderr=subprocess.DEVNULL, timeout=10
            )
            import json as _json
            data = _json.loads(out.strip())
            percent = int(data.get("EstimatedChargeRemaining", 100))
            # BatteryStatus 2 = Connected to AC (charging), 1 = Discharging
            is_charging = int(data.get("BatteryStatus", 2)) == 2
            return percent, is_charging
        except Exception:
            pass
        # Fall back to legacy WMIC for Windows 8/10 without PowerShell
        try:
            out = subprocess.check_output(
                ["wmic", "path", "Win32_Battery", "get",
                 "EstimatedChargeRemaining,BatteryStatus", "/format:list"],
                text=True, stderr=subprocess.DEVNULL, timeout=10
            )
            pct_match = re.search(r'EstimatedChargeRemaining=(\d+)', out)
            status_match = re.search(r'BatteryStatus=(\d+)', out)
            percent = int(pct_match.group(1)) if pct_match else 100
            is_charging = int(status_match.group(1)) == 2 if status_match else True
            return percent, is_charging
        except Exception:
            pass

    # Fallback: assume full battery / charging (safe default — no false alarms)
    return 100, True

def check_battery_before_download():
    """Returns True if it's safe to proceed (battery OK or user accepts risk)."""
    if not config.get("enable_smart_sleep", True):
        return True
    percent, charging = get_battery_status()
    threshold = config.get("battery_threshold", 20)
    if percent < threshold and not charging:
        console.print(f"[bold white]⚠️ Battery is at {percent}% and not charging![/bold white]")
        console.print(f"   Your threshold is set to {threshold}%.")
        return Confirm.ask("Continue download anyway? (may drain battery)", default=False)
    elif percent < 10 and charging:
        console.print(f"[white]🔋 Battery is very low ({percent}%) but charging. Proceeding...[/white]")
    return True

# ----------------------------------------------------------------------
# Bandwidth forecasting & speed test (Feature 20)
# ----------------------------------------------------------------------
def speed_test(url, duration=5):
    """Perform a quick speed test by downloading a small chunk of the video."""
    console.print("[dim]Running speed test...[/dim]")
    test_file = os.path.join(tempfile.gettempdir(), "speed_test_ytdl.bin")
    cmd = _get_ytdlp_base_cmd() + [
        "--limit-rate", "10M",
        "--no-playlist",
        "--quiet",
        "--no-warnings",
        "--max-filesize", "5M",
        "-f", "bestvideo+bestaudio/best",
        "-o", test_file,
        url
    ]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=duration + 5, capture_output=True, check=True)
        elapsed = time.time() - start
        if os.path.exists(test_file):
            size = os.path.getsize(test_file)
            return size / elapsed / 1024 / 1024  # MB/s
    except Exception:
        return None
    finally:
        try:
            if os.path.exists(test_file):
                os.remove(test_file)
        except Exception:
            pass
    return None

def format_speed(speed_mbps):
    if speed_mbps is None:
        return "?"
    if speed_mbps > 100:
        return f"{speed_mbps:.0f} MB/s"
    elif speed_mbps > 1:
        return f"{speed_mbps:.1f} MB/s"
    else:
        return f"{speed_mbps*1024:.0f} KB/s"

# ----------------------------------------------------------------------
# Helper functions
# ----------------------------------------------------------------------
def quit_if_requested(user_input):
    if user_input and str(user_input).strip().lower() in ('q', 'quit'):
        console.print("\n[white]👋 Quit by user request. Exiting.[/white]")
        sys.exit(0)

def get_size_str(bytes_val):
    if bytes_val is None:
        return "Unknown"
    for unit in ['B', 'KB', 'MB', 'GB']:
        if bytes_val < 1024.0:
            return f"{bytes_val:.1f} {unit}"
        bytes_val /= 1024.0
    return f"{bytes_val:.1f} TB"

def check_disk_space(directory, needed_bytes):
    try:
        usage = shutil.disk_usage(directory)
        free = usage.free
        if free < needed_bytes:
            console.print(f"[bold white]⚠️ Not enough disk space. Need {get_size_str(needed_bytes)}, free: {get_size_str(free)}[/bold white]")
            return False
        return True
    except Exception:
        return True

def check_ffmpeg():
    """Check if ffmpeg is available, but don't auto-install again."""
    try:
        subprocess.run(["ffmpeg", "-version"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
        return True
    except Exception:
        console.print("[white]⚠️ ffmpeg not found. Some features (merging, thumbnails) may fail.[/white]")
        console.print("   Run the script again to attempt automatic installation, or install ffmpeg manually.")
        return False

def get_available_impersonate_targets():
    """Return a list of available impersonate target strings (e.g. ['chrome', 'firefox']).
    Returns empty list if curl_cffi is not installed."""
    try:
        from yt_dlp.networking.impersonate import ImpersonateTarget
        with yt_dlp.YoutubeDL({'quiet': True}) as ydl:
            targets = ydl._request_director.get_impersonate_targets() if hasattr(ydl, '_request_director') else []
            # Deduplicate by client name
            seen = set()
            result = []
            for t in targets:
                name = t.client.lower() if hasattr(t, 'client') and t.client else str(t).lower()
                if name not in seen:
                    seen.add(name)
                    result.append(name)
            return result
    except Exception:
        return []

def resolve_impersonate_target(preferred='auto'):
    """Resolve the best available impersonate target.
    'auto' picks the first available target. Returns None if none available.
    FIX W5: warn the user when their explicit choice is unavailable instead
    of silently falling back — they may otherwise blame cookies/proxy for
    a target mismatch they don't know about.
    """
    targets = get_available_impersonate_targets()
    if not targets:
        return None
    if preferred == 'auto':
        return targets[0]
    if preferred not in targets:
        # FIX W5: tell the user their setting was overridden
        console.print(
            f"[white]\u26a0\ufe0f  Impersonate target \'{preferred}\' is not available on this device. "
            f"Falling back to \'{targets[0]}\'. "
            f"Available: {', '.join(targets)}[/white]"
        )
        return targets[0]
    return preferred

def build_impersonate_ydl_opt(preferred='auto'):
    """Return {'impersonate': ImpersonateTarget(...)} dict, or {} if unavailable."""
    target = resolve_impersonate_target(preferred)
    if not target:
        return {}
    try:
        from yt_dlp.networking.impersonate import ImpersonateTarget
        return {'impersonate': ImpersonateTarget(target)}
    except Exception:
        return {}

def build_impersonate_cli_args(preferred='auto'):
    """Return ['--impersonate', 'target'] list, or [] if unavailable."""
    target = resolve_impersonate_target(preferred)
    if not target:
        return []
    return ['--impersonate', target]

def get_video_info(url, playlist=False):
    ydl_opts = {'quiet': True, 'no_warnings': True, 'extract_flat': False, 'noplaylist': not playlist}
    if config.get('proxy'):
        ydl_opts['proxy'] = config['proxy']
    # Apply impersonation for sites that require it (TikTok etc.)
    needs_impersonate = any(s in url.lower() for s in ('tiktok', 'twitter', 'x.com'))
    if needs_impersonate or config.get('impersonate_target', 'auto') not in ('auto', 'off', None, ''):
        preferred = config.get('impersonate_target', 'auto')
        ydl_opts.update(build_impersonate_ydl_opt(preferred))
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        try:
            info = ydl.extract_info(url, download=False)
            if playlist and 'entries' in info:
                return info
            best = info.get('filesize_approx') or info.get('filesize')
            if not best and 'formats' in info:
                for f in info['formats']:
                    if f.get('filesize'):
                        best = f['filesize']
                        break
            return {
                'title': info.get('title', 'Unknown'),
                'duration': info.get('duration', 0),
                'thumbnail': info.get('thumbnail', ''),
                'filesize': best,
                'uploader': info.get('uploader', info.get('channel', 'Unknown')),
                'view_count': info.get('view_count', 0),
                'extractor': info.get('extractor', 'Unknown'),
                'is_live': info.get('is_live', False)
            }
        except Exception as e:
            console.print(f"[bold white]Error fetching info: {e}[/bold white]")
            if 'tiktok' in url.lower():
                console.print("[white]💡 TikTok often requires cookies or a User-Agent header.[/white]")
                console.print("   Try enabling custom headers in Preferences → Custom HTTP Headers.")
            elif 'instagram' in url.lower() or 'twitter' in url.lower() or 'x.com' in url.lower():
                console.print("[white]💡 Instagram and Twitter/X often require cookies to access content.[/white]")
                console.print("   Export cookies from your browser and set the file path in Preferences.")
            else:
                console.print("[white]💡 If the content is private or login-required, try setting a cookies file in Preferences.[/white]")
            return None

def format_duration(seconds):
    seconds = seconds or 0
    m, s = divmod(int(seconds), 60)
    h, m = divmod(m, 60)
    if h:
        return f"{h}h {m}m {s}s"
    elif m:
        return f"{m}m {s}s"
    else:
        return f"{s}s"

def show_video_preview(info):
    if RICH_AVAILABLE:
        table = Table(title="📺 Video Information", box=box.ROUNDED, header_style="bold blue")
        table.add_column("Property", style="bold")
        table.add_column("Value")
        table.add_row("Source", info['extractor'])
        table.add_row("Title", info['title'])
        table.add_row("Uploader", info['uploader'])
        table.add_row("Duration", format_duration(info['duration']))
        table.add_row("Views", f"{info.get('view_count') or 0:,}")
        if info['filesize']:
            table.add_row("Estimated Size", get_size_str(info['filesize']))
        if info.get('is_live'):
            table.add_row("Stream", "[bold blue]LIVE[/bold blue]")
        console.print(table)
    else:
        console.print(f"Source: {info['extractor']}")
        console.print(f"Title: {info['title']}")
        console.print(f"Uploader: {info['uploader']}")
        console.print(f"Duration: {format_duration(info['duration'])}")
        console.print(f"Views: {info.get('view_count') or 0:,}")
        if info['filesize']:
            console.print(f"Estimated Size: {get_size_str(info['filesize'])}")
    return Confirm.ask("Proceed with this video?", default=True)

def show_playlist_preview(playlist_info):
    title = playlist_info.get('title', 'Untitled Playlist')
    count = len(playlist_info.get('entries', []))
    console.print(Panel(f"[bold blue]Playlist: {title}[/bold blue]\nContains {count} videos", border_style="blue"))
    return Confirm.ask("Download this entire playlist?", default=False)

# ----------------------------------------------------------------------
# URL validation
# ----------------------------------------------------------------------
def _get_ytdlp_base_cmd():
    try:
        subprocess.run(["yt-dlp", "--version"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
        return ["yt-dlp"]
    except (FileNotFoundError, subprocess.CalledProcessError):
        return [sys.executable, "-m", "yt_dlp"]

def is_valid_url(url):
    # FIX N1: fast regex pre-check before spawning a full yt-dlp subprocess.
    # Old code always ran --simulate (10-30 s on slow machines) and reported
    # "site not supported" for any non-zero exit, including temporary 429s.
    if not re.match(r'https?://', url, re.IGNORECASE):
        console.print("[white]URL must start with http:// or https://[/white]")
        return False
    try:
        cmd = _get_ytdlp_base_cmd() + ["--simulate", "--no-warnings", "--no-playlist", url]
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, timeout=30)
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        console.print("[white]URL validation timed out — the site may be slow or rate-limiting. Treating as valid.[/white]")
        return True
    except FileNotFoundError:
        console.print("[bold white]❌ yt-dlp not found. Please install it first.[/bold white]")
        return False
    except Exception:
        return False
def get_url():
    # Immediate clipboard check: if there's already a supported URL in the
    # clipboard when this function is entered, offer it as the default so the
    # user can just press Enter instead of typing/pasting.
    _clipboard_prefill = ""
    try:
        _clip_text = _read_clipboard_raw().strip()
        if _is_supported_video_url(_clip_text):
            _clipboard_prefill = _clip_text
            console.print(f"[bold blue]📋 Clipboard URL detected:[/bold blue] [dim]{_clip_text[:80]}[/dim]")
    except Exception:
        pass

    while True:
        if _clipboard_prefill:
            url = Prompt.ask(
                "📎 [bold blue]Enter video/audio URL[/bold blue] (or 'q' to go back)",
                default=_clipboard_prefill,
            )
            _clipboard_prefill = ""  # only pre-fill once per call
        else:
            url = Prompt.ask("📎 [bold blue]Enter video/audio URL[/bold blue] (or 'q' to go back)")
        if url.strip().lower() in ('q', 'quit'):
            return None
        if not url:
            console.print("[bold white]No URL provided. Try again.[/bold white]")
            continue

        with Progress(SpinnerColumn(), TextColumn("[progress.description]{task.description}"), transient=True) as progress:
            progress.add_task(description="Validating URL...", total=None)
            valid = is_valid_url(url)

        if valid:
            confirm = Confirm.ask(f"Download from:\n[bold white]{url}[/bold white]\nCorrect?", default=True)
            if confirm:
                return url
            else:
                console.print("[white]Please re-enter the URL.[/white]")
        else:
            console.print("[bold white]❌ Could not verify this URL. The site may not be supported, or the content may be private/removed.[/bold white]")
            console.print("   yt-dlp supports 1000+ sites. If this is a supported site, check:")
            console.print("   • The URL is correct and the content is public")
            console.print("   • For login-required content, set a cookies file in Preferences")
            console.print("   • For rate-limited sites, enable custom headers (User-Agent / Referer) in Preferences")
            force = Prompt.ask("   Type 'force' to continue anyway, or press Enter to re-enter URL", default="")
            if force.lower() == 'force':
                return url

# ----------------------------------------------------------------------
# Subtitle handling
# ----------------------------------------------------------------------
def get_subtitle_languages(url):
    ydl_opts = {'quiet': True, 'writesubtitles': True, 'skip_download': True, 'noplaylist': True}
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        try:
            info = ydl.extract_info(url, download=False)
            subs = info.get('subtitles', {})
            return list(subs.keys()) if subs else []
        except Exception:
            return []

def build_subtitle_opts(lang, embed=False):
    opts = ['--write-subs', '--sub-lang', lang]
    if embed:
        opts.append('--embed-subs')
    else:
        opts.extend(['--sub-format', 'srt'])
    return opts

# ----------------------------------------------------------------------
# Audio only extraction
# ----------------------------------------------------------------------
def build_audio_format(audio_format, quality=5):
    if audio_format == 'mp3':
        return 'bestaudio/best', ['--extract-audio', '--audio-format', 'mp3', '--audio-quality', str(quality)]
    else:
        return 'bestaudio[ext=m4a]/bestaudio', ['--extract-audio', '--audio-format', 'm4a']

# ----------------------------------------------------------------------
# Show available formats using yt-dlp -F
# ----------------------------------------------------------------------
def show_format_codes(url):
    console.print(Panel("[bold white]Fetching available formats...[/bold white]", border_style="blue"))
    try:
        cmd = _get_ytdlp_base_cmd() + ["-F", url]
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, timeout=30)
        if result.returncode != 0:
            console.print("[bold white]Failed to retrieve format list.[/bold white]")
            console.print(result.stderr)
            return None

        console.print(Panel(result.stdout, title="📋 Available Formats", border_style="blue", overflow="crop"))
        console.print("\n[white]Instructions:[/white] Look for format codes in the first column (e.g., 137, 140, 137+140).")
        console.print("Combine video+audio with '+', e.g., 137+140\n")

        while True:
            fmt_code = Prompt.ask("Enter format code(s) (or press Enter to cancel)", default="")
            if fmt_code == "":
                console.print("[white]Manual format selection cancelled.[/white]")
                return None
            return fmt_code.strip()
    except subprocess.TimeoutExpired:
        console.print("[bold white]Timed out while fetching formats.[/bold white]")
        return None
    except Exception as e:
        console.print(f"[bold white]Error: {e}[/bold white]")
        return None

# ----------------------------------------------------------------------
# Enhanced download with progress parsing
# FIX 3 (Critical): After the 30s silent-mode break, drain stderr in a
# background thread so the main thread never blocks indefinitely waiting
# for a long-running process to exit.
# ----------------------------------------------------------------------
def download_with_progress(cmd):
    """Run yt-dlp command, parse progress, and wait silently if no output within 30 seconds."""
    import threading

    # stdout=DEVNULL: yt-dlp writes progress to stderr; piping stdout without consuming it causes deadlocks
    process = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True, bufsize=1)
    error_lines = []
    started = False
    start_time = time.time()

    def _drain_stderr_in_background():
        """Drain remaining stderr in a daemon thread after we break out of the progress loop."""
        try:
            for line in process.stderr:
                if line.strip() and not line.startswith('[info]'):
                    error_lines.append(line.strip())
        except Exception:
            pass

    if RICH_AVAILABLE:
        with Live(console=console, refresh_per_second=4, transient=True) as live:
            for line in process.stderr:
                # FIX 3: if 30 s pass with no progress line, break and drain
                # stderr in a background thread — never block the main thread.
                if not started and time.time() - start_time > 30:
                    console.print("[dim]No progress display available – download running silently...[/dim]")
                    t = threading.Thread(target=_drain_stderr_in_background, daemon=True)
                    t.start()
                    break
                m = re.search(r'\[download\]\s+([\d\.]+)%\s+of\s+~?[\d\.]+\w+\s+at\s+([\d\.]+\w+/?\w*)\s+ETA\s+(\d{1,2}:\d{2})', line)
                if m:
                    started = True
                    percent = float(m.group(1))
                    speed_str = m.group(2)
                    eta_str = m.group(3)
                    new_table = RichTable(box=box.SIMPLE)
                    new_table.add_column("Progress", style="blue")
                    new_table.add_column("Speed", style="blue")
                    new_table.add_column("ETA", style="white")
                    new_table.add_row(f"{percent:.1f}%", speed_str, eta_str)
                    live.update(new_table)
                else:
                    if line.strip() and not line.startswith('[info]'):
                        error_lines.append(line.strip())
                        console.print(f"[dim]{line.strip()}[/dim]")
        # Drain remaining stderr so the process can exit, then wait for returncode
        for line in process.stderr:
            if line.strip() and not line.startswith('[info]'):
                error_lines.append(line.strip())
        process.wait()
    else:
        # Fallback plain text
        for line in process.stderr:
            if not started and time.time() - start_time > 30:
                print("No progress display – download running silently...")
                # FIX 3: drain in background thread so main thread stays responsive
                t = threading.Thread(target=_drain_stderr_in_background, daemon=True)
                t.start()
                break
            m = re.search(r'\[download\]\s+([\d\.]+)%', line)
            if m:
                started = True
                print(f"\rProgress: {m.group(1)}%", end="", flush=True)
            else:
                if line.strip():
                    error_lines.append(line.strip())
                    print(f"\n{line.strip()}", file=sys.stderr)
        # Drain remaining stderr and wait for returncode
        for line in process.stderr:
            pass
        process.wait()
        print()

    if process.returncode != 0 and error_lines:
        console.print("[bold white]Error output from yt-dlp:[/bold white]")
        for err in error_lines[-5:]:
            console.print(f"  {err}")
    return process.returncode == 0

# ----------------------------------------------------------------------
# Core download function (fixed battery check, progress, retry, JS runtime)
# ----------------------------------------------------------------------
def download_video(url, options, retry_count=0):
    # v2.0: respect download scheduler
    if retry_count == 0:
        wait_for_schedule_window()

    # Feature 12: check battery
    if not options.get('from_batch', False) and not options.get('is_playlist_item', False):
        if not check_battery_before_download():
            console.print("[white]Download cancelled due to battery settings.[/white]")
            return False

    audio_only = options.get('audio_only', False)
    format_opt = options.get('format_opt')
    from_batch = options.get('from_batch', False)

    # Feature 20: speed test
    # FIX W4: warn the user BEFORE running the speed test — it silently downloads
    # up to 5 MB from the target URL, which is surprising on metered connections.
    if not from_batch and not options.get('is_playlist_item', False):
        if config.get('enable_smart_sleep', True):
            console.print("[dim]A quick speed test will download up to 5 MB to estimate bandwidth.[/dim]")
            if Confirm.ask("Run speed test?", default=True):
                speed = speed_test(url, duration=3)
                if speed and speed < 0.5:
                    console.print(f"[white]⚠️ Slow connection detected ({format_speed(speed)}). Download may take a long time.[/white]")
                    if not Confirm.ask("Continue anyway?", default=True):
                        return False

    if not audio_only and format_opt is None:
        if from_batch:
            format_opt = "bestvideo*+bestaudio/best"
            console.print("[white]Batch mode: using default format (bestvideo+bestaudio)[/white]")
        else:
            console.print("\n[bold white]Manual format selection[/bold white]")
            view = Confirm.ask("Show available formats?", default=True)
            if view:
                fmt = show_format_codes(url)
                if fmt is None:
                    console.print("[bold white]Format selection cancelled. Aborting download.[/bold white]")
                    return False
                format_opt = fmt
            else:
                format_opt = Prompt.ask("Enter format code(s) (e.g., 137+140)")
                if not format_opt:
                    console.print("[bold white]No format provided. Aborting.[/bold white]")
                    return False

    cmd = _get_ytdlp_base_cmd()

    # TikTok doesn't serve bestvideo+bestaudio as separate streams —
    # it only offers pre-merged formats. Override to a TikTok-safe selector.
    needs_impersonate = any(s in url.lower() for s in ('tiktok', 'twitter', 'x.com'))
    if not audio_only and format_opt and 'tiktok' in url.lower():
        format_opt = "bestvideo*+bestaudio/best/mp4"
    if needs_impersonate or config.get('impersonate_target', 'auto') not in ('auto', 'off', None, ''):
        preferred = config.get('impersonate_target', 'auto')
        cmd.extend(build_impersonate_cli_args(preferred))

    if not audio_only and format_opt:
        cmd.extend(['-f', format_opt])

    cmd.extend(['-o', options['output_template']])

    # v2.0: yt-dlp native download archive
    archive_path = _get_archive_path()
    if archive_path:
        cmd.extend(['--download-archive', archive_path])

    cmd.append('--continue')          # resume partial downloads
    # DO NOT add --no-overwrites

    if options.get('no_playlist', True):
        cmd.append('--no-playlist')

    if options.get('subtitles'):
        lang = options['subtitles']['lang']
        embed = options['subtitles'].get('embed', False)
        cmd.extend(build_subtitle_opts(lang, embed))

    if options.get('embed_thumbnail', False):
        cmd.append('--embed-thumbnail')
    if options.get('embed_metadata', False):
        cmd.append('--embed-metadata')

    if options.get('speed_limit'):
        cmd.extend(['--limit-rate', options['speed_limit']])

    if options.get('proxy'):
        cmd.extend(['--proxy', options['proxy']])

    if options.get('cookies_file') and os.path.exists(options['cookies_file']):
        cmd.extend(['--cookies', options['cookies_file']])

    if options.get('custom_headers_enabled', False):
        if options.get('referer'):
            cmd.extend(['--add-header', f"Referer: {options['referer']}"])
        if options.get('user_agent'):
            cmd.extend(['--add-header', f"User-Agent: {options['user_agent']}"])
        extra = options.get('custom_headers', {})
        for key, value in extra.items():
            if key and value:
                cmd.extend(['--add-header', f"{key}: {value}"])

    if audio_only:
        audio_fmt, extra_opts = build_audio_format(options.get('audio_format', 'mp3'))
        cmd.extend(['-f', audio_fmt] + extra_opts)

    if options.get('retries', 3):
        cmd.extend(['--retries', str(options['retries']), '--fragment-retries', str(options['retries'])])

    # For live streams
    if options.get('is_live', False):
        cmd.append('--wait-for-video')
        cmd.append('--live-from-start')
        if options.get('live_duration') and options['live_duration'] > 0:
            secs = int(options['live_duration'] * 60)
            cmd.extend(['--download-sections', f'*0-{secs}'])

    # SponsorBlock: only applies to YouTube; silently skipped on other extractors by yt-dlp
    if options.get('sponsorblock_enabled', False) and not options.get('is_live', False):
        action   = options.get('sponsorblock_action', 'remove')   # 'remove' or 'mark'
        cats     = options.get('sponsorblock_categories',
                               ['sponsor', 'intro', 'outro', 'selfpromo', 'interaction'])
        cats_str = ','.join(cats)
        if action == 'remove':
            cmd.extend(['--sponsorblock-remove', cats_str])
        else:
            cmd.extend(['--sponsorblock-mark', cats_str])

    cmd.append(url)

    # FIX N3: mask the cookies file path in the displayed command so screen-sharing
    # users don't inadvertently expose where they store sensitive cookie files.
    _display_cmd = []
    _mask_next = False
    for _token in cmd:
        if _mask_next:
            _display_cmd.append('<cookies-file-hidden>')
            _mask_next = False
        elif _token == '--cookies':
            _display_cmd.append(_token)
            _mask_next = True
        else:
            _display_cmd.append(_token)
    console.print(Panel(f"[bold blue]Download Command[/bold blue]\n[dim]{' '.join(_display_cmd)}[/dim]", border_style="blue"))
    try:
        success = download_with_progress(cmd)
        if not success:
            raise subprocess.CalledProcessError(1, cmd)
        # v2.0: stats + webhook + sound
        stats_record(url, options.get('_title',''), options.get('_extractor',''), ok=True)
        stats_record_speed(None)
        fire_webhook(url, options.get('_title',''), options.get('_extractor',''), ok=True)
        play_notification(success=True)
        return True
    except subprocess.CalledProcessError as e:
        error_msg = str(e)
        if "403" in error_msg or "forbidden" in error_msg.lower():
            error_type = "HTTP 403 Forbidden (site may block downloads)"
        elif "404" in error_msg:
            error_type = "HTTP 404 Not Found (video removed or private)"
        elif "timeout" in error_msg.lower():
            error_type = "Connection timeout"
        elif "network" in error_msg.lower() or "unreachable" in error_msg.lower():
            error_type = "Network error"
        else:
            error_type = f"Unknown error (code {e.returncode})"
        console.print(f"[bold white]Download failed: {error_type}[/bold white]")

        # FIX W3: read max_retries from the options dict which is populated
        # from config['auto_retry'] — old code read 'retry_backoff' which was
        # always hard-coded to 3, making the Preferences retry setting do nothing.
        max_retries = options.get('max_retries', options.get('retries', 3))
        if retry_count < max_retries:
            wait = 2 ** retry_count
            console.print(f"[white]Retrying in {wait} seconds... (attempt {retry_count+1}/{max_retries})[/white]")
            time.sleep(wait)
            return download_video(url, options, retry_count + 1)
        else:
            if 'tiktok' in url.lower():
                console.print("[white]💡 TikTok often requires a User-Agent header or cookies.[/white]")
                console.print("   Go to Preferences → Custom HTTP Headers and add a User-Agent.")
            elif 'instagram' in url.lower() or 'twitter' in url.lower() or 'x.com' in url.lower():
                console.print("[white]💡 Instagram and Twitter/X often require cookies to download.[/white]")
                console.print("   Export cookies from your browser and set the file path in Preferences → Cookies File.")
            elif 'twitch' in url.lower():
                console.print("[white]💡 Twitch VODs may require OAuth tokens or cookies for subscriber-only content.[/white]")
                console.print("   Export cookies from your browser and set the file path in Preferences.")
            elif 'bilibili' in url.lower():
                console.print("[white]💡 Bilibili may require cookies for high-quality or member-only videos.[/white]")
                console.print("   Export cookies from your browser and set the file path in Preferences.")
            elif '403' in error_type or 'forbidden' in error_type.lower():
                console.print("[white]💡 HTTP 403 usually means the site blocks direct downloads.[/white]")
                console.print("   Try enabling custom headers (User-Agent, Referer) or adding cookies in Preferences.")
            else:
                console.print("[white]💡 If this site requires login, try exporting browser cookies and setting them in Preferences.[/white]")
                console.print("   You can also try enabling custom headers (User-Agent / Referer) in Preferences.")
            return False

# ----------------------------------------------------------------------
# Live stream recording (Feature 4)
# ----------------------------------------------------------------------
def record_live_stream():
    url = get_url()
    console.print("[blue]Fetching stream info...[/blue]")
    info = get_video_info(url)
    if info and not info.get('is_live'):
        if not Confirm.ask("This does not appear to be a live stream. Record as normal video?", default=True):
            return
        download_single_video(url)
        return
    console.print("[blue]Live stream detected. Waiting for broadcast to start...[/blue]")
    duration = config.get('live_record_duration', 0)
    if duration > 0:
        console.print(f"Auto-stop after {duration} minutes (set in Preferences).")
    else:
        console.print("Recording will continue until the stream ends.")
    if not Confirm.ask("Start recording now?", default=True):
        return
    out_dir = os.path.expanduser(config['output_dir']) if config['output_dir'] else os.getcwd()
    output_template = os.path.join(out_dir, '%(title)s_%(upload_date)s_%(epoch>%Y%m%d_%H%M%S)s.%(ext)s')
    options = {
        'format_opt': config.get('format_opt'),
        'output_template': output_template,
        'no_playlist': True,
        'subtitles': None,
        'embed_thumbnail': False,
        'embed_metadata': False,
        'speed_limit': config.get('speed_limit'),
        'cookies_file': config.get('cookies_file'),
        'audio_only': False,
        'audio_format': 'mp3',
        'retries': config.get('auto_retry', 3),
        'max_retries': config.get('auto_retry', 3),
        'custom_headers_enabled': config.get('custom_headers_enabled', False),
        'custom_headers': config.get('custom_headers', {}),
        'referer': config.get('referer'),
        'user_agent': config.get('user_agent'),
        'from_batch': False,
        'is_live': True,
        'live_duration': duration,
        'proxy': config.get('proxy'),
    }
    success = download_video(url, options)
    if success:
        console.print("[bold blue]✅ Live stream recording finished![/bold blue]")
    else:
        console.print("[bold white]Recording failed.[/bold white]")

# ----------------------------------------------------------------------
# Playlist download (unchanged)
# ----------------------------------------------------------------------
def download_playlist(url, options):
    ydl_opts = {'quiet': True, 'extract_flat': True, 'noplaylist': False}
    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
            if 'entries' not in info:
                console.print("[bold white]Not a playlist URL.[/bold white]")
                return False
            entries = info['entries']
            total = len(entries)
            console.print(f"[bold white]Playlist: {info.get('title', 'Unknown')} ({total} videos)[/bold white]")
            range_str = Prompt.ask("Enter range (e.g., 1-10, or 'all')", default="all")
            # FIX 2 (Critical): strict validation of range input.
            # Old bare except silently downloaded the ENTIRE playlist on any
            # invalid input ("first-last", "1-5-9", letters, etc.).
            if range_str.lower() != 'all':
                range_match = re.fullmatch(r'(\d+)-(\d+)', range_str.strip())
                if range_match:
                    start, end = int(range_match.group(1)), int(range_match.group(2))
                    if start < 1 or end < start or start > total:
                        console.print(f"[bold white]Invalid range {start}-{end} (playlist has {total} videos). Downloading all.[/bold white]")
                    else:
                        end = min(end, total)
                        entries = entries[start-1:end]
                        console.print(f"[blue]Downloading videos {start}–{end} of {total}.[/blue]")
                else:
                    console.print(f"[bold white]Invalid range format '{range_str}'. Use e.g. 1-10. Downloading all.[/bold white]")
    except Exception as e:
        console.print(f"[bold white]Failed to parse playlist: {e}[/bold white]")
        return False

    out_dir = os.path.expanduser(config['output_dir']) if config['output_dir'] else os.getcwd()
    save_playlist_metadata_json(info, out_dir)

    for idx, entry in enumerate(entries, 1):
        video_url = entry.get('webpage_url') or entry.get('url')
        if not video_url:
            continue
        console.print(f"\n[bold white]Downloading video {idx}/{len(entries)}: {entry.get('title', 'Unknown')}[/bold white]")
        success = download_single_video(video_url, from_batch=True, is_playlist_item=True)
        if not success:
            console.print(f"[bold white]Failed to download video {idx}. Continuing with next...[/bold white]")
        time.sleep(1)
    return True

# ----------------------------------------------------------------------
# Batch download from file (unchanged)
# ----------------------------------------------------------------------
def batch_download():
    file_path = Prompt.ask("📄 Enter path to text file (one URL per line)")
    if not os.path.exists(file_path):
        console.print("[bold white]File not found.[/bold white]")
        return
    with open(file_path, 'r') as f:
        urls = [line.strip() for line in f if line.strip() and not line.startswith('#')]
    if not urls:
        console.print("[bold white]No URLs found in file.[/bold white]")
        return
    console.print(f"[blue]Found {len(urls)} URLs.[/blue]")
    workers = int(config.get("parallel_downloads", 1))
    if workers > 1:
        console.print(f"[blue]Using {workers} parallel workers.[/blue]")
    parallel_batch_download(urls, worker_count=workers)

# ----------------------------------------------------------------------
# Queue management
# FIX W2: persist the queue to QUEUE_FILE so "save for later" survives
# a restart. Old code kept it in a plain list — every exit wiped it.
# ----------------------------------------------------------------------
def _load_queue():
    """Load the persisted queue from disk. Returns [] on any error."""
    if not os.path.exists(QUEUE_FILE):
        return []
    try:
        with open(QUEUE_FILE, 'r') as f:
            data = json.load(f)
            return data if isinstance(data, list) else []
    except Exception:
        return []

def _save_queue(queue):
    """Atomically persist the queue to disk."""
    tmp = QUEUE_FILE + ".tmp"
    try:
        with open(tmp, 'w') as f:
            json.dump(queue, f, indent=2)
        os.replace(tmp, QUEUE_FILE)
    except Exception as e:
        console.print(f"[bold white]Failed to save queue: {e}[/bold white]")
        try:
            os.remove(tmp)
        except Exception:
            pass

# In-memory view of the queue — always synced to disk
download_queue = _load_queue()

def add_to_queue():
    global download_queue
    download_queue = _load_queue()   # re-sync from disk first

    # Immediate clipboard check on entry: offer any supported URL already in
    # the clipboard as the default for the very first prompt.
    _queue_clip_prefill = ""
    try:
        _clip_text = _read_clipboard_raw().strip()
        if _is_supported_video_url(_clip_text):
            _queue_clip_prefill = _clip_text
            console.print(f"[bold blue]📋 Clipboard URL detected:[/bold blue] [dim]{_clip_text[:80]}[/dim]")
    except Exception:
        pass

    _last_seen_clip = _queue_clip_prefill  # track to catch new copies mid-session

    while True:
        # Between prompts, silently re-check clipboard for freshly copied URLs
        try:
            _fresh = _read_clipboard_raw().strip()
            if (_fresh and _fresh != _last_seen_clip
                    and _is_supported_video_url(_fresh)):
                _last_seen_clip = _fresh
                _queue_clip_prefill = _fresh
                console.print(
                    f"[bold blue]📋 New clipboard URL detected:[/bold blue] "
                    f"[dim]{_fresh[:80]}[/dim]")
        except Exception:
            pass

        if _queue_clip_prefill:
            url = Prompt.ask(
                "Enter URL to add to queue (or 'done' to finish)",
                default=_queue_clip_prefill,
            )
            _queue_clip_prefill = ""  # consume the prefill
        else:
            url = Prompt.ask("Enter URL to add to queue (or 'done' to finish)")

        if url.strip().lower() in ('q', 'quit'):
            break
        if url.lower() == 'done':
            break
        if url:
            download_queue.append(url)
            _save_queue(download_queue)
            console.print(f"[blue]Added to queue. ({len(download_queue)} URLs)[/blue]")
        else:
            console.print("[bold white]No URL entered.[/bold white]")
    if download_queue:
        if Confirm.ask(f"Process {len(download_queue)} URLs now?", default=True):
            for i, qurl in enumerate(download_queue, 1):
                console.print(f"\n[bold white]Processing {i}/{len(download_queue)}: {qurl}[/bold white]")
                download_single_video(qurl, from_batch=True)
                time.sleep(1)
            download_queue.clear()
            _save_queue(download_queue)
        else:
            console.print("[white]Queue saved for later (use 'Process queue' in main menu).[/white]")
    else:
        console.print("[white]Queue is empty.[/white]")

def process_queue():
    global download_queue
    download_queue = _load_queue()   # always load fresh from disk
    if not download_queue:
        console.print("[white]Queue is empty. Add URLs first.[/white]")
        return
    console.print(f"[blue]Processing {len(download_queue)} URLs...[/blue]")
    for i, qurl in enumerate(download_queue, 1):
        console.print(f"\n[bold white]Processing {i}/{len(download_queue)}: {qurl}[/bold white]")
        download_single_video(qurl, from_batch=True)
        time.sleep(1)
    download_queue.clear()
    _save_queue(download_queue)
    console.print("[blue]Queue finished.[/blue]")

# ----------------------------------------------------------------------
# Single video download workflow (with history check)
# ----------------------------------------------------------------------
def download_single_video(url, from_batch=False, is_playlist_item=False):
    if not is_playlist_item and not from_batch:
        if is_already_downloaded(url):
            console.print("[white]⚠️ This URL has already been downloaded before.[/white]")
            if not Confirm.ask("Download again?", default=False):
                console.print("[blue]Skipped.[/blue]")
                return True
    try:
        if not from_batch:
            check_ffmpeg()

        info = get_video_info(url)
        if not info:
            if not from_batch:
                console.print("[bold white]Could not retrieve video info. Continue anyway?[/bold white]")
                if not Confirm.ask("Continue?", default=False):
                    console.print("[white]Download cancelled.[/white]")
                    return False
        else:
            if not from_batch and not is_playlist_item:
                if not show_video_preview(info):
                    return False
            if info.get('filesize') is not None:
                needed = info['filesize'] * 1.1
                out_dir = config.get('output_dir', os.getcwd())
                if not check_disk_space(out_dir, needed):
                    if not Confirm.ask("Proceed anyway? (may fail)", default=False):
                        return False

        sub_opt = None
        if not config.get('audio_only', False) and not from_batch and not is_playlist_item:
            if Confirm.ask("📝 Download subtitles?", default=False):
                langs = get_subtitle_languages(url)
                if langs:
                    console.print(f"Available languages: {', '.join(langs)}")
                    lang = Prompt.ask("Language code", default=config.get('subtitles_lang', 'en'))
                    embed = Confirm.ask("Embed subtitles into video?", default=True)
                    sub_opt = {'lang': lang, 'embed': embed}
                else:
                    console.print("[white]No subtitles available for this video.[/white]")

        out_dir = os.path.expanduser(config['output_dir']) if config['output_dir'] else os.getcwd()
        output_template = os.path.join(out_dir, '%(title)s.%(ext)s')
        options = {
            'format_opt': config.get('format_opt'),
            'output_template': output_template,
            'no_playlist': True,
            'subtitles': sub_opt,
            '_title': info.get('title','') if info else '',
            '_extractor': info.get('extractor','') if info else '',
            'embed_thumbnail': config.get('embed_thumbnail', True),
            'embed_metadata': config.get('embed_metadata', True),
            'speed_limit': config.get('speed_limit'),
            'cookies_file': config.get('cookies_file'),
            'audio_only': config.get('audio_only', False),
            'audio_format': config.get('audio_format', 'mp3'),
            'retries': config.get('auto_retry', 3),
            'max_retries': config.get('auto_retry', 3),
            'custom_headers_enabled': config.get('custom_headers_enabled', False),
            'custom_headers': config.get('custom_headers', {}),
            'referer': config.get('referer'),
            'user_agent': config.get('user_agent'),
            'from_batch': from_batch,
            'is_playlist_item': is_playlist_item,
            'is_live': info.get('is_live', False) if info else False,
            'proxy': config.get('proxy'),
            'sponsorblock_enabled': config.get('sponsorblock_enabled', False),
            'sponsorblock_action': config.get('sponsorblock_action', 'remove'),
            'sponsorblock_categories': config.get('sponsorblock_categories',
                                                  ['sponsor', 'intro', 'outro', 'selfpromo', 'interaction']),
        }

        success = download_video(url, options)
        if success:
            console.print("[bold blue]✅ Download complete![/bold blue]")
            if info and info.get('title'):
                add_to_history(url, info['title'], out_dir, info.get('extractor', 'Unknown'))
            if not from_batch and Confirm.ask("📂 Show containing folder path?", default=False):
                console.print(f"File saved in: {out_dir}")
        else:
            console.print("[bold white]Download failed. You may retry later.[/bold white]")
        return success
    except Exception as e:
        console.print(f"[bold blue]Unexpected error:[/bold blue] {e}")
        console.print("[dim]Full traceback:[/dim]")
        traceback.print_exc()
        console.print("\n[white]Please report this issue with the above traceback.[/white]")
        input("Press Enter to return to menu...")
        return False

# ----------------------------------------------------------------------
# Preferences menu (added new options)
# ----------------------------------------------------------------------
def edit_custom_headers():
    _safe_clear()
    console.print(Panel.fit("[bold blue]Custom HTTP Headers[/bold blue]", border_style="blue"))
    console.print("These headers help mimic a browser or provide authentication.\n")

    enabled = Confirm.ask("Enable custom headers?", default=config['custom_headers_enabled'])
    config['custom_headers_enabled'] = enabled
    if enabled:
        console.print("\nCommon headers (leave empty to skip):")
        referer = Prompt.ask("Referer (e.g., https://example.com)", default=config.get('referer') or "")
        config['referer'] = referer if referer else None
        user_agent = Prompt.ask("User-Agent (e.g., Mozilla/5.0...)", default=config.get('user_agent') or "")
        config['user_agent'] = user_agent if user_agent else None

        console.print("\nAdditional headers (one per line, format: `Header: value`). Empty line to finish.")
        new_headers = {}
        while True:
            line = Prompt.ask("Header", default="")
            if not line:
                break
            if ':' in line:
                key, val = line.split(':', 1)
                new_headers[key.strip()] = val.strip()
            else:
                console.print("[bold white]Invalid format. Use 'Header: value'[/bold white]")
        config['custom_headers'] = new_headers

        if config['custom_headers'] or config.get('referer') or config.get('user_agent'):
            console.print("\n[blue]Active headers:[/blue]")
            if config.get('referer'):
                console.print(f"  Referer: {config['referer']}")
            if config.get('user_agent'):
                console.print(f"  User-Agent: {config['user_agent']}")
            for k, v in config.get('custom_headers', {}).items():
                console.print(f"  {k}: {v}")
        else:
            console.print("[white]No headers defined.[/white]")
    else:
        config['referer'] = None
        config['user_agent'] = None
        config['custom_headers'] = {}

    save_config(config)
    console.print("[blue]Custom headers saved.[/blue]")
    input("Press Enter to continue...")

# ----------------------------------------------------------------------
# Proxy configuration helper
# a-Shell note: curl_cffi impersonation and proxy can be used together;
# yt-dlp passes the proxy string directly to the HTTP client.
# Supported formats:
#   http://host:port
#   http://user:pass@host:port
#   socks5://host:port
#   socks5h://host:port  (remote DNS — preferred for Tor/SOCKS5)
# To disable: leave blank.
# ----------------------------------------------------------------------
# ----------------------------------------------------------------------
# SponsorBlock configuration helper
# yt-dlp has native SponsorBlock support via the SponsorBlock API.
# It only applies to YouTube; for all other extractors yt-dlp ignores
# the flags silently, so it is always safe to leave enabled globally.
#
# Requires ffmpeg (for cutting segments from the video file).
# On a-Shell, ffmpeg must be installed via pkg — auto-install runs at
# startup, so by the time this is used it should already be present.
#
# Actions:
#   remove  — cuts the segment out of the video entirely (default)
#   mark    — keeps the video intact but writes chapter markers for each
#             segment, visible in players that support chapters
#
# Categories (from the SponsorBlock spec):
#   sponsor       — paid promotion / sponsorship reads  (most common)
#   intro         — intro / opening title card
#   outro         — outro / end screen / subscribe begging
#   selfpromo     — unpaid self-promotion (merch, social links, etc.)
#   interaction   — "like and subscribe" mid-video reminders
#   preview       — recap of previous content / spoiler preview
#   music_offtopic— non-music sections in music videos
#   filler        — filler tangents the creator considers skippable
# ----------------------------------------------------------------------
_ALL_SB_CATS = [
    'sponsor', 'intro', 'outro', 'selfpromo', 'interaction',
    'preview', 'music_offtopic', 'filler'
]

def _edit_sponsorblock_setting():
    console.print("\n[bold white]SponsorBlock Settings[/bold white]")
    console.print("Automatically skip or mark ad-read, intro, outro, and other")
    console.print("non-content segments in YouTube videos using community data.\n")
    console.print("[white]Requires ffmpeg. Only affects YouTube downloads; safely ignored elsewhere.[/white]\n")

    enabled = Confirm.ask("Enable SponsorBlock?", default=config.get('sponsorblock_enabled', False))
    config['sponsorblock_enabled'] = enabled
    if not enabled:
        console.print("[blue]SponsorBlock disabled.[/blue]")
        return

    # Action: remove or mark
    console.print("\n[bold white]Action[/bold white]")
    console.print("  [dim]remove[/dim] — cut segments out of the downloaded file (requires ffmpeg)")
    console.print("  [dim]mark[/dim]   — keep video intact, add chapter markers for each segment\n")
    action = Prompt.ask("Action", choices=["remove", "mark"],
                        default=config.get('sponsorblock_action', 'remove'))
    config['sponsorblock_action'] = action

    # Categories
    console.print("\n[bold white]Categories to skip[/bold white] (space-separated, or 'all' for everything):")
    for cat in _ALL_SB_CATS:
        desc = {
            'sponsor':        'paid sponsorship reads (most common — almost always wanted)',
            'intro':          'opening intro / title card',
            'outro':          'end screen / outro',
            'selfpromo':      'unpaid self-promotion (merch, socials)',
            'interaction':    '"like and subscribe" reminders',
            'preview':        'recap / spoiler preview of content',
            'music_offtopic': 'non-music sections in music videos',
            'filler':         'filler tangents marked skippable by creator',
        }.get(cat, '')
        current_cats = config.get('sponsorblock_categories', _ALL_SB_CATS[:5])
        tick = '✓' if cat in current_cats else ' '
        console.print(f"  [{tick}] [bold white]{cat}[/bold white]  [dim]{desc}[/dim]")

    console.print("\nEnter categories (e.g. [dim]sponsor intro outro[/dim]), or [dim]all[/dim], or [dim]default[/dim]:")
    raw = Prompt.ask("Categories", default="default").strip().lower()

    if raw == 'all':
        chosen = _ALL_SB_CATS[:]
    elif raw in ('default', ''):
        chosen = ['sponsor', 'intro', 'outro', 'selfpromo', 'interaction']
    else:
        tokens = raw.replace(',', ' ').split()
        valid   = [t for t in tokens if t in _ALL_SB_CATS]
        invalid = [t for t in tokens if t not in _ALL_SB_CATS]
        if invalid:
            console.print(f"[bold white]⚠️  Unknown categories ignored: {', '.join(invalid)}[/bold white]")
        chosen = valid if valid else ['sponsor']

    config['sponsorblock_categories'] = chosen
    console.print(f"\n[blue]SponsorBlock enabled — action:[/blue] [bold white]{action}[/bold white]")
    console.print(f"[blue]Categories:[/blue] {', '.join(chosen)}")

def _edit_proxy_setting():
    console.print("\n[bold white]Proxy Settings[/bold white]")
    console.print("Supported formats:")
    console.print("  [dim]http://host:port[/dim]")
    console.print("  [dim]http://user:pass@host:port[/dim]")
    console.print("  [dim]socks5://host:port[/dim]")
    console.print("  [dim]socks5h://host:port[/dim]  (recommended for Tor — DNS resolved remotely)")
    console.print("  [dim]Leave blank to disable.[/dim]\n")
    console.print("[white]Note: on a-Shell, SOCKS5 proxies work via yt-dlp's built-in handler.[/white]")
    console.print("[white]Impersonation (curl-cffi) is skipped on a-Shell, so proxy+impersonate[/white]")
    console.print("[white]conflicts are not an issue here.[/white]\n")

    current = config.get('proxy') or ''
    raw = Prompt.ask("Proxy URL (or empty to disable)", default=current).strip()

    if not raw:
        config['proxy'] = None
        console.print("[blue]Proxy disabled.[/blue]")
        return

    # Basic sanity check
    valid_schemes = ('http://', 'https://', 'socks4://', 'socks4a://', 'socks5://', 'socks5h://')
    if not any(raw.lower().startswith(s) for s in valid_schemes):
        console.print("[bold white]⚠️  Unrecognised scheme. Expected http://, socks5://, etc.[/bold white]")
        console.print("   Saving anyway — yt-dlp will report an error if it's invalid.")

    config['proxy'] = raw
    console.print(f"[blue]Proxy set to: {raw}[/blue]")

    # Optional: quick reachability test via yt-dlp --dump-json on a known URL
    if Confirm.ask("Test proxy now with a quick yt-dlp connection check?", default=False):
        _test_proxy(raw)

def _test_proxy(proxy_url):
    """Quick proxy connectivity test using yt-dlp on a known-good URL."""
    test_url = "https://www.youtube.com/watch?v=jNQXAC9IVRw"  # 'Me at the zoo' — always public
    console.print(f"[dim]Testing proxy via: {test_url} ...[/dim]")
    cmd = _get_ytdlp_base_cmd() + [
        "--proxy", proxy_url,
        "--quiet", "--no-warnings",
        "--simulate",
        "--no-playlist",
        test_url
    ]
    try:
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, timeout=20)
        if result.returncode == 0:
            console.print("[bold blue]✅ Proxy test passed — connection OK.[/bold blue]")
        else:
            err = (result.stderr or '').strip().splitlines()
            short_err = err[-1] if err else 'unknown error'
            console.print(f"[bold white]❌ Proxy test failed: {short_err}[/bold white]")
            console.print("   Check the proxy URL and ensure the proxy server is running.")
    except subprocess.TimeoutExpired:
        console.print("[bold white]❌ Proxy test timed out (20 s). The proxy may be slow or unreachable.[/bold white]")
    except Exception as e:
        console.print(f"[bold white]❌ Proxy test error: {e}[/bold white]")

def edit_preferences():
    while True:
        _safe_clear()
        console.print(Panel.fit("[bold blue]⚙️ Preferences[/bold blue]", border_style="blue"))
        console.print(f"1. Output directory          : [white]{config['output_dir']}[/white]")
        console.print(f"2. Speed limit               : [white]{config['speed_limit'] or 'None'}[/white]")
        console.print(f"3. Embed thumbnail           : [white]{config['embed_thumbnail']}[/white]")
        console.print(f"4. Embed metadata            : [white]{config['embed_metadata']}[/white]")
        console.print(f"5. Auto retry count          : [white]{config['auto_retry']}[/white]")
        console.print(f"6. Audio only mode           : [white]{config['audio_only']}[/white]")
        console.print(f"7. Audio format              : [white]{config['audio_format']}[/white]")
        console.print(f"8. Cookies file              : [white]{config['cookies_file'] or 'None'}[/white]")
        console.print(f"9. Subtitle language         : [white]{config['subtitles_lang']}[/white]")
        console.print(f"10. Custom HTTP Headers      : [white]{'Enabled' if config['custom_headers_enabled'] else 'Disabled'}[/white]")
        console.print(f"11. Battery threshold (%)    : [white]{config.get('battery_threshold', 20)}[/white]")
        console.print(f"12. Smart battery check      : [white]{'On' if config.get('enable_smart_sleep', True) else 'Off'}[/white]")
        console.print(f"13. Live stream max duration : [white]{config.get('live_record_duration', 0)} minutes (0 = until ends)[/white]")
        console.print(f"14. Impersonate target       : [white]{config.get('impersonate_target', 'auto')} (for TikTok/Twitter etc.)[/white]")
        console.print(f"15. Proxy                    : [white]{config.get('proxy') or 'None'}[/white]")
        _sb_status = 'Enabled (' + config.get('sponsorblock_action','remove') + ')' if config.get('sponsorblock_enabled') else 'Disabled'
        console.print(f"16. SponsorBlock             : [white]{_sb_status}[/white]")
        console.print(f"17. Clipboard watcher        : [white]{'Enabled' if config.get('clipboard_watcher_enabled') else 'Disabled'}[/white]")
        console.print(f"18. Download archive         : [white]{config.get('archive_file') or 'Disabled'}[/white]")
        console.print(f"19. Parallel downloads       : [white]{config.get('parallel_downloads', 1)} worker(s)[/white]")
        console.print(f"20. Download scheduler       : [white]{'Enabled (' + config.get('schedule_start','?') + '-' + config.get('schedule_end','?') + ')' if config.get('schedule_enabled') else 'Disabled'}[/white]")
        console.print(f"21. Webhook URL              : [white]{config.get('webhook_url') or 'Disabled'}[/white]")
        console.print(f"22. Notification sounds      : [white]{'On' if config.get('notify_sound', True) else 'Off'}[/white]")
        console.print(f"23. Save playlist metadata   : [white]{'On' if config.get('save_playlist_metadata') else 'Off'}[/white]")
        console.print("0. Back to main menu")
        choice = Prompt.ask("Choose an option", choices=[str(i) for i in range(24)], default="0")

        if choice == '0':
            break
        elif choice == '1':
            new_dir = Prompt.ask("New output directory", default=config['output_dir'])
            new_dir = os.path.expanduser(new_dir) if new_dir else os.getcwd()
            if not new_dir:
                new_dir = os.getcwd()
            if os.path.isdir(new_dir) or Confirm.ask("Directory does not exist. Create it?", default=True):
                os.makedirs(new_dir, exist_ok=True)
                config['output_dir'] = new_dir
            else:
                console.print("[bold white]Output directory not changed.[/bold white]")
        elif choice == '2':
            speed = Prompt.ask("Speed limit (e.g., 1M, 500K, or empty for none)", default="")
            config['speed_limit'] = speed if speed else None
        elif choice == '3':
            config['embed_thumbnail'] = Confirm.ask("Embed thumbnail?", default=config['embed_thumbnail'])
        elif choice == '4':
            config['embed_metadata'] = Confirm.ask("Embed metadata?", default=config['embed_metadata'])
        elif choice == '5':
            try:
                config['auto_retry'] = int(Prompt.ask("Number of retries", default=str(config['auto_retry'])))
            except ValueError:
                console.print("[bold white]Invalid number. Keeping previous.[/bold white]")
        elif choice == '6':
            config['audio_only'] = Confirm.ask("Download audio only?", default=config['audio_only'])
        elif choice == '7':
            config['audio_format'] = Prompt.ask("Audio format (mp3/m4a)", choices=["mp3", "m4a"], default=config['audio_format'])
        elif choice == '8':
            cookie_path = Prompt.ask("Path to cookies.txt (or empty to disable)", default="")
            if cookie_path:
                cookie_path = os.path.expanduser(cookie_path)
                if os.path.exists(cookie_path):
                    config['cookies_file'] = cookie_path
                else:
                    console.print("[bold white]File not found.[/bold white]")
                    config['cookies_file'] = None
            else:
                config['cookies_file'] = None
        elif choice == '9':
            config['subtitles_lang'] = Prompt.ask("Default subtitle language code", default=config['subtitles_lang'])
        elif choice == '10':
            edit_custom_headers()
        elif choice == '11':
            try:
                val = int(Prompt.ask("Battery threshold (%)", default=str(config.get('battery_threshold', 20))))
                config['battery_threshold'] = max(0, min(100, val))
            except Exception:
                console.print("[bold white]Invalid number.[/bold white]")
        elif choice == '12':
            config['enable_smart_sleep'] = Confirm.ask("Enable smart battery check before downloads?", default=config.get('enable_smart_sleep', True))
        elif choice == '13':
            try:
                minutes = int(Prompt.ask("Max live stream duration in minutes (0 = no limit)", default=str(config.get('live_record_duration', 0))))
                config['live_record_duration'] = max(0, minutes)
            except Exception:
                console.print("[bold white]Invalid number.[/bold white]")
        elif choice == '14':
            console.print("\n[bold white]Impersonate Target[/bold white]")
            console.print("This makes yt-dlp pretend to be a real browser — required by TikTok, Twitter/X, and some other sites.")
            console.print("Requires the [bold white]curl-cffi[/bold white] package (auto-installed on startup).\n")
            available = get_available_impersonate_targets()
            if available:
                console.print(f"[blue]Available targets on this device:[/blue] {', '.join(available)}")
                choices_list = ['auto', 'off'] + available
                console.print("  [dim]auto[/dim] = pick the best available automatically")
                console.print("  [dim]off[/dim]  = disable impersonation entirely\n")
                target = Prompt.ask("Choose target", default=config.get('impersonate_target', 'auto'))
                if target not in choices_list:
                    console.print(f"[bold white]'{target}' is not in the available list. Setting to 'auto'.[/bold white]")
                    target = 'auto'
                config['impersonate_target'] = target
            else:
                console.print("[bold white]⚠️ No impersonate targets available.[/bold white]")
                console.print("   curl-cffi may not be installed or may not support your platform.")
                console.print("   On a-Shell (iOS): curl-cffi is intentionally skipped due to a cffi")
                console.print("   version conflict. Use cookies instead (Preferences → Cookies File).")
                console.print("   On other platforms: try running: pip install curl_cffi==0.1.5")
                console.print("   Setting to 'off' to prevent errors.")
                config['impersonate_target'] = 'off'
        elif choice == '15':
            _edit_proxy_setting()
        elif choice == '16':
            _edit_sponsorblock_setting()
        elif choice == '17':
            _configure_clipboard_settings()
            continue  # _configure_clipboard_settings already saves
        elif choice == '18':
            _configure_archive()
            continue
        elif choice == '19':
            _configure_parallel()
            continue
        elif choice == '20':
            _configure_schedule()
            continue
        elif choice == '21':
            _configure_webhook()
            continue
        elif choice == '22':
            config['notify_sound'] = Confirm.ask(
                "Enable notification sounds on download complete/fail?",
                default=config.get('notify_sound', True))
        elif choice == '23':
            config['save_playlist_metadata'] = Confirm.ask(
                "Save playlist metadata JSON alongside downloads?",
                default=config.get('save_playlist_metadata', False))
        save_config(config)
        console.print("[blue]Preferences saved.[/blue]")
        time.sleep(1)

def select_quality():
    console.print(Panel.fit("[bold blue]Quality & FPS Setup[/bold blue]", border_style="blue"))
    fps_choice = Prompt.ask("Preferred FPS", choices=["any", "144", "120", "60", "30", "24", "custom"], default="any")
    fps_val = None
    if fps_choice == 'custom':
        while True:
            try:
                fps_val = int(Prompt.ask("Enter FPS value"))
                break
            except ValueError:
                console.print("[bold white]Please enter an integer.[/bold white]")
    elif fps_choice != 'any':
        fps_val = int(fps_choice)

    if fps_val is not None:
        fps_filter = f"[fps<={fps_val+0.1}]"
    else:
        fps_filter = ""

    config['fps_pref'] = fps_val

    console.print("\nResolution options:")
    console.print("1. Best quality (MP4/H.264 only)")
    console.print("2. 2160p (4K)")
    console.print("3. 1440p (2K)")
    console.print("4. 1080p (Full HD)")
    console.print("5. 720p (HD)")
    console.print("6. 480p")
    console.print("7. 360p")
    console.print("8. 240p")
    console.print("9. 144p")
    console.print("0. Manual format selection (advanced) - will show all formats and let you choose")
    res_choice = Prompt.ask("Enter number", choices=[str(i) for i in range(10)], default="4")
    if res_choice == '0':
        config['format_opt'] = None
    else:
        res_map = {'1': "best", '2': "2160", '3': "1440", '4': "1080", '5': "720",
                   '6': "480", '7': "360", '8': "240", '9': "144"}
        res = res_map[res_choice]
        codec_filter = "vcodec~='avc1|h264'"
        if res == "best":
            format_opt = (
                f"bestvideo[ext=mp4][{codec_filter}]{fps_filter}+bestaudio[ext=m4a]"
                f"/bestvideo[ext=mp4]{fps_filter}+bestaudio"
                f"/bestvideo{fps_filter}+bestaudio"
                f"/best{fps_filter}"
            )
        else:
            format_opt = (
                f"bestvideo[ext=mp4][{codec_filter}][height<={res}]{fps_filter}+bestaudio[ext=m4a]"
                f"/bestvideo[ext=mp4][height<={res}]{fps_filter}+bestaudio"
                f"/bestvideo[height<={res}]{fps_filter}+bestaudio"
                f"/best[height<={res}]{fps_filter}"
                f"/best{fps_filter}"
            )
        config['format_opt'] = format_opt
    save_config(config)
    console.print("[blue]Quality preferences saved.[/blue]")
    input("Press Enter to continue...")

# ----------------------------------------------------------------------
# Main menu
# ----------------------------------------------------------------------
# ==============================================================================
# v2.0 NEW FEATURES
# ==============================================================================

# ------------------------------------------------------------------------------
# Download stats tracker (in-memory, shown in dashboard at end of session)
# ------------------------------------------------------------------------------
_stats = {
    "session_start": datetime.now().isoformat(),
    "total_attempted": 0,
    "total_success": 0,
    "total_failed": 0,
    "total_bytes": 0,
    "by_source": {},        # extractor -> count
    "speeds_mbps": [],      # list of measured speeds
    "history_added": [],    # list of {url, title, extractor, bytes, duration_s, ok}
}

def stats_record(url, title, extractor, ok, file_bytes=0, duration_s=0):
    """Record one download result into the session stats."""
    _stats["total_attempted"] += 1
    if ok:
        _stats["total_success"] += 1
    else:
        _stats["total_failed"] += 1
    _stats["total_bytes"] += file_bytes
    src = extractor or "Unknown"
    _stats["by_source"][src] = _stats["by_source"].get(src, 0) + 1
    _stats["history_added"].append({
        "url": url, "title": title, "extractor": src,
        "bytes": file_bytes, "duration_s": duration_s, "ok": ok,
    })

def stats_record_speed(mbps):
    """Append a measured speed sample (MB/s) to the session stats."""
    if mbps and mbps > 0:
        _stats["speeds_mbps"].append(round(mbps, 2))

def show_stats_dashboard():
    """Print a rich session stats summary table."""
    elapsed = (datetime.now() - datetime.fromisoformat(_stats["session_start"])).total_seconds()
    total_mb = _stats["total_bytes"] / 1024 / 1024
    avg_speed = (sum(_stats["speeds_mbps"]) / len(_stats["speeds_mbps"])) if _stats["speeds_mbps"] else 0
    success_rate = (
        _stats["total_success"] / _stats["total_attempted"] * 100
        if _stats["total_attempted"] else 0
    )
    console.print("\n")
    console.print(Panel.fit("[bold blue]📊 Session Download Dashboard[/bold blue]", border_style="blue"))
    if RICH_AVAILABLE:
        summary = Table(box=box.ROUNDED, show_lines=False, title="Summary")
        summary.add_column("Metric", style="bold")
        summary.add_column("Value", style="blue")
        summary.add_row("Session duration",     f"{int(elapsed//60)}m {int(elapsed%60)}s")
        summary.add_row("Total attempted",      str(_stats["total_attempted"]))
        summary.add_row("Successful",           f"[bold blue]{_stats['total_success']}[/bold blue]")
        summary.add_row("Failed",               f"[bold white]{_stats['total_failed']}[/bold white]"
                                                if _stats["total_failed"] else "0")
        summary.add_row("Success rate",         f"{success_rate:.1f}%")
        summary.add_row("Total data downloaded",f"{total_mb:.1f} MB")
        summary.add_row("Avg speed",            f"{avg_speed:.1f} MB/s" if avg_speed else "N/A")
        console.print(summary)

        if _stats["by_source"]:
            src_table = Table(box=box.SIMPLE, title="Downloads by Source")
            src_table.add_column("Source", style="bold")
            src_table.add_column("Count", justify="right")
            for src, cnt in sorted(_stats["by_source"].items(), key=lambda x: -x[1]):
                src_table.add_row(src, str(cnt))
            console.print(src_table)
    else:
        print(f"  Session: {int(elapsed//60)}m {int(elapsed%60)}s  |  "
              f"Success: {_stats['total_success']}/{_stats['total_attempted']}  |  "
              f"Data: {total_mb:.1f} MB  |  Avg speed: {avg_speed:.1f} MB/s")
        for src, cnt in sorted(_stats["by_source"].items(), key=lambda x: -x[1]):
            print(f"  {src}: {cnt}")


# ------------------------------------------------------------------------------
# Notification sound (cross-platform)
# ------------------------------------------------------------------------------
def play_notification(success=True):
    """Play a short terminal bell or system sound on download completion."""
    if not config.get("notify_sound", True):
        return
    try:
        if sys.platform == "win32":
            import winsound
            freq, dur = (1000, 200) if success else (400, 400)
            winsound.Beep(freq, dur)
        elif sys.platform == "darwin":
            sound = "Glass" if success else "Basso"
            subprocess.run(["afplay", f"/System/Library/Sounds/{sound}.aiff"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        else:
            # Linux/Termux — try paplay (PulseAudio) then fall back to terminal bell
            bell_played = False
            for cmd_try in [
                ["paplay", "/usr/share/sounds/freedesktop/stereo/complete.oga"],
                ["aplay",  "/usr/share/sounds/alsa/Front_Center.wav"],
            ]:
                if shutil.which(cmd_try[0]):
                    result = subprocess.run(cmd_try, stdout=subprocess.DEVNULL,
                                            stderr=subprocess.DEVNULL)
                    if result.returncode == 0:
                        bell_played = True
                        break
            if not bell_played:
                print("\a", end="", flush=True)  # terminal bell fallback
    except Exception:
        pass


# ------------------------------------------------------------------------------
# Post-download webhook
# ------------------------------------------------------------------------------
def fire_webhook(url, title, extractor, ok, error_msg=""):
    """POST a JSON payload to the configured webhook URL (non-blocking)."""
    webhook_url = config.get("webhook_url")
    if not webhook_url:
        return
    if ok and not config.get("webhook_on_success", True):
        return
    if not ok and not config.get("webhook_on_failure", True):
        return

    payload = json.dumps({
        "status":    "success" if ok else "failure",
        "url":       url,
        "title":     title,
        "extractor": extractor,
        "timestamp": datetime.now().isoformat(),
        "error":     error_msg,
    }).encode("utf-8")

    def _send():
        try:
            req = urllib.request.Request(
                webhook_url,
                data=payload,
                headers={"Content-Type": "application/json", "User-Agent": "UniversalDownloader/2.0"},
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=10) as resp:
                console.print(f"[dim]Webhook → {resp.status} {resp.reason}[/dim]")
        except Exception as e:
            console.print(f"[white]Webhook failed: {e}[/white]")

    t = threading.Thread(target=_send, daemon=True)
    t.start()


# ------------------------------------------------------------------------------
# Download scheduling: wait until inside the allowed time window
# ------------------------------------------------------------------------------
def _in_schedule_window():
    """Return True if current time is inside config schedule_start..schedule_end."""
    if not config.get("schedule_enabled", False):
        return True
    now = datetime.now().strftime("%H:%M")
    start = config.get("schedule_start", "00:00")
    end   = config.get("schedule_end",   "23:59")
    if start <= end:
        return start <= now <= end
    else:  # overnight window e.g. 22:00 – 06:00
        return now >= start or now <= end

def wait_for_schedule_window():
    """Block until we're inside the configured download window, showing a countdown."""
    if _in_schedule_window():
        return
    console.print(Panel.fit(
        f"[bold blue]⏰ Download Scheduler[/bold blue]\n"
        f"Waiting for window: [bold white]{config['schedule_start']}[/bold white] – "
        f"[bold white]{config['schedule_end']}[/bold white]",
        border_style="blue"
    ))
    console.print("[dim]Press Ctrl+C to cancel.[/dim]")
    try:
        while not _in_schedule_window():
            now = datetime.now().strftime("%H:%M:%S")
            console.print(f"\r[white]Current time: {now}  — waiting for window...[/white]",
                          end="")
            time.sleep(30)
    except KeyboardInterrupt:
        console.print("\n[white]Schedule wait cancelled.[/white]")
        return
    console.print("\n[bold blue]✅ Download window started![/bold blue]")


# ------------------------------------------------------------------------------
# Parallel download worker pool
# Wraps download_single_video in a thread pool so multiple items can be
# fetched concurrently (controlled by config['parallel_downloads']).
# ------------------------------------------------------------------------------
def parallel_batch_download(urls, worker_count=None):
    """Download a list of URLs in parallel using a thread pool."""
    if worker_count is None:
        worker_count = max(1, min(int(config.get("parallel_downloads", 1)), 8))
    if worker_count == 1:
        # Fall back to sequential to avoid any thread overhead
        for i, url in enumerate(urls, 1):
            console.print(f"\n[bold white]Downloading {i}/{len(urls)}:[/bold white] {url}")
            download_single_video(url, from_batch=True)
            time.sleep(0.5)
        return

    console.print(f"[bold blue]Starting parallel download with {worker_count} workers "
                  f"({len(urls)} URLs)...[/bold blue]")

    url_queue = _queue.Queue()
    for url in urls:
        url_queue.put(url)

    results = {}
    results_lock = threading.Lock()

    def worker(worker_id):
        while True:
            try:
                url = url_queue.get_nowait()
            except _queue.Empty:
                break
            console.print(f"[dim]Worker {worker_id}: {url[:60]}...[/dim]")
            ok = download_single_video(url, from_batch=True)
            with results_lock:
                results[url] = ok
            url_queue.task_done()

    threads = []
    for i in range(worker_count):
        t = threading.Thread(target=worker, args=(i + 1,), daemon=True)
        t.start()
        threads.append(t)
    for t in threads:
        t.join()

    success = sum(1 for v in results.values() if v)
    fail    = len(results) - success
    console.print(f"\n[bold blue]Parallel batch complete:[/bold blue] "
                  f"[blue]{success} succeeded[/blue], "
                  f"[white]{fail} failed[/white]")


# ------------------------------------------------------------------------------
# Clipboard watcher
# Polls the system clipboard for new video URLs and optionally queues them.
# Uses pyperclip (auto-installed) for cross-platform clipboard access.
# Falls back to xclip/xsel on Linux, pbpaste on macOS, or PowerShell on Windows.
# ------------------------------------------------------------------------------
_SUPPORTED_DOMAINS = [
    "youtube.com", "youtu.be", "tiktok.com", "twitter.com", "x.com",
    "instagram.com", "vimeo.com", "twitch.tv", "reddit.com", "soundcloud.com",
    "bilibili.com", "dailymotion.com", "facebook.com", "fb.watch",
    "streamable.com", "rumble.com", "odysee.com", "bitchute.com",
    "niconico.jp", "nicovideo.jp", "weibo.com", "ok.ru",
]

def _read_clipboard_raw():
    """Read current clipboard text via pyperclip or platform fallbacks."""
    # Try pyperclip first
    try:
        import pyperclip  # type: ignore
        return pyperclip.paste() or ""
    except Exception:
        pass
    # macOS
    if sys.platform == "darwin":
        try:
            return subprocess.check_output(["pbpaste"], text=True, timeout=3)
        except Exception:
            pass
    # Linux — try xclip, xsel, wl-paste
    if sys.platform.startswith("linux"):
        for cmd in (["xclip", "-selection", "clipboard", "-o"],
                    ["xsel", "--clipboard", "--output"],
                    ["wl-paste"]):
            if shutil.which(cmd[0]):
                try:
                    return subprocess.check_output(cmd, text=True, timeout=3,
                                                    stderr=subprocess.DEVNULL)
                except Exception:
                    pass
    # Windows PowerShell
    if sys.platform == "win32":
        try:
            out = subprocess.check_output(
                ["powershell", "-NoProfile", "-Command", "Get-Clipboard"],
                text=True, timeout=5, stderr=subprocess.DEVNULL)
            return out.strip()
        except Exception:
            pass
    return ""

def _is_supported_video_url(text):
    """Return True if text looks like a supported video URL."""
    text = text.strip()
    if not re.match(r"^https?://", text, re.IGNORECASE):
        return False
    try:
        parsed = urllib.parse.urlparse(text)
        domain = parsed.netloc.lower().lstrip("www.")
        return any(domain == d or domain.endswith("." + d) for d in _SUPPORTED_DOMAINS)
    except Exception:
        return False

_clipboard_stop_event = threading.Event()
_clipboard_seen_urls = set()
_clipboard_pending_queue = []   # filled when auto_queue=False, user reviews at end
_clipboard_watcher_thread = None

def _clipboard_watcher_loop(poll_interval, auto_queue, notify_fn):
    """Background thread: poll clipboard, detect new URLs, optionally queue them."""
    last_text = ""
    while not _clipboard_stop_event.is_set():
        try:
            text = _read_clipboard_raw().strip()
            if (text != last_text and text not in _clipboard_seen_urls
                    and _is_supported_video_url(text)):
                last_text = text
                url_hash = hashlib.md5(text.encode()).hexdigest()[:8]
                _clipboard_seen_urls.add(text)
                console.print(f"\n[bold blue]📋 Clipboard URL detected[/bold blue]  "
                               f"[dim]({url_hash})[/dim]\n  {text}")
                if auto_queue:
                    _clipboard_pending_queue.append(text)
                    console.print(f"  [white]→ Added to queue "
                                  f"({len(_clipboard_pending_queue)} total)[/white]")
                if notify_fn:
                    notify_fn(text)
        except Exception:
            pass
        _clipboard_stop_event.wait(timeout=poll_interval)

def start_clipboard_watcher(on_url_detected=None):
    """Start the clipboard watcher in a background daemon thread."""
    global _clipboard_watcher_thread
    if _clipboard_watcher_thread and _clipboard_watcher_thread.is_alive():
        console.print("[white]Clipboard watcher is already running.[/white]")
        return
    _clipboard_stop_event.clear()
    _clipboard_seen_urls.clear()
    _clipboard_pending_queue.clear()

    poll   = float(config.get("clipboard_poll_interval", 1.5))
    auto_q = config.get("clipboard_auto_queue", False)

    _clipboard_watcher_thread = threading.Thread(
        target=_clipboard_watcher_loop,
        args=(poll, auto_q, on_url_detected),
        daemon=True,
        name="ClipboardWatcher",
    )
    _clipboard_watcher_thread.start()
    console.print(f"[bold blue]📋 Clipboard watcher started[/bold blue]  "
                  f"[dim](poll every {poll}s, auto-queue={'on' if auto_q else 'off'})[/dim]")

def stop_clipboard_watcher():
    """Signal the clipboard watcher thread to stop."""
    _clipboard_stop_event.set()
    console.print("[white]Clipboard watcher stopped.[/white]")

def clipboard_watcher_menu():
    """Interactive menu for the clipboard watcher feature."""
    console.print(Panel.fit("[bold blue]📋 Clipboard Watcher[/bold blue]", border_style="blue"))

    running = _clipboard_watcher_thread and _clipboard_watcher_thread.is_alive()
    console.print(f"Status: [bold white]{'🟢 Running' if running else '🔴 Stopped'}[/bold white]")
    console.print(f"Detected this session: [bold blue]{len(_clipboard_seen_urls)}[/bold blue] URL(s)")
    console.print(f"Pending queue: [bold blue]{len(_clipboard_pending_queue)}[/bold blue] URL(s)")
    console.print("")
    console.print("1. Start watcher")
    console.print("2. Stop watcher")
    console.print("3. Show detected URLs")
    console.print("4. Download all pending (queued) URLs now")
    console.print("5. Configure watcher settings")
    console.print("0. Back")

    choice = Prompt.ask("Choose", choices=["0","1","2","3","4","5"], default="0")

    if choice == "1":
        auto_install("pyperclip", "pyperclip (clipboard support)", pip_name="pyperclip")
        start_clipboard_watcher()
        console.print("[dim]Watcher is running in background. Return to main menu and copy a URL to test.[/dim]")
        input("Press Enter to continue...")
    elif choice == "2":
        stop_clipboard_watcher()
        input("Press Enter to continue...")
    elif choice == "3":
        if not _clipboard_seen_urls:
            console.print("[white]No URLs detected yet.[/white]")
        else:
            for i, url in enumerate(_clipboard_seen_urls, 1):
                console.print(f"  {i}. {url}")
        input("Press Enter to continue...")
    elif choice == "4":
        if not _clipboard_pending_queue:
            console.print("[white]No pending URLs in queue.[/white]")
            input("Press Enter to continue...")
            return
        console.print(f"[bold white]{len(_clipboard_pending_queue)} URL(s) to download:[/bold white]")
        for u in _clipboard_pending_queue:
            console.print(f"  • {u}")
        if Confirm.ask("Download all now?", default=True):
            workers = int(config.get("parallel_downloads", 1))
            parallel_batch_download(list(_clipboard_pending_queue), worker_count=workers)
            _clipboard_pending_queue.clear()
        input("Press Enter to continue...")
    elif choice == "5":
        _configure_clipboard_settings()

def _configure_clipboard_settings():
    """Sub-menu to configure clipboard watcher preferences."""
    console.print("\n[bold white]Clipboard Watcher Settings[/bold white]")
    interval = config.get("clipboard_poll_interval", 1.5)
    try:
        new_interval = float(Prompt.ask(
            "Poll interval in seconds (min 0.5)", default=str(interval)))
        config["clipboard_poll_interval"] = max(0.5, new_interval)
    except ValueError:
        console.print("[bold white]Invalid value; keeping previous.[/bold white]")

    config["clipboard_auto_queue"] = Confirm.ask(
        "Auto-add detected URLs to queue without prompting?",
        default=config.get("clipboard_auto_queue", False))

    save_config(config)
    console.print("[blue]Clipboard watcher settings saved.[/blue]")
    input("Press Enter to continue...")


# ------------------------------------------------------------------------------
# Download archive (deduplication via yt-dlp native --download-archive)
# ------------------------------------------------------------------------------
def _get_archive_path():
    """Return the active archive file path, or None if disabled."""
    return config.get("archive_file") or None

def _configure_archive():
    """Let the user enable/disable yt-dlp download archive."""
    console.print("\n[bold white]Download Archive[/bold white]")
    console.print("When enabled, yt-dlp writes the ID of every downloaded video to a file.")
    console.print("Re-running the same URL skips it automatically — no re-downloads.")
    console.print("[white]The archive file is shared across all downloads.[/white]\n")

    current = config.get("archive_file") or ""
    if current:
        console.print(f"Current archive file: [blue]{current}[/blue]")
        if Confirm.ask("Disable archive?", default=False):
            config["archive_file"] = None
            save_config(config)
            console.print("[blue]Archive disabled.[/blue]")
            input("Press Enter to continue...")
            return

    default_path = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), ".ytdl_archive.txt")
    path = Prompt.ask("Archive file path (Enter for default)", default=current or default_path)
    path = os.path.expanduser(path.strip()) if path.strip() else default_path
    config["archive_file"] = path
    # Create the file if it doesn't exist yet
    if not os.path.exists(path):
        try:
            open(path, "a").close()
            console.print(f"[blue]Archive file created: {path}[/blue]")
        except Exception as e:
            console.print(f"[bold white]Could not create archive file: {e}[/bold white]")
    else:
        # Count existing entries
        try:
            with open(path) as af:
                count = sum(1 for l in af if l.strip())
            console.print(f"[blue]Archive file has {count} existing entries.[/blue]")
        except Exception:
            pass
    save_config(config)
    console.print("[blue]Download archive enabled.[/blue]")
    input("Press Enter to continue...")


# ------------------------------------------------------------------------------
# Webhook configuration sub-menu
# ------------------------------------------------------------------------------
def _configure_webhook():
    """Let the user set up a post-download webhook URL."""
    console.print("\n[bold white]Post-Download Webhook[/bold white]")
    console.print("Claude will POST a JSON payload to this URL after each download.")
    console.print("Payload: { status, url, title, extractor, timestamp, error }\n")

    current = config.get("webhook_url") or ""
    if current:
        console.print(f"Current URL: [blue]{current}[/blue]")
    raw = Prompt.ask("Webhook URL (leave blank to disable)", default=current).strip()
    if not raw:
        config["webhook_url"] = None
        console.print("[blue]Webhook disabled.[/blue]")
    else:
        if not re.match(r"^https?://", raw, re.IGNORECASE):
            console.print("[bold white]⚠️  URL must start with http:// or https://[/bold white]")
        else:
            config["webhook_url"] = raw
            config["webhook_on_success"] = Confirm.ask(
                "Fire webhook on success?", default=config.get("webhook_on_success", True))
            config["webhook_on_failure"] = Confirm.ask(
                "Fire webhook on failure?", default=config.get("webhook_on_failure", True))
            console.print(f"[blue]Webhook set: {raw}[/blue]")
    save_config(config)
    input("Press Enter to continue...")


# ------------------------------------------------------------------------------
# Parallel downloads configuration sub-menu
# ------------------------------------------------------------------------------
def _configure_parallel():
    """Configure the number of parallel download workers."""
    console.print("\n[bold white]Parallel Downloads[/bold white]")
    console.print("[white]Recommended: 1-3 to avoid rate-limiting. Max 8.[/white]\n")
    current = int(config.get("parallel_downloads", 1))
    try:
        val = int(Prompt.ask(
            "Number of parallel workers (1 = sequential)",
            default=str(current)))
        config["parallel_downloads"] = max(1, min(val, 8))
    except ValueError:
        console.print("[bold white]Invalid number; keeping previous.[/bold white]")
    save_config(config)
    console.print(f"[blue]Parallel workers set to {config['parallel_downloads']}.[/blue]")
    input("Press Enter to continue...")


# ------------------------------------------------------------------------------
# Download scheduling configuration sub-menu
# ------------------------------------------------------------------------------
def _configure_schedule():
    """Configure the download time-window scheduler."""
    console.print("\n[bold white]Download Scheduler[/bold white]")
    console.print("Restrict downloads to a specific time window (e.g. off-peak hours).")
    console.print("[white]Format: HH:MM (24-hour). Overnight windows are supported.[/white]\n")

    enabled = Confirm.ask(
        "Enable scheduler?",
        default=config.get("schedule_enabled", False))
    config["schedule_enabled"] = enabled
    if enabled:
        start = Prompt.ask("Window start time (HH:MM)", default=config.get("schedule_start", "02:00"))
        end   = Prompt.ask("Window end time   (HH:MM)", default=config.get("schedule_end",   "06:00"))
        # Basic validation
        for label, val in [("Start", start), ("End", end)]:
            if not re.match(r"^\d{2}:\d{2}$", val):
                console.print(f"[bold white]{label} time format invalid. Use HH:MM.[/bold white]")
                return
        config["schedule_start"] = start
        config["schedule_end"]   = end
        console.print(f"[blue]Scheduler enabled: {start} → {end}[/blue]")
    else:
        console.print("[blue]Scheduler disabled.[/blue]")
    save_config(config)
    input("Press Enter to continue...")


# ------------------------------------------------------------------------------
# Playlist metadata saver
# ------------------------------------------------------------------------------
def save_playlist_metadata_json(playlist_info, out_dir):
    """Dump playlist info dict to a JSON file alongside the downloads."""
    if not config.get("save_playlist_metadata", False):
        return
    title_slug = re.sub(r"[^\w\-]", "_", playlist_info.get("title", "playlist"))[:40]
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_path = os.path.join(out_dir, f"{title_slug}_metadata_{ts}.json")
    try:
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(playlist_info, f, indent=2, ensure_ascii=False)
        console.print(f"[white]Playlist metadata saved: {out_path}[/white]")
    except Exception as e:
        console.print(f"[bold white]Could not save playlist metadata: {e}[/bold white]")


# ------------------------------------------------------------------------------
# Search & Download  (NEW in v2.1)
# Uses yt-dlp's built-in ytsearch: extractor — no extra API key required.
# Supports YouTube text search as well as direct keyword-to-download.
# ------------------------------------------------------------------------------
def search_and_download():
    """Interactive search: enter keywords → pick a result → download it."""
    console.print(Panel.fit(
        "[bold blue]🔍 Search & Download[/bold blue]\n"
        "[dim]Search YouTube (or any supported site) by keyword and pick a result to download[/dim]",
        border_style="blue"))

    # --- Step 1: get query & result count ---
    query = Prompt.ask("🔎 [bold blue]Enter search keywords[/bold blue] (or 'q' to go back)").strip()
    # BUG FIX: don't call quit_if_requested here — that calls sys.exit() and
    # kills the whole script. Instead check inline and just return to the menu.
    if query.lower() in ('q', 'quit'):
        return
    if not query:
        console.print("[white]No query entered. Returning to menu.[/white]")
        input("Press Enter to continue...")
        return

    try:
        max_results_raw = Prompt.ask(
            "How many results to show? (1-100)",
            default="5",
        ).strip()
        # BUG FIX: raised cap from 20 → 100 so requesting 21-100 results works
        # correctly. The old hard cap of 20 meant any request over 20 was silently
        # clipped, which confused users who asked for more.
        max_results = max(1, min(int(max_results_raw), 100))
    except ValueError:
        max_results = 5

    # --- Step 2: fetch search results via yt-dlp ytsearch ---
    console.print(f"\n[dim]Searching for:[/dim] [bold white]{query}[/bold white]  "
                  f"[dim](top {max_results} results)[/dim]\n")

    search_url = f"ytsearch{max_results}:{query}"
    ydl_search_opts = {
        'quiet': True,
        'no_warnings': True,
        'extract_flat': True,       # fast: metadata only, no actual download
        'noplaylist': False,        # needed to iterate search results
        'ignoreerrors': True,
    }
    if config.get('proxy'):
        ydl_search_opts['proxy'] = config['proxy']

    results = []
    with Progress(SpinnerColumn(), TextColumn("[progress.description]{task.description}"),
                  transient=True) as prog:
        prog.add_task(description="Searching…", total=None)
        try:
            with yt_dlp.YoutubeDL(ydl_search_opts) as ydl:
                info = ydl.extract_info(search_url, download=False)
                if info and 'entries' in info:
                    results = [e for e in info['entries'] if e]
        except Exception as e:
            console.print(f"[bold white]Search error: {e}[/bold white]")

    if not results:
        console.print("[bold white]No results found. Try different keywords.[/bold white]")
        input("Press Enter to continue...")
        return

    # BUG FIX: tell the user how many results were actually returned.
    # yt-dlp may return fewer items than requested (e.g. 12 instead of 100
    # if YouTube has fewer matches). Without this, users type numbers that
    # appear valid on-screen but are above len(results) and get confusing
    # "out of range" warnings.
    actual_count = len(results)
    if actual_count < max_results:
        console.print(f"[white]ℹ️  {actual_count} result(s) returned "
                      f"(fewer than the {max_results} requested). "
                      f"Valid selections: 1–{actual_count}.[/white]")

    # --- Step 3: display results ---
    # Two-line layout per entry: works on any terminal width (including narrow
    # mobile screens like a-Shell on iPhone) without truncating the # column
    # or squeezing Title out of existence.
    #   Line 1:  [#] Title
    #   Line 2:      Channel · Duration · Views
    if RICH_AVAILABLE:
        console.print(Panel.fit("[bold white]🔍 Search Results[/bold white]", border_style="blue"))
        for i, entry in enumerate(results, 1):
            title    = entry.get('title') or 'Unknown'
            channel  = (entry.get('uploader') or entry.get('channel') or '?')
            dur_sec  = entry.get('duration') or 0
            duration = format_duration(dur_sec) if dur_sec else '?'
            views    = f"{entry.get('view_count'):,}" if entry.get('view_count') else '?'
            console.print(f"[dim]{i:>3}.[/dim] [white]{title}[/white]")
            console.print(f"     [blue]{channel}[/blue]  "
                          f"[white]{duration}  ·  {views} views[/white]")
    else:
        print("\n── Search Results ──")
        for i, entry in enumerate(results, 1):
            title    = entry.get('title') or 'Unknown'
            channel  = (entry.get('uploader') or entry.get('channel') or '?')
            dur_sec  = entry.get('duration') or 0
            duration = format_duration(dur_sec) if dur_sec else '?'
            views    = f"{entry.get('view_count'):,}" if entry.get('view_count') else '?'
            print(f"{i:>3}. {title}")
            print(f"     {channel}  {duration}  {views} views")

    console.print()

    # --- Step 4: pick a result (allow multiple selections or all) ---
    raw = Prompt.ask(
        "Enter result number(s) to download (e.g. 1 or 1,3,5 or 'all'), or 'q' to go back",
        default="q",
    ).strip().lower()
    # BUG FIX: was quit_if_requested(raw) which calls sys.exit() on 'q',
    # terminating the whole script. Use an inline check so 'q' just returns
    # to the main menu instead.
    if raw in ('q', 'quit', 'back', ''):
        return

    # Parse selection
    chosen_indices = []
    if raw == 'all':
        chosen_indices = list(range(len(results)))
    else:
        for part in re.split(r'[,\s]+', raw):
            part = part.strip()
            if not part:
                continue
            try:
                idx = int(part) - 1
                if 0 <= idx < len(results):
                    chosen_indices.append(idx)
                else:
                    console.print(f"[bold white]⚠️  #{int(part)} is out of range — skipped.[/bold white]")
            except ValueError:
                console.print(f"[bold white]⚠️  '{part}' is not a valid number — skipped.[/bold white]")

    if not chosen_indices:
        console.print("[white]Nothing selected. Returning to menu.[/white]")
        input("Press Enter to continue...")
        return

    # --- Step 5: confirm & download each chosen video ---
    for idx in chosen_indices:
        entry = results[idx]
        # Build the direct watch URL
        video_id  = entry.get('id') or entry.get('url', '')
        video_url = entry.get('webpage_url') or entry.get('url') or ''
        if not video_url:
            # Fallback: construct YouTube URL from id
            if video_id and not video_id.startswith('http'):
                video_url = f"https://www.youtube.com/watch?v={video_id}"
            else:
                video_url = video_id

        title = entry.get('title') or 'Unknown'
        console.print(f"\n[bold blue]▶  Selected:[/bold blue] {title}")
        console.print(f"   [dim]{video_url}[/dim]")

        if not Confirm.ask(f"Download this video?", default=True):
            console.print("[white]Skipped.[/white]")
            continue

        if not video_url or not video_url.startswith('http'):
            console.print("[bold white]❌ Could not resolve a valid URL for this result. Skipped.[/bold white]")
            continue

        # Reuse the existing single-video download pipeline (handles all
        # quality/audio/subtitle/archive/webhook/stats logic already).
        download_single_video(video_url)

    input("\nPress Enter to continue...")


# ==============================================================================
# IMAGE UPSCALER  (v3.0)
# ==============================================================================
# Upscales any local image to a chosen resolution preset.
# Backends (tried in priority order):
#   1. Real-ESRGAN  — AI super-resolution (best quality, GPU or CPU)
#   2. OpenCV       — Lanczos / bicubic interpolation (fast, good)
#   3. Pillow       — LANCZOS resampling (always available as final fallback)
#
# Resolution presets (target HEIGHT in pixels; width is auto-calculated to
# preserve the original aspect ratio):
#
#   240p   →   426 × 240
#   360p   →   640 × 360
#   480p   →   854 × 480
#   540p   →   960 × 540
#   720p   →  1280 × 720   (HD)
#   900p   →  1600 × 900
#   1080p  →  1920 × 1080  (Full HD)
#   1440p  →  2560 × 1440  (2K)
#   2160p  →  3840 × 2160  (4K)
#   4320p  →  7680 × 4320  (8K)
#   custom →  user-specified height
#
# Output is saved alongside the source file with _upscaled_<preset> suffix.
# ==============================================================================

# Preset table: name → target height (px)
UPSCALE_PRESETS = {
    "240p":   240,
    "360p":   360,
    "480p":   480,
    "540p":   540,
    "720p":   720,
    "900p":   900,
    "1080p":  1080,
    "1440p":  1440,
    "2160p":  2160,
    "4320p":  4320,
    "custom":  None,   # resolved interactively
}

_UPSCALE_PRESET_LABELS = list(UPSCALE_PRESETS.keys())


def _upscale_get_backend():
    """
    Return the best available upscaling backend as a string:
      'realesrgan' | 'opencv' | 'pillow'
    Installs packages lazily if needed.
    """
    # ── Real-ESRGAN (Python binding) ───────────────────────────────────
    try:
        from basicsr.archs.rrdbnet_arch import RRDBNet          # noqa
        from realesrgan import RealESRGANer                     # noqa
        return "realesrgan"
    except ImportError:
        pass

    # ── OpenCV ─────────────────────────────────────────────────────────
    try:
        import cv2                                               # noqa
        return "opencv"
    except ImportError:
        pass

    # ── Pillow (always available after a fresh install) ─────────────────
    if auto_install("PIL", "Pillow", pip_name="Pillow"):
        try:
            from PIL import Image                                # noqa
            return "pillow"
        except ImportError:
            pass

    return None


def _upscale_try_install_realesrgan():
    """
    Attempt to install Real-ESRGAN and its dependencies.
    Returns True on success.  Does NOT raise — always returns bool.
    """
    console.print(
        "[white]Attempting to install Real-ESRGAN (AI upscaler)...[/white]\n"
        "[dim]This may take a few minutes and requires ~2 GB of disk space.[/dim]"
    )
    pkgs = [
        ("basicsr",    "basicsr"),
        ("facexlib",   "facexlib"),
        ("gfpgan",     "gfpgan"),
        ("realesrgan", "realesrgan"),
    ]
    for mod, pkg in pkgs:
        if not auto_install(mod, pkg, pip_name=pkg):
            console.print(f"[bold white]Could not install {pkg}. Falling back to OpenCV/Pillow.[/bold white]")
            return False
    return True


def _upscale_with_realesrgan(src_path, dst_path, scale_factor):
    """Upscale src_path → dst_path using Real-ESRGAN at the given scale."""
    from basicsr.archs.rrdbnet_arch import RRDBNet
    from realesrgan import RealESRGANer
    import torch

    # Pick the right model for the scale
    if scale_factor <= 2:
        model_name = "RealESRGAN_x2plus"
        model      = RRDBNet(num_in_ch=3, num_out_ch=3, num_feat=64,
                             num_block=23, num_grow_ch=32, scale=2)
        netscale   = 2
    else:
        model_name = "RealESRGAN_x4plus"
        model      = RRDBNet(num_in_ch=3, num_out_ch=3, num_feat=64,
                             num_block=23, num_grow_ch=32, scale=4)
        netscale   = 4

    # Locate or download the model weights
    model_dir  = os.path.join(os.path.expanduser("~"), ".cache", "realesrgan")
    model_path = os.path.join(model_dir, f"{model_name}.pth")
    os.makedirs(model_dir, exist_ok=True)

    if not os.path.exists(model_path):
        urls = {
            "RealESRGAN_x2plus": (
                "https://github.com/xinntao/Real-ESRGAN/releases/download/"
                "v0.2.1/RealESRGAN_x2plus.pth"
            ),
            "RealESRGAN_x4plus": (
                "https://github.com/xinntao/Real-ESRGAN/releases/download/"
                "v0.1.0/RealESRGAN_x4plus.pth"
            ),
        }
        console.print(f"[dim]Downloading model weights for {model_name}...[/dim]")
        try:
            urllib.request.urlretrieve(urls[model_name], model_path)
        except Exception as e:
            raise RuntimeError(f"Failed to download model: {e}") from e

    device = "cuda" if torch.cuda.is_available() else "cpu"
    upsampler = RealESRGANer(
        scale=netscale,
        model_path=model_path,
        model=model,
        tile=400,          # tile processing for low-VRAM / CPU
        tile_pad=10,
        pre_pad=0,
        half=False,
        device=device,
    )

    import cv2
    img = cv2.imread(src_path, cv2.IMREAD_UNCHANGED)
    if img is None:
        raise ValueError(f"Could not open image: {src_path}")

    # Real-ESRGAN always upscales by netscale; we resize afterwards if needed
    out_img, _ = upsampler.enhance(img, outscale=scale_factor)
    cv2.imwrite(dst_path, out_img)


def _upscale_with_opencv(src_path, dst_path, target_w, target_h):
    """Upscale src_path → dst_path using OpenCV Lanczos."""
    import cv2
    img = cv2.imread(src_path, cv2.IMREAD_UNCHANGED)
    if img is None:
        raise ValueError(f"Could not open image: {src_path}")
    out = cv2.resize(img, (target_w, target_h), interpolation=cv2.INTER_LANCZOS4)
    cv2.imwrite(dst_path, out)


def _upscale_with_pillow(src_path, dst_path, target_w, target_h):
    """Upscale src_path → dst_path using Pillow LANCZOS."""
    from PIL import Image
    with Image.open(src_path) as img:
        # Preserve alpha / palette modes
        if img.mode in ("P", "PA"):
            img = img.convert("RGBA")
        out = img.resize((target_w, target_h), Image.LANCZOS)
        out.save(dst_path)


def _get_image_dimensions(path):
    """
    Return (width, height) of an image file.
    Tries Pillow first, then falls back to reading header bytes.
    """
    try:
        from PIL import Image
        with Image.open(path) as im:
            return im.size      # (width, height)
    except Exception:
        pass
    try:
        import cv2
        img = cv2.imread(path)
        if img is not None:
            h, w = img.shape[:2]
            return w, h
    except Exception:
        pass
    return None, None


def _resolve_target_dimensions(src_w, src_h, target_h):
    """
    Given source dimensions and a target HEIGHT, compute the target WIDTH
    that preserves the aspect ratio (rounding to nearest even integer).
    Returns (target_w, target_h).
    """
    if not src_w or not src_h:
        return target_h * 16 // 9, target_h   # assume 16:9 if unknown
    ratio    = src_w / src_h
    target_w = int(round(target_h * ratio))
    # Round to nearest even (many codecs require even dimensions)
    target_w = target_w + (target_w % 2)
    return target_w, target_h


def upscale_image_menu():
    """
    Interactive image upscaling menu.
    Guides the user through:
      1. Entering the source image path
      2. Choosing a resolution preset
      3. Selecting (or auto-detecting) a backend
      4. Running the upscale and reporting the result
    """
    console.print(Panel.fit(
        "[bold blue]{icon} Image Upscaler[/bold blue]\n"
        "[dim]Upscale any local image from 240p up to 8K[/dim]".format(
            icon=_e("🖼️", "[IMG]")),
        border_style="blue",
    ))

    # ── Step 1: source file ────────────────────────────────────────────
    while True:
        src_path = Prompt.ask(
            "Path to source image (or 'q' to go back)"
        ).strip()
        if src_path.lower() in ("q", "quit", "back", ""):
            return
        src_path = os.path.expanduser(src_path)
        if not os.path.isfile(src_path):
            console.print(
                f"[bold white]File not found: {src_path}[/bold white]\n"
                "Please enter a valid path to an image file."
            )
            continue
        # Quick sanity check: does it look like an image?
        _ext = os.path.splitext(src_path)[1].lower()
        _img_exts = {".jpg", ".jpeg", ".png", ".bmp", ".tiff", ".tif",
                     ".webp", ".gif", ".heic", ".heif", ".avif"}
        if _ext not in _img_exts:
            console.print(
                f"[bold white]'{_ext}' is not a recognised image extension.[/bold white]\n"
                f"Supported: {', '.join(sorted(_img_exts))}\n"
                "Type 'force' to proceed anyway, or press Enter to re-enter."
            )
            _f = Prompt.ask("", default="").strip().lower()
            if _f != "force":
                continue
        break

    # Show source dimensions if detectable
    src_w, src_h = _get_image_dimensions(src_path)
    if src_w and src_h:
        console.print(
            f"[blue]Source dimensions:[/blue] {src_w} × {src_h} px"
        )
    else:
        console.print("[dim]Could not read source dimensions — will proceed anyway.[/dim]")

    # ── Step 2: resolution preset ──────────────────────────────────────
    console.print("\n[bold white]Choose target resolution:[/bold white]")
    preset_rows = [
        ("1",  "240p",   "426 × 240    (mobile / thumbnail)"),
        ("2",  "360p",   "640 × 360    (low quality)"),
        ("3",  "480p",   "854 × 480    (SD)"),
        ("4",  "540p",   "960 × 540    (qHD)"),
        ("5",  "720p",   "1280 × 720   (HD)"),
        ("6",  "900p",   "1600 × 900   (HD+)"),
        ("7",  "1080p",  "1920 × 1080  (Full HD)"),
        ("8",  "1440p",  "2560 × 1440  (2K / QHD)"),
        ("9",  "2160p",  "3840 × 2160  (4K UHD)"),
        ("10", "4320p",  "7680 × 4320  (8K UHD)"),
        ("11", "custom", "Enter your own height in pixels"),
    ]
    for num, name, desc in preset_rows:
        if RICH_AVAILABLE:
            console.print(
                f"[bold blue]{num:>3}.[/bold blue]  "
                f"[white]{name:<8}[/white]  [dim]{desc}[/dim]"
            )
        else:
            _safe_print(f"{num:>3}. {name:<8}  {desc}")

    preset_choice = Prompt.ask(
        "Select preset",
        choices=[str(i) for i in range(1, 12)],
        default="7",
    )
    preset_map = {str(i): r[1] for i, r in enumerate(preset_rows, 1)}
    chosen_preset = preset_map[preset_choice]

    if chosen_preset == "custom":
        while True:
            try:
                target_h = int(Prompt.ask("Enter target height (pixels)"))
                if target_h < 1:
                    raise ValueError
                break
            except ValueError:
                console.print("[bold white]Please enter a positive integer.[/bold white]")
    else:
        target_h = UPSCALE_PRESETS[chosen_preset]

    target_w, target_h = _resolve_target_dimensions(src_w, src_h, target_h)
    console.print(
        f"[blue]Target dimensions:[/blue] {target_w} × {target_h} px"
    )

    # Warn if upscaling would actually downscale
    if src_h and target_h < src_h:
        console.print(
            "[bold white]⚠️  The chosen preset is SMALLER than the source image.\n"
            "   This will downscale (shrink) the image, not upscale it.[/bold white]"
        )
        if not Confirm.ask("Continue anyway?", default=False):
            console.print("[white]Cancelled.[/white]")
            return

    # ── Step 3: backend ────────────────────────────────────────────────
    console.print("\n[bold white]Upscaling backend:[/bold white]")
    console.print("  [dim]auto[/dim]       — use the best available (recommended)")
    console.print("  [dim]realesrgan[/dim] — AI super-resolution (best quality; installs ~2 GB)")
    console.print("  [dim]opencv[/dim]     — fast Lanczos interpolation")
    console.print("  [dim]pillow[/dim]     — basic LANCZOS (always available)")
    backend_choice = Prompt.ask(
        "Backend",
        choices=["auto", "realesrgan", "opencv", "pillow"],
        default="auto",
    )

    if backend_choice == "auto":
        backend = _upscale_get_backend()
        if backend is None:
            console.print("[bold white]No upscaling backend available. Attempting to install Pillow...[/bold white]")
            if auto_install("PIL", "Pillow", pip_name="Pillow"):
                backend = "pillow"
            else:
                console.print("[bold white]❌ Cannot upscale without at least Pillow installed.[/bold white]")
                input("Press Enter to continue...")
                return
        console.print(f"[blue]Auto-selected backend:[/blue] [white]{backend}[/white]")
    elif backend_choice == "realesrgan":
        # Try to import; offer install if missing
        try:
            from realesrgan import RealESRGANer  # noqa
            backend = "realesrgan"
        except ImportError:
            if Confirm.ask(
                "Real-ESRGAN is not installed. Install now? (~2 GB, may be slow)",
                default=True,
            ):
                if _upscale_try_install_realesrgan():
                    backend = "realesrgan"
                else:
                    console.print("[white]Falling back to auto-selection.[/white]")
                    backend = _upscale_get_backend() or "pillow"
            else:
                backend = _upscale_get_backend() or "pillow"
    else:
        backend = backend_choice
        # Ensure the chosen backend is available
        if backend == "opencv":
            if not auto_install("cv2", "OpenCV", pip_name="opencv-python-headless"):
                console.print("[white]OpenCV unavailable, falling back to Pillow.[/white]")
                backend = "pillow"
        elif backend == "pillow":
            auto_install("PIL", "Pillow", pip_name="Pillow")

    # ── Step 4: build output path ──────────────────────────────────────
    base, ext = os.path.splitext(src_path)
    # Use PNG for lossless output; keep original ext otherwise
    out_ext    = ext if ext.lower() in (".png", ".bmp", ".tiff", ".tif") else ".png"
    dst_path   = f"{base}_upscaled_{chosen_preset}{out_ext}"

    # Avoid overwriting without confirmation
    if os.path.exists(dst_path):
        if not Confirm.ask(
            f"Output file already exists:\n  {dst_path}\nOverwrite?",
            default=False,
        ):
            ts_suffix = datetime.now().strftime("%Y%m%d_%H%M%S")
            dst_path  = f"{base}_upscaled_{chosen_preset}_{ts_suffix}{out_ext}"
            console.print(f"[dim]Output will be saved as: {dst_path}[/dim]")

    # ── Step 5: run upscale ────────────────────────────────────────────
    console.print(
        f"\n[bold blue]{_e('🚀', '>>')} Starting upscale...[/bold blue]  "
        f"[dim]({backend})[/dim]"
    )
    start_t = time.time()

    try:
        if backend == "realesrgan":
            # Compute a float scale factor relative to the source height
            if src_h:
                scale_factor = target_h / src_h
            else:
                scale_factor = 4.0   # safe default
            _upscale_with_realesrgan(src_path, dst_path, scale_factor)

        elif backend == "opencv":
            _upscale_with_opencv(src_path, dst_path, target_w, target_h)

        else:   # pillow
            _upscale_with_pillow(src_path, dst_path, target_w, target_h)

        elapsed = time.time() - start_t
        console.print(
            f"\n[bold blue]{_e('✅', 'OK')} Upscale complete![/bold blue]  "
            f"[dim]({elapsed:.1f}s)[/dim]"
        )
        console.print(f"[blue]Saved to:[/blue] {dst_path}")

        # Verify output and show final dimensions
        out_w, out_h = _get_image_dimensions(dst_path)
        if out_w and out_h:
            console.print(
                f"[blue]Output dimensions:[/blue] {out_w} × {out_h} px"
            )

    except Exception as exc:
        console.print(
            f"[bold white]{_e('❌', 'ERROR')} Upscale failed: {exc}[/bold white]"
        )
        console.print("[dim]Full traceback:[/dim]")
        traceback.print_exc()
        console.print(
            "\n[white]Tips:[/white]\n"
            "  • Make sure the source file is not corrupted.\n"
            "  • For Real-ESRGAN, model weights are downloaded on first run (~100 MB).\n"
            "  • Try a different backend (opencv or pillow) if this persists.\n"
            "  • Ensure you have enough free disk space."
        )

    input("\nPress Enter to continue...")


def _print_banner():
    """Print the PacketHound Vid Downloader header, adapting to terminal width."""
    _narrow = TERM_ENV.get("is_narrow", False)
    _emoji  = TERM_ENV.get("emoji_support", True)
    _arrow  = ">>" if not _emoji else "▸"
    if RICH_AVAILABLE and TERM_ENV.get("color_support"):
        _sub = (
            "[dim white]clipboard · parallel · schedule · webhooks · archive · "
            "image upscaler[/dim white]"
        )
        if _narrow:
            # Compact two-line banner for narrow screens (iPhone portrait etc.)
            console.print(Panel(
                "[bold blue]PacketHound[/bold blue] [white]v3.0[/white]\n" + _sub,
                border_style="blue", padding=(0, 1),
            ))
        else:
            console.print(Panel(
                "[bold blue]  PacketHound[/bold blue]  [white]Vid Downloader  v3.0[/white]\n"
                "[white]  1000+ sites via yt-dlp  |  Image Upscaler[/white]\n"
                "  " + _sub,
                border_style="blue", padding=(0, 2),
            ))
    else:
        sep = "-" * min(TERM_ENV.get("term_cols", 60), 60)
        _safe_print(sep)
        _safe_print("  PacketHound -- Vid Downloader  v3.0")
        _safe_print("  1000+ sites | clipboard | parallel | scheduler | webhooks")
        _safe_print("  archive | image upscaler (240p to 8K)")
        _safe_print(sep)
        _safe_print()


def main():
    os.makedirs(config['output_dir'], exist_ok=True)
    # Use the cross-platform safe clear instead of console.clear()
    _safe_clear()
    _print_banner()
    # Auto-start clipboard watcher if previously enabled
    if config.get("clipboard_watcher_enabled", False):
        auto_install("pyperclip", "pyperclip (clipboard support)", pip_name="pyperclip")
        start_clipboard_watcher()
    while True:
        console.print("\n[bold white]Main Menu[/bold white]")
        menu_items = [
            (1,  f"{_e('📥','[DL]')} Download a single video/audio"),
            (2,  "Manage queue (add/process multiple URLs)"),
            (3,  "Show download history"),
            (4,  "Change quality / FPS settings"),
            (5,  "Edit preferences"),
            (6,  "Show current configuration"),
            (7,  f"{_e('🎥','[REC]')} Record live stream (auto-wait & auto-stop)"),
            (8,  "Clear download history"),
            (9,  "Export download history (CSV / HTML)"),
            (10, f"{_e('📊','[STATS]')} Session stats dashboard"),
            (11, f"{_e('🔍','[SEARCH]')} Search & Download"),
            (12, f"{_e('🖼️','[UPSCALE]')} Image Upscaler (240p to 8K)"),
            (0,  "Exit"),
        ]
        for num, label in menu_items:
            if RICH_AVAILABLE:
                console.print(f"[bold blue]{num}.[/bold blue]  [white]{label}[/white]")
            else:
                _safe_print(f"{num}.  {label}")
        choice = Prompt.ask(
            "Choose",
            choices=["0","1","2","3","4","5","6","7","8","9","10","11","12"],
            default="1",
        )
        if choice == "0":
            console.print("[white]Goodbye![/white]")
            break
        elif choice == "1":
            url = get_url()
            if url is None:
                continue
            if 'playlist' in url.lower() or 'list=' in url:
                if Confirm.ask("This looks like a playlist. Download as playlist?", default=True):
                    download_playlist(url, {})
                    continue
            download_single_video(url)
        elif choice == "2":
            console.print("[bold white]Queue Management[/bold white]")
            console.print("1. Add URLs to queue")
            console.print("2. Process current queue")
            q_choice = Prompt.ask("Choose", choices=["1","2"], default="1")
            if q_choice == "1":
                add_to_queue()
            else:
                process_queue()
        elif choice == "3":
            show_history()
        elif choice == "4":
            select_quality()
        elif choice == "5":
            edit_preferences()
        elif choice == "6":
            safe_config = config.copy()
            if safe_config.get('cookies_file'):
                safe_config['cookies_file'] = safe_config['cookies_file'] + " (hidden)"
            console.print(Panel(json.dumps(safe_config, indent=2), title="Current Configuration", border_style="blue"))
            input("Press Enter to continue...")
        elif choice == "7":
            record_live_stream()
        elif choice == "8":
            clear_history()
        elif choice == "9":
            export_history()
        elif choice == "10":
            show_stats_dashboard()
            input("\nPress Enter to continue...")
        elif choice == "11":
            search_and_download()
        elif choice == "12":
            upscale_image_menu()
        _safe_clear()

if __name__ == "__main__":
    main()
