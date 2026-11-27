#!/usr/bin/env python3
"""
Image Sorter
============

A drag-and-drop filing desk for images.

You map up to 200 destination folders (local drives or network/UNC paths) to big
clickable tiles. Drag one or many images from your Desktop / Downloads (or anywhere
in Explorer) onto a tile, and they get filed into that folder. You can also pick an
"active target" and cycle through targets, dropping into one large zone.

Highlights
----------
- Map / edit / remove folders easily; saved between sessions.
- Move (default) or Copy, toggled at the top. Move is what you want for clearing
  Downloads; Copy is there when you'd rather keep the original.
- Per-tile reachability light. If a network drive is down, the tile goes red and a
  drop is blocked with a clear "drive not reachable" message.
- Collision-safe: a same-named file is auto-renamed "name (1).jpg" instead of
  overwriting (configurable: rename / skip / overwrite).
- Undo the last batch (Ctrl+Z) - important when Move is on.
- Search box + category filter to find the right folder among many.
- Right-click a tile: open the folder, edit, recolor, reorder, copy path, remove.
- Transfers run on a background thread with a progress bar, so big network copies
  never freeze the window.
- Network scan: point it at one or more roots (a mapped drive, a UNC share, any
  local folder) and every real subfolder underneath is auto-mapped, mirroring
  your actual folder tree as nested groups up to 10 levels deep (anything
  deeper still gets filed, just flattened into labeled tiles). Runs
  automatically on launch (configurable) or on demand via "Scan now".
- Folder counter in the toolbar so you can see how close you are to the
  200-folder limit before you hit it.
- Ctrl+click to multi-select any mix of folders and groups, then remove the
  whole selection in one click from the selection bar (or from any selected
  tile's right-click menu).
- A group can be removed two ways: "Ungroup" keeps its contents and moves them
  up a level, while "Remove group" deletes the group and everything nested
  inside it in one step (still just untracking - real files are never touched).
- Click a group tile to jump straight to its real folder on disk (when it has
  one); double-click still browses the group's contents inside the app.
- Every tile - folders and groups/subfolders alike - shows a random image
  from inside its folder (a folder with only subfolders borrows from them).
  A fresh one is picked each time you open a level.
- Adding a folder brings its whole subfolder tree with it: the folder becomes
  a group mirroring every real subfolder underneath (same mechanics as a
  network scan), so you can double-click it and reach anything below it.
- Two ways to work, switchable from the toolbar (Ctrl+I):
    * Original Mode  - the tile dashboard described above.
    * Interactive Mode - a split view. Left: the images sitting in your source
      folders (Desktop + Downloads by default), shown large, one at a time;
      step through them with the arrows / wheel. Right: every destination
      folder and its subfolders as a tree. Drag the big image onto a folder
      and it is filed in the background with exactly the same Move/Copy,
      collision, reachability, undo and logging rules as Original Mode.
      A Single/Multiple toggle switches to a 3 x 2 grid: click a tile to
      select it, Ctrl+click (or Shift+click) to select several, then drag
      them onto a folder together; Prev/Next page 6 at a time.
      A red Delete button (or the Delete key) removes the image on screen
      from your computer - to the Recycle Bin on Windows - and moves on.

Run
---
    pip install PySide6
    python image_sorter.py
"""

import os
import sys
import json
import uuid
import random
import shutil
import socket
import threading
from collections import OrderedDict
from datetime import datetime, timedelta
from dataclasses import dataclass, asdict
from concurrent.futures import ThreadPoolExecutor
from queue import Queue

from PySide6.QtCore import (
    Qt, QObject, Signal, QThread, QTimer, QSize, QRect, QPoint, QMimeData,
    QUrl, QStandardPaths, QFileSystemWatcher, QBuffer, QByteArray, QIODevice,
)
from PySide6.QtGui import (
    QColor, QFont, QShortcut, QKeySequence, QFontMetrics,
    QPixmap, QImage, QPainter, QPainterPath, QDrag, QTextCursor,
    QImageReader, QMovie, QIcon, QPen,
)
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QFrame, QLabel, QPushButton, QLineEdit,
    QComboBox, QVBoxLayout, QHBoxLayout, QScrollArea, QLayout,
    QFileDialog, QColorDialog, QDialog, QFormLayout, QDialogButtonBox, QMessageBox,
    QMenu, QPlainTextEdit, QCheckBox, QSpinBox, QProgressBar, QInputDialog,
    QSplitter, QStackedWidget, QTreeWidget, QTreeWidgetItem, QButtonGroup, QStyle,
    QListWidget, QListWidgetItem, QAbstractItemView, QGridLayout, QSizePolicy,
)

APP_NAME = "Image Sorter"
APP_VERSION = "3.3.0"
MAX_FOLDERS = 200
GROUP_MIME = "application/x-imagesorter-group"   # drag payload: a group id
FOLDER_MIME = "application/x-imagesorter-folders"  # drag payload: folder ids (csv)
STAGE_MIME = "application/x-imagesorter-stage"     # drag payload: Interactive Mode image
PREVIEW_MAX_SIDE = 3200   # Interactive Mode: decode big images down to this long side
PREVIEW_CACHE = 10        # decoded big-view images kept in memory (current + neighbors)
GRID_ROWS, GRID_COLS = 2, 3   # Interactive Mode "Multiple" view: up to 6 images at once
GRID_SIZE = GRID_ROWS * GRID_COLS
GRID_THUMB_SIDE = 900     # grid tiles decode smaller than the single view (memory)
GRID_CACHE = 30           # decoded grid thumbnails kept (this page + next/prev pages)
RAW_READ_CAP = 80 * 1024 * 1024    # read at most this much of a RAW file for its preview
RAW_SLICE_CAP = 40 * 1024 * 1024   # max bytes handed to the JPEG decoder per attempt
BATCH_LIMIT = 10          # max folders addable in one "Add folders" session
MAX_GROUP_DEPTH = 4       # how deep groups may nest (Books > Action > ... )
SCAN_MAX_GROUP_DEPTH = 10  # how deep a network scan mirrors real folders as
                            # nested groups before flattening the rest into tiles
BIG_FILE_BYTES = 8 * 1024 * 1024   # show per-file % and chunked copy above this
SHOW_DIALOG_BYTES = 8 * 1024 * 1024  # pop the progress window for batches >= this
SHOW_DIALOG_FILES = 25               # ...or with at least this many files
TILE_W = 156
TILE_H = 150
COVER_W = 136             # thumbnail cover banner inside a tile
COVER_H = 72
COVER_RADIUS = 8
COVER_SCAN_DIRS = 80      # folders a cover search may open when a folder has no own images
COVER_SCAN_DEPTH = 4      # ...and how far below the folder it may look
COVER_CAND_CAP = 400      # stop collecting cover candidates past this many images

# Raster formats Qt can reliably decode for tile covers (RAW/SVG excluded).
THUMB_EXTS = {
    ".jpg", ".jpeg", ".jpe", ".jfif", ".png", ".gif", ".bmp", ".dib",
    ".webp", ".tif", ".tiff", ".ico",
}

# Distinct colors auto-assigned to tiles when adding several at once.
TILE_PALETTE = [
    "#3b82f6", "#ef4444", "#22c55e", "#f59e0b", "#a855f7",
    "#06b6d4", "#ec4899", "#84cc16", "#f97316", "#14b8a6",
]

IMAGE_EXTS = {
    ".jpg", ".jpeg", ".jpe", ".jfif", ".png", ".gif", ".bmp", ".dib", ".webp",
    ".tif", ".tiff", ".heic", ".heif", ".avif", ".svg", ".ico", ".jxl",
    # common camera RAW
    ".raw", ".cr2", ".cr3", ".nef", ".nrw", ".arw", ".srf", ".sr2", ".dng",
    ".orf", ".rw2", ".raf", ".pef", ".x3f",
}

VIDEO_EXTS = {
    ".mkv", ".mp4", ".mov", ".m4v", ".avi", ".wmv", ".flv", ".webm",
    ".mpg", ".mpeg", ".m2ts", ".mts", ".ts", ".3gp", ".3g2", ".ogv", ".vob",
}

AUDIO_EXTS = {
    ".mp3", ".m4a", ".aac", ".ogg", ".oga", ".opus", ".flac", ".alac",
    ".wav", ".wma", ".aiff", ".aif", ".wv", ".ape", ".mka", ".mid",
    ".midi", ".amr", ".ac3", ".dts", ".pcm", ".caf", ".mp2", ".spx",
    ".dsf", ".dff", ".ra", ".ram",
}

MEDIA_EXTS = IMAGE_EXTS | VIDEO_EXTS | AUDIO_EXTS

# Camera RAW: Qt can't decode these, but they embed a JPEG preview we can show.
RAW_EXTS = {
    ".raw", ".cr2", ".cr3", ".nef", ".nrw", ".arw", ".srf", ".sr2", ".dng",
    ".orf", ".rw2", ".raf", ".pef", ".x3f",
}

DEFAULT_SETTINGS = {
    "mode": "move",            # "move" or "copy"
    "collision": "rename",     # "rename" | "skip" | "overwrite"
    "media_only": True,        # if True, non-media (non image/video/audio) files are skipped
    "confirm_each": False,     # if True, ask before every drop
    "auto_check_seconds": 20,  # how often to re-check reachability
    "background_image": "",    # optional home-screen wallpaper path
    "scan_roots": [],          # root folders/drives to auto-map on scan
    "auto_scan_startup": True, # run a scan automatically when the app opens
    "ignored_scan_paths": [],  # normalized paths a scan should never re-add
    "view_mode": "original",   # "original" (tile dashboard) | "interactive" (split view)
    "interactive_sources": None,     # None = Desktop + Downloads; else list of folders
    "interactive_sort": "newest",    # "newest" | "oldest" | "name"
    "interactive_hidden_roots": [],  # top-level group/folder ids hidden from the tree
    "interactive_split": [],         # remembered splitter sizes [left, right]
    "confirm_delete": False,         # ask before Interactive Mode's Delete button deletes
    "interactive_layout": "single",  # "single" (one big image) | "multi" (up to 6)
}


def decode_folder_ids(mime):
    """Folder ids carried by a folder-tile drag, or []."""
    if mime.hasFormat(FOLDER_MIME):
        raw = bytes(mime.data(FOLDER_MIME)).decode("utf-8")
        return [x for x in raw.split(",") if x]
    return []


# --------------------------------------------------------------------------- #
# Config storage
# --------------------------------------------------------------------------- #
def config_dir() -> str:
    if sys.platform.startswith("win"):
        base = os.environ.get("APPDATA") or os.path.expanduser("~")
    elif sys.platform == "darwin":
        base = os.path.expanduser("~/Library/Application Support")
    else:
        base = os.environ.get("XDG_CONFIG_HOME") or os.path.expanduser("~/.config")
    path = os.path.join(base, "ImageSorter")
    os.makedirs(path, exist_ok=True)
    return path


CONFIG_PATH = os.path.join(config_dir(), "config.json")
LOG_PATH = os.path.join(config_dir(), "activity_log.jsonl")
LOG_RETENTION_DAYS = 365          # keep about a year of activity
LOG_VIEW_MAX = 3000               # most-recent entries to show in the panel


@dataclass
class Mapping:
    id: str
    name: str
    path: str
    color: str = "#3b82f6"
    category: str = ""
    favorite: bool = False
    group: str = ""            # group id, "" = top level
    cover: str = ""            # basename of the chosen cover image, "" = none
    scanned: bool = False      # True if a network scan created this tile

    @staticmethod
    def from_dict(d: dict) -> "Mapping":
        return Mapping(
            id=str(d.get("id") or uuid.uuid4().hex),
            name=str(d.get("name", "")).strip(),
            path=str(d.get("path", "")).strip(),
            color=str(d.get("color") or "#3b82f6"),
            category=str(d.get("category", "")).strip(),
            favorite=bool(d.get("favorite", False)),
            group=str(d.get("group", "")).strip(),
            cover=str(d.get("cover", "")).strip(),
            scanned=bool(d.get("scanned", False)),
        )


@dataclass
class Group:
    id: str
    name: str
    color: str = "#64748b"
    parent: str = ""           # parent group id, "" = top level
    path: str = ""             # optional destination folder; when set, files can be dropped here
    scanned: bool = False      # True if a network scan created this group

    @staticmethod
    def from_dict(d: dict) -> "Group":
        return Group(
            id=str(d.get("id") or uuid.uuid4().hex),
            name=str(d.get("name", "")).strip(),
            color=str(d.get("color") or "#64748b"),
            parent=str(d.get("parent", "")).strip(),
            path=str(d.get("path", "")).strip(),
            scanned=bool(d.get("scanned", False)),
        )


def load_config():
    data = {}
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            data = {}
    mappings = []
    for m in data.get("mappings", []):
        mp = Mapping.from_dict(m)
        if mp.name and mp.path:
            mappings.append(mp)
    groups = []
    for g in data.get("groups", []):
        gp = Group.from_dict(g)
        if gp.name:
            groups.append(gp)
    # drop dangling group references
    valid = {g.id for g in groups}
    for m in mappings:
        if m.group and m.group not in valid:
            m.group = ""
    # sanitize group parents: dangling -> top level; break any cycles
    by_id = {g.id: g for g in groups}
    for g in groups:
        if g.parent and g.parent not in by_id:
            g.parent = ""
        if g.parent == g.id:
            g.parent = ""
    for g in groups:
        seen = set()
        cur = g
        steps = 0
        while cur.parent:
            if cur.parent in seen or steps > len(groups):
                cur.parent = ""        # cycle -> detach here
                break
            seen.add(cur.id)
            cur = by_id[cur.parent]
            steps += 1
    # deep copy: list-valued defaults (scan_roots, ignored_scan_paths, ...) must
    # never be the shared DEFAULT_SETTINGS objects, or appending to them would
    # silently change the defaults themselves
    settings = json.loads(json.dumps(DEFAULT_SETTINGS))
    stored = dict(data.get("settings", {}) or {})
    # migrate legacy "images_only" -> "media_only"
    if "media_only" not in stored and "images_only" in stored:
        stored["media_only"] = bool(stored.get("images_only"))
    stored.pop("images_only", None)
    settings.update(stored)
    return mappings, groups, settings


def save_config(mappings, groups, settings):
    data = {
        "mappings": [asdict(m) for m in mappings],
        "groups": [asdict(g) for g in groups],
        "settings": settings,
    }
    tmp = CONFIG_PATH + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
        os.replace(tmp, CONFIG_PATH)
    except Exception as e:
        print("Could not save config:", e)


# --------------------------------------------------------------------------- #
# Persistent activity log (JSON-lines, pruned to ~1 year)
# --------------------------------------------------------------------------- #
def _log_line(ts_iso, msg):
    return json.dumps({"ts": ts_iso, "msg": msg}, ensure_ascii=False)


def _rewrite_log(entries):
    try:
        tmp = LOG_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            for ts, msg in entries:
                f.write(_log_line(ts.isoformat(timespec="seconds"), msg) + "\n")
        os.replace(tmp, LOG_PATH)
    except Exception:
        pass


def load_log_entries():
    """Return [(datetime, msg)] within retention, pruning the file if needed."""
    if not os.path.exists(LOG_PATH):
        return []
    cutoff = datetime.now() - timedelta(days=LOG_RETENTION_DAYS)
    kept, pruned = [], False
    try:
        with open(LOG_PATH, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                    ts = datetime.fromisoformat(obj["ts"])
                    msg = str(obj.get("msg", ""))
                except Exception:
                    pruned = True
                    continue
                if ts >= cutoff:
                    kept.append((ts, msg))
                else:
                    pruned = True
    except Exception:
        return []
    if pruned:
        _rewrite_log(kept)
    return kept


def append_log_entry(ts, msg):
    try:
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(_log_line(ts.isoformat(timespec="seconds"), msg) + "\n")
    except Exception:
        pass


def clear_log_file():
    try:
        if os.path.exists(LOG_PATH):
            os.remove(LOG_PATH)
    except Exception:
        pass


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #
def is_image(path: str) -> bool:
    return os.path.splitext(path)[1].lower() in IMAGE_EXTS


def is_video(path: str) -> bool:
    return os.path.splitext(path)[1].lower() in VIDEO_EXTS


def is_audio(path: str) -> bool:
    return os.path.splitext(path)[1].lower() in AUDIO_EXTS


def is_media(path: str) -> bool:
    return os.path.splitext(path)[1].lower() in MEDIA_EXTS


def contrast_text(hex_color: str) -> str:
    c = QColor(hex_color)
    lum = 0.299 * c.red() + 0.587 * c.green() + 0.114 * c.blue()
    return "#0b0d12" if lum > 150 else "#ffffff"


def list_cover_candidates(folder: str):
    """Sorted basenames of decodable images directly inside `folder`."""
    out = []
    for name in os.listdir(folder):
        if os.path.splitext(name)[1].lower() in THUMB_EXTS:
            if os.path.isfile(os.path.join(folder, name)):
                out.append(name)
    out.sort(key=str.casefold)
    return out


def find_cover_candidates(folder: str):
    """Full paths of decodable images to pick a tile cover from.

    The folder's own images win. A folder holding only subfolders (e.g. "Trips"
    -> "Paris", "Rome") borrows from the images inside its subfolders, searched
    breadth-first within COVER_SCAN_DIRS / COVER_SCAN_DEPTH so a huge tree can't
    stall the worker. Raises OSError if `folder` itself can't be listed."""
    out = []
    queue = [(folder, 0)]
    opened = 0
    while queue and opened < COVER_SCAN_DIRS and len(out) < COVER_CAND_CAP:
        d, depth = queue.pop(0)
        opened += 1
        try:
            entries = list(os.scandir(d))
        except OSError:
            if d == folder:
                raise
            continue
        subs = []
        for e in entries:
            try:
                if e.is_file():
                    if os.path.splitext(e.name)[1].lower() in THUMB_EXTS:
                        out.append(e.path)
                elif e.is_dir(follow_symlinks=False):
                    if not e.name.startswith(".") and e.name.casefold() not in SCAN_SKIP_DIRS:
                        subs.append(e.path)
            except OSError:
                continue
        if d == folder and out:
            return out              # the folder has images of its own: use only those
        if depth < COVER_SCAN_DEPTH:
            random.shuffle(subs)    # so a capped search doesn't always favor A..., B...
            queue.extend((s, depth + 1) for s in subs)
    return out


def scaled_cover_image(path: str, w: int, h: int):
    """Load an image and center-crop it to w x h. Returns a QImage or None.
    Safe to call off the GUI thread (uses QImage, not QPixmap)."""
    img = QImage(path)
    if img.isNull():
        return None
    scaled = img.scaled(w, h, Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
    x = max(0, (scaled.width() - w) // 2)
    y = max(0, (scaled.height() - h) // 2)
    return scaled.copy(x, y, w, h)


def rounded_cover_pixmap(src: QPixmap, w: int, h: int, radius: int) -> QPixmap:
    """Return a rounded-corner pixmap of exactly w x h (GUI thread only)."""
    if src.width() != w or src.height() != h:
        src = src.scaled(w, h, Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
        x = max(0, (src.width() - w) // 2)
        y = max(0, (src.height() - h) // 2)
        src = src.copy(x, y, w, h)
    out = QPixmap(w, h)
    out.fill(Qt.transparent)
    p = QPainter(out)
    p.setRenderHint(QPainter.Antialiasing, True)
    path = QPainterPath()
    path.addRoundedRect(0, 0, w, h, radius, radius)
    p.setClipPath(path)
    p.drawPixmap(0, 0, src)
    p.end()
    return out


def _drag_badge(base: QPixmap, count: int) -> QPixmap:
    """Overlay a small count badge on a drag pixmap when dragging several tiles."""
    if count <= 1:
        return base
    out = QPixmap(base.size())
    out.fill(Qt.transparent)
    p = QPainter(out)
    p.setRenderHint(QPainter.Antialiasing, True)
    p.setOpacity(0.9)
    p.drawPixmap(0, 0, base)
    p.setOpacity(1.0)
    d = 26
    x = out.width() - d - 4
    y = 4
    p.setBrush(QColor("#2563eb"))
    p.setPen(QColor("#0e1116"))
    p.drawEllipse(x, y, d, d)
    f = QFont()
    f.setBold(True)
    f.setPointSize(11)
    p.setFont(f)
    p.setPen(QColor("#ffffff"))
    p.drawText(QRect(x, y, d, d), Qt.AlignCenter, str(count))
    p.end()
    return out


def extract_local_files(mime) -> list:
    """Pull dropped local file/dir paths out of a QMimeData."""
    out = []
    if mime is not None and mime.hasUrls():
        for url in mime.urls():
            p = url.toLocalFile()
            if p:
                out.append(os.path.normpath(p))
    return out


def _tcp_open(host: str, port: int, timeout: float) -> bool:
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True
    except Exception:
        return False


def _unc_host(path: str):
    p = path.replace("/", "\\")
    if p.startswith("\\\\"):
        parts = p.lstrip("\\").split("\\")
        if parts and parts[0]:
            return parts[0]
    return None


def is_path_reachable(path: str, timeout: float = 3.0) -> bool:
    """
    True if the folder exists and is reachable, without hanging the caller for
    long. UNC paths get a fast TCP pre-check on the SMB port so a dead NAS fails
    quickly. The os.path.isdir() call is run in a side thread bounded by timeout.
    """
    if not path:
        return False
    host = _unc_host(path)
    if host and not _tcp_open(host, 445, min(timeout, 2.0)):
        return False

    result = {"ok": None}

    def _check():
        try:
            result["ok"] = os.path.isdir(path)
        except Exception:
            result["ok"] = False

    t = threading.Thread(target=_check, daemon=True)
    t.start()
    t.join(timeout)
    if t.is_alive():
        return False  # took too long -> treat as not reachable
    return bool(result["ok"])


def _norm_path(path: str) -> str:
    """Case- and separator-normalized path, used only to compare/dedupe locations."""
    return os.path.normcase(os.path.normpath(path or ""))


# Folder names a network scan skips outright (junk/system, never real content).
SCAN_SKIP_DIRS = {
    "$recycle.bin", "system volume information", "@eadir", "@eadir2",
    ".trash-1000", "lost+found", ".git", ".svn", "__pycache__",
    "$recycle bin", "recycler",
}
SCAN_FOLDER_CAP = 4000   # safety net: stop walking a single root past this many folders


def resolve_destination(folder: str, filename: str, collision: str):
    """
    Decide the final path for a file landing in `folder`.
    Returns a path string, or None meaning "skip this file".
    """
    target = os.path.join(folder, filename)
    if not os.path.exists(target):
        return target
    if collision == "overwrite":
        return target
    if collision == "skip":
        return None
    base, ext = os.path.splitext(filename)
    i = 1
    while True:
        cand = os.path.join(folder, f"{base} ({i}){ext}")
        if not os.path.exists(cand):
            return cand
        i += 1


def human_bytes(n: int) -> str:
    n = float(max(0, n))
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return (f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}")
        n /= 1024
    return f"{n:.1f} TB"


def _copy_chunked(src, dst, size, progress_cb, chunk=1024 * 1024):
    copied = 0
    with open(src, "rb") as fsrc, open(dst, "wb") as fdst:
        while True:
            buf = fsrc.read(chunk)
            if not buf:
                break
            fdst.write(buf)
            copied += len(buf)
            if progress_cb:
                progress_cb(copied, size)
    try:
        shutil.copystat(src, dst)
    except OSError:
        pass


def transfer_one(src, dst, mode, progress_cb=None):
    """Move or copy a single file, reporting byte progress for big files.
    progress_cb(copied_bytes, total_bytes) is called as the file is written."""
    try:
        size = os.path.getsize(src)
    except OSError:
        size = 0
    if progress_cb:
        progress_cb(0, size)
    if mode == "move":
        try:
            os.replace(src, dst)          # same-volume: atomic + instant
            if progress_cb:
                progress_cb(size, size)
            return
        except OSError:
            pass                          # cross-volume: fall back to copy+remove
    if size >= BIG_FILE_BYTES:
        _copy_chunked(src, dst, size, progress_cb)
    else:
        shutil.copyfile(src, dst)
        try:
            shutil.copystat(src, dst)
        except OSError:
            pass
        if progress_cb:
            progress_cb(size, size)
    if mode == "move":
        os.remove(src)


def path_size(p) -> int:
    """Total bytes of a file, or of an entire directory tree."""
    try:
        if os.path.isdir(p):
            total = 0
            for root, _dirs, files in os.walk(p):
                for f in files:
                    try:
                        total += os.path.getsize(os.path.join(root, f))
                    except OSError:
                        pass
            return total
        return os.path.getsize(p)
    except OSError:
        return 0


def resolve_destination_dir(folder: str, name: str, collision: str):
    """Decide the final path for a dropped folder landing in `folder`.
    Returns a path, or None meaning "skip"."""
    target = os.path.join(folder, name)
    if not os.path.exists(target):
        return target
    if collision == "skip":
        return None
    if collision == "overwrite":
        try:
            if os.path.isdir(target):
                shutil.rmtree(target)
            else:
                os.remove(target)
        except OSError:
            pass
        return target
    i = 1
    while True:
        cand = os.path.join(folder, f"{name} ({i})")
        if not os.path.exists(cand):
            return cand
        i += 1


def transfer_dir(src, dst, mode, progress_cb=None):
    """Move or copy an entire folder tree (all files + subfolders) into dst.
    progress_cb(copied_bytes, total_bytes) reports cumulative progress."""
    total = path_size(src)
    state = {"copied": 0}
    if progress_cb:
        progress_cb(0, total)
    if mode == "move":
        try:
            os.rename(src, dst)          # same volume: instant tree move
            if progress_cb:
                progress_cb(total, total)
            return
        except OSError:
            pass                         # cross-volume: copy the tree, then remove

    def _copyfile(s, d, follow_symlinks=True):
        try:
            sz = os.path.getsize(s)
        except OSError:
            sz = 0
        if sz >= BIG_FILE_BYTES:
            with open(s, "rb") as fs, open(d, "wb") as fd:
                while True:
                    buf = fs.read(1024 * 1024)
                    if not buf:
                        break
                    fd.write(buf)
                    state["copied"] += len(buf)
                    if progress_cb:
                        progress_cb(state["copied"], total)
        else:
            shutil.copyfile(s, d)
            state["copied"] += sz
            if progress_cb:
                progress_cb(state["copied"], total)
        try:
            shutil.copystat(s, d)
        except OSError:
            pass
        return d

    try:
        shutil.copytree(src, dst, copy_function=_copyfile)
    except Exception:
        shutil.rmtree(dst, ignore_errors=True)   # clean a partial copy
        raise
    if progress_cb:
        progress_cb(total, total)
    if mode == "move":
        shutil.rmtree(src, ignore_errors=True)


# --------------------------------------------------------------------------- #
# Flow layout (wraps tiles to available width)
# --------------------------------------------------------------------------- #
class FlowLayout(QLayout):
    def __init__(self, parent=None, margin=0, spacing=14):
        super().__init__(parent)
        if parent is not None:
            self.setContentsMargins(margin, margin, margin, margin)
        self.setSpacing(spacing)
        self._items = []

    def addItem(self, item):
        self._items.append(item)

    def count(self):
        return len(self._items)

    def itemAt(self, index):
        if 0 <= index < len(self._items):
            return self._items[index]
        return None

    def takeAt(self, index):
        if 0 <= index < len(self._items):
            return self._items.pop(index)
        return None

    def hasHeightForWidth(self):
        return True

    def heightForWidth(self, width):
        return self._layout(QRect(0, 0, width, 0), apply=False)

    def setGeometry(self, rect):
        super().setGeometry(rect)
        self._layout(rect, apply=True)

    def sizeHint(self):
        return self.minimumSize()

    def minimumSize(self):
        size = QSize()
        for item in self._items:
            size = size.expandedTo(item.minimumSize())
        m = self.contentsMargins()
        size += QSize(m.left() + m.right(), m.top() + m.bottom())
        return size

    def _layout(self, rect, apply):
        m = self.contentsMargins()
        x = rect.x() + m.left()
        y = rect.y() + m.top()
        right = rect.right() - m.right()
        line_h = 0
        sp = self.spacing()
        for item in self._items:
            w = item.sizeHint().width()
            h = item.sizeHint().height()
            if x + w > right and line_h > 0:
                x = rect.x() + m.left()
                y = y + line_h + sp
                line_h = 0
            if apply:
                item.setGeometry(QRect(QPoint(x, y), QSize(w, h)))
            x = x + w + sp
            line_h = max(line_h, h)
        return (y + line_h) - rect.y() + m.bottom()


# --------------------------------------------------------------------------- #
# A destination tile
# --------------------------------------------------------------------------- #
class DropTile(QFrame):
    filesDropped = Signal(object, list)   # (Mapping, [paths])
    clicked = Signal(object)              # Mapping (plain click -> set active)
    ctrlClicked = Signal(object)          # Mapping (ctrl+click -> toggle select)
    editRequested = Signal(object)
    removeRequested = Signal(object)
    recolorRequested = Signal(object)
    openRequested = Signal(object)
    copyPathRequested = Signal(object)
    moveRequested = Signal(object, int)   # (Mapping, direction -1/+1)
    favoriteToggled = Signal(object)
    removeFromGroupRequested = Signal(object)
    removeFromAllGroupsRequested = Signal(object)
    addToGroupRequested = Signal(object, str)   # (Mapping, group id)
    newGroupForRequested = Signal(object)
    refreshCoverRequested = Signal(object)
    foldersDroppedOnFolder = Signal(list, object)   # (dragged folder ids, target Mapping)

    def __init__(self, mapping: Mapping):
        super().__init__()
        self.mapping = mapping
        self.reachable = None     # None unknown / True / False
        self.active = False
        self.selected = False
        self._hover_drag = False
        self._has_cover = False
        self.cover_path = ""          # full path of the image currently shown
        self._press_pos = None
        self._press_ctrl = False
        self.drag_ids_provider = None   # callable(mid) -> [ids], set by the window
        self.available_groups = []   # set by the window before refresh

        self.setObjectName("tile")
        self.setFixedSize(TILE_W, TILE_H)
        self.setAcceptDrops(True)
        self.setCursor(Qt.PointingHandCursor)
        self.setContextMenuPolicy(Qt.CustomContextMenu)
        self.customContextMenuRequested.connect(self._show_menu)

        root = QVBoxLayout(self)
        root.setContentsMargins(10, 8, 10, 8)
        root.setSpacing(4)

        # top row: star (pin) on the left, red minus (remove from group) on right
        top = QHBoxLayout()
        top.setContentsMargins(0, 0, 0, 0)
        top.setSpacing(0)
        self.star_btn = QPushButton("\u2606")
        self.star_btn.setObjectName("starBtn")
        self.star_btn.setFixedSize(22, 20)
        self.star_btn.setCursor(Qt.PointingHandCursor)
        self.star_btn.clicked.connect(lambda: self.favoriteToggled.emit(self.mapping))
        top.addWidget(self.star_btn, 0)
        top.addStretch(1)
        self.minus_btn = QPushButton("\u2212")
        self.minus_btn.setObjectName("minusBtn")
        self.minus_btn.setFixedSize(22, 20)
        self.minus_btn.setCursor(Qt.PointingHandCursor)
        self.minus_btn.setToolTip("Remove from group")
        self.minus_btn.setStyleSheet(
            "border:none;background:transparent;padding:0;"
            "color:#ef4444;font-weight:bold;font-size:16px;")
        self.minus_btn.clicked.connect(
            lambda: self.removeFromGroupRequested.emit(self.mapping))
        top.addWidget(self.minus_btn, 0)
        root.addLayout(top)

        self.cover_lbl = QLabel()
        self.cover_lbl.setFixedSize(COVER_W, COVER_H)
        self.cover_lbl.setAlignment(Qt.AlignCenter)
        self.cover_lbl.setScaledContents(False)
        root.addWidget(self.cover_lbl, 0, Qt.AlignHCenter)

        self.name_lbl = QLabel()
        self.name_lbl.setAlignment(Qt.AlignHCenter)
        self.name_lbl.setObjectName("tileName")
        root.addWidget(self.name_lbl)

        bottom = QHBoxLayout()
        bottom.setContentsMargins(0, 0, 0, 0)
        self.cat_lbl = QLabel()
        self.cat_lbl.setObjectName("tileCat")
        bottom.addWidget(self.cat_lbl, 1)
        self.dot = QLabel()
        self.dot.setFixedSize(11, 11)
        bottom.addWidget(self.dot, 0, Qt.AlignVCenter)
        root.addLayout(bottom)

        self.refresh()

    # ---- visuals ----
    def refresh(self):
        name = self.mapping.name or "(unnamed)"
        fm = QFontMetrics(self.name_lbl.font())
        self.name_lbl.setText(fm.elidedText(name, Qt.ElideRight, TILE_W - 22))
        self.cat_lbl.setText(self.mapping.category or "")
        self.setToolTip(f"{name}\n{self.mapping.path}")
        if not self._has_cover:
            self._render_letter()
        # star reflects favorite state
        if self.mapping.favorite:
            self.star_btn.setText("\u2605")
            self.star_btn.setStyleSheet(
                "border:none;background:transparent;padding:0;"
                "color:#fbbf24;font-size:16px;")
            self.star_btn.setToolTip("Pinned to front \u2014 click to unpin")
        else:
            self.star_btn.setText("\u2606")
            self.star_btn.setStyleSheet(
                "border:none;background:transparent;padding:0;"
                "color:#8b95a3;font-size:16px;")
            self.star_btn.setToolTip("Pin to front")
        self.minus_btn.setVisible(bool(self.mapping.group))
        self._apply_dot()
        self._apply_border()

    def _render_letter(self):
        """Fallback cover: a colored panel with the folder's initial."""
        name = self.mapping.name or "(unnamed)"
        initial = next((ch for ch in name if ch.isalnum()), "?").upper()
        fg = contrast_text(self.mapping.color)
        f = QFont()
        f.setPointSize(26)
        f.setBold(True)
        self.cover_lbl.setFont(f)
        self.cover_lbl.setPixmap(QPixmap())   # clear any image
        self.cover_lbl.setText(initial)
        self.cover_lbl.setStyleSheet(
            f"background:{self.mapping.color}; color:{fg};"
            f"border-radius:{COVER_RADIUS}px;"
        )

    def set_cover(self, pixmap: QPixmap, path=""):
        self._has_cover = True
        self.cover_path = path
        self.cover_lbl.setText("")
        self.cover_lbl.setStyleSheet("background:transparent;")
        self.cover_lbl.setPixmap(pixmap)

    def clear_cover(self):
        self._has_cover = False
        self.cover_path = ""
        self._render_letter()

    def _apply_dot(self):
        if self.reachable is True:
            color, tip = "#22c55e", "Reachable"
        elif self.reachable is False:
            color, tip = "#ef4444", "Not reachable"
        else:
            color, tip = "#6b7280", "Checking..."
        self.dot.setStyleSheet(f"background:{color}; border-radius:5px;")
        self.dot.setToolTip(tip)

    def _apply_border(self):
        if self._hover_drag:
            border, bw = "#f59e0b", 2
        elif self.selected:
            border, bw = "#38bdf8", 2
        elif self.active:
            border, bw = "#fbbf24", 2
        else:
            border, bw = "#2a2f3a", 1
        if self._hover_drag:
            bg = "#222a39"
        elif self.selected:
            bg = "#16263a"
        else:
            bg = "#1b1f27"
        self.setStyleSheet(
            f"QFrame#tile{{background:{bg};border:{bw}px solid {border};"
            f"border-radius:14px;}}"
        )

    def set_reachable(self, value):
        self.reachable = value
        self._apply_dot()

    def set_active(self, value):
        self.active = value
        self._apply_border()

    def set_selected(self, value):
        self.selected = value
        self._apply_border()

    # ---- events ----
    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._press_pos = e.position().toPoint()
            self._press_ctrl = bool(e.modifiers() & Qt.ControlModifier)
            if self._press_ctrl:
                self.ctrlClicked.emit(self.mapping)   # toggle selection now
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if ((e.buttons() & Qt.LeftButton) and self._press_pos is not None
                and not self._press_ctrl):
            moved = (e.position().toPoint() - self._press_pos).manhattanLength()
            if moved >= QApplication.startDragDistance():
                ids = []
                if self.drag_ids_provider:
                    ids = self.drag_ids_provider(self.mapping.id)
                if not ids:
                    ids = [self.mapping.id]
                drag = QDrag(self)
                mime = QMimeData()
                mime.setData(FOLDER_MIME, ",".join(ids).encode("utf-8"))
                drag.setMimeData(mime)
                drag.setPixmap(_drag_badge(self.grab(), len(ids)))
                drag.setHotSpot(e.position().toPoint())
                self._press_pos = None
                drag.exec(Qt.MoveAction)
                return
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        if (e.button() == Qt.LeftButton and self._press_pos is not None
                and not self._press_ctrl):
            self.clicked.emit(self.mapping)   # plain click (no drag) -> set active
        self._press_pos = None
        super().mouseReleaseEvent(e)

    def _accepts_folder_drop(self, md):
        ids = decode_folder_ids(md)
        return bool(ids) and self.mapping.id not in ids

    def dragEnterEvent(self, e):
        md = e.mimeData()
        if md.hasUrls() or self._accepts_folder_drop(md):
            e.acceptProposedAction()
            self._hover_drag = True
            self._apply_border()
        else:
            e.ignore()

    def dragMoveEvent(self, e):
        md = e.mimeData()
        if md.hasUrls() or self._accepts_folder_drop(md):
            e.acceptProposedAction()
        else:
            e.ignore()

    def dragLeaveEvent(self, e):
        self._hover_drag = False
        self._apply_border()

    def dropEvent(self, e):
        self._hover_drag = False
        self._apply_border()
        md = e.mimeData()
        if md.hasUrls():
            paths = extract_local_files(md)
            if paths:
                e.acceptProposedAction()
                self.filesDropped.emit(self.mapping, paths)
            return
        ids = decode_folder_ids(md)
        if ids and self.mapping.id not in ids:
            e.acceptProposedAction()
            self.foldersDroppedOnFolder.emit(ids, self.mapping)
            return
        e.ignore()

    def _show_menu(self, pos):
        menu = QMenu(self)
        menu.addAction("Open folder", lambda: self.openRequested.emit(self.mapping))
        menu.addAction("Set as active target", lambda: self.clicked.emit(self.mapping))
        fav_label = "Unpin from front" if self.mapping.favorite else "Pin to front"
        menu.addAction(fav_label, lambda: self.favoriteToggled.emit(self.mapping))
        menu.addSeparator()
        gmenu = menu.addMenu("Add to group")
        gmenu.addAction("New group\u2026",
                        lambda: self.newGroupForRequested.emit(self.mapping))
        others = [g for g in self.available_groups if g.id != self.mapping.group]
        if others:
            gmenu.addSeparator()
            for g in others:
                gmenu.addAction(
                    g.name,
                    lambda checked=False, gid=g.id:
                        self.addToGroupRequested.emit(self.mapping, gid))
        if self.mapping.group:
            nested = any(g.id == self.mapping.group and g.parent
                         for g in self.available_groups)
            if nested:
                menu.addAction(
                    "Remove from group (up one level)",
                    lambda: self.removeFromGroupRequested.emit(self.mapping))
                menu.addAction(
                    "Remove from all groups (to top)",
                    lambda: self.removeFromAllGroupsRequested.emit(self.mapping))
            else:
                menu.addAction(
                    "Remove from group",
                    lambda: self.removeFromGroupRequested.emit(self.mapping))
        menu.addSeparator()
        menu.addAction("Edit...", lambda: self.editRequested.emit(self.mapping))
        menu.addAction("Change color...", lambda: self.recolorRequested.emit(self.mapping))
        menu.addAction("Refresh cover image",
                       lambda: self.refreshCoverRequested.emit(self.mapping))
        menu.addAction("Copy path", lambda: self.copyPathRequested.emit(self.mapping))
        menu.addSeparator()
        menu.addAction("Move left", lambda: self.moveRequested.emit(self.mapping, -1))
        menu.addAction("Move right", lambda: self.moveRequested.emit(self.mapping, +1))
        menu.addSeparator()
        menu.addAction("Remove", lambda: self.removeRequested.emit(self.mapping))
        menu.exec(self.mapToGlobal(pos))


# --------------------------------------------------------------------------- #
# A group tile (double-click to open)
# --------------------------------------------------------------------------- #
class GroupTile(QFrame):
    enterRequested = Signal(object)
    renameRequested = Signal(object)
    recolorRequested = Signal(object)
    ungroupRequested = Signal(object)
    deleteRequested = Signal(object)
    newSubgroupRequested = Signal(object)
    moveUpRequested = Signal(object)
    moveTopRequested = Signal(object)
    reparentRequested = Signal(str, str)    # source group id, target (new parent) id
    foldersDroppedOnGroup = Signal(list, object)   # (dragged folder ids, this Group)
    filesDroppedOnGroup = Signal(object, list)     # (Group, [file paths]) - OS file drop
    ctrlClicked = Signal(object)            # Group (ctrl+click -> toggle select)
    clicked = Signal(object)                # Group (plain click, debounced vs double-click)

    def __init__(self, group: "Group"):
        super().__init__()
        self.group = group
        self.can_nest = True       # set by the window before refresh
        self.has_parent = False
        self.validate_drop = None  # callable(src_gid, dst_gid) -> bool, set by window
        self.selected = False
        self._press_pos = None
        self._press_ctrl = False
        self._drop_hover = False
        self._has_cover = False
        self.cover_path = ""
        self._click_timer = QTimer(self)
        self._click_timer.setSingleShot(True)
        self._click_timer.timeout.connect(self._fire_pending_click)
        self.setObjectName("groupTile")
        self.setFixedSize(TILE_W, TILE_H)
        self.setCursor(Qt.PointingHandCursor)
        self.setAcceptDrops(True)
        self.setContextMenuPolicy(Qt.CustomContextMenu)
        self.customContextMenuRequested.connect(self._menu)

        root = QVBoxLayout(self)
        root.setContentsMargins(10, 8, 10, 8)
        root.setSpacing(4)

        top = QHBoxLayout()
        top.setContentsMargins(0, 0, 0, 0)
        tag = QLabel("GROUP")
        tag.setObjectName("groupTag")
        top.addWidget(tag, 0)
        top.addStretch(1)
        self.count_lbl = QLabel("0")
        self.count_lbl.setObjectName("groupCount")
        top.addWidget(self.count_lbl, 0)
        root.addLayout(top)

        # cover banner: a random image from inside the group's folder, with the
        # colored-initial panel as the fallback (same look as folder tiles)
        self.icon = QLabel()
        self.icon.setFixedSize(COVER_W, COVER_H)
        self.icon.setAlignment(Qt.AlignCenter)
        f = QFont()
        f.setPointSize(24)
        f.setBold(True)
        self.icon.setFont(f)
        root.addWidget(self.icon, 0, Qt.AlignHCenter)

        self.name_lbl = QLabel()
        self.name_lbl.setObjectName("tileName")
        self.name_lbl.setAlignment(Qt.AlignHCenter)
        root.addWidget(self.name_lbl)

        self.hint = QLabel("click to open \u00b7 drag to move")
        self.hint.setObjectName("tileCat")
        self.hint.setAlignment(Qt.AlignHCenter)
        root.addWidget(self.hint)

        self.refresh()

    def set_count(self, n):
        self.count_lbl.setText(str(n))

    def _render_letter(self):
        name = self.group.name or "(group)"
        initial = next((ch for ch in name if ch.isalnum()), "?").upper()
        fg = contrast_text(self.group.color)
        self.icon.setPixmap(QPixmap())
        self.icon.setText(initial)
        self.icon.setStyleSheet(
            f"background:{self.group.color}; color:{fg}; border-radius:{COVER_RADIUS}px;"
        )

    def set_cover(self, pixmap: QPixmap, path=""):
        self._has_cover = True
        self.cover_path = path
        self.icon.setText("")
        self.icon.setStyleSheet("background:transparent;")
        self.icon.setPixmap(pixmap)

    def clear_cover(self):
        self._has_cover = False
        self.cover_path = ""
        self._render_letter()

    def refresh(self):
        name = self.group.name or "(group)"
        if not self._has_cover:
            self._render_letter()
        fm = QFontMetrics(self.name_lbl.font())
        self.name_lbl.setText(fm.elidedText(name, Qt.ElideRight, TILE_W - 22))
        if self.group.path:
            # short enough to fit the tile; the tooltip spells out click vs double-click
            self.hint.setText("double-click to browse")
            self.setToolTip(f"Group: {name}\n{self.group.path}\n"
                            f"Click to open the folder \u00b7 double-click to browse "
                            f"its contents here \u00b7 drop files to file them here")
        else:
            self.hint.setText("click to open")
            self.setToolTip(f"Group: {name}\nClick to open \u00b7 "
                            f"set a path in the right-click menu to accept files")
        self._apply_style()

    def _apply_style(self):
        if self._drop_hover:
            self.setStyleSheet(
                "QFrame#groupTile{background:#202a3a;border:2px dashed #f59e0b;"
                "border-radius:14px;}")
        elif self.selected:
            self.setStyleSheet(
                "QFrame#groupTile{background:#16263a;border:2px solid #38bdf8;"
                "border-radius:14px;}")
        else:
            self.setStyleSheet(
                f"QFrame#groupTile{{background:#171c26;"
                f"border:2px solid {self.group.color};border-radius:14px;}}")

    def _set_drop_hover(self, on):
        if on != self._drop_hover:
            self._drop_hover = on
            self._apply_style()

    def set_selected(self, value):
        self.selected = value
        self._apply_style()

    def mouseDoubleClickEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._click_timer.stop()   # a real double-click cancels the pending single-click
            self.enterRequested.emit(self.group)

    def _fire_pending_click(self):
        self.clicked.emit(self.group)

    # ---- drag source (move this group) ----
    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._press_pos = e.position().toPoint()
            self._press_ctrl = bool(e.modifiers() & Qt.ControlModifier)
            if self._press_ctrl:
                self.ctrlClicked.emit(self.group)   # toggle selection now
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if ((e.buttons() & Qt.LeftButton) and self._press_pos is not None
                and not self._press_ctrl):
            moved = (e.position().toPoint() - self._press_pos).manhattanLength()
            if moved >= QApplication.startDragDistance():
                drag = QDrag(self)
                mime = QMimeData()
                mime.setData(GROUP_MIME, self.group.id.encode("utf-8"))
                drag.setMimeData(mime)
                pm = self.grab()
                drag.setPixmap(pm)
                drag.setHotSpot(e.position().toPoint())
                self._press_pos = None
                drag.exec(Qt.MoveAction)
                return
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        if (e.button() == Qt.LeftButton and self._press_pos is not None
                and not self._press_ctrl):
            # Debounce: wait out the double-click interval before treating this
            # as a plain click, so a real double-click doesn't also open the
            # real folder on its first release.
            self._click_timer.start(QApplication.doubleClickInterval())
        self._press_pos = None
        super().mouseReleaseEvent(e)

    # ---- drop target (accept a group OR folders dropped onto this one) ----
    def _dragged_group(self, e):
        md = e.mimeData()
        if md.hasFormat(GROUP_MIME):
            return bytes(md.data(GROUP_MIME)).decode("utf-8")
        return None

    def _group_ok(self, src):
        return bool(src) and src != self.group.id and (
            self.validate_drop is None or self.validate_drop(src, self.group.id))

    def _folders_ok(self, e):
        return bool(decode_folder_ids(e.mimeData()))

    def _accepts_any(self, e):
        md = e.mimeData()
        return (self._group_ok(self._dragged_group(e))
                or self._folders_ok(e)
                or md.hasUrls())

    def dragEnterEvent(self, e):
        if self._accepts_any(e):
            e.acceptProposedAction()
            self._set_drop_hover(True)
        else:
            e.ignore()

    def dragMoveEvent(self, e):
        if self._accepts_any(e):
            e.acceptProposedAction()
        else:
            e.ignore()

    def dragLeaveEvent(self, e):
        self._set_drop_hover(False)

    def dropEvent(self, e):
        self._set_drop_hover(False)
        md = e.mimeData()
        src = self._dragged_group(e)
        if self._group_ok(src):
            e.acceptProposedAction()
            self.reparentRequested.emit(src, self.group.id)
            return
        ids = decode_folder_ids(md)
        if ids:
            e.acceptProposedAction()
            self.foldersDroppedOnGroup.emit(ids, self.group)
            return
        if md.hasUrls():
            paths = extract_local_files(md)
            if paths:
                e.acceptProposedAction()
                self.filesDroppedOnGroup.emit(self.group, paths)
                return
        e.ignore()

    setPathRequested = Signal(object)
    openPathRequested = Signal(object)

    def _menu(self, pos):
        menu = QMenu(self)
        menu.addAction("Open group", lambda: self.enterRequested.emit(self.group))
        if self.group.path:
            menu.addAction("Open destination folder",
                           lambda: self.openPathRequested.emit(self.group))
        sub = menu.addAction("New subgroup\u2026",
                             lambda: self.newSubgroupRequested.emit(self.group))
        sub.setEnabled(self.can_nest)
        if not self.can_nest:
            sub.setToolTip("Maximum nesting depth reached")
        menu.addSeparator()
        path_label = ("Change folder path\u2026" if self.group.path
                      else "Set folder path\u2026 (to accept file drops)")
        menu.addAction(path_label,
                       lambda: self.setPathRequested.emit(self.group))
        menu.addAction("Rename\u2026", lambda: self.renameRequested.emit(self.group))
        menu.addAction("Change color\u2026", lambda: self.recolorRequested.emit(self.group))
        if self.has_parent:
            menu.addSeparator()
            menu.addAction("Move up one level",
                           lambda: self.moveUpRequested.emit(self.group))
            menu.addAction("Move to top level",
                           lambda: self.moveTopRequested.emit(self.group))
        menu.addSeparator()
        menu.addAction("Ungroup (keep contents, move up a level)",
                       lambda: self.ungroupRequested.emit(self.group))
        menu.addAction("Remove group (delete it and everything inside)\u2026",
                       lambda: self.deleteRequested.emit(self.group))
        menu.exec(self.mapToGlobal(pos))


# --------------------------------------------------------------------------- #
# A button that also accepts a dragged group (for un-nesting via drag-and-drop)
# --------------------------------------------------------------------------- #
class GroupDropButton(QPushButton):
    groupDropped = Signal(str)     # the dragged group's id
    foldersDropped = Signal(list)  # dragged folder ids

    def __init__(self, text):
        super().__init__(text)
        self.setAcceptDrops(True)

    def _gid(self, e):
        md = e.mimeData()
        if md.hasFormat(GROUP_MIME):
            return bytes(md.data(GROUP_MIME)).decode("utf-8")
        return None

    def _accepts(self, e):
        return bool(self._gid(e)) or bool(decode_folder_ids(e.mimeData()))

    def dragEnterEvent(self, e):
        if self._accepts(e):
            e.acceptProposedAction()
        else:
            e.ignore()

    def dragMoveEvent(self, e):
        if self._accepts(e):
            e.acceptProposedAction()
        else:
            e.ignore()

    def dropEvent(self, e):
        gid = self._gid(e)
        if gid:
            e.acceptProposedAction()
            self.groupDropped.emit(gid)
            return
        ids = decode_folder_ids(e.mimeData())
        if ids:
            e.acceptProposedAction()
            self.foldersDropped.emit(ids)
            return
        e.ignore()


# --------------------------------------------------------------------------- #
# Big active-target drop zone
# --------------------------------------------------------------------------- #
class ActiveZone(QFrame):
    filesDropped = Signal(list)
    prevClicked = Signal()
    nextClicked = Signal()

    def __init__(self):
        super().__init__()
        self.setObjectName("activeZone")
        self.setAcceptDrops(True)
        self.setMinimumHeight(110)
        self._hover = False
        self._mapping = None

        root = QVBoxLayout(self)
        root.setContentsMargins(16, 12, 16, 14)
        root.setSpacing(6)

        header = QHBoxLayout()
        self.prev_btn = QPushButton("\u25c0")
        self.next_btn = QPushButton("\u25b6")
        for b in (self.prev_btn, self.next_btn):
            b.setObjectName("cycleBtn")
            b.setFixedWidth(38)
        self.prev_btn.clicked.connect(self.prevClicked.emit)
        self.next_btn.clicked.connect(self.nextClicked.emit)

        self.title = QLabel("No target selected")
        self.title.setObjectName("activeTitle")
        self.title.setAlignment(Qt.AlignCenter)

        header.addWidget(self.prev_btn, 0)
        header.addWidget(self.title, 1)
        header.addWidget(self.next_btn, 0)
        root.addLayout(header)

        self.hint = QLabel("Drag files here to file them into the active target")
        self.hint.setObjectName("activeHint")
        self.hint.setAlignment(Qt.AlignCenter)
        root.addWidget(self.hint, 1)

        self._apply_style()

    def set_mapping(self, mapping):
        self._mapping = mapping
        if mapping:
            self.title.setText(f"Active target:  {mapping.name}")
            self.hint.setText(f"Drop files here  \u2192  {mapping.path}")
        else:
            self.title.setText("No target selected")
            self.hint.setText("Add a folder, then pick it here to start filing")
        self._apply_style()

    def _apply_style(self):
        border = "#f59e0b" if self._hover else "#3a4250"
        bg = "#202a3a" if self._hover else "#161a22"
        self.setStyleSheet(
            f"QFrame#activeZone{{background:{bg};border:2px dashed {border};"
            f"border-radius:16px;}}"
        )

    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()
            self._hover = True
            self._apply_style()

    def dragMoveEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()

    def dragLeaveEvent(self, e):
        self._hover = False
        self._apply_style()

    def dropEvent(self, e):
        self._hover = False
        self._apply_style()
        paths = extract_local_files(e.mimeData())
        if paths:
            e.acceptProposedAction()
            self.filesDropped.emit(paths)


# --------------------------------------------------------------------------- #
# Background transfer worker (move / copy / undo), serialized via a queue
# --------------------------------------------------------------------------- #
class TransferSignals(QObject):
    started = Signal(str, int, int)         # target name, total files, total bytes
    progress = Signal(int, int, str)        # done, total, current name
    fileProgress = Signal(str, int, int)    # current name, copied bytes, total bytes
    log = Signal(str)
    batchDone = Signal(dict)                # summary + undo records


class TransferManager(QThread):
    def __init__(self):
        super().__init__()
        self.signals = TransferSignals()
        self._queue = Queue()
        self._stop = False

    def enqueue(self, batch: dict):
        self._queue.put(batch)

    def stop(self):
        self._stop = True
        self._queue.put(None)

    def run(self):
        while not self._stop:
            batch = self._queue.get()
            if batch is None:
                break
            try:
                self._process(batch)
            except Exception as e:  # never let the worker die
                self.signals.log.emit(f"Unexpected error: {e}")

    def _process(self, batch):
        kind = batch.get("kind", "transfer")
        if kind == "undo":
            self._process_undo(batch)
            return

        files = batch["files"]
        dest = batch["dest"]
        mode = batch["mode"]
        collision = batch["collision"]
        name = batch["name"]
        total = len(files)
        total_bytes = 0
        for s in files:
            total_bytes += path_size(s)
        self.signals.started.emit(name, total, total_bytes)
        ok = 0
        skipped = 0
        errors = []
        undo = []

        for i, src in enumerate(files, start=1):
            is_dir = os.path.isdir(src)
            base = os.path.basename(src.rstrip("\\/")) or src
            self.signals.progress.emit(i - 1, total, base)
            final = None
            try:
                cb = (lambda copied, tot, _b=base:
                      self.signals.fileProgress.emit(_b, copied, tot))
                if is_dir:
                    final = resolve_destination_dir(dest, base, collision)
                    if final is None:
                        skipped += 1
                        self.signals.log.emit(f"Skipped (folder exists): {base}")
                        continue
                    transfer_dir(src, final, mode, cb)
                    undo.append({"mode": mode, "src": src, "dest": final, "is_dir": True})
                else:
                    final = resolve_destination(dest, base, collision)
                    if final is None:
                        skipped += 1
                        self.signals.log.emit(f"Skipped (already exists): {base}")
                        continue
                    if os.path.exists(final):       # overwrite mode
                        os.remove(final)
                    transfer_one(src, final, mode, cb)
                    undo.append({"mode": mode, "src": src, "dest": final})
                ok += 1
            except Exception as e:
                errors.append((base, str(e)))
                # best-effort: clean a partial copy we created
                try:
                    if final and mode == "copy" and os.path.exists(final):
                        if os.path.isdir(final):
                            shutil.rmtree(final, ignore_errors=True)
                        else:
                            os.remove(final)
                except Exception:
                    pass
                self.signals.log.emit(f"FAILED {base}: {e}")

        self.signals.progress.emit(total, total, "")
        self.signals.batchDone.emit({
            "name": name, "mode": mode, "total": total,
            "ok": ok, "skipped": skipped, "errors": errors, "undo": undo,
            "files": list(files),
        })

    def _process_undo(self, batch):
        records = batch["records"]
        total = len(records)
        total_bytes = 0
        for rec in records:
            total_bytes += path_size(rec["dest"])
        self.signals.started.emit(batch.get("name", "Undo"), total, total_bytes)
        restored = 0
        errors = []
        for i, rec in enumerate(reversed(records), start=1):
            base = os.path.basename(rec["dest"].rstrip("\\/")) or rec["dest"]
            is_dir = rec.get("is_dir", False)
            self.signals.progress.emit(i - 1, total, base)
            try:
                if rec["mode"] == "move":
                    os.makedirs(os.path.dirname(rec["src"]), exist_ok=True)
                    if os.path.exists(rec["dest"]):
                        cb = (lambda copied, tot, _b=base:
                              self.signals.fileProgress.emit(_b, copied, tot))
                        if is_dir:
                            transfer_dir(rec["dest"], rec["src"], "move", cb)
                        else:
                            transfer_one(rec["dest"], rec["src"], "move", cb)
                        restored += 1
                else:  # copy -> remove the copy we made
                    if os.path.exists(rec["dest"]):
                        if is_dir:
                            shutil.rmtree(rec["dest"], ignore_errors=True)
                        else:
                            os.remove(rec["dest"])
                        restored += 1
            except Exception as e:
                errors.append((base, str(e)))
                self.signals.log.emit(f"Undo failed for {rec['dest']}: {e}")
        self.signals.progress.emit(total, total, "")
        self.signals.batchDone.emit({
            "name": batch.get("name", "Undo"), "mode": "undo",
            "total": total, "ok": restored, "skipped": 0,
            "errors": errors, "undo": [],
        })


# --------------------------------------------------------------------------- #
# Reachability checker (thread pool -> signals back to GUI)
# --------------------------------------------------------------------------- #
class ReachabilitySignals(QObject):
    result = Signal(str, bool)   # mapping id, reachable


class ReachabilityChecker:
    def __init__(self):
        self.signals = ReachabilitySignals()
        self._pool = ThreadPoolExecutor(max_workers=8)

    def check_many(self, mappings):
        for m in mappings:
            self._pool.submit(self._one, m.id, m.path)

    def _one(self, mid, path):
        ok = is_path_reachable(path, timeout=3.0)
        self.signals.result.emit(mid, ok)

    def shutdown(self):
        self._pool.shutdown(wait=False)


class ThumbnailSignals(QObject):
    # tile key ("m:<id>" / "g:<id>"), request seq, chosen full path, QImage
    # chosen == ""   -> nothing usable inside; show the letter fallback
    # chosen is None -> folder unreachable / transient error; leave the tile as-is
    result = Signal(str, int, object, object)


class ThumbnailLoader:
    """Picks a RANDOM image from inside a tile's folder(s) and decodes it off
    the GUI thread. Every request is a fresh pick, so covers change each time a
    level is opened; `avoid` steers away from the image already on the tile."""
    def __init__(self):
        self.signals = ThumbnailSignals()
        self._pool = ThreadPoolExecutor(max_workers=4)

    def request(self, key, seq, folders, avoid=""):
        try:
            self._pool.submit(self._one, key, seq, list(folders), avoid or "")
        except RuntimeError:
            pass                      # pool shut down (app closing)

    def _one(self, key, seq, folders, avoid):
        cands, any_ok = [], False
        for folder in folders:
            if not folder:
                continue
            if _unc_host(folder) and not is_path_reachable(folder, timeout=3.0):
                continue
            try:
                cands.extend(find_cover_candidates(folder))
                any_ok = True
            except Exception:
                continue
            if len(cands) >= COVER_CAND_CAP:
                break
        if not any_ok:
            self.signals.result.emit(key, seq, None, None)
            return
        pool = [c for c in cands if c != avoid] or cands
        for _ in range(6):
            if not pool:
                break
            chosen = random.choice(pool)
            pool.remove(chosen)
            img = scaled_cover_image(chosen, COVER_W, COVER_H)
            if img is not None and not img.isNull():
                self.signals.result.emit(key, seq, chosen, img)
                return
        if avoid and avoid in cands:
            self.signals.result.emit(key, seq, None, None)   # only the current one decodes
            return
        self.signals.result.emit(key, seq, "", None)

    def shutdown(self):
        self._pool.shutdown(wait=False)


# --------------------------------------------------------------------------- #
# Network drive/folder scan (thread pool -> signals back to GUI)
# --------------------------------------------------------------------------- #
class ScanSignals(QObject):
    # root path, [(rel_parts tuple, abs_path), ...] in top-down order, truncated?
    resultReady = Signal(str, list, bool)
    error = Signal(str, str)          # root path, message


class DriveScanner:
    """Walks configured root folders off the GUI thread to find every real
    subfolder underneath, so MainWindow can auto-map them as nested groups."""
    def __init__(self):
        self.signals = ScanSignals()
        self._pool = ThreadPoolExecutor(max_workers=3)

    def scan_roots(self, roots, ignored_norm):
        ignored = set(ignored_norm)
        for root in roots:
            self._pool.submit(self._scan_one, root, ignored)

    def _scan_one(self, root, ignored_norm):
        if _norm_path(root) in ignored_norm:
            # must still report back - otherwise MainWindow's pending-scan count
            # never reaches 0 and "Scan now" stays stuck as "already running"
            self.signals.error.emit(root, "removed earlier, so it is skipped")
            return
        if not is_path_reachable(root, timeout=6.0):
            self.signals.error.emit(root, "not reachable")
            return
        found = []
        visited = {_norm_path(root)}
        truncated = [False]

        def walk(abs_path, rel_parts):
            try:
                entries = sorted(
                    (e.name for e in os.scandir(abs_path) if e.is_dir(follow_symlinks=False)),
                    key=str.casefold)
            except OSError:
                return
            for name in entries:
                if len(found) >= SCAN_FOLDER_CAP:
                    truncated[0] = True
                    return
                if name.startswith(".") or name.casefold() in SCAN_SKIP_DIRS:
                    continue
                child_abs = os.path.join(abs_path, name)
                norm = _norm_path(child_abs)
                if norm in ignored_norm or norm in visited:
                    continue          # explicitly ignored, or a symlink/junction loop
                visited.add(norm)
                child_rel = rel_parts + (name,)
                found.append((child_rel, child_abs))
                walk(child_abs, child_rel)

        try:
            walk(root, ())
        except Exception as e:
            self.signals.error.emit(root, str(e))
            return
        self.signals.resultReady.emit(root, found, truncated[0])

    def shutdown(self):
        self._pool.shutdown(wait=False)


# --------------------------------------------------------------------------- #
# Folder drop box (used inside the Add / Edit dialog)
# --------------------------------------------------------------------------- #
class FolderDropBox(QFrame):
    """A small dashed area: drag a folder onto it to capture its path."""
    folderDropped = Signal(str)

    def __init__(self):
        super().__init__()
        self.setObjectName("folderDrop")
        self.setAcceptDrops(True)
        self.setMinimumHeight(74)
        self._hover = False

        lay = QVBoxLayout(self)
        lay.setContentsMargins(12, 10, 12, 10)
        lay.setSpacing(2)
        self.label = QLabel("Drag a folder here to capture its path")
        self.label.setObjectName("folderDropLabel")
        self.label.setAlignment(Qt.AlignCenter)
        self.label.setWordWrap(True)
        self.sub = QLabel("or type it above / use Browse")
        self.sub.setObjectName("folderDropSub")
        self.sub.setAlignment(Qt.AlignCenter)
        lay.addWidget(self.label)
        lay.addWidget(self.sub)
        self._apply_style()

    @staticmethod
    def folder_from_paths(paths):
        """Pick a folder from dropped paths: first directory, else a file's parent."""
        for p in paths:
            try:
                if os.path.isdir(p):
                    return os.path.normpath(p)
            except Exception:
                pass
        if paths:
            return os.path.normpath(os.path.dirname(paths[0]))
        return None

    def show_captured(self, path):
        self.label.setText(path)
        self.sub.setText("Folder captured \u2713  \u00b7  drop another to change")

    def _apply_style(self):
        border = "#f59e0b" if self._hover else "#3a4250"
        bg = "#202a3a" if self._hover else "#161a22"
        self.setStyleSheet(
            f"QFrame#folderDrop{{background:{bg};border:2px dashed {border};"
            f"border-radius:12px;}}"
        )

    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()
            self._hover = True
            self._apply_style()

    def dragMoveEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()

    def dragLeaveEvent(self, e):
        self._hover = False
        self._apply_style()

    def dropEvent(self, e):
        self._hover = False
        self._apply_style()
        folder = self.folder_from_paths(extract_local_files(e.mimeData()))
        if folder:
            e.acceptProposedAction()
            self.folderDropped.emit(folder)


# --------------------------------------------------------------------------- #
# Add many folders at once
# --------------------------------------------------------------------------- #
class MultiFolderDrop(QFrame):
    """Dashed area that accepts several folders dropped together."""
    foldersDropped = Signal(list)   # [paths]

    def __init__(self):
        super().__init__()
        self.setObjectName("folderDrop")
        self.setAcceptDrops(True)
        self.setMinimumHeight(72)
        self._hover = False

        lay = QVBoxLayout(self)
        lay.setContentsMargins(12, 10, 12, 10)
        lay.setSpacing(2)
        self.label = QLabel("Drag one or more folders here")
        self.label.setObjectName("folderDropLabel")
        self.label.setAlignment(Qt.AlignCenter)
        self.sub = QLabel("you can drop several at once")
        self.sub.setObjectName("folderDropSub")
        self.sub.setAlignment(Qt.AlignCenter)
        lay.addWidget(self.label)
        lay.addWidget(self.sub)
        self._apply_style()

    def set_caption(self, text):
        self.sub.setText(text)

    @staticmethod
    def folders_from_paths(paths):
        """Map each dropped path to a folder (itself if a dir, else its parent),
        de-duplicated, order preserved."""
        out, seen = [], set()
        for p in paths:
            try:
                folder = p if os.path.isdir(p) else os.path.dirname(p)
            except Exception:
                folder = os.path.dirname(p)
            if folder:
                np = os.path.normpath(folder)
                key = np.lower()
                if key not in seen:
                    seen.add(key)
                    out.append(np)
        return out

    def _apply_style(self):
        border = "#f59e0b" if self._hover else "#3a4250"
        bg = "#202a3a" if self._hover else "#161a22"
        self.setStyleSheet(
            f"QFrame#folderDrop{{background:{bg};border:2px dashed {border};"
            f"border-radius:12px;}}"
        )

    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()
            self._hover = True
            self._apply_style()

    def dragMoveEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()

    def dragLeaveEvent(self, e):
        self._hover = False
        self._apply_style()

    def dropEvent(self, e):
        self._hover = False
        self._apply_style()
        folders = self.folders_from_paths(extract_local_files(e.mimeData()))
        if folders:
            e.acceptProposedAction()
            self.foldersDropped.emit(folders)


class FolderRow(QWidget):
    """One queued folder in the add-many dialog: color, name, path, remove."""
    removeClicked = Signal(object)

    def __init__(self, path, name, color):
        super().__init__()
        self.path = path
        self._color = color

        row = QHBoxLayout(self)
        row.setContentsMargins(0, 0, 0, 0)
        row.setSpacing(8)

        self.color_btn = QPushButton()
        self.color_btn.setFixedSize(26, 22)
        self.color_btn.setToolTip("Tile color")
        self.color_btn.setCursor(Qt.PointingHandCursor)
        self.color_btn.clicked.connect(self._pick_color)
        self._refresh_color()
        row.addWidget(self.color_btn, 0)

        self.name_edit = QLineEdit(name)
        self.name_edit.setPlaceholderText("Name")
        self.name_edit.setFixedWidth(150)
        row.addWidget(self.name_edit, 0)

        self.path_lbl = QLabel()
        self.path_lbl.setObjectName("rowPath")
        fm = QFontMetrics(self.path_lbl.font())
        self.path_lbl.setText(fm.elidedText(path, Qt.ElideMiddle, 320))
        self.path_lbl.setToolTip(path)
        row.addWidget(self.path_lbl, 1)

        self.del_btn = QPushButton("\u2715")
        self.del_btn.setObjectName("rowDel")
        self.del_btn.setFixedSize(26, 22)
        self.del_btn.setToolTip("Remove from list")
        self.del_btn.setCursor(Qt.PointingHandCursor)
        self.del_btn.clicked.connect(lambda: self.removeClicked.emit(self))
        row.addWidget(self.del_btn, 0)

    def _pick_color(self):
        c = QColorDialog.getColor(QColor(self._color), self, "Tile color")
        if c.isValid():
            self._color = c.name()
            self._refresh_color()

    def _refresh_color(self):
        self.color_btn.setStyleSheet(
            f"background:{self._color}; border:1px solid #2c3442; border-radius:6px;"
        )

    def values(self):
        return {"name": self.name_edit.text().strip(),
                "path": self.path, "color": self._color}


class AddFoldersDialog(QDialog):
    def __init__(self, parent, categories, remaining):
        super().__init__(parent)
        self.setWindowTitle("Add folders")
        self.setMinimumWidth(600)
        self.cap = max(0, min(BATCH_LIMIT, remaining))
        self._rows = []

        outer = QVBoxLayout(self)
        outer.setSpacing(10)

        self.include_subs = QCheckBox(
            "Also import every subfolder inside (mapped as nested groups you can "
            "double-click into)")
        self.include_subs.setChecked(True)
        outer.addWidget(self.include_subs)

        self.drop = MultiFolderDrop()
        self.drop.foldersDropped.connect(self._add_paths)
        outer.addWidget(self.drop)

        add_row = QHBoxLayout()
        self.path_edit = QLineEdit()
        self.path_edit.setPlaceholderText(
            r"Type a path:  \\NAS\share\Funny   or   D:\Pics\Funny")
        self.path_edit.returnPressed.connect(self._add_typed)
        self.add_btn = QPushButton("Add path")
        self.add_btn.clicked.connect(self._add_typed)
        self.browse_btn = QPushButton("Browse\u2026")
        self.browse_btn.clicked.connect(self._browse)
        add_row.addWidget(self.path_edit, 1)
        add_row.addWidget(self.add_btn, 0)
        add_row.addWidget(self.browse_btn, 0)
        outer.addLayout(add_row)

        self.list_host = QWidget()
        self.list_lay = QVBoxLayout(self.list_host)
        self.list_lay.setContentsMargins(0, 0, 0, 0)
        self.list_lay.setSpacing(6)
        self.list_lay.addStretch(1)
        self.empty = QLabel(
            "No folders queued yet \u2014 drag folders above, or add a path.")
        self.empty.setObjectName("emptyLabel")
        self.empty.setAlignment(Qt.AlignCenter)
        self.list_lay.insertWidget(0, self.empty)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setObjectName("scroll")
        scroll.setWidget(self.list_host)
        scroll.setMinimumHeight(210)
        outer.addWidget(scroll, 1)

        bottom = QHBoxLayout()
        bottom.addWidget(QLabel("Category for all (optional):"))
        self.cat_edit = QComboBox()
        self.cat_edit.setEditable(True)
        self.cat_edit.setFixedWidth(170)
        self.cat_edit.addItem("")
        for c in sorted(categories):
            if c:
                self.cat_edit.addItem(c)
        bottom.addWidget(self.cat_edit, 0)
        bottom.addStretch(1)
        self.counter = QLabel()
        self.counter.setObjectName("activeHint")
        bottom.addWidget(self.counter, 0)
        outer.addLayout(bottom)

        self.buttons = QDialogButtonBox(
            QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        self.buttons.button(QDialogButtonBox.Ok).setText("Add all")
        self.buttons.accepted.connect(self._accept)
        self.buttons.rejected.connect(self.reject)
        outer.addWidget(self.buttons)

        self._update_state()

    def _next_color(self):
        return TILE_PALETTE[len(self._rows) % len(TILE_PALETTE)]

    def _add_paths(self, paths):
        for p in paths:
            if len(self._rows) >= self.cap:
                break
            name = os.path.basename(p.rstrip("\\/")) or p
            row = FolderRow(p, name, self._next_color())
            row.removeClicked.connect(self._remove_row)
            self._rows.append(row)
            self.list_lay.insertWidget(self.list_lay.count() - 1, row)
        self._update_state()

    def _add_typed(self):
        text = self.path_edit.text().strip()
        if text:
            self._add_paths([os.path.normpath(text)])
            self.path_edit.clear()

    def _browse(self):
        d = QFileDialog.getExistingDirectory(
            self, "Select a folder", os.path.expanduser("~"))
        if d:
            self._add_paths([os.path.normpath(d)])

    def _remove_row(self, row):
        if row in self._rows:
            self._rows.remove(row)
            row.setParent(None)
            row.deleteLater()
        self._update_state()

    def _update_state(self):
        n = len(self._rows)
        full = n >= self.cap
        self.empty.setVisible(n == 0)
        self.counter.setText(f"{n} / {self.cap} folders")
        self.path_edit.setEnabled(not full)
        self.add_btn.setEnabled(not full)
        self.browse_btn.setEnabled(not full)
        self.buttons.button(QDialogButtonBox.Ok).setEnabled(n > 0)
        self.drop.set_caption(
            "Limit reached" if full else f"you can add {self.cap - n} more")

    def _accept(self):
        for r in self._rows:
            if not r.values()["name"]:
                QMessageBox.warning(self, APP_NAME, "Every folder needs a name.")
                return
        self.accept()

    def values(self):
        cat = self.cat_edit.currentText().strip()
        subs = self.include_subs.isChecked()
        out = []
        for r in self._rows:
            v = r.values()
            v["category"] = cat
            v["subfolders"] = subs
            out.append(v)
        return out


# --------------------------------------------------------------------------- #
# Add / Edit dialog
# --------------------------------------------------------------------------- #
class MappingDialog(QDialog):
    def __init__(self, parent, categories, mapping=None):
        super().__init__(parent)
        self.setWindowTitle("Edit folder" if mapping else "Add folder")
        self.setMinimumWidth(440)
        self._color = mapping.color if mapping else "#3b82f6"

        form = QFormLayout(self)

        self.name_edit = QLineEdit(mapping.name if mapping else "")
        self.name_edit.setPlaceholderText("e.g. Funny Stuff")
        form.addRow("Name", self.name_edit)

        path_row = QHBoxLayout()
        self.path_edit = QLineEdit(mapping.path if mapping else "")
        self.path_edit.setPlaceholderText(r"\\NAS\share\Funny Stuff   or   D:\Pics\Funny")
        browse = QPushButton("Browse...")
        browse.clicked.connect(self._browse)
        path_row.addWidget(self.path_edit, 1)
        path_row.addWidget(browse, 0)
        form.addRow("Folder path", path_row)

        self.drop_box = FolderDropBox()
        self.drop_box.folderDropped.connect(self._on_folder_dropped)
        form.addRow("", self.drop_box)

        self.cat_edit = QComboBox()
        self.cat_edit.setEditable(True)
        self.cat_edit.addItem("")
        for c in sorted(categories):
            if c:
                self.cat_edit.addItem(c)
        if mapping and mapping.category:
            self.cat_edit.setCurrentText(mapping.category)
        form.addRow("Category (optional)", self.cat_edit)

        self.color_btn = QPushButton("Pick color...")
        self.color_btn.clicked.connect(self._pick_color)
        form.addRow("Tile color", self.color_btn)
        self._refresh_color_btn()

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self._accept)
        buttons.rejected.connect(self.reject)
        form.addRow(buttons)

    def _on_folder_dropped(self, path):
        self.path_edit.setText(path)
        self.drop_box.show_captured(path)
        # Offer a sensible default name from the folder, only if name is empty.
        if not self.name_edit.text().strip():
            base = os.path.basename(path.rstrip("\\/")) or path
            self.name_edit.setText(base)

    def _browse(self):
        start = self.path_edit.text().strip() or os.path.expanduser("~")
        d = QFileDialog.getExistingDirectory(self, "Select destination folder", start)
        if d:
            self.path_edit.setText(os.path.normpath(d))

    def _pick_color(self):
        c = QColorDialog.getColor(QColor(self._color), self, "Tile color")
        if c.isValid():
            self._color = c.name()
            self._refresh_color_btn()

    def _refresh_color_btn(self):
        self.color_btn.setStyleSheet(
            f"background:{self._color}; color:{contrast_text(self._color)};"
            f"padding:6px; border-radius:6px;"
        )

    def _accept(self):
        if not self.name_edit.text().strip():
            QMessageBox.warning(self, APP_NAME, "Please enter a name.")
            return
        if not self.path_edit.text().strip():
            QMessageBox.warning(self, APP_NAME, "Please enter a folder path.")
            return
        self.accept()

    def values(self):
        return {
            "name": self.name_edit.text().strip(),
            "path": os.path.normpath(self.path_edit.text().strip()),
            "category": self.cat_edit.currentText().strip(),
            "color": self._color,
        }


# --------------------------------------------------------------------------- #
# Network scan roots (which drives/folders to auto-map, and how)
# --------------------------------------------------------------------------- #
class ScanRootsDialog(QDialog):
    def __init__(self, parent, roots, auto_scan, ignored_count):
        super().__init__(parent)
        self.setWindowTitle("Network scan roots")
        self.setMinimumWidth(540)
        self._roots = list(roots)
        self._reset_ignored = False
        self._ignored_count = ignored_count

        outer = QVBoxLayout(self)
        outer.setSpacing(10)

        info = QLabel(
            "Point Image Sorter at one or more roots \u2014 a mapped network drive, "
            "a UNC share, or any local folder. Every real subfolder underneath is "
            "mapped automatically as a nested group you can browse or drop files "
            "onto, mirroring your actual folder tree."
        )
        info.setWordWrap(True)
        info.setObjectName("activeHint")
        outer.addWidget(info)

        add_row = QHBoxLayout()
        self.path_edit = QLineEdit()
        self.path_edit.setPlaceholderText(
            r"Type a root:  \\NAS\share   or   Z:\   or   D:\Photos")
        self.path_edit.returnPressed.connect(self._add_typed)
        add_btn = QPushButton("Add path")
        add_btn.clicked.connect(self._add_typed)
        browse_btn = QPushButton("Browse\u2026")
        browse_btn.clicked.connect(self._browse)
        add_row.addWidget(self.path_edit, 1)
        add_row.addWidget(add_btn, 0)
        add_row.addWidget(browse_btn, 0)
        outer.addLayout(add_row)

        self.list_host = QWidget()
        self.list_lay = QVBoxLayout(self.list_host)
        self.list_lay.setContentsMargins(0, 0, 0, 0)
        self.list_lay.setSpacing(6)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setObjectName("scroll")
        scroll.setWidget(self.list_host)
        scroll.setMinimumHeight(160)
        outer.addWidget(scroll, 1)

        self.auto_check = QCheckBox("Scan automatically every time the app starts")
        self.auto_check.setChecked(bool(auto_scan))
        outer.addWidget(self.auto_check)

        ignored_row = QHBoxLayout()
        self.ignored_label = QLabel()
        self.ignored_label.setObjectName("activeHint")
        ignored_row.addWidget(self.ignored_label, 1)
        reset_btn = QPushButton("Un-ignore all")
        reset_btn.setToolTip(
            "Folders you removed after a scan are skipped on future scans.\n"
            "This forgets that list, so a scan can re-add them.")
        reset_btn.clicked.connect(self._reset_ignore)
        ignored_row.addWidget(reset_btn, 0)
        outer.addLayout(ignored_row)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        outer.addWidget(buttons)

        self._refresh_ignored_label()
        self._rebuild_rows()

    def _refresh_ignored_label(self):
        n = self._ignored_count
        self.ignored_label.setText(
            "No folders are being skipped." if n == 0 else
            f"{n} previously-removed folder(s) are skipped on future scans.")

    def _reset_ignore(self):
        self._reset_ignored = True
        self._ignored_count = 0
        self._refresh_ignored_label()

    def _make_row(self, path):
        row = QWidget()
        rl = QHBoxLayout(row)
        rl.setContentsMargins(0, 0, 0, 0)
        rl.setSpacing(8)
        lbl = QLabel()
        fm = QFontMetrics(lbl.font())
        lbl.setText(fm.elidedText(path, Qt.ElideMiddle, 400))
        lbl.setToolTip(path)
        rl.addWidget(lbl, 1)
        rm = QPushButton("\u2715")
        rm.setFixedSize(26, 22)
        rm.setToolTip("Remove this root")
        rm.setCursor(Qt.PointingHandCursor)
        rm.clicked.connect(lambda: self._remove_path(path))
        rl.addWidget(rm, 0)
        return row

    def _rebuild_rows(self):
        while self.list_lay.count():
            item = self.list_lay.takeAt(0)
            w = item.widget()
            if w:
                w.setParent(None)
                w.deleteLater()
        if not self._roots:
            empty = QLabel("No scan roots yet \u2014 add a drive or folder above.")
            empty.setObjectName("emptyLabel")
            empty.setAlignment(Qt.AlignCenter)
            self.list_lay.addWidget(empty)
        else:
            for p in self._roots:
                self.list_lay.addWidget(self._make_row(p))
        self.list_lay.addStretch(1)

    def _add_paths(self, paths):
        changed = False
        for p in paths:
            norm = os.path.normpath(p.strip())
            if norm and norm not in self._roots:
                self._roots.append(norm)
                changed = True
        if changed:
            self._rebuild_rows()

    def _add_typed(self):
        text = self.path_edit.text().strip()
        if text:
            self._add_paths([text])
            self.path_edit.clear()

    def _browse(self):
        d = QFileDialog.getExistingDirectory(
            self, "Select a root folder", os.path.expanduser("~"))
        if d:
            self._add_paths([d])

    def _remove_path(self, path):
        self._roots = [p for p in self._roots if p != path]
        self._rebuild_rows()

    def values(self):
        return {
            "scan_roots": list(self._roots),
            "auto_scan": self.auto_check.isChecked(),
            "reset_ignored": self._reset_ignored,
        }


# --------------------------------------------------------------------------- #
# Settings dialog
# --------------------------------------------------------------------------- #
class SettingsDialog(QDialog):
    def __init__(self, parent, settings):
        super().__init__(parent)
        self.setWindowTitle("Settings")
        self.setMinimumWidth(420)
        form = QFormLayout(self)

        self.collision = QComboBox()
        self.collision.addItems(["rename", "skip", "overwrite"])
        self.collision.setCurrentText(settings.get("collision", "rename"))
        form.addRow("If a file already exists", self.collision)

        self.media_only = QCheckBox(
            "Only file media types \u2014 images, videos & audio (skip other files in a drop)")
        self.media_only.setChecked(bool(settings.get("media_only", True)))
        form.addRow(self.media_only)

        self.confirm_each = QCheckBox("Ask for confirmation before every drop")
        self.confirm_each.setChecked(bool(settings.get("confirm_each", False)))
        form.addRow(self.confirm_each)

        self.confirm_delete = QCheckBox(
            "Ask before the Interactive Mode Delete button deletes an image")
        self.confirm_delete.setChecked(bool(settings.get("confirm_delete", False)))
        form.addRow(self.confirm_delete)

        self.interval = QSpinBox()
        self.interval.setRange(0, 600)
        self.interval.setSuffix(" s")
        self.interval.setValue(int(settings.get("auto_check_seconds", 20)))
        form.addRow("Auto re-check drives every (0 = off)", self.interval)

        self._bg_path = settings.get("background_image", "") or ""
        bg_row = QHBoxLayout()
        self.bg_label = QLabel()
        self.bg_label.setObjectName("activeHint")
        choose = QPushButton("Choose\u2026")
        choose.clicked.connect(self._choose_bg)
        clear = QPushButton("Clear")
        clear.clicked.connect(self._clear_bg)
        bg_row.addWidget(self.bg_label, 1)
        bg_row.addWidget(choose, 0)
        bg_row.addWidget(clear, 0)
        form.addRow("Home background", bg_row)
        self._refresh_bg_label()

        self._scan_roots = list(settings.get("scan_roots", []) or [])
        self._auto_scan = bool(settings.get("auto_scan_startup", True))
        self._reset_ignored = False
        self._ignored_count = len(settings.get("ignored_scan_paths", []) or [])
        scan_row = QHBoxLayout()
        self.scan_summary = QLabel()
        self.scan_summary.setObjectName("activeHint")
        manage_btn = QPushButton("Manage\u2026")
        manage_btn.clicked.connect(self._manage_scan_roots)
        scan_row.addWidget(self.scan_summary, 1)
        scan_row.addWidget(manage_btn, 0)
        form.addRow("Network scan roots", scan_row)
        self._refresh_scan_summary()

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        form.addRow(buttons)

    def _refresh_scan_summary(self):
        n = len(self._scan_roots)
        if n == 0:
            self.scan_summary.setText("None configured")
        else:
            state = "on" if self._auto_scan else "off"
            self.scan_summary.setText(f"{n} root(s) \u00b7 auto-scan on start: {state}")

    def _manage_scan_roots(self):
        dlg = ScanRootsDialog(self, self._scan_roots, self._auto_scan, self._ignored_count)
        if dlg.exec() == QDialog.Accepted:
            v = dlg.values()
            self._scan_roots = v["scan_roots"]
            self._auto_scan = v["auto_scan"]
            if v["reset_ignored"]:
                self._reset_ignored = True
                self._ignored_count = 0
            self._refresh_scan_summary()

    def _refresh_bg_label(self):
        if self._bg_path:
            fm = QFontMetrics(self.bg_label.font())
            self.bg_label.setText(fm.elidedText(
                os.path.basename(self._bg_path), Qt.ElideMiddle, 220))
            self.bg_label.setToolTip(self._bg_path)
        else:
            self.bg_label.setText("(none)")
            self.bg_label.setToolTip("")

    def _choose_bg(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Choose a background image", os.path.expanduser("~"),
            "Images (*.png *.jpg *.jpeg *.bmp *.webp *.gif *.tif *.tiff)")
        if path:
            self._bg_path = os.path.normpath(path)
            self._refresh_bg_label()

    def _clear_bg(self):
        self._bg_path = ""
        self._refresh_bg_label()

    def values(self):
        out = {
            "collision": self.collision.currentText(),
            "media_only": self.media_only.isChecked(),
            "confirm_each": self.confirm_each.isChecked(),
            "confirm_delete": self.confirm_delete.isChecked(),
            "auto_check_seconds": self.interval.value(),
            "background_image": self._bg_path,
            "scan_roots": list(self._scan_roots),
            "auto_scan_startup": self._auto_scan,
        }
        if self._reset_ignored:
            out["ignored_scan_paths"] = []
        return out


# --------------------------------------------------------------------------- #
# Transfer progress window (modeless; shown for large transfers)
# --------------------------------------------------------------------------- #
class TransferProgressDialog(QDialog):
    def __init__(self, parent):
        super().__init__(parent)
        self.setWindowTitle("Transferring")
        self.setModal(False)
        self.setMinimumWidth(460)

        lay = QVBoxLayout(self)
        lay.setContentsMargins(18, 16, 18, 16)
        lay.setSpacing(9)

        self.title = QLabel("Preparing\u2026")
        self.title.setObjectName("progTitle")
        self.title.setWordWrap(True)
        lay.addWidget(self.title)

        self.overall_lbl = QLabel("")
        self.overall_lbl.setObjectName("activeHint")
        lay.addWidget(self.overall_lbl)
        self.overall_bar = QProgressBar()
        self.overall_bar.setTextVisible(False)
        self.overall_bar.setFixedHeight(10)
        lay.addWidget(self.overall_bar)

        lay.addSpacing(4)
        self.file_lbl = QLabel("")
        self.file_lbl.setObjectName("progFile")
        lay.addWidget(self.file_lbl)
        self.file_bar = QProgressBar()
        self.file_bar.setFixedHeight(18)
        lay.addWidget(self.file_bar)
        self.bytes_lbl = QLabel("")
        self.bytes_lbl.setObjectName("activeHint")
        self.bytes_lbl.setAlignment(Qt.AlignRight)
        lay.addWidget(self.bytes_lbl)

        row = QHBoxLayout()
        row.addStretch(1)
        self.close_btn = QPushButton("Run in background")
        self.close_btn.clicked.connect(self.hide)
        row.addWidget(self.close_btn)
        lay.addLayout(row)

    def start(self, target, total_files, total_bytes):
        if total_bytes > 0:
            self.title.setText(
                f"Filing {total_files} item(s) \u00b7 {human_bytes(total_bytes)}"
                f"  \u2192  {target}")
        else:
            self.title.setText(f"Filing {total_files} item(s)  \u2192  {target}")
        self.overall_bar.setRange(0, max(1, total_files))
        self.overall_bar.setValue(0)
        self.overall_lbl.setText("Starting\u2026")
        self.file_lbl.setText("")
        self.file_bar.setRange(0, 100)
        self.file_bar.setValue(0)
        self.bytes_lbl.setText("")
        self.close_btn.setText("Run in background")

    def set_overall(self, done, total):
        total = max(1, total)
        self.overall_bar.setRange(0, total)
        self.overall_bar.setValue(done)
        self.overall_lbl.setText(f"File {min(done + 1, total)} of {total}")

    def set_file(self, name, copied, total):
        fm = QFontMetrics(self.file_lbl.font())
        self.file_lbl.setText(fm.elidedText(name, Qt.ElideMiddle, 400))
        if total > 0:
            pct = int(copied * 100 / total)
            self.file_bar.setRange(0, 100)
            self.file_bar.setValue(pct)
            self.bytes_lbl.setText(
                f"{human_bytes(copied)} / {human_bytes(total)}  ({pct}%)")
        else:
            self.file_bar.setRange(0, 0)   # unknown size -> busy indicator
            self.bytes_lbl.setText("")

    def finish(self, summary):
        self.overall_bar.setRange(0, 1)
        self.overall_bar.setValue(1)
        self.file_bar.setRange(0, 100)
        self.file_bar.setValue(100)
        if summary.get("mode") == "undo":
            self.title.setText(
                f"Undo complete \u2014 {summary.get('ok', 0)} restored")
        else:
            self.title.setText(
                f"Done \u2014 {summary.get('ok', 0)} filed to "
                f"\u201c{summary.get('name', '')}\u201d")
        self.overall_lbl.setText("")
        self.file_lbl.setText("")
        self.bytes_lbl.setText("")
        self.close_btn.setText("Close")


# --------------------------------------------------------------------------- #
# Home-screen wallpaper backdrop (paints behind the tile canvas)
# --------------------------------------------------------------------------- #
class WallpaperWidget(QWidget):
    def __init__(self):
        super().__init__()
        self.setObjectName("wallpaper")
        self.setAttribute(Qt.WA_StyledBackground, False)
        self._pixmap = None
        self._scaled = None
        self._scaled_for = None
        self._base = QColor("#0e1116")

    def set_wallpaper(self, pixmap):
        self._pixmap = pixmap if (pixmap and not pixmap.isNull()) else None
        self._scaled = None
        self._scaled_for = None
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        r = self.rect()
        if self._pixmap is not None:
            if self._scaled is None or self._scaled_for != r.size():
                self._scaled = self._pixmap.scaled(
                    r.size(), Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
                self._scaled_for = r.size()
            sx = max(0, (self._scaled.width() - r.width()) // 2)
            sy = max(0, (self._scaled.height() - r.height()) // 2)
            p.drawPixmap(r, self._scaled, QRect(sx, sy, r.width(), r.height()))
            p.fillRect(r, QColor(10, 12, 18, 150))   # scrim for tile readability
        else:
            p.fillRect(r, self._base)
        p.end()


# --------------------------------------------------------------------------- #
# Main window
# --------------------------------------------------------------------------- #
# --------------------------------------------------------------------------- #
# Interactive Mode: big one-at-a-time image viewer (left) + destination tree
# (right). Drag the open image onto any folder in the tree to file it. Filing
# goes through MainWindow.handle_drop(), i.e. the exact same transfer pipeline
# (move/copy, collision rule, reachability guard, undo, log) Original Mode uses.
# --------------------------------------------------------------------------- #
def default_source_dirs():
    """The user's Desktop and Downloads folders (Windows known-folder aware)."""
    out = []
    for loc in (QStandardPaths.DesktopLocation, QStandardPaths.DownloadLocation):
        try:
            p = QStandardPaths.writableLocation(loc)
        except Exception:
            p = ""
        if p and os.path.isdir(p):
            p = os.path.normpath(p)
            if _norm_path(p) not in {_norm_path(x) for x in out}:
                out.append(p)
    return out


def list_source_images(dirs):
    """Image files sitting directly inside each source folder (not recursive).
    Returns a list of dicts: path, name, src (folder), mtime, size."""
    out, seen = [], set()
    for d in dirs:
        if not d:
            continue
        if _unc_host(d) and not is_path_reachable(d, timeout=2.0):
            continue
        try:
            with os.scandir(d) as it:
                for e in it:
                    try:
                        if not e.is_file(follow_symlinks=True) or not is_image(e.name):
                            continue
                        norm = _norm_path(e.path)
                        if norm in seen:
                            continue
                        seen.add(norm)
                        st = e.stat()
                        out.append({"path": os.path.normpath(e.path), "name": e.name,
                                    "src": d, "mtime": st.st_mtime, "size": st.st_size})
                    except OSError:
                        continue
        except OSError:
            continue
    return out


def sort_source_images(items, how):
    if how == "oldest":
        items.sort(key=lambda x: (x["mtime"], x["name"].casefold()))
    elif how == "name":
        items.sort(key=lambda x: (x["name"].casefold(), x["mtime"]))
    else:  # newest first
        items.sort(key=lambda x: (-x["mtime"], x["name"].casefold()))
    return items


def _raw_embedded_preview(path):
    """Most camera RAW files carry a full-size JPEG preview inside them. Find the
    JPEG start markers and keep the largest one Qt can decode."""
    try:
        with open(path, "rb") as f:
            data = f.read(RAW_READ_CAP)
    except OSError:
        return None
    best, start, tries = None, 0, 0
    while tries < 12:
        i = data.find(b"\xff\xd8\xff", start)
        if i < 0:
            break
        tries += 1
        img = QImage.fromData(data[i:i + RAW_SLICE_CAP])
        if not img.isNull() and (best is None or
                                 img.width() * img.height() > best.width() * best.height()):
            best = img
            if best.width() >= 1600 or best.height() >= 1600:
                break
        start = i + 3
    return best


def load_preview_image(path, max_side=None):
    """Decode an image for the big viewer, honoring EXIF rotation and capping the
    long side at max_side to keep memory sane. Returns a QImage or None when Qt
    can't decode the format (HEIC/AVIF/JXL...). Safe off the GUI thread."""
    max_side = max_side or PREVIEW_MAX_SIDE
    ext = os.path.splitext(path)[1].lower()
    img = None
    if ext in RAW_EXTS:
        img = _raw_embedded_preview(path)
    else:
        reader = QImageReader(path)
        reader.setAutoTransform(True)
        if not reader.canRead():
            return None
        sz = reader.size()
        if sz.isValid() and sz.width() > 0 and sz.height() > 0:
            if ext in (".svg", ".svgz") or max(sz.width(), sz.height()) > max_side:
                reader.setScaledSize(sz.scaled(max_side, max_side, Qt.KeepAspectRatio))
        img = reader.read()
    if img is None or img.isNull():
        return None
    if max(img.width(), img.height()) > max_side:
        img = img.scaled(max_side, max_side, Qt.KeepAspectRatio, Qt.SmoothTransformation)
    return img


def send_to_trash(path):
    """Delete a file from disk. On Windows it goes to the Recycle Bin (so a
    mis-click can be recovered from there); elsewhere it is removed outright.
    Returns "recycled" or "deleted"; raises OSError if the file is still there."""
    path = os.path.abspath(path)
    if not os.path.isfile(path):
        raise OSError(f"File not found: {path}")
    how = "deleted"
    if sys.platform.startswith("win"):
        import ctypes
        from ctypes import wintypes

        class SHFILEOPSTRUCTW(ctypes.Structure):
            _fields_ = [
                ("hwnd", wintypes.HWND),
                ("wFunc", wintypes.UINT),
                ("pFrom", wintypes.LPCWSTR),
                ("pTo", wintypes.LPCWSTR),
                ("fFlags", ctypes.c_ushort),
                ("fAnyOperationsAborted", wintypes.BOOL),
                ("hNameMappings", ctypes.c_void_p),
                ("lpszProgressTitle", wintypes.LPCWSTR),
            ]

        FO_DELETE = 0x0003
        FOF_SILENT, FOF_NOCONFIRMATION = 0x0004, 0x0010
        FOF_ALLOWUNDO, FOF_NOERRORUI = 0x0040, 0x0400
        op = SHFILEOPSTRUCTW()
        op.hwnd = None
        op.wFunc = FO_DELETE
        op.pFrom = path + "\0"       # the API wants a double-NUL-terminated list
        op.pTo = None
        op.fFlags = FOF_ALLOWUNDO | FOF_NOCONFIRMATION | FOF_SILENT | FOF_NOERRORUI
        rc = ctypes.windll.shell32.SHFileOperationW(ctypes.byref(op))
        if rc == 0 and not op.fAnyOperationsAborted and not os.path.exists(path):
            # network shares have no Recycle Bin; the shell deletes those outright
            return "deleted" if _unc_host(path) else "recycled"
        # shell refused (rare) -> fall through to a plain delete
    os.remove(path)
    if os.path.exists(path):
        raise OSError(f"Could not delete: {path}")
    return how


def open_path_default(path):
    """Open a file (or folder) with the OS default application."""
    try:
        if sys.platform.startswith("win"):
            os.startfile(path)  # type: ignore[attr-defined]
        else:
            import subprocess
            subprocess.Popen(["open" if sys.platform == "darwin" else "xdg-open", path])
        return True
    except Exception:
        return False


def _dot_icon(color, d=12):
    pm = QPixmap(d, d)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing, True)
    p.setPen(Qt.NoPen)
    p.setBrush(QColor(color))
    p.drawEllipse(1, 1, d - 2, d - 2)
    p.end()
    return QIcon(pm)


class PreviewSignals(QObject):
    loaded = Signal(str, object)     # path, QImage or None (no preview possible)


class PreviewLoader:
    """Decodes big-view images off the GUI thread (and prefetches neighbors)."""
    def __init__(self, max_side=None):
        self.max_side = max_side
        self.signals = PreviewSignals()
        self._pool = ThreadPoolExecutor(max_workers=2)
        self._pending = set()
        self._lock = threading.Lock()

    def request(self, path):
        with self._lock:
            if path in self._pending:
                return
            self._pending.add(path)
        try:
            self._pool.submit(self._one, path)
        except RuntimeError:          # pool already shut down (app closing)
            with self._lock:
                self._pending.discard(path)

    def _one(self, path):
        try:
            img = load_preview_image(path, self.max_side)
        except Exception:
            img = None
        with self._lock:
            self._pending.discard(path)
        self.signals.loaded.emit(path, img)

    def shutdown(self):
        self._pool.shutdown(wait=False)


class ImageStage(QWidget):
    """The big image on the left. Click-and-drag it onto a destination folder.
    Arrow keys / mouse wheel step through the source images."""
    prevRequested = Signal()
    nextRequested = Signal()
    openRequested = Signal(str)
    dragStarted = Signal(str)
    deleteRequested = Signal()

    def __init__(self):
        super().__init__()
        self.setObjectName("imageStage")
        self.setMinimumSize(320, 240)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setCursor(Qt.OpenHandCursor)
        self.setToolTip("Drag this image onto a folder on the right to file it.\n"
                        "\u2190 / \u2192 or the mouse wheel step through images; "
                        "double-click opens it.")
        self._path = None
        self._state = "empty"         # empty | loading | image | nopreview
        self._message = ""
        self._pix = None              # full decoded QPixmap
        self._scaled = None
        self._scaled_key = None
        self._movie = None
        self._movie_buf = None
        self._press = None
        self._wheel_acc = 0

    # ---- state ----
    def current_path(self):
        return self._path

    def state(self):
        return self._state

    def _reset(self):
        if self._movie is not None:
            self._movie.stop()
            self._movie.deleteLater()
            self._movie = None
        self._movie_buf = None
        self._pix = None
        self._scaled = None
        self._scaled_key = None

    def show_empty(self, message):
        self._reset()
        self._path = None
        self._state = "empty"
        self._message = message
        self.setCursor(Qt.ArrowCursor)
        self.update()

    def show_loading(self, path):
        self._reset()
        self._path = path
        self._state = "loading"
        self.setCursor(Qt.OpenHandCursor)
        self.update()

    def show_image(self, path, image):
        self._reset()
        self._path = path
        self._pix = QPixmap.fromImage(image)
        self._state = "image" if not self._pix.isNull() else "nopreview"
        self.setCursor(Qt.OpenHandCursor)
        self.update()

    def show_movie(self, path):
        """Animated GIF: play it. Returns False if Qt can't animate it.
        The GIF is read into memory first: a QMovie playing from the file keeps
        it open, and Windows then refuses to move or delete it."""
        try:
            with open(path, "rb") as f:
                data = f.read()
        except OSError:
            return False
        buf = QBuffer()
        buf.setData(QByteArray(data))
        buf.open(QIODevice.ReadOnly)
        mv = QMovie(buf)
        if not mv.isValid() or mv.frameCount() == 1:
            mv.deleteLater()
            return False
        self._reset()
        self._path = path
        self._movie = mv
        self._movie_buf = buf
        self._state = "image"
        mv.frameChanged.connect(self._on_frame)
        mv.start()
        self.setCursor(Qt.OpenHandCursor)
        return True

    def show_no_preview(self, path):
        self._reset()
        self._path = path
        self._state = "nopreview"
        self.setCursor(Qt.OpenHandCursor)
        self.update()

    def _on_frame(self, _n):
        self._scaled = None
        self.update()

    def _current_pixmap(self):
        if self._movie is not None:
            return self._movie.currentPixmap()
        return self._pix

    # ---- painting ----
    def _image_rect(self):
        return self.rect().adjusted(14, 14, -14, -14)

    def paintEvent(self, _e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.setRenderHint(QPainter.SmoothPixmapTransform, True)
        p.fillRect(self.rect(), QColor("#0a0d12"))
        area = self._image_rect()
        if self._state == "image":
            src = self._current_pixmap()
            if src is not None and not src.isNull():
                dpr = self.devicePixelRatioF()
                key = (area.width(), area.height(), src.cacheKey(), dpr)
                if self._scaled is None or self._scaled_key != key:
                    tgt = QSize(max(1, int(area.width() * dpr)), max(1, int(area.height() * dpr)))
                    if src.width() > tgt.width() or src.height() > tgt.height():
                        sc = src.scaled(tgt, Qt.KeepAspectRatio, Qt.SmoothTransformation)
                    else:
                        # small image: enlarge to fill most of the pane, but keep it crisp-ish
                        sc = src.scaled(tgt, Qt.KeepAspectRatio, Qt.SmoothTransformation)
                    sc.setDevicePixelRatio(dpr)
                    self._scaled, self._scaled_key = sc, key
                sc = self._scaled
                w = sc.width() / sc.devicePixelRatio()
                h = sc.height() / sc.devicePixelRatio()
                x = area.x() + (area.width() - w) / 2
                y = area.y() + (area.height() - h) / 2
                p.drawPixmap(int(x), int(y), sc)
        elif self._state == "nopreview":
            ext = os.path.splitext(self._path or "")[1].upper().lstrip(".") or "FILE"
            cw, ch = min(360, area.width() - 20), min(260, area.height() - 20)
            card = QRect(area.x() + (area.width() - cw) // 2,
                         area.y() + (area.height() - ch) // 2, cw, ch)
            p.setPen(QColor("#2c3442"))
            p.setBrush(QColor("#151a23"))
            p.drawRoundedRect(card, 16, 16)
            f = QFont(self.font())
            f.setPointSize(28)
            f.setBold(True)
            p.setFont(f)
            p.setPen(QColor("#93c5fd"))
            p.drawText(card.adjusted(0, 24, 0, -ch // 2), Qt.AlignCenter, ext)
            f2 = QFont(self.font())
            f2.setPointSize(10)
            p.setFont(f2)
            p.setPen(QColor("#cbd5e1"))
            p.drawText(card.adjusted(16, ch // 2, -16, -16), Qt.AlignHCenter | Qt.TextWordWrap,
                       f"{os.path.basename(self._path or '')}\n\n"
                       "No preview available for this format \u2014\n"
                       "you can still drag it onto a folder to file it.")
        else:
            p.setPen(QColor("#7b8696"))
            f = QFont(self.font())
            f.setPointSize(12)
            p.setFont(f)
            text = "Loading\u2026" if self._state == "loading" else self._message
            p.drawText(area, Qt.AlignCenter | Qt.TextWordWrap, text)
        if self.hasFocus() and self._state != "empty":
            p.setPen(QColor("#1d4ed8"))
            p.setBrush(Qt.NoBrush)
            p.drawRoundedRect(self.rect().adjusted(1, 1, -2, -2), 10, 10)
        p.end()

    def resizeEvent(self, e):
        self._scaled = None
        super().resizeEvent(e)

    # ---- interaction ----
    def mousePressEvent(self, e):
        self.setFocus()
        if e.button() == Qt.LeftButton and self._path:
            self._press = e.position().toPoint()
            self.setCursor(Qt.ClosedHandCursor)
        super().mousePressEvent(e)

    def mouseReleaseEvent(self, e):
        self._press = None
        if self._path:
            self.setCursor(Qt.OpenHandCursor)
        super().mouseReleaseEvent(e)

    def mouseMoveEvent(self, e):
        if self._press is None or not self._path or not (e.buttons() & Qt.LeftButton):
            return
        if (e.position().toPoint() - self._press).manhattanLength() < \
                QApplication.startDragDistance():
            return
        self._press = None
        self.start_drag()

    def drag_pixmap(self):
        src = self._current_pixmap() if self._state == "image" else None
        if src is not None and not src.isNull():
            pm = src.scaled(200, 200, Qt.KeepAspectRatio, Qt.SmoothTransformation)
        else:
            pm = QPixmap(140, 100)
            pm.fill(QColor("#1f2532"))
            q = QPainter(pm)
            q.setPen(QColor("#e5e7eb"))
            q.drawText(pm.rect(), Qt.AlignCenter,
                       os.path.splitext(self._path or "")[1].upper().lstrip("."))
            q.end()
        return pm

    def build_mime(self):
        mime = QMimeData()
        mime.setUrls([QUrl.fromLocalFile(self._path)])
        mime.setData(STAGE_MIME, self._path.encode("utf-8"))
        return mime

    def start_drag(self):
        path = self._path
        if not path:
            return
        self.dragStarted.emit(path)
        drag = QDrag(self)
        drag.setMimeData(self.build_mime())
        pm = self.drag_pixmap()
        drag.setPixmap(pm)
        drag.setHotSpot(QPoint(pm.width() // 2, pm.height() // 2))
        # Copy only: if the image is dropped somewhere outside the app (Explorer),
        # the shell must never move the original. Inside the app, the destination
        # tree performs the user's configured Move/Copy itself.
        drag.exec(Qt.CopyAction, Qt.CopyAction)
        if self._path:
            self.setCursor(Qt.OpenHandCursor)

    def mouseDoubleClickEvent(self, e):
        if self._path:
            self.openRequested.emit(self._path)

    def wheelEvent(self, e):
        self._wheel_acc += e.angleDelta().y()
        while self._wheel_acc >= 120:
            self._wheel_acc -= 120
            self.prevRequested.emit()
        while self._wheel_acc <= -120:
            self._wheel_acc += 120
            self.nextRequested.emit()
        e.accept()

    def keyPressEvent(self, e):
        k = e.key()
        if k in (Qt.Key_Left, Qt.Key_Up, Qt.Key_PageUp, Qt.Key_Backspace):
            self.prevRequested.emit()
        elif k in (Qt.Key_Right, Qt.Key_Down, Qt.Key_PageDown, Qt.Key_Space):
            self.nextRequested.emit()
        elif k in (Qt.Key_Return, Qt.Key_Enter) and self._path:
            self.openRequested.emit(self._path)
        elif k == Qt.Key_Delete and self._path:
            self.deleteRequested.emit()
        else:
            super().keyPressEvent(e)

    def focusInEvent(self, e):
        self.update()
        super().focusInEvent(e)

    def focusOutEvent(self, e):
        self.update()
        super().focusOutEvent(e)


class DestinationTree(QTreeWidget):
    """Folder tree on the right. Accepts the dragged image (or any files dragged
    from Explorer) onto any item that has a real folder path. Hovering over a
    collapsed branch while dragging expands it."""
    filesDropped = Signal(object, list)      # target payload dict, [paths]
    fileHereRequested = Signal(object)       # payload: file the current image here
    openRequested = Signal(object)
    copyPathRequested = Signal(object)

    def __init__(self):
        super().__init__()
        self.setObjectName("destTree")
        self.setHeaderHidden(True)
        self.setColumnCount(1)
        self.setAcceptDrops(True)
        self.viewport().setAcceptDrops(True)
        self.setDragDropMode(QAbstractItemView.DropOnly)
        self.setDropIndicatorShown(False)
        self.setAutoExpandDelay(650)
        self.setAutoScroll(True)
        self.setAnimated(True)
        self.setIndentation(18)
        self.setUniformRowHeights(True)
        self.setExpandsOnDoubleClick(True)
        self.setContextMenuPolicy(Qt.CustomContextMenu)
        self.customContextMenuRequested.connect(self._menu)
        self._hover = None

    @staticmethod
    def payload(item):
        return item.data(0, Qt.UserRole) if item is not None else None

    def target_at(self, pos):
        item = self.itemAt(pos)
        data = self.payload(item)
        if data and data.get("path"):
            return item, data
        return item, None

    def _set_hover(self, item):
        if item is self._hover:
            return
        self._hover = item
        if item is not None:
            self.setCurrentItem(item)
        else:
            self.clearSelection()

    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.setDropAction(Qt.CopyAction)
            e.accept()
            self.setState(QAbstractItemView.DraggingState)
        else:
            e.ignore()

    def dragMoveEvent(self, e):
        if not e.mimeData().hasUrls():
            e.ignore()
            return
        super().dragMoveEvent(e)      # Qt's auto-scroll + hover-to-expand timers
        item, data = self.target_at(e.position().toPoint())
        if data:
            self._set_hover(item)
            e.setDropAction(Qt.CopyAction)
            e.accept()
        else:
            self._set_hover(None)
            e.ignore()

    def dragLeaveEvent(self, e):
        self._set_hover(None)
        self.setState(QAbstractItemView.NoState)
        e.accept()

    def dropEvent(self, e):
        item, data = self.target_at(e.position().toPoint())
        paths = extract_local_files(e.mimeData())
        self._hover = None
        self.setState(QAbstractItemView.NoState)
        if not data or not paths:
            e.ignore()
            return
        self.setCurrentItem(item)
        e.setDropAction(Qt.CopyAction)
        e.accept()
        self.filesDropped.emit(data, paths)

    def _menu(self, pos):
        item = self.itemAt(pos)
        data = self.payload(item)
        if not data:
            return
        m = QMenu(self)
        has_path = bool(data.get("path"))
        a_file = m.addAction("File the current image here")
        a_file.setEnabled(has_path)
        m.addSeparator()
        a_open = m.addAction("Open folder")
        a_open.setEnabled(has_path)
        a_copy = m.addAction("Copy path")
        a_copy.setEnabled(has_path)
        m.addSeparator()
        a_exp = m.addAction("Expand everything below")
        a_col = m.addAction("Collapse")
        chosen = m.exec(self.viewport().mapToGlobal(pos))
        if chosen is a_file:
            self.fileHereRequested.emit(data)
        elif chosen is a_open:
            self.openRequested.emit(data)
        elif chosen is a_copy:
            self.copyPathRequested.emit(data)
        elif chosen is a_exp:
            self.expandRecursively(self.indexFromItem(item))
        elif chosen is a_col:
            item.setExpanded(False)


class PathListDialog(QDialog):
    """Edit a simple list of folder paths (used for Interactive Mode sources)."""
    def __init__(self, parent, title, info, paths, defaults=None):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setMinimumWidth(540)
        self._paths = list(paths)
        self._defaults = list(defaults or [])
        outer = QVBoxLayout(self)
        outer.setSpacing(10)
        lbl = QLabel(info)
        lbl.setWordWrap(True)
        lbl.setObjectName("activeHint")
        outer.addWidget(lbl)
        row = QHBoxLayout()
        self.path_edit = QLineEdit()
        self.path_edit.setPlaceholderText(r"Type a folder:  C:\Users\you\Desktop   or   \\NAS\inbox")
        self.path_edit.returnPressed.connect(self._add_typed)
        add_btn = QPushButton("Add path")
        add_btn.clicked.connect(self._add_typed)
        browse = QPushButton("Browse\u2026")
        browse.clicked.connect(self._browse)
        row.addWidget(self.path_edit, 1)
        row.addWidget(add_btn, 0)
        row.addWidget(browse, 0)
        outer.addLayout(row)
        self.list = QListWidget()
        self.list.setMinimumHeight(150)
        outer.addWidget(self.list, 1)
        brow = QHBoxLayout()
        rm = QPushButton("Remove selected")
        rm.clicked.connect(self._remove)
        brow.addWidget(rm, 0)
        if self._defaults:
            reset = QPushButton("Reset to Desktop + Downloads")
            reset.clicked.connect(self._reset)
            brow.addWidget(reset, 0)
        brow.addStretch(1)
        outer.addLayout(brow)
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        outer.addWidget(buttons)
        self._rebuild()

    def _rebuild(self):
        self.list.clear()
        for p in self._paths:
            it = QListWidgetItem(p)
            it.setToolTip(p)
            self.list.addItem(it)

    def add_paths(self, paths):
        known = {_norm_path(p) for p in self._paths}
        for p in paths:
            p = os.path.normpath(p.strip()) if p and p.strip() else ""
            if p and _norm_path(p) not in known:
                self._paths.append(p)
                known.add(_norm_path(p))
        self._rebuild()

    def _add_typed(self):
        t = self.path_edit.text().strip()
        if t:
            self.add_paths([t])
            self.path_edit.clear()

    def _browse(self):
        d = QFileDialog.getExistingDirectory(self, "Select a source folder",
                                             os.path.expanduser("~"))
        if d:
            self.add_paths([d])

    def _remove(self):
        rows = sorted((self.list.row(i) for i in self.list.selectedItems()), reverse=True)
        for r in rows:
            if 0 <= r < len(self._paths):
                self._paths.pop(r)
        self._rebuild()

    def _reset(self):
        self._paths = list(self._defaults)
        self._rebuild()

    def values(self):
        return list(self._paths)


class CheckListDialog(QDialog):
    """Tick which top-level destinations appear in Interactive Mode's tree."""
    def __init__(self, parent, title, info, entries):
        # entries: [(key, label, tooltip, checked)]
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setMinimumWidth(460)
        outer = QVBoxLayout(self)
        lbl = QLabel(info)
        lbl.setWordWrap(True)
        lbl.setObjectName("activeHint")
        outer.addWidget(lbl)
        self.list = QListWidget()
        self.list.setMinimumHeight(220)
        for key, label, tip, checked in entries:
            it = QListWidgetItem(label)
            it.setToolTip(tip)
            it.setData(Qt.UserRole, key)
            it.setFlags(it.flags() | Qt.ItemIsUserCheckable)
            it.setCheckState(Qt.Checked if checked else Qt.Unchecked)
            self.list.addItem(it)
        outer.addWidget(self.list, 1)
        row = QHBoxLayout()
        all_btn = QPushButton("Show all")
        all_btn.clicked.connect(lambda: self._set_all(True))
        none_btn = QPushButton("Hide all")
        none_btn.clicked.connect(lambda: self._set_all(False))
        row.addWidget(all_btn)
        row.addWidget(none_btn)
        row.addStretch(1)
        outer.addLayout(row)
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        outer.addWidget(buttons)

    def _set_all(self, on):
        for i in range(self.list.count()):
            self.list.item(i).setCheckState(Qt.Checked if on else Qt.Unchecked)

    def hidden_keys(self):
        out = []
        for i in range(self.list.count()):
            it = self.list.item(i)
            if it.checkState() != Qt.Checked:
                out.append(it.data(Qt.UserRole))
        return out


class GridCell(QWidget):
    """One tile of Interactive Mode's Multiple view: a thumbnail + file name.
    Selected tiles get a thick blue border and a check badge; the focused tile
    (what Open / the info line refer to) gets a thin outline."""
    pressed = Signal(int, object)        # slot, keyboard modifiers
    clicked = Signal(int, object)        # slot, modifiers (released without dragging)
    dragStart = Signal(int)
    doubleClicked = Signal(int)

    CAPTION_H = 24

    def __init__(self, slot):
        super().__init__()
        self.slot = slot
        self.setObjectName("gridCell")
        self.setMinimumSize(110, 96)
        self.setFocusPolicy(Qt.NoFocus)
        self.setCursor(Qt.OpenHandCursor)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.path = None
        self.name = ""
        self.state = "empty"          # empty | loading | image | nopreview
        self._pix = None
        self._scaled = None
        self._scaled_key = None
        self.selected = False
        self.focused = False
        self._press = None
        self._dragged = False

    def clear(self):
        self.path, self.name, self.state = None, "", "empty"
        self._pix = self._scaled = self._scaled_key = None
        self.selected = self.focused = False
        self.setToolTip("")
        self.setCursor(Qt.ArrowCursor)
        self.update()

    def set_item(self, path, name, image, state):
        if path != self.path or state != self.state or (
                image is not None and self._pix is None):
            self._pix = QPixmap.fromImage(image) if image is not None else None
            self._scaled = self._scaled_key = None
        self.path, self.name, self.state = path, name, state
        self.setToolTip(f"{name}\n\nClick to select \u00b7 Ctrl+click to add/remove \u00b7 "
                        "drag onto a folder to file \u00b7 double-click to open")
        self.setCursor(Qt.OpenHandCursor)
        self.update()

    def thumb_pixmap(self):
        return self._pix

    def _image_rect(self):
        return self.rect().adjusted(8, 8, -8, -(8 + self.CAPTION_H))

    def paintEvent(self, _e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.setRenderHint(QPainter.SmoothPixmapTransform, True)
        r = self.rect().adjusted(2, 2, -2, -2)
        p.setPen(Qt.NoPen)
        p.setBrush(QColor("#0a0d12" if self.state != "empty" else "#0c1016"))
        p.drawRoundedRect(r, 10, 10)
        area = self._image_rect()
        if self.state == "image" and self._pix is not None and not self._pix.isNull():
            dpr = self.devicePixelRatioF()
            key = (area.width(), area.height(), dpr)
            if self._scaled is None or self._scaled_key != key:
                tgt = QSize(max(1, int(area.width() * dpr)), max(1, int(area.height() * dpr)))
                sc = self._pix.scaled(tgt, Qt.KeepAspectRatio, Qt.SmoothTransformation)
                sc.setDevicePixelRatio(dpr)
                self._scaled, self._scaled_key = sc, key
            sc = self._scaled
            w = sc.width() / sc.devicePixelRatio()
            h = sc.height() / sc.devicePixelRatio()
            p.drawPixmap(int(area.x() + (area.width() - w) / 2),
                         int(area.y() + (area.height() - h) / 2), sc)
        elif self.state == "nopreview":
            ext = os.path.splitext(self.path or "")[1].upper().lstrip(".") or "FILE"
            f = QFont(self.font())
            f.setPointSize(18)
            f.setBold(True)
            p.setFont(f)
            p.setPen(QColor("#93c5fd"))
            p.drawText(area, Qt.AlignCenter, ext)
        elif self.state == "loading":
            p.setPen(QColor("#5b6574"))
            p.drawText(area, Qt.AlignCenter, "Loading\u2026")
        if self.state != "empty":
            cap = QRect(r.x() + 8, r.bottom() - self.CAPTION_H - 2, r.width() - 16, self.CAPTION_H)
            f2 = QFont(self.font())
            f2.setPointSize(9)
            p.setFont(f2)
            p.setPen(QColor("#e5e7eb" if self.selected else "#aab3c0"))
            p.drawText(cap, Qt.AlignCenter,
                       QFontMetrics(f2).elidedText(self.name, Qt.ElideMiddle, cap.width()))
        if self.selected:
            p.setPen(QPen(QColor("#3b82f6"), 4))
            p.setBrush(Qt.NoBrush)
            p.drawRoundedRect(self.rect().adjusted(3, 3, -3, -3), 10, 10)
            d = 24
            badge = QRect(self.width() - d - 10, 10, d, d)
            p.setPen(Qt.NoPen)
            p.setBrush(QColor("#2563eb"))
            p.drawEllipse(badge)
            p.setPen(QPen(QColor("#ffffff"), 2.5))
            p.drawLine(badge.x() + 6, badge.y() + 12, badge.x() + 10, badge.y() + 17)
            p.drawLine(badge.x() + 10, badge.y() + 17, badge.x() + 18, badge.y() + 7)
        elif self.focused and self.state != "empty":
            p.setPen(QPen(QColor("#64748b"), 1.5))
            p.setBrush(Qt.NoBrush)
            p.drawRoundedRect(self.rect().adjusted(2, 2, -2, -2), 10, 10)
        p.end()

    def resizeEvent(self, e):
        self._scaled = None
        super().resizeEvent(e)

    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton and self.path:
            self._press = e.position().toPoint()
            self._dragged = False
            self.pressed.emit(self.slot, e.modifiers())
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if self._press is None or not self.path or not (e.buttons() & Qt.LeftButton):
            return
        if (e.position().toPoint() - self._press).manhattanLength() < \
                QApplication.startDragDistance():
            return
        self._press = None
        self._dragged = True
        self.dragStart.emit(self.slot)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.LeftButton and self.path and not self._dragged \
                and self._press is not None:
            self.clicked.emit(self.slot, e.modifiers())
        self._press = None
        super().mouseReleaseEvent(e)

    def mouseDoubleClickEvent(self, e):
        if self.path:
            self.doubleClicked.emit(self.slot)


class ImageGrid(QWidget):
    """Interactive Mode's Multiple view: up to GRID_ROWS x GRID_COLS images.
    Owns keyboard handling; the panel owns all state."""
    moveFocus = Signal(int)          # +-1 (left/right) or +-GRID_COLS (up/down)
    pageRequested = Signal(int)      # +-1
    toggleFocused = Signal()
    selectPage = Signal()
    clearSelection = Signal()
    deleteRequested = Signal()
    openFocused = Signal()

    def __init__(self):
        super().__init__()
        self.setObjectName("imageGrid")
        self.setFocusPolicy(Qt.StrongFocus)
        g = QGridLayout(self)
        g.setContentsMargins(0, 0, 0, 0)
        g.setSpacing(10)
        self.cells = []
        for i in range(GRID_ROWS * GRID_COLS):
            c = GridCell(i)
            g.addWidget(c, i // GRID_COLS, i % GRID_COLS)
            self.cells.append(c)
        for r in range(GRID_ROWS):
            g.setRowStretch(r, 1)
        for col in range(GRID_COLS):
            g.setColumnStretch(col, 1)
        self._wheel_acc = 0

    def wheelEvent(self, e):
        self._wheel_acc += e.angleDelta().y()
        while self._wheel_acc >= 120:
            self._wheel_acc -= 120
            self.pageRequested.emit(-1)
        while self._wheel_acc <= -120:
            self._wheel_acc += 120
            self.pageRequested.emit(+1)
        e.accept()

    def keyPressEvent(self, e):
        k, mods = e.key(), e.modifiers()
        if k == Qt.Key_Left:
            self.moveFocus.emit(-1)
        elif k == Qt.Key_Right:
            self.moveFocus.emit(+1)
        elif k == Qt.Key_Up:
            self.moveFocus.emit(-GRID_COLS)
        elif k == Qt.Key_Down:
            self.moveFocus.emit(+GRID_COLS)
        elif k == Qt.Key_PageUp:
            self.pageRequested.emit(-1)
        elif k == Qt.Key_PageDown:
            self.pageRequested.emit(+1)
        elif k == Qt.Key_Space:
            self.toggleFocused.emit()
        elif k == Qt.Key_A and (mods & Qt.ControlModifier):
            self.selectPage.emit()
        elif k == Qt.Key_Escape:
            self.clearSelection.emit()
        elif k == Qt.Key_Delete:
            self.deleteRequested.emit()
        elif k in (Qt.Key_Return, Qt.Key_Enter):
            self.openFocused.emit()
        else:
            super().keyPressEvent(e)


class InteractivePanel(QWidget):
    """Interactive Mode page: source images one at a time on the left, the
    destination folder tree on the right. Reads the same groups/folders the
    Original Mode dashboard shows (including everything a scan mapped)."""

    def __init__(self, win):
        super().__init__()
        self.win = win
        self.images = []              # dicts from list_source_images()
        self.index = 0
        self._cache = OrderedDict()   # path -> QImage (or None = no preview)
        self._in_flight = set()       # normalized paths being moved right now
        self._active = False
        self._dest_dirty = True
        self._expanded = None         # payload ids expanded in the tree (None = first build)
        self._last_filed = None
        # Multiple view state
        self.layout_mode = "multi" if win.settings.get("interactive_layout") == "multi" \
            else "single"
        self.page_start = 0           # images[page_start : page_start + GRID_SIZE] shown
        self.selected = set()         # normalized paths Ctrl/Shift/clicked in the grid
        self._anchor = None           # index Shift+click ranges start from
        self._grid_cache = OrderedDict()

        self.loader = PreviewLoader()
        self.loader.signals.loaded.connect(self._on_loaded)
        self.grid_loader = PreviewLoader(max_side=GRID_THUMB_SIDE)
        self.grid_loader.signals.loaded.connect(self._on_grid_loaded)

        self.watcher = QFileSystemWatcher(self)
        self.watcher.directoryChanged.connect(self._schedule_refresh)
        self._refresh_timer = QTimer(self)
        self._refresh_timer.setSingleShot(True)
        self._refresh_timer.setInterval(450)
        self._refresh_timer.timeout.connect(lambda: self.refresh_sources())

        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        self.splitter = QSplitter(Qt.Horizontal)
        self.splitter.setChildrenCollapsible(False)
        self.splitter.setHandleWidth(6)
        lay.addWidget(self.splitter)

        # ---------- left: sources ----------
        left = QWidget()
        left.setObjectName("srcPane")
        lv = QVBoxLayout(left)
        lv.setContentsMargins(14, 10, 8, 10)
        lv.setSpacing(8)
        head = QHBoxLayout()
        t = QLabel("SOURCES")
        t.setObjectName("paneTitle")
        head.addWidget(t)
        self.layout_btn = QPushButton()
        self.layout_btn.setObjectName("layoutToggle")
        self.layout_btn.setCheckable(True)
        self.layout_btn.setCursor(Qt.PointingHandCursor)
        self.layout_btn.clicked.connect(self.toggle_layout)
        head.addWidget(self.layout_btn, 0)
        self.src_combo = QComboBox()
        self.src_combo.setMinimumWidth(170)
        self.src_combo.setToolTip("Show images from every source folder, or just one")
        self.src_combo.currentIndexChanged.connect(lambda _i: self.refresh_sources())
        head.addWidget(self.src_combo, 0)
        head.addStretch(1)
        self.sort_combo = QComboBox()
        for label, key in (("Newest first", "newest"), ("Oldest first", "oldest"),
                           ("Name A\u2013Z", "name")):
            self.sort_combo.addItem(label, key)
        i = self.sort_combo.findData(self.win.settings.get("interactive_sort", "newest"))
        self.sort_combo.setCurrentIndex(max(0, i))
        self.sort_combo.currentIndexChanged.connect(self._sort_changed)
        head.addWidget(self.sort_combo, 0)
        self.sources_btn = QPushButton("Sources\u2026")
        self.sources_btn.setToolTip("Choose which folders the images come from")
        self.sources_btn.clicked.connect(self.manage_sources)
        head.addWidget(self.sources_btn, 0)
        self.reload_btn = QPushButton("\u21bb")
        self.reload_btn.setToolTip("Re-read the source folders")
        self.reload_btn.setFixedWidth(34)
        self.reload_btn.clicked.connect(lambda: self.refresh_sources())
        head.addWidget(self.reload_btn, 0)
        head.addSpacing(6)
        self.delete_btn = QPushButton("\U0001F5D1  Delete")
        self.delete_btn.setObjectName("deleteBtn")
        self.delete_btn.setCursor(Qt.PointingHandCursor)
        self.delete_btn.setToolTip(
            "Delete the image shown below from your computer and move on to the "
            "next one.\nOn Windows it goes to the Recycle Bin.  (Delete key)")
        self.delete_btn.clicked.connect(self.delete_current)
        head.addWidget(self.delete_btn, 0)
        lv.addLayout(head)

        self.stage = ImageStage()
        self.stage.prevRequested.connect(lambda: self.step(-1))
        self.stage.nextRequested.connect(lambda: self.step(+1))
        self.stage.openRequested.connect(self._open_image)
        self.stage.deleteRequested.connect(self.delete_current)

        self.grid = ImageGrid()
        for c in self.grid.cells:
            c.pressed.connect(self._cell_pressed)
            c.clicked.connect(self._cell_clicked)
            c.dragStart.connect(self._cell_drag)
            c.doubleClicked.connect(self._cell_open)
        self.grid.moveFocus.connect(self.move_focus)
        self.grid.pageRequested.connect(self.page)
        self.grid.toggleFocused.connect(self._toggle_focused)
        self.grid.selectPage.connect(self.select_page)
        self.grid.clearSelection.connect(self.clear_selection)
        self.grid.deleteRequested.connect(self.delete_current)
        self.grid.openFocused.connect(lambda: self._open_image(self.current_path()))

        self.view_stack = QStackedWidget()
        self.view_stack.addWidget(self.stage)
        self.view_stack.addWidget(self.grid)
        lv.addWidget(self.view_stack, 1)

        self.name_lbl = QLabel("")
        self.name_lbl.setObjectName("stageName")
        self.name_lbl.setTextInteractionFlags(Qt.TextSelectableByMouse)
        lv.addWidget(self.name_lbl)
        self.meta_lbl = QLabel("")
        self.meta_lbl.setObjectName("activeHint")
        lv.addWidget(self.meta_lbl)

        nav = QHBoxLayout()
        self.prev_btn = QPushButton("\u25c0  Prev")
        self.prev_btn.clicked.connect(lambda: self.step(-1))
        nav.addWidget(self.prev_btn)
        self.counter_lbl = QLabel("0 / 0")
        self.counter_lbl.setObjectName("counterLbl")
        self.counter_lbl.setAlignment(Qt.AlignCenter)
        self.counter_lbl.setMinimumWidth(80)
        nav.addWidget(self.counter_lbl)
        self.sel_lbl = QLabel("")
        self.sel_lbl.setObjectName("selCountLbl")
        nav.addWidget(self.sel_lbl)
        self.next_btn = QPushButton("Next  \u25b6")
        self.next_btn.clicked.connect(lambda: self.step(+1))
        nav.addWidget(self.next_btn)
        nav.addStretch(1)
        self.last_lbl = QLabel("")
        self.last_lbl.setObjectName("activeHint")
        nav.addWidget(self.last_lbl, 0)
        self.open_btn = QPushButton("Open")
        self.open_btn.setToolTip("Open this image in your default viewer")
        self.open_btn.clicked.connect(lambda: self._open_image(self.current_path()))
        nav.addWidget(self.open_btn)
        self.undo_btn = QPushButton("Undo")
        self.undo_btn.setToolTip("Undo the last filing (Ctrl+Z)")
        self.undo_btn.clicked.connect(self.win.undo_last)
        nav.addWidget(self.undo_btn)
        lv.addLayout(nav)
        self.splitter.addWidget(left)

        # ---------- right: destinations ----------
        right = QWidget()
        right.setObjectName("destPane")
        rv = QVBoxLayout(right)
        rv.setContentsMargins(8, 10, 14, 10)
        rv.setSpacing(8)
        rhead = QHBoxLayout()
        t2 = QLabel("DESTINATIONS")
        t2.setObjectName("paneTitle")
        rhead.addWidget(t2)
        self.dest_count_lbl = QLabel("")
        self.dest_count_lbl.setObjectName("activeHint")
        rhead.addWidget(self.dest_count_lbl)
        rhead.addStretch(1)
        add_btn = QPushButton("+ Add")
        add_btn.setToolTip("Add a destination folder (with all of its subfolders)")
        add_btn.clicked.connect(self.win.add_folder)
        rhead.addWidget(add_btn)
        choose_btn = QPushButton("Choose\u2026")
        choose_btn.setToolTip("Pick which top-level destinations are listed here")
        choose_btn.clicked.connect(self.choose_destinations)
        rhead.addWidget(choose_btn)
        rv.addLayout(rhead)
        frow = QHBoxLayout()
        self.dest_filter = QLineEdit()
        self.dest_filter.setPlaceholderText("Filter folders\u2026")
        self.dest_filter.setClearButtonEnabled(True)
        self.dest_filter.textChanged.connect(self.apply_filter)
        frow.addWidget(self.dest_filter, 1)
        exp_btn = QPushButton("Expand all")
        exp_btn.clicked.connect(lambda: self.tree.expandAll())
        frow.addWidget(exp_btn)
        col_btn = QPushButton("Collapse")
        col_btn.clicked.connect(lambda: self.tree.collapseAll())
        frow.addWidget(col_btn)
        rv.addLayout(frow)
        self.tree = DestinationTree()
        self.tree.filesDropped.connect(self._on_tree_drop)
        self.tree.fileHereRequested.connect(self._file_current_into)
        self.tree.openRequested.connect(lambda d: self.win.open_in_explorer(d["path"]))
        self.tree.copyPathRequested.connect(lambda d: self.win._copy_path(d["path"]))
        rv.addWidget(self.tree, 1)
        self.dest_hint = QLabel("")
        self.dest_hint.setObjectName("activeHint")
        self.dest_hint.setWordWrap(True)
        rv.addWidget(self.dest_hint)
        self.splitter.addWidget(right)

        sizes = self.win.settings.get("interactive_split") or []
        if isinstance(sizes, list) and len(sizes) == 2 and all(
                isinstance(s, int) and s > 50 for s in sizes):
            self.splitter.setSizes(sizes)
        else:
            self.splitter.setSizes([640, 380])
        self.splitter.setStretchFactor(0, 3)
        self.splitter.setStretchFactor(1, 2)
        self._apply_layout_button()
        self.refresh_hint()

    # ---------------- Single / Multiple ----------------
    def is_multi(self):
        return self.layout_mode == "multi"

    def _apply_layout_button(self):
        multi = self.is_multi()
        self.layout_btn.setChecked(multi)
        # the label names the view you're in
        self.layout_btn.setText("\u25a6  Multiple" if multi else "\u25a2  Single")
        self.layout_btn.setToolTip(
            "Showing up to 6 images. Click a tile to select it, Ctrl+click to add "
            "more, then drag them onto a folder together.\nClick to go back to one "
            "big image." if multi else
            "Showing one big image. Click to show up to 6 at a time "
            "(Ctrl+click several and drag them together).")
        self.next_btn.setText("Next 6  \u25b6" if multi else "Next  \u25b6")
        self.prev_btn.setText("\u25c0  Prev 6" if multi else "\u25c0  Prev")

    def toggle_layout(self):
        self.set_layout("single" if self.is_multi() else "multi")

    def set_layout(self, mode, save=True):
        mode = "multi" if mode == "multi" else "single"
        if mode == "multi":
            # the image you were looking at becomes the first tile
            self.page_start = self.index if self.images else 0
        self.selected.clear()
        self._anchor = None
        self.layout_mode = mode
        self._apply_layout_button()
        self.refresh_hint()
        if self.win.settings.get("interactive_layout") != mode:
            self.win.settings["interactive_layout"] = mode
            if save:
                self.win._save()
        self.show_current()
        self._focus_view()

    def _focus_view(self):
        (self.grid if self.is_multi() and self.images else self.stage).setFocus()

    # ---------------- activation ----------------
    def activate(self):
        self._active = True
        self._rebuild_source_combo()
        self.refresh_sources()
        if self._dest_dirty:
            self.refresh_destinations()
        self.refresh_hint()
        self._focus_view()

    def deactivate(self):
        self._active = False
        dirs = self.watcher.directories()
        if dirs:
            self.watcher.removePaths(dirs)

    def is_active(self):
        return self._active

    # ---------------- sources ----------------
    def source_dirs(self):
        stored = self.win.settings.get("interactive_sources")
        if stored is None:
            return default_source_dirs()
        return [p for p in stored if p]

    def _rebuild_source_combo(self):
        cur = self.src_combo.currentData()
        self.src_combo.blockSignals(True)
        self.src_combo.clear()
        self.src_combo.addItem("All sources", "")
        for d in self.source_dirs():
            self.src_combo.addItem(os.path.basename(d.rstrip("\\/")) or d, d)
            self.src_combo.setItemData(self.src_combo.count() - 1, d, Qt.ToolTipRole)
        i = self.src_combo.findData(cur) if cur else 0
        self.src_combo.setCurrentIndex(max(0, i))
        self.src_combo.blockSignals(False)

    def _active_dirs(self):
        pick = self.src_combo.currentData()
        dirs = self.source_dirs()
        if pick:
            dirs = [d for d in dirs if _norm_path(d) == _norm_path(pick)] or dirs
        return dirs

    def manage_sources(self):
        dlg = PathListDialog(
            self, "Interactive Mode sources",
            "Images sitting directly inside these folders are shown one at a time "
            "on the left so you can drag each one to its destination. "
            "Typical choices: your Desktop and Downloads.",
            self.source_dirs(), defaults=default_source_dirs())
        if dlg.exec() == QDialog.Accepted:
            self.win.settings["interactive_sources"] = dlg.values()
            self.win._save()
            self._rebuild_source_combo()
            self.refresh_sources()
            self.win.log("Interactive sources: " + (", ".join(dlg.values()) or "(none)"))

    def _sort_changed(self, _i):
        self.win.settings["interactive_sort"] = self.sort_combo.currentData()
        self.win._save()
        self.refresh_sources()

    def _schedule_refresh(self, _path=""):
        if self._active:
            self._refresh_timer.start()

    def current_path(self):
        if 0 <= self.index < len(self.images):
            return self.images[self.index]["path"]
        return None

    def refresh_sources(self, keep_path=None):
        """Re-read the source folders, keeping the same image on screen when it
        still exists (else the one that slid into its slot)."""
        keep = keep_path or self.current_path()
        dirs = self._active_dirs()
        items = [x for x in list_source_images(dirs)
                 if _norm_path(x["path"]) not in self._in_flight]
        sort_source_images(items, self.sort_combo.currentData() or "newest")
        self.images = items
        if keep:
            kn = _norm_path(keep)
            idx = next((i for i, x in enumerate(items) if _norm_path(x["path"]) == kn), None)
            if idx is not None:
                self.index = idx
        self.index = max(0, min(self.index, len(self.images) - 1))
        live = {_norm_path(x["path"]) for x in items}
        for k in [k for k in self._cache if _norm_path(k) not in live]:
            self._cache.pop(k, None)
        for k in [k for k in self._grid_cache if _norm_path(k) not in live]:
            self._grid_cache.pop(k, None)
        self.selected &= live
        if self._active:
            want = [d for d in self.source_dirs() if os.path.isdir(d)]
            have = self.watcher.directories()
            if have:
                self.watcher.removePaths(have)
            if want:
                self.watcher.addPaths(want)
        self.show_current()

    def step(self, delta):
        """Prev/Next: one image in Single view, one page of 6 in Multiple."""
        if self.is_multi():
            self.page(delta)
            return
        if not self.images:
            return
        self.index = (self.index + delta) % len(self.images)
        self.show_current()

    def show_current(self):
        n = len(self.images)
        multi = self.is_multi()
        self.prev_btn.setEnabled(n > (GRID_SIZE if multi else 1))
        self.next_btn.setEnabled(n > (GRID_SIZE if multi else 1))
        self.open_btn.setEnabled(n > 0)
        self.delete_btn.setEnabled(n > 0)
        if multi and n > 0:
            self._show_grid()
            return
        self.view_stack.setCurrentWidget(self.stage)
        self.sel_lbl.setText("")
        if n == 0:
            names = ", ".join(os.path.basename(d.rstrip("\\/")) or d
                              for d in self._active_dirs()) or "none set"
            self.stage.show_empty(
                "No images waiting in your source folders.\n\n"
                f"Sources: {names}\n\n"
                "Click \u201cSources\u2026\u201d to choose where images come from.")
            self.counter_lbl.setText("0 / 0")
            self.name_lbl.setText("All clear \u2714")
            self.meta_lbl.setText("")
            return
        it = self.images[self.index]
        path = it["path"]
        self.counter_lbl.setText(f"{self.index + 1} / {n}")
        self.name_lbl.setText(it["name"])
        src = os.path.basename(it["src"].rstrip("\\/")) or it["src"]
        when = datetime.fromtimestamp(it["mtime"]).strftime("%Y-%m-%d %H:%M")
        self._meta_base = f"{src}  \u00b7  {human_bytes(it['size'])}  \u00b7  {when}"
        self.meta_lbl.setText(self._meta_base)
        self.meta_lbl.setToolTip(path)
        if path.lower().endswith(".gif") and self.stage.show_movie(path):
            pass
        elif path in self._cache:
            self._display(path, self._cache[path])
        else:
            self.stage.show_loading(path)
            self.loader.request(path)
        # prefetch the neighbors so stepping feels instant
        for d in (1, -1, 2):
            if n > 1:
                p2 = self.images[(self.index + d) % n]["path"]
                if p2 not in self._cache and not p2.lower().endswith(".gif"):
                    self.loader.request(p2)

    # ---------------- Multiple view ----------------
    def _show_grid(self):
        n = len(self.images)
        self.view_stack.setCurrentWidget(self.grid)
        # always fill the grid when there are enough images (no lonely last
        # tile after images were filed/deleted - the earlier ones slide in)
        self.page_start = max(0, min(self.page_start, n - GRID_SIZE))
        if not (self.page_start <= self.index < self.page_start + GRID_SIZE) \
                or self.index >= n:
            self.index = self.page_start
        for slot, cell in enumerate(self.grid.cells):
            i = self.page_start + slot
            if i >= n:
                cell.clear()
                continue
            it = self.images[i]
            p = it["path"]
            if p in self._grid_cache:
                img = self._grid_cache[p]
                cell.set_item(p, it["name"], img, "image" if img is not None else "nopreview")
            else:
                cell.set_item(p, it["name"], None, "loading")
                self.grid_loader.request(p)
        self._refresh_grid_marks()
        # prefetch the next page so paging feels instant
        for i in range(self.page_start + GRID_SIZE,
                       min(n, self.page_start + 2 * GRID_SIZE)):
            p = self.images[i]["path"]
            if p not in self._grid_cache:
                self.grid_loader.request(p)

    def _refresh_grid_marks(self):
        """Selection / focus outlines + the info line, without reloading tiles."""
        n = len(self.images)
        for slot, cell in enumerate(self.grid.cells):
            i = self.page_start + slot
            if i < n and cell.path:
                cell.selected = _norm_path(cell.path) in self.selected
                cell.focused = (i == self.index)
                cell.update()
        last = min(n, self.page_start + GRID_SIZE)
        self.counter_lbl.setText(f"{self.page_start + 1}\u2013{last} / {n}")
        k = len(self.selected)
        self.sel_lbl.setText(f"\u2714 {k} selected" if k else "")
        if 0 <= self.index < n:
            it = self.images[self.index]
            self.name_lbl.setText(it["name"])
            src = os.path.basename(it["src"].rstrip("\\/")) or it["src"]
            when = datetime.fromtimestamp(it["mtime"]).strftime("%Y-%m-%d %H:%M")
            self._meta_base = f"{src}  \u00b7  {human_bytes(it['size'])}  \u00b7  {when}"
            self.meta_lbl.setText(self._meta_base)
            self.meta_lbl.setToolTip(it["path"])

    def _on_grid_loaded(self, path, img):
        if self.win._closing:
            return
        self._grid_cache[path] = img
        self._grid_cache.move_to_end(path)
        while len(self._grid_cache) > GRID_CACHE:
            self._grid_cache.popitem(last=False)
        if not self.is_multi():
            return
        for cell in self.grid.cells:
            if cell.path == path and cell.state == "loading":
                cell.set_item(path, cell.name, img, "image" if img is not None else "nopreview")
                cell.selected = _norm_path(path) in self.selected
                cell.update()

    def page(self, delta):
        n = len(self.images)
        if n <= GRID_SIZE:
            return
        if delta > 0:
            self.page_start = self.page_start + GRID_SIZE \
                if self.page_start + GRID_SIZE < n else 0
        else:
            self.page_start = max(0, self.page_start - GRID_SIZE) \
                if self.page_start > 0 else max(0, n - GRID_SIZE)
        self.index = self.page_start
        self.show_current()

    def move_focus(self, delta):
        """Arrow keys in the grid: move the focused tile, paging when needed."""
        n = len(self.images)
        if not n:
            return
        self.index = (self.index + delta) % n
        if self.index >= self.page_start + GRID_SIZE:
            self.page_start = self.index - (self.index - self.page_start) % GRID_SIZE \
                if self.index - self.page_start < 2 * GRID_SIZE else self.index
        elif self.index < self.page_start:
            self.page_start = max(0, self.index - GRID_SIZE + 1) \
                if self.page_start - self.index <= GRID_SIZE else self.index
        self.show_current()

    def _cell_index(self, slot):
        i = self.page_start + slot
        return i if 0 <= i < len(self.images) else None

    def _cell_pressed(self, slot, mods):
        i = self._cell_index(slot)
        if i is None:
            return
        p = _norm_path(self.images[i]["path"])
        if mods & Qt.ControlModifier:
            self.selected ^= {p}                 # Ctrl+click: add / remove
            self._anchor = i
        elif mods & Qt.ShiftModifier and self._anchor is not None:
            a, b = sorted((self._anchor, i))
            self.selected |= {_norm_path(x["path"]) for x in self.images[a:b + 1]}
        elif p not in self.selected:
            self.selected = {p}                   # plain press on a new tile
            self._anchor = i
        # (plain press on an already-selected tile keeps the group, so it can
        #  be dragged together; releasing without a drag narrows to that tile)
        self.index = i
        self.grid.setFocus()
        self._refresh_grid_marks()

    def _cell_clicked(self, slot, mods):
        i = self._cell_index(slot)
        if i is None or mods & (Qt.ControlModifier | Qt.ShiftModifier):
            return
        self.selected = {_norm_path(self.images[i]["path"])}
        self._anchor = i
        self._refresh_grid_marks()

    def _cell_open(self, slot):
        i = self._cell_index(slot)
        if i is not None:
            self._open_image(self.images[i]["path"])

    def _toggle_focused(self):
        p = self.current_path()
        if p:
            self.selected ^= {_norm_path(p)}
            self._anchor = self.index
            self._refresh_grid_marks()

    def select_page(self):
        self.selected |= {_norm_path(x["path"])
                          for x in self.images[self.page_start:self.page_start + GRID_SIZE]}
        self._refresh_grid_marks()

    def clear_selection(self):
        self.selected.clear()
        self._refresh_grid_marks()

    def selected_paths(self):
        """Selected images in list order (selection can span pages)."""
        return [x["path"] for x in self.images if _norm_path(x["path"]) in self.selected]

    def drag_paths_for(self, i):
        """Dragging a selected tile carries the whole selection; an unselected
        tile goes alone."""
        p = self.images[i]["path"]
        if _norm_path(p) in self.selected:
            return self.selected_paths()
        return [p]

    def build_grid_mime(self, paths):
        mime = QMimeData()
        mime.setUrls([QUrl.fromLocalFile(p) for p in paths])
        mime.setData(STAGE_MIME, "\n".join(paths).encode("utf-8"))
        return mime

    def grid_drag_pixmap(self, paths):
        """A small fanned stack of the dragged thumbnails with a count badge."""
        thumbs = []
        for p in paths[:3]:
            img = self._grid_cache.get(p)
            if img is not None:
                thumbs.append(QPixmap.fromImage(img).scaled(
                    150, 150, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        W, H = 200, 190
        pm = QPixmap(W, H)
        pm.fill(Qt.transparent)
        q = QPainter(pm)
        q.setRenderHint(QPainter.Antialiasing, True)
        if not thumbs:
            q.setBrush(QColor("#1f2532"))
            q.setPen(QColor("#3b82f6"))
            q.drawRoundedRect(20, 20, 150, 110, 10, 10)
        for k, t in enumerate(reversed(thumbs)):
            off = (len(thumbs) - 1 - k) * 12
            q.drawPixmap(10 + off, 10 + off, t)
            q.setPen(QPen(QColor("#e5e7eb"), 2))
            q.setBrush(Qt.NoBrush)
            q.drawRect(10 + off, 10 + off, t.width(), t.height())
        if len(paths) > 1:
            q.setPen(Qt.NoPen)
            q.setBrush(QColor("#2563eb"))
            q.drawEllipse(W - 54, H - 54, 46, 46)
            f = QFont()
            f.setPointSize(13)
            f.setBold(True)
            q.setFont(f)
            q.setPen(QColor("#ffffff"))
            q.drawText(QRect(W - 54, H - 54, 46, 46), Qt.AlignCenter, str(len(paths)))
        q.end()
        return pm

    def _cell_drag(self, slot):
        i = self._cell_index(slot)
        if i is None:
            return
        paths = self.drag_paths_for(i)
        drag = QDrag(self.grid.cells[slot])
        drag.setMimeData(self.build_grid_mime(paths))
        pm = self.grid_drag_pixmap(paths)
        drag.setPixmap(pm)
        drag.setHotSpot(QPoint(pm.width() // 2, pm.height() // 2))
        # Copy only, for the same reason as the single view: a drop outside the
        # app must never let the shell move the originals.
        drag.exec(Qt.CopyAction, Qt.CopyAction)

    def _display(self, path, img):
        if img is None:
            self.stage.show_no_preview(path)
            self.meta_lbl.setText(self._meta_base)
        else:
            self.stage.show_image(path, img)
            self.meta_lbl.setText(f"{self._meta_base}  \u00b7  {img.width()} \u00d7 {img.height()}")

    def _on_loaded(self, path, img):
        if self.win._closing:
            return
        self._cache[path] = img
        self._cache.move_to_end(path)
        while len(self._cache) > PREVIEW_CACHE:
            self._cache.popitem(last=False)
        if path == self.current_path() and self.stage.current_path() == path \
                and self.stage.state() == "loading":
            self._display(path, img)

    def delete_current(self):
        """Delete button / Delete key. Single view: the image on screen.
        Multiple view: the selected images (or the focused one if none)."""
        if self.is_multi():
            paths = self.selected_paths() or ([self.current_path()]
                                              if self.current_path() else [])
            if len(paths) > 1:
                self.delete_paths(paths)
                return
            if paths:
                self.index = next((i for i, x in enumerate(self.images)
                                   if x["path"] == paths[0]), self.index)
        path = self.current_path()
        if not path:
            return
        name = os.path.basename(path)
        if self.win.settings.get("confirm_delete", False):
            r = QMessageBox.question(
                self, "Delete image",
                f"Delete \u201c{name}\u201d from your computer?\n\n{path}",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
            if r != QMessageBox.Yes:
                return
        # let go of anything holding the file (animated GIF player, cached image)
        self.stage.show_loading(path)
        self._cache.pop(path, None)
        try:
            how = send_to_trash(path)
        except Exception as e:
            self.win.log(f"ERROR deleting {path}: {e}")
            QMessageBox.warning(self, "Could not delete",
                                f"\u201c{name}\u201d could not be deleted:\n\n{e}")
            # re-read the folder: if the file vanished on its own, drop it from
            # the list (otherwise it would sit there undeletable forever)
            self.refresh_sources(keep_path=path)
            return
        norm = _norm_path(path)
        self.images = [x for x in self.images if _norm_path(x["path"]) != norm]
        self.selected.discard(norm)
        self._grid_cache.pop(path, None)
        self.index = max(0, min(self.index, len(self.images) - 1))  # next slides in
        where = "to the Recycle Bin" if how == "recycled" else "permanently"
        self.win.log(f"Deleted {name} {where} ({os.path.dirname(path)})")
        self.win.statusBar().showMessage(
            f"Deleted \u201c{name}\u201d" + (" \u2014 it's in the Recycle Bin"
                                              if how == "recycled" else ""), 5000)
        self._last_filed = f"Deleted {name}"
        fm = QFontMetrics(self.last_lbl.font())
        self.last_lbl.setText(fm.elidedText(self._last_filed, Qt.ElideMiddle, 320))
        self.last_lbl.setToolTip(f"{self._last_filed} ({where})")
        self.show_current()
        self._focus_view()

    def delete_paths(self, paths):
        """Multiple view: delete several images (always asks first)."""
        names = [os.path.basename(p) for p in paths]
        shown = "\n".join(names[:8]) + (f"\n\u2026 and {len(names) - 8} more"
                                         if len(names) > 8 else "")
        r = QMessageBox.question(
            self, "Delete images",
            f"Delete these {len(paths)} images from your computer?\n\n{shown}",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if r != QMessageBox.Yes:
            return
        first = min((i for i, x in enumerate(self.images) if x["path"] in set(paths)),
                    default=self.index)
        done, failed, recycled = [], [], 0
        for p in paths:
            self._cache.pop(p, None)
            self._grid_cache.pop(p, None)
            try:
                if send_to_trash(p) == "recycled":
                    recycled += 1
                done.append(p)
            except Exception as e:
                failed.append((p, e))
                self.win.log(f"ERROR deleting {p}: {e}")
        gone = {_norm_path(p) for p in done}
        self.images = [x for x in self.images if _norm_path(x["path"]) not in gone]
        self.selected -= gone
        self.index = max(0, min(first, len(self.images) - 1))
        where = "to the Recycle Bin" if recycled == len(done) and done else \
            ("permanently" if not recycled else "(Recycle Bin where available)")
        if done:
            self.win.log(f"Deleted {len(done)} images {where}: " + ", ".join(
                os.path.basename(p) for p in done))
            self._last_filed = f"Deleted {len(done)} images"
            self.last_lbl.setText(self._last_filed)
            self.last_lbl.setToolTip(f"{self._last_filed} ({where})")
            self.win.statusBar().showMessage(
                f"Deleted {len(done)} images" + (" \u2014 they're in the Recycle Bin"
                                                 if recycled else ""), 5000)
        if failed:
            QMessageBox.warning(self, "Could not delete",
                                f"{len(failed)} image(s) could not be deleted:\n\n" +
                                "\n".join(f"{os.path.basename(p)}: {e}" for p, e in failed[:6]))
            self.refresh_sources()
            return
        self.show_current()
        self._focus_view()

    def _open_image(self, path):
        if path and not open_path_default(path):
            QMessageBox.warning(self, APP_NAME, f"Could not open:\n{path}")

    # ---------------- filing ----------------
    def _target_mapping(self, data):
        """Resolve a tree payload to the Mapping the shared drop pipeline needs."""
        if data.get("kind") == "folder":
            return self.win._mapping_by_id(data["id"])
        g = self.win._group_by_id(data["id"])
        if g and g.path:
            return Mapping(id=f"_grp_{g.id}", name=g.name, path=g.path)
        return None

    def _on_tree_drop(self, data, paths):
        m = self._target_mapping(data)
        if m is None:
            return
        queued = self.win.handle_drop(m, paths)
        if queued:
            self.after_filed(paths, m.name)

    def _file_current_into(self, data):
        """Tree right-click "File here": the selection in Multiple view, else
        the image on screen."""
        paths = self.selected_paths() if self.is_multi() else []
        if not paths and self.current_path():
            paths = [self.current_path()]
        if paths:
            self._on_tree_drop(data, paths)

    def after_filed(self, paths, dest_name):
        """Advance past what was just filed without waiting for the transfer."""
        mode = self.win.settings.get("mode", "move")
        filed = {_norm_path(p) for p in paths}
        cur = self.current_path()
        hit_current = cur is not None and _norm_path(cur) in filed
        if mode == "move":
            if self.is_multi():
                # the remaining images slide up into the freed tiles
                first = min((i for i, x in enumerate(self.images)
                             if _norm_path(x["path"]) in filed), default=self.index)
                self.index = first
            self._in_flight |= filed
            self.images = [x for x in self.images if _norm_path(x["path"]) not in filed]
            for k in [k for k in self._cache if _norm_path(k) in filed]:
                self._cache.pop(k, None)
            for k in [k for k in self._grid_cache if _norm_path(k) in filed]:
                self._grid_cache.pop(k, None)
            self.index = max(0, min(self.index, len(self.images) - 1))
        elif hit_current and self.images and not self.is_multi():
            self.index = (self.index + 1) % len(self.images)
        self.selected -= filed
        names = [os.path.basename(p) for p in paths]
        verb = "Moved" if mode == "move" else "Copied"
        what = names[0] if len(names) == 1 else f"{len(names)} items"
        self._last_filed = f"{verb} {what} \u2192 {dest_name}"
        fm = QFontMetrics(self.last_lbl.font())
        self.last_lbl.setText(fm.elidedText(self._last_filed, Qt.ElideMiddle, 320))
        self.last_lbl.setToolTip(self._last_filed)
        self.show_current()
        self._focus_view()

    def on_batch_done(self, summary):
        if summary.get("mode") != "undo":
            for p in summary.get("files", []) or []:
                self._in_flight.discard(_norm_path(p))
        else:
            self.last_lbl.setText("Undone \u21b6")
            self.last_lbl.setToolTip("")
        if self._active:
            self.refresh_sources()

    # ---------------- destinations ----------------
    def refresh_hint(self):
        mode = self.win.settings.get("mode", "move")
        verb = "move" if mode == "move" else "copy"
        what = "an image (or your Ctrl+click selection)" if self.is_multi() else "the image"
        self.dest_hint.setText(
            f"Drag {what} onto any folder to {verb} it there. Hover over a "
            f"collapsed folder while dragging to open it. Right-click a folder for more.")

    def mark_destinations_dirty(self):
        self._dest_dirty = True
        if self._active:
            self.refresh_destinations()

    def _remember_expanded(self):
        if self.tree.topLevelItemCount() == 0:
            return
        # merge, don't replace: items not in the tree right now (hidden roots)
        # keep whatever expansion state they had last time they were shown
        exp, seen = set(), set()
        stack = [self.tree.topLevelItem(i) for i in range(self.tree.topLevelItemCount())]
        while stack:
            it = stack.pop()
            d = DestinationTree.payload(it)
            if d:
                seen.add(d["id"])
                if it.isExpanded():
                    exp.add(d["id"])
            stack.extend(it.child(i) for i in range(it.childCount()))
        self._expanded = ((self._expanded or set()) - seen) | exp

    def top_level_entries(self):
        """[(key, label, tooltip)] for the top-level groups and folders."""
        win = self.win
        out = []
        for g in sorted((g for g in win.groups if not g.parent),
                        key=lambda g: g.name.casefold()):
            out.append((g.id, g.name, g.path or "(organizer group, no folder)"))
        for m in sorted((m for m in win.mappings if not m.group),
                        key=lambda m: (not m.favorite, m.name.casefold())):
            out.append((m.id, m.name, m.path))
        return out

    def _group_icon(self, g, top):
        st = self.style()
        if top and g.path:
            p = g.path.replace("/", "\\")
            if p.startswith("\\\\"):
                return st.standardIcon(QStyle.SP_DriveNetIcon)
            if len(p) <= 3 and p[1:2] == ":":
                return st.standardIcon(QStyle.SP_DriveHDIcon)
        return st.standardIcon(QStyle.SP_DirIcon)

    def refresh_destinations(self):
        win = self.win
        self._remember_expanded()
        cur = DestinationTree.payload(self.tree.currentItem())
        cur_id = cur["id"] if cur else None
        self.tree.setUpdatesEnabled(False)
        self.tree.clear()
        hidden = set(win.settings.get("interactive_hidden_roots") or [])
        kids = {}
        for g in win.groups:
            kids.setdefault(g.parent or "", []).append(g)
        members = {}
        for m in win.mappings:
            members.setdefault(m.group or "", []).append(m)
        muted = QColor("#6b7280")
        counts = {"dest": 0}
        restore = None

        def add_folder(parent, m):
            nonlocal restore
            it = QTreeWidgetItem([m.name])
            it.setData(0, Qt.UserRole, {"kind": "folder", "id": m.id,
                                        "path": m.path, "name": m.name})
            it.setToolTip(0, m.path)
            it.setIcon(0, _dot_icon(m.color))
            counts["dest"] += 1
            if m.id == cur_id:
                restore = it
            return it

        def add_group(parent, g, top, seen):
            nonlocal restore
            if g.id in seen:
                return None
            seen = seen | {g.id}
            label = g.name if g.path else f"{g.name}   (no folder)"
            it = QTreeWidgetItem([label])
            it.setData(0, Qt.UserRole, {"kind": "group", "id": g.id,
                                        "path": g.path, "name": g.name})
            it.setToolTip(0, g.path or "Organizer group \u2014 no folder path set, so it "
                                       "can't receive files itself. Its folders can.")
            it.setIcon(0, self._group_icon(g, top))
            if g.path:
                counts["dest"] += 1
            else:
                it.setForeground(0, muted)
            for sub in sorted(kids.get(g.id, []), key=lambda x: x.name.casefold()):
                c = add_group(it, sub, False, seen)
                if c is not None:
                    it.addChild(c)
            for m in sorted(members.get(g.id, []), key=lambda x: x.name.casefold()):
                it.addChild(add_folder(it, m))
            if g.id == cur_id:
                restore = it
            return it

        tops = []
        for g in sorted(kids.get("", []), key=lambda x: x.name.casefold()):
            if g.id not in hidden:
                tops.append(add_group(None, g, True, set()))
        for m in sorted(members.get("", []), key=lambda x: (not x.favorite, x.name.casefold())):
            if m.id not in hidden:
                tops.append(add_folder(None, m))
        self.tree.addTopLevelItems([t for t in tops if t is not None])

        # restore expansion (first build: open the top level one step)
        stack = [self.tree.topLevelItem(i) for i in range(self.tree.topLevelItemCount())]
        first = self._expanded is None
        while stack:
            it = stack.pop()
            d = DestinationTree.payload(it)
            if first:
                if it.parent() is None and it.childCount():
                    it.setExpanded(True)
            elif d and d["id"] in self._expanded:
                it.setExpanded(True)
            stack.extend(it.child(i) for i in range(it.childCount()))
        if restore is not None:
            self.tree.setCurrentItem(restore)
        self.tree.setUpdatesEnabled(True)
        self._dest_dirty = False
        n_hidden = len([k for k in hidden if win._group_by_id(k) or win._mapping_by_id(k)])
        txt = f"{counts['dest']} folder(s)"
        if n_hidden:
            txt += f" \u00b7 {n_hidden} hidden"
        self.dest_count_lbl.setText(txt)
        if self.tree.topLevelItemCount() == 0:
            empty = QTreeWidgetItem(["No destinations yet \u2014 click \u201c+ Add\u201d "
                                     "to add a drive or folder."])
            empty.setForeground(0, muted)
            empty.setFlags(Qt.NoItemFlags)
            self.tree.addTopLevelItem(empty)
        if self.dest_filter.text().strip():
            self.apply_filter(self.dest_filter.text())

    def apply_filter(self, text):
        q = (text or "").strip().casefold()

        def visit(it):
            d = DestinationTree.payload(it) or {}
            own = (not q) or q in (d.get("name") or it.text(0)).casefold() \
                or q in (d.get("path") or "").casefold()
            any_child = False
            for i in range(it.childCount()):
                if visit(it.child(i)):
                    any_child = True
            show = own or any_child
            it.setHidden(not show)
            if q and any_child:
                it.setExpanded(True)
            return show

        for i in range(self.tree.topLevelItemCount()):
            visit(self.tree.topLevelItem(i))

    def choose_destinations(self):
        hidden = set(self.win.settings.get("interactive_hidden_roots") or [])
        entries = [(k, lbl, tip, k not in hidden) for k, lbl, tip in self.top_level_entries()]
        if not entries:
            QMessageBox.information(self, APP_NAME,
                                    "No destinations yet \u2014 click \u201c+ Add\u201d first.")
            return
        dlg = CheckListDialog(
            self, "Choose destinations",
            "Tick the drives / folders to list on the right. Each one shows "
            "with all of its subfolders.", entries)
        if dlg.exec() == QDialog.Accepted:
            self.win.settings["interactive_hidden_roots"] = dlg.hidden_keys()
            self.win._save()
            self.refresh_destinations()

    def save_state(self):
        self.win.settings["interactive_split"] = [int(s) for s in self.splitter.sizes()]

    def shutdown(self):
        for ld in (self.loader, self.grid_loader):
            try:
                ld.shutdown()
            except Exception:
                pass


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(f"{APP_NAME} v{APP_VERSION}")
        self.resize(960, 720)

        self.mappings, self.groups, self.settings = load_config()
        self.tiles = {}            # mapping id -> DropTile
        self.group_tiles = {}      # group id -> GroupTile
        self.active_id = self.mappings[0].id if self.mappings else None
        self.current_group = None  # None = top level, else a group id
        self.selected_ids = set()  # mapping ids selected via Ctrl+click
        self.selected_group_ids = set()  # group ids selected via Ctrl+click
        self.undo_stack = []       # list of undo-record lists
        self._busy = False
        self._closing = False     # set during closeEvent so late async results are ignored

        self.transfer = TransferManager()
        self.transfer.signals.started.connect(self._on_transfer_started)
        self.transfer.signals.progress.connect(self._on_progress)
        self.transfer.signals.fileProgress.connect(self._on_file_progress)
        self.transfer.signals.log.connect(self.log)
        self.transfer.signals.batchDone.connect(self._on_batch_done)
        self.transfer.start()
        self.progress_dialog = TransferProgressDialog(self)

        self.checker = ReachabilityChecker()
        self.checker.signals.result.connect(self._on_reachable)

        self.thumbs = ThumbnailLoader()
        self.thumbs.signals.result.connect(self._on_thumb)

        self.scanner = DriveScanner()
        self.scanner.signals.resultReady.connect(self._on_scan_result)
        self.scanner.signals.error.connect(self._on_scan_error)
        self._scan_busy = False
        self._scan_pending = 0
        self._pending_imports = {}   # norm path -> Add-folder values awaiting their tree scan
        self._cover_seq = {}         # tile key -> latest cover request number
        self._cover_inflight = set() # tile keys with a cover request outstanding
        self._shuffle_covers = True  # next grid build re-picks every visible cover

        self._build_ui()
        self._apply_wallpaper()
        self._rebuild_grid()
        self._update_active_zone()
        self.recheck_all()

        self.timer = QTimer(self)
        self.timer.timeout.connect(self.recheck_all)
        self._apply_timer()

        self._install_shortcuts()
        self.set_view_mode(self.settings.get("view_mode", "original"), save=False)

        if self.settings.get("auto_scan_startup", True) and self.settings.get("scan_roots"):
            self.scan_now()

    # ---- UI construction ----
    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        outer = QVBoxLayout(central)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(0)

        # toolbar row
        bar = QWidget()
        bar.setObjectName("toolbar")
        tb = QHBoxLayout(bar)
        tb.setContentsMargins(14, 10, 14, 10)
        tb.setSpacing(8)

        title = QLabel(f"{APP_NAME}  v{APP_VERSION}")
        title.setObjectName("appTitle")
        tb.addWidget(title)

        self.folder_count_lbl = QLabel()
        self.folder_count_lbl.setObjectName("activeHint")
        tb.addSpacing(14)
        tb.addWidget(self.folder_count_lbl)

        self.mode_btn = QPushButton()
        self.mode_btn.setCheckable(True)
        self.mode_btn.setChecked(self.settings.get("mode", "move") == "move")
        self.mode_btn.clicked.connect(self._toggle_mode)
        self._refresh_mode_btn()
        tb.addSpacing(8)
        tb.addWidget(self.mode_btn)

        # Original / Interactive view switch (segmented pair)
        tb.addSpacing(10)
        self.view_group = QButtonGroup(self)
        self.view_group.setExclusive(True)
        self.view_orig_btn = QPushButton("Original Mode")
        self.view_inter_btn = QPushButton("Interactive Mode")
        for b, key, tip in (
            (self.view_orig_btn, "original",
             "Tile dashboard: drag files from Explorer onto folder tiles."),
            (self.view_inter_btn, "interactive",
             "Split view: your Desktop/Downloads images shown large one at a time on "
             "the left; drag each onto a folder in the tree on the right. (Ctrl+I)"),
        ):
            b.setCheckable(True)
            b.setObjectName("viewSeg")
            b.setToolTip(tip)
            b.clicked.connect(lambda _c=False, k=key: self.set_view_mode(k))
            self.view_group.addButton(b)
            tb.addWidget(b)

        tb.addStretch(1)

        self.search = QLineEdit()
        self.search.setPlaceholderText("Search folders...")
        self.search.setClearButtonEnabled(True)
        self.search.setFixedWidth(200)
        self.search.textChanged.connect(self._rebuild_grid)
        tb.addWidget(self.search)

        self.cat_filter = QComboBox()
        self.cat_filter.setFixedWidth(150)
        self.cat_filter.currentIndexChanged.connect(self._rebuild_grid)
        tb.addWidget(self.cat_filter)

        self.tb_buttons = {}
        for text, slot in [
            ("Add folder", self.add_folder),
            ("New group", self.create_group_here),
            ("Scan now", self.scan_now),
            ("Undo", self.undo_last),
            ("Re-check", self.recheck_all),
            ("Log", self.toggle_log),
            ("Settings", self.open_settings),
        ]:
            b = QPushButton(text)
            b.clicked.connect(slot)
            tb.addWidget(b)
            self.tb_buttons[text] = b

        outer.addWidget(bar)

        # Body: a stack with the Original dashboard page and the Interactive page.
        self.original_page = QWidget()
        page = QVBoxLayout(self.original_page)
        page.setContentsMargins(0, 0, 0, 0)
        page.setSpacing(0)

        # active zone
        wrap = QWidget()
        wl = QVBoxLayout(wrap)
        wl.setContentsMargins(16, 14, 16, 6)
        self.active_zone = ActiveZone()
        self.active_zone.filesDropped.connect(self._drop_on_active)
        self.active_zone.prevClicked.connect(lambda: self.cycle_target(-1))
        self.active_zone.nextClicked.connect(lambda: self.cycle_target(+1))
        wl.addWidget(self.active_zone)
        page.addWidget(wrap)

        # breadcrumb (shown only inside a group)
        self.crumb = QWidget()
        self.crumb.setObjectName("crumb")
        cl = QHBoxLayout(self.crumb)
        cl.setContentsMargins(16, 4, 16, 4)
        cl.setSpacing(8)
        self.up_btn = GroupDropButton("\u2191  Up")
        self.up_btn.clicked.connect(self.go_up)
        self.up_btn.groupDropped.connect(self._drop_group_up)
        self.up_btn.foldersDropped.connect(self._drop_folders_up)
        self.up_btn.setToolTip("Go up \u00b7 or drop groups/folders here to move them up a level")
        cl.addWidget(self.up_btn, 0)
        self.home_btn = GroupDropButton("\u2302  Home")
        self.home_btn.clicked.connect(self.go_home)
        self.home_btn.groupDropped.connect(self._drop_group_top)
        self.home_btn.foldersDropped.connect(self._drop_folders_top)
        self.home_btn.setToolTip("Go home \u00b7 or drop groups/folders here to move them to the top")
        cl.addWidget(self.home_btn, 0)
        self.crumb_label = QLabel("")
        self.crumb_label.setObjectName("crumbLabel")
        cl.addWidget(self.crumb_label, 1)
        self.subgroup_btn = QPushButton("+ New subgroup")
        self.subgroup_btn.clicked.connect(self.create_group_here)
        cl.addWidget(self.subgroup_btn, 0)
        self.crumb.hide()
        page.addWidget(self.crumb)

        # selection action bar (shown when one or more tiles are Ctrl-selected)
        self.sel_bar = QWidget()
        self.sel_bar.setObjectName("selBar")
        sl = QHBoxLayout(self.sel_bar)
        sl.setContentsMargins(16, 4, 16, 4)
        sl.setSpacing(8)
        self.sel_label = QLabel("0 selected")
        self.sel_label.setObjectName("selLabel")
        sl.addWidget(self.sel_label, 0)
        sl.addStretch(1)
        self.group_btn = QPushButton("Group \u25be")
        self.group_btn.clicked.connect(self._open_group_menu)
        sl.addWidget(self.group_btn, 0)
        self.remove_sel_btn = QPushButton("Remove selected")
        self.remove_sel_btn.setStyleSheet("QPushButton{color:#ef4444;}")
        self.remove_sel_btn.clicked.connect(self.remove_selected)
        sl.addWidget(self.remove_sel_btn, 0)
        self.clear_sel_btn = QPushButton("Clear")
        self.clear_sel_btn.clicked.connect(self.clear_selection)
        sl.addWidget(self.clear_sel_btn, 0)
        self.sel_bar.hide()
        page.addWidget(self.sel_bar)

        # scrollable tile grid
        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setObjectName("scroll")
        self.grid_host = QWidget()
        self.flow = FlowLayout(self.grid_host, margin=16, spacing=14)
        self.scroll.setWidget(self.grid_host)
        # transparent so the wallpaper behind shows through the gaps between tiles
        self.scroll.setStyleSheet("QScrollArea{background:transparent;border:none;}")
        self.scroll.viewport().setStyleSheet("background:transparent;")
        self.grid_host.setStyleSheet("background:transparent;")
        self.canvas = WallpaperWidget()
        canvas_lay = QVBoxLayout(self.canvas)
        canvas_lay.setContentsMargins(0, 0, 0, 0)
        canvas_lay.addWidget(self.scroll)
        page.addWidget(self.canvas, 1)

        self.interactive = InteractivePanel(self)
        self.stack = QStackedWidget()
        self.stack.addWidget(self.original_page)
        self.stack.addWidget(self.interactive)
        outer.addWidget(self.stack, 1)

        self.empty_lbl = QLabel(
            "No folders yet.\n\nClick \u201cAdd folder\u201d, give it a name and a path\n"
            "(local like D:\\Pics\\Funny, or network like \\\\NAS\\share\\Funny),\n"
            "then drag images onto its tile."
        )
        self.empty_lbl.setObjectName("emptyLabel")
        self.empty_lbl.setAlignment(Qt.AlignCenter)
        self.empty_lbl.setParent(self.grid_host)

        # activity log panel (hidden by default), with a header + Clear button
        self.log_panel = QWidget()
        self.log_panel.setObjectName("logPanel")
        lp = QVBoxLayout(self.log_panel)
        lp.setContentsMargins(10, 6, 10, 8)
        lp.setSpacing(6)
        lp_head = QHBoxLayout()
        lp_title = QLabel("Activity log")
        lp_title.setObjectName("logTitle")
        lp_head.addWidget(lp_title, 0)
        lp_head.addStretch(1)
        self.clear_log_btn = QPushButton("Clear logs")
        self.clear_log_btn.clicked.connect(self.clear_logs)
        lp_head.addWidget(self.clear_log_btn, 0)
        lp.addLayout(lp_head)
        self.log_view = QPlainTextEdit()
        self.log_view.setReadOnly(True)
        self.log_view.setFixedHeight(150)
        self.log_view.setObjectName("log")
        lp.addWidget(self.log_view)
        self.log_panel.hide()
        outer.addWidget(self.log_panel)
        self._load_log_into_view()

        # status bar + progress
        self.progress = QProgressBar()
        self.progress.setFixedWidth(240)
        self.progress.hide()
        self.statusBar().addPermanentWidget(self.progress)
        self.statusBar().showMessage("Ready")

        self._refresh_category_filter()
        self._refresh_folder_count()
        self.setStyleSheet(STYLESHEET)

    def _refresh_folder_count(self):
        n = len(self.mappings)
        self.folder_count_lbl.setText(f"{n} / {MAX_FOLDERS} folders")
        if n >= MAX_FOLDERS:
            self.folder_count_lbl.setStyleSheet("color:#ef4444;")
            note = " You're at the limit \u2014 remove some before adding more."
        elif n >= MAX_FOLDERS * 0.9:
            self.folder_count_lbl.setStyleSheet("color:#f59e0b;")
            note = " Approaching the limit."
        else:
            self.folder_count_lbl.setStyleSheet("")   # fall back to the muted #activeHint color
            note = ""
        self.folder_count_lbl.setToolTip(
            f"{n} of {MAX_FOLDERS} destination folders mapped.{note}")

    def _install_shortcuts(self):
        QShortcut(QKeySequence("Ctrl+N"), self, self.add_folder)
        QShortcut(QKeySequence("Ctrl+Z"), self, self.undo_last)
        QShortcut(QKeySequence("Ctrl+F"), self, self._focus_search)
        QShortcut(QKeySequence("Ctrl+Right"), self, lambda: self._ctrl_arrow(+1))
        QShortcut(QKeySequence("Ctrl+Left"), self, lambda: self._ctrl_arrow(-1))
        QShortcut(QKeySequence("Ctrl+M"), self, self._toggle_mode)
        QShortcut(QKeySequence("Ctrl+I"), self, self.toggle_view_mode)

    def _focus_search(self):
        if self.view_mode() == "interactive":
            self.interactive.dest_filter.setFocus()
            self.interactive.dest_filter.selectAll()
        else:
            self.search.setFocus()

    def _ctrl_arrow(self, direction):
        if self.view_mode() == "interactive":
            self.interactive.step(direction)
        else:
            self.cycle_target(direction)

    # ---- Original / Interactive view ----
    def view_mode(self):
        return "interactive" if self.stack.currentWidget() is self.interactive else "original"

    def toggle_view_mode(self):
        self.set_view_mode("original" if self.view_mode() == "interactive" else "interactive")

    def set_view_mode(self, mode, save=True):
        mode = "interactive" if mode == "interactive" else "original"
        inter = mode == "interactive"
        self.view_orig_btn.setChecked(not inter)
        self.view_inter_btn.setChecked(inter)
        # dashboard-only controls make no sense in the split view
        self.search.setVisible(not inter)
        self.cat_filter.setVisible(not inter)
        self.tb_buttons["New group"].setVisible(not inter)
        if inter:
            self.clear_selection()
            self.stack.setCurrentWidget(self.interactive)
            self.interactive.activate()
        else:
            self.interactive.deactivate()
            self.stack.setCurrentWidget(self.original_page)
        if self.settings.get("view_mode") != mode:
            self.settings["view_mode"] = mode
            if save:
                self._save()
                self.log(f"Switched to {'Interactive' if inter else 'Original'} Mode")

    # ---- mode ----
    def _toggle_mode(self):
        new = "copy" if self.settings.get("mode") == "move" else "move"
        self.settings["mode"] = new
        self.mode_btn.setChecked(new == "move")
        self._refresh_mode_btn()
        if hasattr(self, "interactive"):
            self.interactive.refresh_hint()
        self._save()

    def _refresh_mode_btn(self):
        mode = self.settings.get("mode", "move")
        if mode == "move":
            self.mode_btn.setText("Mode:  MOVE")
            self.mode_btn.setStyleSheet(
                "QPushButton{background:#7c2d12;color:#fed7aa;border:1px solid #c2410c;"
                "padding:6px 12px;border-radius:8px;font-weight:bold;}"
            )
            self.mode_btn.setToolTip("Files are MOVED out of the source folder. Click to switch to Copy.")
        else:
            self.mode_btn.setText("Mode:  COPY")
            self.mode_btn.setStyleSheet(
                "QPushButton{background:#14532d;color:#bbf7d0;border:1px solid #15803d;"
                "padding:6px 12px;border-radius:8px;font-weight:bold;}"
            )
            self.mode_btn.setToolTip("Originals are kept; a copy is placed in the target. Click to switch to Move.")

    # ---- category filter ----
    def _categories(self):
        return sorted({m.category for m in self.mappings if m.category})

    def _refresh_category_filter(self):
        current = self.cat_filter.currentText() if self.cat_filter.count() else "All categories"
        self.cat_filter.blockSignals(True)
        self.cat_filter.clear()
        self.cat_filter.addItem("All categories")
        for c in self._categories():
            self.cat_filter.addItem(c)
        idx = self.cat_filter.findText(current)
        self.cat_filter.setCurrentIndex(idx if idx >= 0 else 0)
        self.cat_filter.blockSignals(False)

    # ---- grid ----
    def _matches(self, mapping):
        q = self.search.text().strip().lower()
        if q and q not in mapping.name.lower() and q not in mapping.category.lower():
            return False
        cat = self.cat_filter.currentText()
        if cat and cat != "All categories" and mapping.category != cat:
            return False
        return True

    def _ensure_tile(self, mapping):
        tile = self.tiles.get(mapping.id)
        if tile is None:
            tile = DropTile(mapping)
            tile.filesDropped.connect(self.handle_drop)
            tile.clicked.connect(self._folder_clicked)
            tile.ctrlClicked.connect(self.toggle_select)
            tile.editRequested.connect(self.edit_folder)
            tile.removeRequested.connect(self.remove_folder)
            tile.recolorRequested.connect(self.recolor_folder)
            tile.openRequested.connect(lambda m: self.open_in_explorer(m.path))
            tile.copyPathRequested.connect(lambda m: self._copy_path(m.path))
            tile.moveRequested.connect(self.reorder_folder)
            tile.favoriteToggled.connect(self.toggle_favorite)
            tile.removeFromGroupRequested.connect(self.remove_from_group)
            tile.removeFromAllGroupsRequested.connect(self.remove_from_all_groups)
            tile.addToGroupRequested.connect(self.add_to_group)
            tile.newGroupForRequested.connect(self.add_to_new_group)
            tile.refreshCoverRequested.connect(self.refresh_cover)
            tile.foldersDroppedOnFolder.connect(self.nest_folders_into_folder)
            tile.drag_ids_provider = self._drag_ids_for
            self.tiles[mapping.id] = tile
        else:
            tile.mapping = mapping
            tile.drag_ids_provider = self._drag_ids_for
        tile.available_groups = self.groups
        tile.refresh()
        return tile

    def _ensure_group_tile(self, group):
        gt = self.group_tiles.get(group.id)
        if gt is None:
            gt = GroupTile(group)
            gt.enterRequested.connect(self.enter_group)
            gt.renameRequested.connect(self.rename_group)
            gt.recolorRequested.connect(self.recolor_group)
            gt.ungroupRequested.connect(self.ungroup)
            gt.deleteRequested.connect(self.delete_group)
            gt.ctrlClicked.connect(self.toggle_group_select)
            gt.clicked.connect(self.open_group_click)
            gt.newSubgroupRequested.connect(self.new_subgroup_in)
            gt.moveUpRequested.connect(self.move_group_up)
            gt.moveTopRequested.connect(self.move_group_top)
            gt.reparentRequested.connect(self.reparent_group)
            gt.foldersDroppedOnGroup.connect(self.add_folders_to_group)
            gt.filesDroppedOnGroup.connect(self.handle_group_file_drop)
            gt.setPathRequested.connect(self.set_group_path)
            gt.openPathRequested.connect(self.open_group_path)
            gt.validate_drop = self._can_reparent
            self.group_tiles[group.id] = gt
        else:
            gt.group = group
            gt.validate_drop = self._can_reparent
        gt.can_nest = self._group_depth(group.id) < MAX_GROUP_DEPTH
        gt.has_parent = bool(group.parent)
        gt.set_count(self._direct_child_count(group.id))
        gt.refresh()
        return gt

    def _group_by_id(self, gid):
        return next((g for g in self.groups if g.id == gid), None)

    def _group_depth(self, gid):
        """Depth of a group: top-level group = 1, its child = 2, ..."""
        depth = 1
        seen = set()
        g = self._group_by_id(gid)
        while g and g.parent and g.parent not in seen:
            seen.add(g.parent)
            depth += 1
            g = self._group_by_id(g.parent)
        return depth

    def _group_chain(self, gid):
        """Groups from root down to gid (inclusive)."""
        chain = []
        seen = set()
        g = self._group_by_id(gid)
        while g and g.id not in seen:
            seen.add(g.id)
            chain.append(g)
            g = self._group_by_id(g.parent) if g.parent else None
        chain.reverse()
        return chain

    def _group_path(self, gid):
        return " / ".join(g.name for g in self._group_chain(gid))

    def _can_nest_here(self):
        """Can a new subgroup be created inside the current container?"""
        if self.current_group is None:
            return True                       # new top-level group
        return self._group_depth(self.current_group) < MAX_GROUP_DEPTH

    def _direct_child_count(self, gid):
        subs = sum(1 for g in self.groups if g.parent == gid)
        maps = sum(1 for m in self.mappings if m.group == gid)
        return subs + maps

    def _group_subtree_ids(self, root_gid):
        """All group ids in this group's subtree (including itself), and every
        mapping id anywhere within that subtree. Used to delete a group and
        everything nested inside it, rather than just releasing its contents."""
        group_ids = {root_gid}
        frontier = [root_gid]
        while frontier:
            gid = frontier.pop()
            for g in self.groups:
                if g.parent == gid and g.id not in group_ids:
                    group_ids.add(g.id)
                    frontier.append(g.id)
        mapping_ids = {m.id for m in self.mappings if m.group in group_ids}
        return group_ids, mapping_ids

    def _searching(self):
        q = self.search.text().strip()
        cat = self.cat_filter.currentText()
        return bool(q) or (cat and cat != "All categories")

    def _dashboard_items(self):
        """Ordered list of ('folder', mapping) / ('group', group) for the grid."""
        if self._searching():
            # flat find across every folder, regardless of nesting
            matches = [m for m in self.mappings if self._matches(m)]
            matches.sort(key=lambda m: (not m.favorite, m.name.casefold()))
            return [("folder", m) for m in matches]
        pid = "" if self.current_group is None else self.current_group
        subgroups = [g for g in self.groups if g.parent == pid]
        members = [m for m in self.mappings if m.group == pid]
        if self.current_group is None:
            # top level: pinned favorites, then groups, then the rest
            favs = [m for m in members if m.favorite]
            rest = [m for m in members if not m.favorite]
            items = [("folder", m) for m in favs]
            items += [("group", g) for g in subgroups]
            items += [("folder", m) for m in rest]
            return items
        # inside a group: subgroups then folders, both alphabetical
        subgroups.sort(key=lambda g: g.name.casefold())
        members.sort(key=lambda m: m.name.casefold())
        return [("group", g) for g in subgroups] + [("folder", m) for m in members]

    def _rebuild_grid(self):
        # detach everything (keep widgets alive, hidden)
        while self.flow.count():
            item = self.flow.takeAt(0)
            w = item.widget()
            if w:
                w.setParent(self.grid_host)
                w.hide()
        items = self._dashboard_items()
        for kind, obj in items:
            if kind == "folder":
                tile = self._ensure_tile(obj)
                tile.set_active(obj.id == self.active_id)
                tile.set_selected(obj.id in self.selected_ids)
                self.flow.addWidget(tile)
                tile.show()
            else:
                gt = self._ensure_group_tile(obj)
                gt.set_selected(obj.id in self.selected_group_ids)
                self.flow.addWidget(gt)
                gt.show()
        self._update_breadcrumb()
        self._update_selection_bar()
        shuffle = self._shuffle_covers
        self._shuffle_covers = False
        for kind, obj in items:
            self._request_tile_cover("m" if kind == "folder" else "g", obj, force=shuffle)
        # empty state
        show_empty = len(items) == 0
        self.empty_lbl.setVisible(show_empty)
        if show_empty:
            self.empty_lbl.setText(self._empty_text())
            self.empty_lbl.resize(self.grid_host.width(), 200)
            self.empty_lbl.move(0, 40)

    def _empty_text(self):
        if self.current_group is not None:
            return ("This group is empty.\n\n"
                    "Add a \u201cNew subgroup\u201d here, drag folders in from the dashboard\n"
                    "(right-click a folder \u2192 Add to group), or use the red \u2212 on a\n"
                    "folder inside another group to move it up to here.")
        if self._searching():
            return "No folders match your search."
        return (
            "No folders yet.\n\nClick \u201cAdd folder\u201d, give it a name and a path\n"
            "(local like D:\\Pics\\Funny, or network like \\\\NAS\\share\\Funny),\n"
            "then drag files onto its tile.\n\n"
            "Adding a folder brings all of its subfolders along \u2014 add a whole\n"
            "drive once and double-click it to reach anything inside.\n\n"
            "Prefer one image at a time? Switch to Interactive Mode (Ctrl+I)."
        )

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if self.empty_lbl.isVisible():
            self.empty_lbl.resize(self.grid_host.width(), 200)

    # ---- navigation ----
    # Opening a level (Home, a group, Up) re-picks a random cover for every
    # tile on it; other rebuilds (search, rename, scan) only fill missing ones.
    def enter_group(self, group):
        self.current_group = group.id
        self.clear_selection()
        self._shuffle_covers = True
        self._rebuild_grid()

    def go_home(self):
        self.current_group = None
        self.clear_selection()
        self._shuffle_covers = True
        self._rebuild_grid()

    def go_up(self):
        g = self._group_by_id(self.current_group) if self.current_group else None
        self.current_group = g.parent if (g and g.parent) else None
        self.clear_selection()
        self._shuffle_covers = True
        self._rebuild_grid()

    def _update_breadcrumb(self):
        if self.current_group is not None:
            path = self._group_path(self.current_group)
            depth = self._group_depth(self.current_group)
            self.crumb_label.setText(f"Home / {path}    (level {depth}/{MAX_GROUP_DEPTH})")
            can = self._can_nest_here()
            self.subgroup_btn.setEnabled(can)
            self.subgroup_btn.setToolTip(
                "" if can else f"Maximum nesting is {MAX_GROUP_DEPTH} levels deep")
            self.crumb.show()
        else:
            self.crumb.hide()

    # ---- selection + grouping ----
    def _folder_clicked(self, mapping):
        self.clear_selection()
        self.set_active(mapping.id)

    def toggle_select(self, mapping):
        if mapping.id in self.selected_ids:
            self.selected_ids.discard(mapping.id)
        else:
            self.selected_ids.add(mapping.id)
        tile = self.tiles.get(mapping.id)
        if tile:
            tile.set_selected(mapping.id in self.selected_ids)
        self._update_selection_bar()

    def toggle_group_select(self, group):
        if group.id in self.selected_group_ids:
            self.selected_group_ids.discard(group.id)
        else:
            self.selected_group_ids.add(group.id)
        gt = self.group_tiles.get(group.id)
        if gt:
            gt.set_selected(group.id in self.selected_group_ids)
        self._update_selection_bar()

    def clear_selection(self):
        had = bool(self.selected_ids) or bool(self.selected_group_ids)
        self.selected_ids.clear()
        self.selected_group_ids.clear()
        if had:
            for t in self.tiles.values():
                t.set_selected(False)
            for gt in self.group_tiles.values():
                gt.set_selected(False)
        self._update_selection_bar()

    def _update_selection_bar(self):
        n_maps = len(self.selected_ids)
        n_groups = len(self.selected_group_ids)
        total = n_maps + n_groups
        if n_maps and n_groups:
            self.sel_label.setText(
                f"{total} selected ({n_maps} folder(s), {n_groups} group(s))")
        elif n_groups:
            self.sel_label.setText(f"{n_groups} group(s) selected")
        else:
            self.sel_label.setText(f"{n_maps} selected")
        self.group_btn.setEnabled(n_maps > 0)
        self.remove_sel_btn.setEnabled(total > 0)
        self.sel_bar.setVisible(total > 0)

    def _open_group_menu(self):
        if not self.selected_ids:
            return
        menu = QMenu(self)
        act = menu.addAction("New group from selection\u2026",
                             self._new_group_from_selection)
        if not self._can_nest_here():
            act.setEnabled(False)
        if self.groups:
            menu.addSeparator()
            for g in sorted(self.groups, key=lambda x: self._group_path(x.id).casefold()):
                menu.addAction(
                    f"Move to: {self._group_path(g.id)}",
                    lambda checked=False, gid=g.id: self._add_selection_to_group(gid))
        menu.exec(self.group_btn.mapToGlobal(self.group_btn.rect().bottomLeft()))

    def _selected_mappings(self):
        return [m for m in self.mappings if m.id in self.selected_ids]

    def _make_group(self, name, parent_pid, path=""):
        gid = uuid.uuid4().hex
        color = TILE_PALETTE[len(self.groups) % len(TILE_PALETTE)]
        self.groups.append(Group(id=gid, name=name, color=color,
                                 parent=parent_pid, path=path))
        return gid

    def _new_group_from_selection(self):
        sel = self._selected_mappings()
        if not sel:
            return
        if not self._can_nest_here():
            QMessageBox.information(
                self, APP_NAME, f"Maximum nesting is {MAX_GROUP_DEPTH} levels deep.")
            return
        name, ok = QInputDialog.getText(self, "New group", "Group name:")
        name = (name or "").strip()
        if not ok or not name:
            return
        pid = "" if self.current_group is None else self.current_group
        gid = self._make_group(name, pid)
        for m in sel:
            m.group = gid
        n = len(sel)
        self.clear_selection()
        self._after_change()
        self.log(f"Grouped {n} folder(s) into \u201c{name}\u201d")

    def _add_selection_to_group(self, gid):
        sel = self._selected_mappings()
        for m in sel:
            m.group = gid
        g = self._group_by_id(gid)
        self.clear_selection()
        self._after_change()
        if g:
            self.log(f"Moved {len(sel)} folder(s) to \u201c{g.name}\u201d")

    # ---- favorites / group membership ----
    def toggle_favorite(self, mapping):
        mapping.favorite = not mapping.favorite
        self._after_change()
        self.log(f"{'Pinned' if mapping.favorite else 'Unpinned'} \u201c{mapping.name}\u201d")

    def remove_from_group(self, mapping):
        # lift one level: into the parent group (or to the top level)
        g = self._group_by_id(mapping.group)
        mapping.group = g.parent if (g and g.parent) else ""
        self._after_change()
        dest = self._group_by_id(mapping.group)
        where = f"\u201c{dest.name}\u201d" if dest else "the top level"
        self.log(f"Removed \u201c{mapping.name}\u201d from group \u2192 {where}")

    def remove_from_all_groups(self, mapping):
        mapping.group = ""        # all the way out to the top level
        self._after_change()
        self.log(f"Removed \u201c{mapping.name}\u201d from all groups \u2192 top level")

    def add_to_group(self, mapping, gid):
        mapping.group = gid
        self._after_change()
        g = self._group_by_id(gid)
        if g:
            self.log(f"Moved \u201c{mapping.name}\u201d into group \u201c{g.name}\u201d")

    def add_to_new_group(self, mapping):
        if not self._can_nest_here():
            QMessageBox.information(
                self, APP_NAME, f"Maximum nesting is {MAX_GROUP_DEPTH} levels deep.")
            return
        name, ok = QInputDialog.getText(self, "New group", "Group name:")
        name = (name or "").strip()
        if not ok or not name:
            return
        pid = "" if self.current_group is None else self.current_group
        gid = self._make_group(name, pid)
        mapping.group = gid
        self._after_change()
        self.log(f"Grouped \u201c{mapping.name}\u201d into \u201c{name}\u201d")

    # ---- group ops ----
    def create_group_here(self):
        """Create an empty (sub)group inside the current container."""
        if not self._can_nest_here():
            QMessageBox.information(
                self, APP_NAME, f"Maximum nesting is {MAX_GROUP_DEPTH} levels deep.")
            return
        name, ok = QInputDialog.getText(self, "New group", "Group name:")
        name = (name or "").strip()
        if not ok or not name:
            return
        pid = "" if self.current_group is None else self.current_group
        self._make_group(name, pid)
        self._after_change()
        self.log(f"Created group \u201c{name}\u201d")

    def new_subgroup_in(self, group):
        """Create a subgroup inside a specific group and open it."""
        if self._group_depth(group.id) >= MAX_GROUP_DEPTH:
            QMessageBox.information(
                self, APP_NAME, f"Maximum nesting is {MAX_GROUP_DEPTH} levels deep.")
            return
        name, ok = QInputDialog.getText(
            self, "New subgroup", f"Subgroup of \u201c{group.name}\u201d:")
        name = (name or "").strip()
        if not ok or not name:
            return
        gid = self._make_group(name, group.id)
        self.current_group = gid          # drop into the new subgroup
        self._after_change()
        self.log(f"Created subgroup \u201c{name}\u201d in \u201c{group.name}\u201d")

    def move_group_up(self, group):
        if not group.parent:
            return
        pg = self._group_by_id(group.parent)
        group.parent = pg.parent if pg else ""
        self._after_change()
        self.log(f"Moved group \u201c{group.name}\u201d up a level")

    def move_group_top(self, group):
        if not group.parent:
            return
        group.parent = ""
        self._after_change()
        self.log(f"Moved group \u201c{group.name}\u201d to the top level")

    # ---- drag-and-drop reparenting ----
    def _subtree_height(self, gid):
        """Levels of groups below `gid` (0 if it has no subgroups)."""
        children = [g for g in self.groups if g.parent == gid]
        if not children:
            return 0
        return 1 + max(self._subtree_height(c.id) for c in children)

    def _is_ancestor(self, anc_gid, gid):
        """True if anc_gid is gid itself or an ancestor of gid."""
        seen = set()
        cur = self._group_by_id(gid)
        while cur and cur.id not in seen:
            if cur.id == anc_gid:
                return True
            seen.add(cur.id)
            cur = self._group_by_id(cur.parent) if cur.parent else None
        return False

    def _can_reparent(self, src_gid, dst_gid):
        """Can group src become a child of group dst?"""
        if src_gid == dst_gid:
            return False
        src = self._group_by_id(src_gid)
        dst = self._group_by_id(dst_gid)
        if not src or not dst:
            return False
        if src.parent == dst_gid:
            return False                       # already a direct child (no-op)
        if self._is_ancestor(src_gid, dst_gid):
            return False                       # would create a loop
        # the deepest descendant of src must still fit under dst
        if self._group_depth(dst_gid) + 1 + self._subtree_height(src_gid) > MAX_GROUP_DEPTH:
            return False
        return True

    def reparent_group(self, src_gid, dst_gid):
        if not self._can_reparent(src_gid, dst_gid):
            QMessageBox.information(
                self, APP_NAME,
                "Can't nest there \u2014 it would create a loop or go deeper "
                f"than {MAX_GROUP_DEPTH} levels.")
            return
        src = self._group_by_id(src_gid)
        dst = self._group_by_id(dst_gid)
        src.parent = dst_gid
        self._after_change()
        self.log(f"Moved group \u201c{src.name}\u201d into \u201c{dst.name}\u201d")

    def _drop_group_up(self, gid):
        g = self._group_by_id(gid)
        if g and g.parent:
            self.move_group_up(g)

    def _drop_group_top(self, gid):
        g = self._group_by_id(gid)
        if g and g.parent:
            self.move_group_top(g)

    # ---- folder drag-and-drop ----
    def _drag_ids_for(self, mid):
        """Which folders to drag: the whole selection if this tile is in it."""
        if mid in self.selected_ids and len(self.selected_ids) > 1:
            return list(self.selected_ids)
        return [mid]

    def nest_folders_into_folder(self, ids, target):
        """Drop folders onto another folder -> make a new group holding all of them."""
        ids = [i for i in ids if i != target.id]
        if not ids:
            return
        if not self._can_nest_here():
            QMessageBox.information(
                self, APP_NAME, f"Maximum nesting is {MAX_GROUP_DEPTH} levels deep.")
            return
        name, ok = QInputDialog.getText(
            self, "New group", "Name this group:", text="New Group")
        name = (name or "").strip()
        if not ok or not name:
            return
        pid = "" if self.current_group is None else self.current_group
        gid = self._make_group(name, pid)
        target.group = gid
        for i in ids:
            m = self._mapping_by_id(i)
            if m:
                m.group = gid
        self.clear_selection()
        self._after_change()
        self.log(f"Grouped {len(ids) + 1} folder(s) into \u201c{name}\u201d")

    def add_folders_to_group(self, ids, group):
        """Drop folders onto a group tile -> add them to that group."""
        n = 0
        for i in ids:
            m = self._mapping_by_id(i)
            if m and m.group != group.id:
                m.group = group.id
                n += 1
        self.clear_selection()
        self._after_change()
        if n:
            self.log(f"Moved {n} folder(s) into \u201c{group.name}\u201d")

    def _drop_folders_up(self, ids):
        n = 0
        for i in ids:
            m = self._mapping_by_id(i)
            if m and m.group:
                g = self._group_by_id(m.group)
                m.group = g.parent if (g and g.parent) else ""
                n += 1
        self.clear_selection()
        self._after_change()
        if n:
            self.log(f"Moved {n} folder(s) up a level")

    def _drop_folders_top(self, ids):
        n = 0
        for i in ids:
            m = self._mapping_by_id(i)
            if m and m.group:
                m.group = ""
                n += 1
        self.clear_selection()
        self._after_change()
        if n:
            self.log(f"Moved {n} folder(s) to the top level")

    # ---- group as a file destination ----
    def handle_group_file_drop(self, group, paths):
        """Files dropped onto a group tile from the OS."""
        if not group.path:
            # Prompt the user to set a path
            r = QMessageBox.question(
                self, APP_NAME,
                f"Group \u201c{group.name}\u201d has no folder path set.\n\n"
                f"Would you like to set a destination folder now so files "
                f"can be dropped here?",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
            if r != QMessageBox.Yes:
                return
            d = QFileDialog.getExistingDirectory(
                self, f"Set destination for \u201c{group.name}\u201d",
                os.path.expanduser("~"))
            if not d:
                return
            group.path = os.path.normpath(d)
            self._after_change()
            self.log(f"Set path for group \u201c{group.name}\u201d: {group.path}")
        # Now file the dropped items using the same logic as folder tiles
        m = Mapping(id=f"_grp_{group.id}", name=group.name, path=group.path)
        self.handle_drop(m, paths)

    def set_group_path(self, group):
        d = QFileDialog.getExistingDirectory(
            self, f"Set destination for \u201c{group.name}\u201d",
            group.path or os.path.expanduser("~"))
        if d:
            group.path = os.path.normpath(d)
            self._after_change()
            self.log(f"Set path for group \u201c{group.name}\u201d: {group.path}")

    def open_group_path(self, group):
        if group.path:
            self.open_in_explorer(group.path)

    def open_group_click(self, group):
        """A plain (debounced) click on a group tile: open its real on-disk
        folder if it has one, otherwise fall back to browsing it in-app."""
        if group.path:
            self.open_in_explorer(group.path)
        else:
            self.enter_group(group)

    def rename_group(self, group):
        old = group.name
        name, ok = QInputDialog.getText(
            self, "Rename group", "Group name:", text=group.name)
        name = (name or "").strip()
        if ok and name and name != old:
            group.name = name
            self._after_change()
            self.log(f"Renamed group \u201c{old}\u201d \u2192 \u201c{name}\u201d")

    def recolor_group(self, group):
        c = QColorDialog.getColor(QColor(group.color), self, "Group color")
        if c.isValid():
            group.color = c.name()
            self._after_change()
            self.log(f"Recolored group \u201c{group.name}\u201d")

    def ungroup(self, group):
        # dissolve one level: children and member folders move up to this
        # group's parent; the group itself is removed.
        if group.scanned:
            # a future scan should not silently recreate this exact node; its
            # real children (if any) stay tracked and simply move up a level
            self._ignore_scan_path(group.path)
        for g in self.groups:
            if g.parent == group.id:
                g.parent = group.parent
        for m in self.mappings:
            if m.group == group.id:
                m.group = group.parent
        self.groups = [g for g in self.groups if g.id != group.id]
        gt = self.group_tiles.pop(group.id, None)
        if gt:
            gt.setParent(None)
            gt.deleteLater()
        if self.current_group == group.id:
            self.current_group = group.parent or None
        self._after_change()
        self.log(f"Ungrouped \u201c{group.name}\u201d")

    # ---- active target ----
    def set_active(self, mid):
        self.active_id = mid
        for tid, tile in self.tiles.items():
            tile.set_active(tid == mid)
        self._update_active_zone()

    def _active_mapping(self):
        return next((m for m in self.mappings if m.id == self.active_id), None)

    def _update_active_zone(self):
        self.active_zone.set_mapping(self._active_mapping())

    def cycle_target(self, direction):
        if not self.mappings:
            return
        ids = [m.id for m in self.mappings]
        if self.active_id in ids:
            idx = (ids.index(self.active_id) + direction) % len(ids)
        else:
            idx = 0
        self.set_active(ids[idx])
        m = self._active_mapping()
        if m:
            self.statusBar().showMessage(f"Active target: {m.name}", 2500)

    def _drop_on_active(self, paths):
        m = self._active_mapping()
        if not m:
            QMessageBox.information(self, APP_NAME, "Pick a target folder first.")
            return
        self.handle_drop(m, paths)

    # ---- folder CRUD ----
    def add_folder(self):
        remaining = MAX_FOLDERS - len(self.mappings)
        if remaining <= 0:
            QMessageBox.information(self, APP_NAME, f"You can map up to {MAX_FOLDERS} folders.")
            return
        dlg = AddFoldersDialog(self, self._categories(), remaining)
        if dlg.exec() == QDialog.Accepted:
            vals = dlg.values()
            flat = [v for v in vals if not v.get("subfolders", True)]
            trees = [v for v in vals if v.get("subfolders", True)]
            if flat:
                self._add_plain_folders(flat)
            if trees:
                self.import_folder_trees(trees)

    def _add_plain_folders(self, vals):
        """The pre-3.0 behavior: one plain tile per folder, no subfolders."""
        new_ms = []
        for v in vals:
            m = Mapping(id=uuid.uuid4().hex, name=v["name"], path=v["path"],
                        color=v.get("color", "#3b82f6"), category=v.get("category", ""))
            self.mappings.append(m)
            new_ms.append(m)
        if not new_ms:
            return []
        if self.active_id is None:
            self.active_id = new_ms[0].id
        self._after_change()
        self.checker.check_many(new_ms)
        if len(new_ms) == 1:
            self.log(f"Added folder: {new_ms[0].name}")
        else:
            self.log(f"Added {len(new_ms)} folders: "
                     + ", ".join(m.name for m in new_ms))
        return new_ms

    # ---- add folder = add its whole tree ----
    def import_folder_trees(self, vals):
        """Add each folder together with every real subfolder beneath it.

        The folder's tree is walked off the GUI thread by the same DriveScanner
        a network scan uses. When the walk comes back (_finish_import):
          - folder has subfolders -> it becomes a group (with its path, so it
            still accepts drops) mirroring the whole tree, and it is registered
            as a scan root so later scans pick up new subfolders;
          - folder has none -> a plain folder tile, exactly as before.
        """
        roots = []
        for v in vals:
            path = os.path.normpath(v["path"])
            norm = _norm_path(path)
            if norm in self._pending_imports:
                continue
            # an explicit add overrides anything previously removed under it
            self._unignore_tree(path)
            self._pending_imports[norm] = dict(v, path=path)
            roots.append(path)
        if roots:
            self.statusBar().showMessage(
                f"Importing {len(roots)} folder(s) and all of their subfolders\u2026")
            self._start_scan(roots)

    def _unignore_tree(self, path):
        norm = _norm_path(path)
        prefix = norm.rstrip("\\/") + os.sep
        lst = self.settings.get("ignored_scan_paths") or []
        kept = [p for p in lst if p != norm and not p.startswith(prefix)]
        if len(kept) != len(lst):
            self.settings["ignored_scan_paths"] = kept

    def _add_scan_root(self, path):
        roots = self.settings.setdefault("scan_roots", [])
        if _norm_path(path) not in {_norm_path(r) for r in roots}:
            roots.append(path)

    def _finish_import(self, root, v, folders, reachable=True):
        norm = _norm_path(root)
        name = v.get("name") or os.path.basename(root.rstrip("\\/")) or root
        color = v.get("color", "#3b82f6")
        gid = self._find_group_id_by_path(norm)
        plain = next((m for m in self.mappings
                      if m.path and _norm_path(m.path) == norm), None)

        if reachable and not folders and gid is None:
            # no subfolders: an ordinary folder tile (unless it's already one)
            if plain is not None:
                self.log(f"\u201c{plain.name}\u201d is already mapped ({root})")
                self.statusBar().showMessage("That folder is already mapped.", 4000)
                return
            self._add_plain_folders([dict(v, path=root, name=name)])
            return

        if plain is not None and gid is None:
            # re-adding a folder that was a single tile: upgrade it to a tree
            name, color = plain.name, plain.color
            self.mappings = [m for m in self.mappings if m.id != plain.id]
            tile = self.tiles.pop(plain.id, None)
            if tile:
                tile.setParent(None)
                tile.deleteLater()
            if self.active_id == plain.id:
                self.active_id = self.mappings[0].id if self.mappings else None
            self.log(f"Upgraded folder tile \u201c{name}\u201d to include its subfolders")
        if gid is None:
            gid = self._make_group(name, "", path=root)
            g = self._group_by_id(gid)
            g.color = color
            g.scanned = True      # removing it later remembers not to re-add it
        self._add_scan_root(root)
        added_g, added_m = self._apply_scan_results(root, folders) if folders else (0, 0)
        self._after_change()
        if reachable:
            self.log(f"Added folder \u201c{name}\u201d with {added_g} subfolder group(s)"
                     + (f" and {added_m} deep folder tile(s)" if added_m else ""))
            self.statusBar().showMessage(
                f"Added \u201c{name}\u201d \u2014 {added_g + added_m} subfolder(s) mapped. "
                f"Double-click it to browse inside.", 6000)
        else:
            self.log(f"Added \u201c{name}\u201d ({root}) but it isn't reachable right now "
                     f"\u2014 its subfolders will be mapped on the next scan.")

    def edit_folder(self, mapping):
        old_path = mapping.path
        dlg = MappingDialog(self, self._categories(), mapping)
        if dlg.exec() == QDialog.Accepted:
            v = dlg.values()
            mapping.name, mapping.path = v["name"], v["path"]
            mapping.category, mapping.color = v["category"], v["color"]
            if mapping.path != old_path:
                mapping.cover = ""        # different folder -> re-pick a cover
            tile = self.tiles.get(mapping.id)
            if tile:
                tile.mapping = mapping
                tile.set_reachable(None)
                if mapping.path != old_path:
                    tile.clear_cover()
                tile.refresh()
            self._after_change()
            self.checker.check_many([mapping])
            self.log(f"Updated folder: {mapping.name}")

    def recolor_folder(self, mapping):
        c = QColorDialog.getColor(QColor(mapping.color), self, "Tile color")
        if c.isValid():
            mapping.color = c.name()
            tile = self.tiles.get(mapping.id)
            if tile:
                tile.refresh()
            self._save()
            self.log(f"Recolored \u201c{mapping.name}\u201d")

    def remove_folder(self, mapping):
        # Part of an active multi-selection? "Remove" acts on the whole
        # selection, not just the tile that was right-clicked.
        if mapping.id in self.selected_ids and (
                len(self.selected_ids) > 1 or self.selected_group_ids):
            self.remove_selected()
            return
        if QMessageBox.question(
            self, APP_NAME,
            f"Remove the tile for \u201c{mapping.name}\u201d?\n\n"
            f"This only removes it from {APP_NAME}. The folder and its files are not touched.",
        ) != QMessageBox.Yes:
            return
        if mapping.scanned:
            self._ignore_scan_path(mapping.path)
        self.mappings = [m for m in self.mappings if m.id != mapping.id]
        tile = self.tiles.pop(mapping.id, None)
        if tile:
            tile.setParent(None)
            tile.deleteLater()
        if self.active_id == mapping.id:
            self.active_id = self.mappings[0].id if self.mappings else None
        self._after_change()
        self.log(f"Removed folder: {mapping.name}")

    def _delete_groups_and_mappings(self, group_ids, mapping_ids):
        """Core removal mechanics shared by delete_group() and
        remove_selected(): untrack the given groups and mappings (already
        expanded to include everything nested inside any of the groups).
        Real files/folders on disk are never touched."""
        for mid in mapping_ids:
            m = self._mapping_by_id(mid)
            if m and m.scanned:
                self._ignore_scan_path(m.path)
        for gid in group_ids:
            g = self._group_by_id(gid)
            if g and g.scanned:
                self._ignore_scan_path(g.path)
        self.mappings = [m for m in self.mappings if m.id not in mapping_ids]
        self.groups = [g for g in self.groups if g.id not in group_ids]
        for mid in mapping_ids:
            tile = self.tiles.pop(mid, None)
            if tile:
                tile.setParent(None)
                tile.deleteLater()
        for gid in group_ids:
            gt = self.group_tiles.pop(gid, None)
            if gt:
                gt.setParent(None)
                gt.deleteLater()
        if self.active_id in mapping_ids:
            self.active_id = self.mappings[0].id if self.mappings else None
        if self.current_group in group_ids:
            self.current_group = None
        self.selected_ids -= mapping_ids
        self.selected_group_ids -= group_ids

    def delete_group(self, group):
        # Part of an active multi-selection? Act on the whole selection.
        if group.id in self.selected_group_ids and (
                len(self.selected_group_ids) > 1 or self.selected_ids):
            self.remove_selected()
            return
        group_ids, mapping_ids = self._group_subtree_ids(group.id)
        sub_count = len(group_ids) - 1
        map_count = len(mapping_ids)
        msg = f"Remove the group \u201c{group.name}\u201d?"
        extras = []
        if sub_count:
            extras.append(f"{sub_count} subgroup(s)")
        if map_count:
            extras.append(f"{map_count} folder tile(s)")
        if extras:
            msg += "\n\nThis also removes " + " and ".join(extras) + " that are inside it."
        msg += (f"\n\nThis only removes them from {APP_NAME} \u2014 real folders and "
                f"files on disk are not touched.")
        if QMessageBox.question(self, APP_NAME, msg) != QMessageBox.Yes:
            return
        self._delete_groups_and_mappings(group_ids, mapping_ids)
        self._after_change()
        extra_txt = (f" (+{sub_count} subgroup(s), {map_count} tile(s) inside)"
                     if extras else "")
        self.log(f"Removed group \u201c{group.name}\u201d{extra_txt}")

    def remove_selected(self):
        sel_group_ids = set(self.selected_group_ids)
        sel_mapping_ids = set(self.selected_ids)
        if not sel_group_ids and not sel_mapping_ids:
            return
        all_group_ids, pulled_in_mapping_ids = set(), set()
        for gid in sel_group_ids:
            gids, mids = self._group_subtree_ids(gid)
            all_group_ids |= gids
            pulled_in_mapping_ids |= mids
        all_mapping_ids = sel_mapping_ids | pulled_in_mapping_ids

        parts = []
        if sel_mapping_ids:
            parts.append(f"{len(sel_mapping_ids)} folder tile(s)")
        if sel_group_ids:
            parts.append(f"{len(sel_group_ids)} group(s)")
        msg = "Remove " + " and ".join(parts) + "?"
        extra_groups = len(all_group_ids) - len(sel_group_ids)
        extra_maps = len(all_mapping_ids) - len(sel_mapping_ids)
        extras = []
        if extra_groups:
            extras.append(f"{extra_groups} nested subgroup(s)")
        if extra_maps:
            extras.append(f"{extra_maps} folder tile(s) inside them")
        if extras:
            msg += "\n\nThis also removes " + " and ".join(extras) + "."
        msg += (f"\n\nThis only removes them from {APP_NAME} \u2014 real folders and "
                f"files on disk are not touched.")
        if QMessageBox.question(self, APP_NAME, msg) != QMessageBox.Yes:
            return
        self._delete_groups_and_mappings(all_group_ids, all_mapping_ids)
        self._after_change()   # rebuilds the grid, which also refreshes the selection bar
        self.log(f"Removed {len(all_mapping_ids)} folder tile(s) and "
                 f"{len(all_group_ids)} group(s)")

    def reorder_folder(self, mapping, direction):
        ids = [m.id for m in self.mappings]
        if mapping.id not in ids:
            return
        i = ids.index(mapping.id)
        j = i + direction
        if 0 <= j < len(self.mappings):
            self.mappings[i], self.mappings[j] = self.mappings[j], self.mappings[i]
            self._after_change()

    def _after_change(self):
        self._refresh_category_filter()
        self._refresh_folder_count()
        self._rebuild_grid()
        self._update_active_zone()
        self.interactive.mark_destinations_dirty()
        self._save()

    # ---- the drop -> transfer ----
    def handle_drop(self, mapping, paths):
        """File `paths` into `mapping.path`. Shared by every drop surface (tiles,
        group tiles, the active zone and Interactive Mode's tree). Returns True
        when a transfer was queued, False if nothing was filed."""
        items, dirs, skipped_type = [], 0, 0
        media_only = self.settings.get("media_only", True)
        for p in paths:
            if os.path.isdir(p):
                items.append(p)      # whole folder + contents + subfolders
                dirs += 1
                continue
            if media_only and not is_media(p):
                skipped_type += 1
                continue
            items.append(p)

        notes = []
        if skipped_type:
            notes.append(f"{skipped_type} non-media file(s) skipped")

        if not items:
            msg = "Nothing to file."
            if notes:
                msg += " (" + ", ".join(notes) + ")"
            self.statusBar().showMessage(msg, 4000)
            return False

        if not is_path_reachable(mapping.path):
            tile = self.tiles.get(mapping.id)
            if tile:
                tile.set_reachable(False)
            self.log(f"ERROR: \u201c{mapping.name}\u201d not reachable ({mapping.path}) "
                     f"\u2014 {len(items)} item(s) not moved")
            QMessageBox.warning(
                self, "Drive not reachable",
                f"\u201c{mapping.name}\u201d could not be reached:\n\n{mapping.path}\n\n"
                f"The drive may be disconnected or the network share is offline. "
                f"No files were moved.",
            )
            return False

        mode = self.settings.get("mode", "move")
        n_files = len(items) - dirs
        if self.settings.get("confirm_each", False):
            verb = "Move" if mode == "move" else "Copy"
            what = []
            if n_files:
                what.append(f"{n_files} file(s)")
            if dirs:
                what.append(f"{dirs} folder(s)")
            if QMessageBox.question(
                self, APP_NAME,
                f"{verb} {' and '.join(what)} to \u201c{mapping.name}\u201d?\n{mapping.path}",
            ) != QMessageBox.Yes:
                return False

        if notes:
            self.statusBar().showMessage(", ".join(notes), 4000)

        self.progress.setRange(0, len(items))
        self.progress.setValue(0)
        self.progress.show()
        self._busy = True
        self.transfer.enqueue({
            "kind": "transfer",
            "files": items,
            "dest": mapping.path,
            "mode": mode,
            "collision": self.settings.get("collision", "rename"),
            "name": mapping.name,
        })
        what = []
        if n_files:
            what.append(f"{n_files} file(s)")
        if dirs:
            what.append(f"{dirs} folder(s)")
        self.log(f"{'Moving' if mode == 'move' else 'Copying'} "
                 f"{' + '.join(what)} -> {mapping.name}")
        return True

    def _on_transfer_started(self, name, total_files, total_bytes):
        big = total_bytes >= SHOW_DIALOG_BYTES or total_files >= SHOW_DIALOG_FILES
        if big:
            self.progress_dialog.start(name, total_files, total_bytes)
            self.progress_dialog.show()
            self.progress_dialog.raise_()

    def _on_file_progress(self, name, copied, total):
        if self.progress_dialog.isVisible():
            self.progress_dialog.set_file(name, copied, total)

    def _on_progress(self, done, total, name):
        self.progress.setRange(0, max(total, 1))
        self.progress.setValue(done)
        if name:
            self.statusBar().showMessage(f"Filing {done + 1}/{total}: {name}")
        if self.progress_dialog.isVisible():
            self.progress_dialog.set_overall(done, total)

    def _on_batch_done(self, summary):
        self._busy = False
        self.progress.hide()
        if self.progress_dialog.isVisible():
            self.progress_dialog.finish(summary)
            QTimer.singleShot(1500, self.progress_dialog.hide)
        errs = summary.get("errors", [])
        if summary["mode"] == "undo":
            self.statusBar().showMessage(
                f"Undo complete: {summary['ok']} restored", 5000)
            self.log(f"Undo complete: {summary['ok']} restored"
                     + (f", {len(errs)} failed" if errs else ""))
        else:
            parts = [f"{summary['ok']} filed to \u201c{summary['name']}\u201d"]
            if summary["skipped"]:
                parts.append(f"{summary['skipped']} skipped")
            if errs:
                parts.append(f"{len(errs)} failed")
            self.statusBar().showMessage(" \u00b7 ".join(parts), 6000)
            self.log("Filed " + " \u00b7 ".join(parts))
            if summary["undo"]:
                self.undo_stack.append(summary["undo"])

        # Errors are recorded individually and surfaced in a popup.
        if errs:
            for n, e in errs:
                self.log(f"ERROR filing {n}: {e}")
            detail = "\n".join(f"\u2022 {n}: {e}" for n, e in errs[:12])
            more = "" if len(errs) <= 12 else f"\n\u2026and {len(errs) - 12} more"
            where = summary.get("name", "")
            head = (f"{len(errs)} file(s) could not be "
                    + ("restored" if summary["mode"] == "undo" else "filed")
                    + (f" to \u201c{where}\u201d" if where and summary['mode'] != 'undo' else "")
                    + ":")
            QMessageBox.warning(self, "Some files had problems",
                                f"{head}\n\n{detail}{more}")
        self.interactive.on_batch_done(summary)
        # destinations may have changed; light re-check of the involved drive
        self.recheck_all()

    # ---- undo ----
    def undo_last(self):
        if self._busy:
            self.statusBar().showMessage("Busy - try undo again in a moment.", 3000)
            return
        if not self.undo_stack:
            self.statusBar().showMessage("Nothing to undo.", 3000)
            return
        records = self.undo_stack.pop()
        self.progress.setRange(0, len(records))
        self.progress.setValue(0)
        self.progress.show()
        self._busy = True
        self.transfer.enqueue({"kind": "undo", "records": records, "name": "Undo"})
        self.log(f"Undoing last batch ({len(records)} file(s))...")

    # ---- reachability ----
    def recheck_all(self):
        if self.mappings:
            self.checker.check_many(self.mappings)

    def _on_reachable(self, mid, ok):
        if self._closing:
            return
        tile = self.tiles.get(mid)
        if tile:
            tile.set_reachable(ok)
        if ok:
            m = self._mapping_by_id(mid)
            tile = self.tiles.get(mid)
            # only fill a missing cover here - the periodic re-check must not
            # keep reshuffling covers while the user is looking at them
            if m and tile and tile.isVisible() and not tile._has_cover:
                self._request_tile_cover("m", m, force=False)

    def _mapping_by_id(self, mid):
        return next((m for m in self.mappings if m.id == mid), None)

    def _cover_folders(self, kind, obj):
        """Folders a tile's cover may come from. A group with no path of its
        own borrows from the folders nested inside it."""
        if kind == "m":
            return [obj.path] if obj.path else []
        if obj.path:
            return [obj.path]
        gids, mids = self._group_subtree_ids(obj.id)
        out = [g.path for g in self.groups if g.id in gids and g.path]
        out += [m.path for m in self.mappings if m.id in mids and m.path]
        random.shuffle(out)
        return out[:12]

    def _tile_for(self, key):
        kind, _, oid = key.partition(":")
        return (self.tiles if kind == "m" else self.group_tiles).get(oid)

    def _request_tile_cover(self, kind, obj, force=False):
        key = f"{kind}:{obj.id}"
        tile = self._tile_for(key)
        if tile is None:
            return
        if not force and (tile._has_cover or key in self._cover_inflight
                          or getattr(tile, "_cover_empty", False)):
            return
        folders = self._cover_folders(kind, obj)
        if not folders:
            tile.clear_cover()
            return
        seq = self._cover_seq.get(key, 0) + 1
        self._cover_seq[key] = seq
        self._cover_inflight.add(key)
        self.thumbs.request(key, seq, folders, avoid=tile.cover_path)

    def _request_cover(self, mapping):
        """Back-compat entry point: pick a fresh random cover for a folder tile."""
        self._request_tile_cover("m", mapping, force=True)

    def _on_thumb(self, key, seq, chosen, image):
        if self._closing:
            return
        if seq != self._cover_seq.get(key):
            return                      # an older pick finished after a newer request
        self._cover_inflight.discard(key)
        tile = self._tile_for(key)
        if tile is None:
            return
        if image is not None and not image.isNull():
            pm = rounded_cover_pixmap(
                QPixmap.fromImage(image), COVER_W, COVER_H, COVER_RADIUS)
            tile.set_cover(pm, chosen or "")
            tile._cover_empty = False
        elif chosen == "":
            tile.clear_cover()
            tile._cover_empty = True    # retried only when a level is (re)opened
        elif not tile._has_cover:
            tile._cover_empty = True
        # chosen None: unreachable/transient -> keep whatever is shown

    def refresh_cover(self, mapping):
        """Right-click "Refresh cover image": pick another random image now."""
        self._request_tile_cover("m", mapping, force=True)

    def _apply_timer(self):
        secs = int(self.settings.get("auto_check_seconds", 20))
        if secs > 0:
            self.timer.start(secs * 1000)
        else:
            self.timer.stop()

    # ---- network folder scan ----
    def scan_now(self):
        roots = [r for r in (self.settings.get("scan_roots") or []) if r]
        if not roots:
            QMessageBox.information(
                self, APP_NAME,
                "No scan roots configured yet.\n\n"
                "Open Settings \u2192 Network scan roots \u2192 Manage\u2026 to add a "
                "drive or folder to scan.")
            return
        if self._scan_busy:
            self.statusBar().showMessage("A scan is already running\u2026", 3000)
            return
        self.statusBar().showMessage(f"Scanning {len(roots)} root(s)\u2026")
        self._start_scan(roots)

    def _start_scan(self, roots):
        self._scan_busy = True
        self._scan_pending += len(roots)
        ignored = {_norm_path(p) for p in (self.settings.get("ignored_scan_paths") or [])}
        self.scanner.scan_roots(roots, ignored)

    def _scan_step_done(self):
        self._scan_pending = max(0, self._scan_pending - 1)
        if self._scan_pending == 0:
            self._scan_busy = False
            self.statusBar().showMessage("Scan complete.", 4000)

    def _on_scan_result(self, root, folders, truncated):
        if self._closing:
            return
        pend = self._pending_imports.pop(_norm_path(root), None)
        if pend is not None:
            self._scan_step_done()
            self._finish_import(root, pend, folders, reachable=True)
            if truncated:
                self.log(f"Import of \u201c{root}\u201d stopped after {SCAN_FOLDER_CAP} "
                         f"folders \u2014 add a more specific subfolder to see the rest.")
            return
        added_g, added_m = self._apply_scan_results(root, folders)
        if added_g or added_m:
            self.log(f"Scan of \u201c{root}\u201d: added {added_g} group(s) and "
                     f"{added_m} folder tile(s)")
        if truncated:
            self.log(f"Scan of \u201c{root}\u201d stopped early after "
                      f"{SCAN_FOLDER_CAP} folders \u2014 point a root at a more "
                      f"specific subfolder to see everything below it.")
        self._scan_step_done()

    def _on_scan_error(self, root, msg):
        if self._closing:
            return
        pend = self._pending_imports.pop(_norm_path(root), None)
        if pend is not None:
            self._scan_step_done()
            self._finish_import(root, pend, [], reachable=False)
            return
        self.log(f"Scan skipped \u201c{root}\u201d: {msg}")
        self._scan_step_done()

    def _existing_scan_paths(self):
        paths = {_norm_path(m.path) for m in self.mappings if m.path}
        paths |= {_norm_path(g.path) for g in self.groups if g.path}
        return paths

    def _find_group_id_by_path(self, norm):
        for g in self.groups:
            if g.path and _norm_path(g.path) == norm:
                return g.id
        return None

    def _ignore_scan_path(self, path):
        """Remember a removed scanned tile's path so future scans skip it."""
        if not path:
            return
        norm = _norm_path(path)
        lst = self.settings.setdefault("ignored_scan_paths", [])
        if norm not in lst:
            lst.append(norm)
            self._save()

    def _apply_scan_results(self, root_path, folders):
        """
        folders: top-down list of (rel_parts, abs_path) under root_path, as found
        by DriveScanner (parents always appear before their children).

        Mirrors the real tree using nested Groups up to MAX_GROUP_DEPTH levels
        (a Group with `path` set is already a valid drop destination). Anything
        nested deeper is added as a flat Mapping tile inside its deepest allowed
        Group ancestor, labeled with the remaining relative path so nothing is
        silently left unmapped. Paths that already match an existing Mapping or
        Group (manual or from an earlier scan) are left alone; a folder whose
        existing entry is a plain Mapping (not a Group) can't hold children, so
        anything under it is skipped rather than guessed at.
        """
        ignored = {_norm_path(p) for p in (self.settings.get("ignored_scan_paths") or [])}
        root_norm = _norm_path(root_path)
        if root_norm in ignored:
            return 0, 0

        existing = self._existing_scan_paths()
        added_groups = 0
        new_mappings = []
        cap_hit = False

        group_id_of = {}        # rel_parts (a realized group) -> group id
        nearest_group = {}      # rel_parts -> rel_parts of nearest group ancestor (or itself)

        if root_norm in existing:
            root_gid = self._find_group_id_by_path(root_norm)
            if root_gid is not None:
                group_id_of[()] = root_gid
                nearest_group[()] = ()
            # else: root is already a plain Mapping -> nothing can nest under it
        else:
            name = os.path.basename(root_path.rstrip("\\/")) or root_path
            root_gid = self._make_group(name, "", path=root_path)
            self._group_by_id(root_gid).scanned = True
            existing.add(root_norm)
            added_groups += 1
            group_id_of[()] = root_gid
            nearest_group[()] = ()

        for rel_parts, abs_path in folders:
            norm = _norm_path(abs_path)

            # Existence/ignore are checked before looking at the parent chain:
            # a folder already tracked from an earlier scan (or already ignored)
            # must be recognized on its own, even if its filesystem parent was
            # since ungrouped/ignored and can no longer host *new* children.
            if norm in ignored:
                continue   # explicitly removed before; don't recreate, and don't descend
            if norm in existing:
                gid = self._find_group_id_by_path(norm)
                if gid is not None:
                    group_id_of[rel_parts] = gid
                    nearest_group[rel_parts] = rel_parts
                # else: an existing plain Mapping - can't host children, leave unset
                continue

            parent_key = rel_parts[:-1]
            parent_group_key = nearest_group.get(parent_key)
            if parent_group_key is None:
                continue   # ancestor wasn't (and couldn't become) a group; nothing to attach to

            depth = len(rel_parts) + 1
            if depth <= SCAN_MAX_GROUP_DEPTH:
                parent_gid = group_id_of[parent_group_key]
                gid = self._make_group(rel_parts[-1], parent_gid, path=abs_path)
                self._group_by_id(gid).scanned = True
                group_id_of[rel_parts] = gid
                nearest_group[rel_parts] = rel_parts
                existing.add(norm)
                added_groups += 1
            elif len(self.mappings) + len(new_mappings) >= MAX_FOLDERS:
                cap_hit = True
                nearest_group[rel_parts] = parent_group_key   # keep chain alive for siblings' sake
            else:
                parent_gid = group_id_of[parent_group_key]
                label = " / ".join(rel_parts[len(parent_group_key):])
                mp = Mapping(id=uuid.uuid4().hex, name=label, path=abs_path,
                             color=TILE_PALETTE[(len(self.mappings) + len(new_mappings))
                                                 % len(TILE_PALETTE)],
                             group=parent_gid, scanned=True)
                self.mappings.append(mp)
                new_mappings.append(mp)
                existing.add(norm)
                nearest_group[rel_parts] = parent_group_key

        if cap_hit:
            self.log(f"Scan stopped adding folder tiles from \u201c{root_path}\u201d: "
                      f"the {MAX_FOLDERS}-folder limit was reached.")

        if added_groups or new_mappings:
            if self.active_id is None and new_mappings:
                self.active_id = new_mappings[0].id
            self._after_change()
            if new_mappings:
                self.checker.check_many(new_mappings)
        return added_groups, len(new_mappings)

    # ---- misc actions ----
    def open_in_explorer(self, path):
        if not is_path_reachable(path):
            QMessageBox.warning(
                self, "Drive not reachable",
                f"Could not open:\n{path}\n\nThe drive or share appears to be offline.")
            return
        try:
            if sys.platform.startswith("win"):
                os.startfile(path)  # type: ignore[attr-defined]
            elif sys.platform == "darwin":
                import subprocess
                subprocess.Popen(["open", path])
            else:
                import subprocess
                subprocess.Popen(["xdg-open", path])
        except Exception as e:
            QMessageBox.warning(self, APP_NAME, f"Could not open folder:\n{e}")

    def _copy_path(self, path):
        QApplication.clipboard().setText(path)
        self.statusBar().showMessage("Path copied to clipboard.", 2500)

    def open_settings(self):
        dlg = SettingsDialog(self, self.settings)
        if dlg.exec() == QDialog.Accepted:
            self.settings.update(dlg.values())
            self._apply_timer()
            self._apply_wallpaper()
            self._save()
            self.recheck_all()

    def _apply_wallpaper(self):
        path = self.settings.get("background_image", "")
        pm = None
        if path and os.path.isfile(path):
            loaded = QPixmap(path)
            if not loaded.isNull():
                pm = loaded
        self.canvas.set_wallpaper(pm)

    def toggle_log(self):
        self.log_panel.setVisible(not self.log_panel.isVisible())
        if self.log_panel.isVisible():
            self.log_view.moveCursor(QTextCursor.End)

    def _load_log_into_view(self):
        entries = load_log_entries()
        shown = entries[-LOG_VIEW_MAX:]
        if shown:
            self.log_view.setPlainText("\n".join(
                f"[{ts.strftime('%Y-%m-%d %H:%M:%S')}] {msg}" for ts, msg in shown))
            self.log_view.moveCursor(QTextCursor.End)

    def log(self, msg):
        ts = datetime.now()
        self.log_view.appendPlainText(f"[{ts.strftime('%Y-%m-%d %H:%M:%S')}] {msg}")
        append_log_entry(ts, msg)

    def clear_logs(self):
        r = QMessageBox.question(
            self, APP_NAME,
            "Clear the entire activity log? This can't be undone.",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if r == QMessageBox.Yes:
            clear_log_file()
            self.log_view.clear()
            self.log("Activity log cleared")

    def _save(self):
        save_config(self.mappings, self.groups, self.settings)

    # ---- shutdown ----
    def closeEvent(self, e):
        self._closing = True
        try:
            self.interactive.save_state()
            self.interactive.deactivate()
            self.interactive.shutdown()
        except Exception:
            pass
        self._save()
        try:
            self.transfer.stop()
            self.transfer.wait(2000)
        except Exception:
            pass
        try:
            self.checker.shutdown()
        except Exception:
            pass
        try:
            self.thumbs.shutdown()
        except Exception:
            pass
        try:
            self.scanner.shutdown()
        except Exception:
            pass
        super().closeEvent(e)


# --------------------------------------------------------------------------- #
# Style
# --------------------------------------------------------------------------- #
STYLESHEET = """
* { font-family: "Segoe UI", "Inter", sans-serif; font-size: 13px; color: #e5e7eb; }
QMainWindow, QWidget { background: #0e1116; }
#toolbar { background: #131722; border-bottom: 1px solid #232a36; }
#appTitle { font-size: 16px; font-weight: 700; color: #f3f4f6; }
QPushButton {
    background: #1f2532; border: 1px solid #2c3442; border-radius: 8px;
    padding: 6px 12px;
}
QPushButton:hover { background: #28303f; }
QPushButton:pressed { background: #161b25; }
#cycleBtn { font-size: 16px; padding: 4px; }
QLineEdit, QComboBox, QSpinBox, QPlainTextEdit {
    background: #161b24; border: 1px solid #2c3442; border-radius: 8px; padding: 6px;
    selection-background-color: #2563eb;
}
QComboBox QAbstractItemView {
    background: #161b24; border: 1px solid #2c3442; selection-background-color: #2563eb;
}
#activeTitle { font-size: 15px; font-weight: 700; color: #f9fafb; }
#activeHint { color: #9aa4b2; }
#folderDropLabel { color: #cbd5e1; font-weight: 600; }
#folderDropSub { color: #8b95a3; font-size: 11px; }
#rowPath { color: #9aa4b2; }
#rowDel { padding: 0px; font-weight: bold; }
#tileName { font-weight: 600; color: #eef2f7; }
#tileCat { color: #8b95a3; font-size: 11px; }
#groupTag { color: #93c5fd; font-size: 9px; font-weight: 700; letter-spacing: 1px; }
#groupCount {
    color: #cbd5e1; background: #2a3344; border-radius: 8px;
    padding: 0px 6px; font-size: 11px; font-weight: 700;
}
#crumb { background: #10141c; border-bottom: 1px solid #232a36; }
#crumbLabel { color: #cbd5e1; font-weight: 600; }
#selBar { background: #122031; border-bottom: 1px solid #1e3350; }
#selLabel { color: #bae6fd; font-weight: 600; }
#progTitle { color: #eef2f7; font-size: 14px; font-weight: 600; }
#progFile { color: #cbd5e1; }
#logPanel { background: #10141c; border-top: 1px solid #232a36; }
#logTitle { color: #cbd5e1; font-weight: 600; }
#emptyLabel { color: #7b8696; font-size: 14px; }
#scroll { border: none; }
QScrollArea > QWidget > QWidget { background: #0e1116; }
QProgressBar {
    border: 1px solid #2c3442; border-radius: 7px; background: #161b24;
    text-align: center; height: 16px;
}
QProgressBar::chunk { background: #2563eb; border-radius: 6px; }
QStatusBar { background: #131722; border-top: 1px solid #232a36; color: #b9c2cf; }
#log { font-family: Consolas, monospace; font-size: 12px; }
QMenu { background: #161b24; border: 1px solid #2c3442; }
QMenu::item:selected { background: #2563eb; }
QToolTip { background: #1f2532; color: #e5e7eb; border: 1px solid #2c3442; }
#viewSeg { padding: 6px 12px; }
#layoutToggle { padding: 6px 12px; font-weight: 700; }
#layoutToggle:checked { background: #1d4ed8; border: 1px solid #3b82f6; color: #ffffff; }
#selCountLbl { color: #93c5fd; font-weight: 700; }
#deleteBtn {
    background: #7f1d1d; border: 1px solid #dc2626; color: #fee2e2; font-weight: 700;
    padding: 6px 12px;
}
#deleteBtn:hover { background: #991b1b; border-color: #ef4444; }
#deleteBtn:pressed { background: #5f1414; }
#deleteBtn:disabled { background: #2a1a1a; border-color: #3f2a2a; color: #7a5a5a; }
#viewSeg:checked { background: #1d4ed8; border: 1px solid #3b82f6; color: #ffffff; font-weight: 700; }
#srcPane, #destPane { background: #0e1116; }
#paneTitle { color: #93c5fd; font-size: 11px; font-weight: 700; letter-spacing: 1px; }
#stageName { color: #f3f4f6; font-size: 14px; font-weight: 600; }
#counterLbl { color: #e5e7eb; font-weight: 700; }
#imageStage { border-radius: 10px; }
QSplitter::handle { background: #1a202b; }
QSplitter::handle:hover { background: #2563eb; }
QTreeWidget, QListWidget {
    background: #121720; border: 1px solid #232a36; border-radius: 8px; padding: 4px;
    outline: 0;
}
QTreeWidget::item, QListWidget::item { padding: 4px 2px; border-radius: 5px; }
QTreeWidget::item:hover { background: #1c2331; }
QTreeWidget::item:selected, QListWidget::item:selected { background: #2563eb; color: #ffffff; }
"""


def main():
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    win = MainWindow()
    win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
