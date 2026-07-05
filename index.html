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
from datetime import datetime, timedelta
from dataclasses import dataclass, asdict
from concurrent.futures import ThreadPoolExecutor
from queue import Queue

from PySide6.QtCore import Qt, QObject, Signal, QThread, QTimer, QSize, QRect, QPoint, QMimeData
from PySide6.QtGui import (
    QColor, QFont, QShortcut, QKeySequence, QFontMetrics,
    QPixmap, QImage, QPainter, QPainterPath, QDrag, QTextCursor,
)
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QFrame, QLabel, QPushButton, QLineEdit,
    QComboBox, QVBoxLayout, QHBoxLayout, QScrollArea, QLayout,
    QFileDialog, QColorDialog, QDialog, QFormLayout, QDialogButtonBox, QMessageBox,
    QMenu, QPlainTextEdit, QCheckBox, QSpinBox, QProgressBar, QInputDialog,
)

APP_NAME = "Image Sorter"
MAX_FOLDERS = 200
GROUP_MIME = "application/x-imagesorter-group"   # drag payload: a group id
FOLDER_MIME = "application/x-imagesorter-folders"  # drag payload: folder ids (csv)
BATCH_LIMIT = 10          # max folders addable in one "Add folders" session
MAX_GROUP_DEPTH = 4       # how deep groups may nest (Books > Action > ... )
BIG_FILE_BYTES = 8 * 1024 * 1024   # show per-file % and chunked copy above this
SHOW_DIALOG_BYTES = 8 * 1024 * 1024  # pop the progress window for batches >= this
SHOW_DIALOG_FILES = 25               # ...or with at least this many files
TILE_W = 156
TILE_H = 150
COVER_W = 136             # thumbnail cover banner inside a tile
COVER_H = 72
COVER_RADIUS = 8

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

MEDIA_EXTS = IMAGE_EXTS | VIDEO_EXTS

DEFAULT_SETTINGS = {
    "mode": "move",            # "move" or "copy"
    "collision": "rename",     # "rename" | "skip" | "overwrite"
    "media_only": True,        # if True, non-media (non image/video) files are skipped
    "confirm_each": False,     # if True, ask before every drop
    "auto_check_seconds": 20,  # how often to re-check reachability
    "background_image": "",    # optional home-screen wallpaper path
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
        )


@dataclass
class Group:
    id: str
    name: str
    color: str = "#64748b"
    parent: str = ""           # parent group id, "" = top level

    @staticmethod
    def from_dict(d: dict) -> "Group":
        return Group(
            id=str(d.get("id") or uuid.uuid4().hex),
            name=str(d.get("name", "")).strip(),
            color=str(d.get("color") or "#64748b"),
            parent=str(d.get("parent", "")).strip(),
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
    settings = dict(DEFAULT_SETTINGS)
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

    def set_cover(self, pixmap: QPixmap):
        self._has_cover = True
        self.cover_lbl.setText("")
        self.cover_lbl.setStyleSheet("background:transparent;")
        self.cover_lbl.setPixmap(pixmap)

    def clear_cover(self):
        self._has_cover = False
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
    newSubgroupRequested = Signal(object)
    moveUpRequested = Signal(object)
    moveTopRequested = Signal(object)
    reparentRequested = Signal(str, str)    # source group id, target (new parent) id
    foldersDroppedOnGroup = Signal(list, object)   # (dragged folder ids, this Group)

    def __init__(self, group: "Group"):
        super().__init__()
        self.group = group
        self.can_nest = True       # set by the window before refresh
        self.has_parent = False
        self.validate_drop = None  # callable(src_gid, dst_gid) -> bool, set by window
        self._press_pos = None
        self._drop_hover = False
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
        root.addStretch(1)

        self.icon = QLabel()
        self.icon.setFixedSize(56, 56)
        self.icon.setAlignment(Qt.AlignCenter)
        f = QFont()
        f.setPointSize(20)
        f.setBold(True)
        self.icon.setFont(f)
        root.addWidget(self.icon, 0, Qt.AlignHCenter)

        self.name_lbl = QLabel()
        self.name_lbl.setObjectName("tileName")
        self.name_lbl.setAlignment(Qt.AlignHCenter)
        root.addWidget(self.name_lbl)

        self.hint = QLabel("double-click to open \u00b7 drag to move")
        self.hint.setObjectName("tileCat")
        self.hint.setAlignment(Qt.AlignHCenter)
        root.addWidget(self.hint)
        root.addStretch(1)

        self.refresh()

    def set_count(self, n):
        self.count_lbl.setText(str(n))

    def refresh(self):
        name = self.group.name or "(group)"
        initial = next((ch for ch in name if ch.isalnum()), "?").upper()
        fg = contrast_text(self.group.color)
        self.icon.setText(initial)
        self.icon.setStyleSheet(
            f"background:{self.group.color}; color:{fg}; border-radius:8px;"
        )
        fm = QFontMetrics(self.name_lbl.font())
        self.name_lbl.setText(fm.elidedText(name, Qt.ElideRight, TILE_W - 22))
        self.setToolTip(f"Group: {name}\nDouble-click to open \u00b7 drag onto another "
                        f"group to nest it")
        self._apply_style()

    def _apply_style(self):
        if self._drop_hover:
            self.setStyleSheet(
                "QFrame#groupTile{background:#202a3a;border:2px dashed #f59e0b;"
                "border-radius:14px;}")
        else:
            self.setStyleSheet(
                f"QFrame#groupTile{{background:#171c26;"
                f"border:2px solid {self.group.color};border-radius:14px;}}")

    def _set_drop_hover(self, on):
        if on != self._drop_hover:
            self._drop_hover = on
            self._apply_style()

    def mouseDoubleClickEvent(self, e):
        if e.button() == Qt.LeftButton:
            self.enterRequested.emit(self.group)

    # ---- drag source (move this group) ----
    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._press_pos = e.position().toPoint()
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if (e.buttons() & Qt.LeftButton) and self._press_pos is not None:
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

    def dragEnterEvent(self, e):
        if self._group_ok(self._dragged_group(e)) or self._folders_ok(e):
            e.acceptProposedAction()
            self._set_drop_hover(True)
        else:
            e.ignore()

    def dragMoveEvent(self, e):
        if self._group_ok(self._dragged_group(e)) or self._folders_ok(e):
            e.acceptProposedAction()
        else:
            e.ignore()

    def dragLeaveEvent(self, e):
        self._set_drop_hover(False)

    def dropEvent(self, e):
        self._set_drop_hover(False)
        src = self._dragged_group(e)
        if self._group_ok(src):
            e.acceptProposedAction()
            self.reparentRequested.emit(src, self.group.id)
            return
        ids = decode_folder_ids(e.mimeData())
        if ids:
            e.acceptProposedAction()
            self.foldersDroppedOnGroup.emit(ids, self.group)
            return
        e.ignore()

    def _menu(self, pos):
        menu = QMenu(self)
        menu.addAction("Open", lambda: self.enterRequested.emit(self.group))
        sub = menu.addAction("New subgroup\u2026",
                             lambda: self.newSubgroupRequested.emit(self.group))
        sub.setEnabled(self.can_nest)
        if not self.can_nest:
            sub.setToolTip("Maximum nesting depth reached")
        menu.addSeparator()
        menu.addAction("Rename\u2026", lambda: self.renameRequested.emit(self.group))
        menu.addAction("Change color\u2026", lambda: self.recolorRequested.emit(self.group))
        if self.has_parent:
            menu.addSeparator()
            menu.addAction("Move up one level",
                           lambda: self.moveUpRequested.emit(self.group))
            menu.addAction("Move to top level",
                           lambda: self.moveTopRequested.emit(self.group))
        menu.addSeparator()
        menu.addAction("Ungroup (free contents)",
                       lambda: self.ungroupRequested.emit(self.group))
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

        self.hint = QLabel("Drag images or videos here to file them into the active target")
        self.hint.setObjectName("activeHint")
        self.hint.setAlignment(Qt.AlignCenter)
        root.addWidget(self.hint, 1)

        self._apply_style()

    def set_mapping(self, mapping):
        self._mapping = mapping
        if mapping:
            self.title.setText(f"Active target:  {mapping.name}")
            self.hint.setText(f"Drop images or videos here  \u2192  {mapping.path}")
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
            try:
                total_bytes += os.path.getsize(s)
            except OSError:
                pass
        self.signals.started.emit(name, total, total_bytes)
        ok = 0
        skipped = 0
        errors = []
        undo = []

        for i, src in enumerate(files, start=1):
            base = os.path.basename(src)
            self.signals.progress.emit(i - 1, total, base)
            final = None
            try:
                final = resolve_destination(dest, base, collision)
                if final is None:
                    skipped += 1
                    self.signals.log.emit(f"Skipped (already exists): {base}")
                    continue
                if os.path.exists(final):       # overwrite mode
                    os.remove(final)
                cb = (lambda copied, tot, _b=base:
                      self.signals.fileProgress.emit(_b, copied, tot))
                transfer_one(src, final, mode, cb)
                ok += 1
                undo.append({"mode": mode, "src": src, "dest": final})
            except Exception as e:
                errors.append((base, str(e)))
                # best-effort: clean a partial file we created
                try:
                    if final and os.path.exists(final) and mode == "copy":
                        os.remove(final)
                except Exception:
                    pass
                self.signals.log.emit(f"FAILED {base}: {e}")

        self.signals.progress.emit(total, total, "")
        self.signals.batchDone.emit({
            "name": name, "mode": mode, "total": total,
            "ok": ok, "skipped": skipped, "errors": errors, "undo": undo,
        })

    def _process_undo(self, batch):
        records = batch["records"]
        total = len(records)
        total_bytes = 0
        for rec in records:
            try:
                total_bytes += os.path.getsize(rec["dest"])
            except OSError:
                pass
        self.signals.started.emit(batch.get("name", "Undo"), total, total_bytes)
        restored = 0
        errors = []
        for i, rec in enumerate(reversed(records), start=1):
            base = os.path.basename(rec["dest"])
            self.signals.progress.emit(i - 1, total, base)
            try:
                if rec["mode"] == "move":
                    os.makedirs(os.path.dirname(rec["src"]), exist_ok=True)
                    if os.path.exists(rec["dest"]):
                        cb = (lambda copied, tot, _b=base:
                              self.signals.fileProgress.emit(_b, copied, tot))
                        transfer_one(rec["dest"], rec["src"], "move", cb)
                        restored += 1
                else:  # copy -> remove the copy we made
                    if os.path.exists(rec["dest"]):
                        os.remove(rec["dest"])
                        restored += 1
            except Exception as e:
                errors.append((os.path.basename(rec["dest"]), str(e)))
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
    # mapping id, chosen basename ("" = no cover), QImage or None
    result = Signal(str, str, object)


class ThumbnailLoader:
    """Resolves and decodes a folder's cover image off the GUI thread.

    Result semantics (chosen, image):
      - (name, QImage) -> a new cover to display + persist
      - ("",   None)   -> folder has no usable image; show the letter fallback
      - (name, None)   -> stored cover is still valid and already shown; keep it
    """
    def __init__(self):
        self.signals = ThumbnailSignals()
        self._pool = ThreadPoolExecutor(max_workers=4)

    def request(self, mid, folder, stored, have_cover):
        self._pool.submit(self._one, mid, folder, stored or "", bool(have_cover))

    def _one(self, mid, folder, stored, have_cover):
        try:
            imgs = list_cover_candidates(folder)
        except Exception:
            return  # unreachable / transient error: leave the tile as-is
        if not imgs:
            self.signals.result.emit(mid, "", None)
            return
        chosen = stored if stored in imgs else random.choice(imgs)
        if have_cover and chosen == stored:
            self.signals.result.emit(mid, chosen, None)   # unchanged; keep
            return
        img = scaled_cover_image(os.path.join(folder, chosen), COVER_W, COVER_H)
        pool = [f for f in imgs if f != chosen]
        tries = 0
        while (img is None or img.isNull()) and pool and tries < 5:
            chosen = random.choice(pool)
            pool.remove(chosen)
            tries += 1
            img = scaled_cover_image(os.path.join(folder, chosen), COVER_W, COVER_H)
        if img is None or img.isNull():
            self.signals.result.emit(mid, "", None)
        else:
            self.signals.result.emit(mid, chosen, img)

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
        out = []
        for r in self._rows:
            v = r.values()
            v["category"] = cat
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
            "Only file image & video types (skip other files in a drop)")
        self.media_only.setChecked(bool(settings.get("media_only", True)))
        form.addRow(self.media_only)

        self.confirm_each = QCheckBox("Ask for confirmation before every drop")
        self.confirm_each.setChecked(bool(settings.get("confirm_each", False)))
        form.addRow(self.confirm_each)

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

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        form.addRow(buttons)

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
        return {
            "collision": self.collision.currentText(),
            "media_only": self.media_only.isChecked(),
            "confirm_each": self.confirm_each.isChecked(),
            "auto_check_seconds": self.interval.value(),
            "background_image": self._bg_path,
        }


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
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.resize(960, 720)

        self.mappings, self.groups, self.settings = load_config()
        self.tiles = {}            # mapping id -> DropTile
        self.group_tiles = {}      # group id -> GroupTile
        self.active_id = self.mappings[0].id if self.mappings else None
        self.current_group = None  # None = top level, else a group id
        self.selected_ids = set()  # mapping ids selected via Ctrl+click
        self.undo_stack = []       # list of undo-record lists
        self._busy = False

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

        self._build_ui()
        self._apply_wallpaper()
        self._rebuild_grid()
        self._update_active_zone()
        self.recheck_all()

        self.timer = QTimer(self)
        self.timer.timeout.connect(self.recheck_all)
        self._apply_timer()

        self._install_shortcuts()

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

        title = QLabel(APP_NAME)
        title.setObjectName("appTitle")
        tb.addWidget(title)

        self.mode_btn = QPushButton()
        self.mode_btn.setCheckable(True)
        self.mode_btn.setChecked(self.settings.get("mode", "move") == "move")
        self.mode_btn.clicked.connect(self._toggle_mode)
        self._refresh_mode_btn()
        tb.addSpacing(8)
        tb.addWidget(self.mode_btn)

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

        for text, slot in [
            ("Add folder", self.add_folder),
            ("New group", self.create_group_here),
            ("Undo", self.undo_last),
            ("Re-check", self.recheck_all),
            ("Log", self.toggle_log),
            ("Settings", self.open_settings),
        ]:
            b = QPushButton(text)
            b.clicked.connect(slot)
            tb.addWidget(b)

        outer.addWidget(bar)

        # active zone
        wrap = QWidget()
        wl = QVBoxLayout(wrap)
        wl.setContentsMargins(16, 14, 16, 6)
        self.active_zone = ActiveZone()
        self.active_zone.filesDropped.connect(self._drop_on_active)
        self.active_zone.prevClicked.connect(lambda: self.cycle_target(-1))
        self.active_zone.nextClicked.connect(lambda: self.cycle_target(+1))
        wl.addWidget(self.active_zone)
        outer.addWidget(wrap)

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
        outer.addWidget(self.crumb)

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
        self.clear_sel_btn = QPushButton("Clear")
        self.clear_sel_btn.clicked.connect(self.clear_selection)
        sl.addWidget(self.clear_sel_btn, 0)
        self.sel_bar.hide()
        outer.addWidget(self.sel_bar)

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
        outer.addWidget(self.canvas, 1)

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
        self.setStyleSheet(STYLESHEET)

    def _install_shortcuts(self):
        QShortcut(QKeySequence("Ctrl+N"), self, self.add_folder)
        QShortcut(QKeySequence("Ctrl+Z"), self, self.undo_last)
        QShortcut(QKeySequence("Ctrl+F"), self, lambda: self.search.setFocus())
        QShortcut(QKeySequence("Ctrl+Right"), self, lambda: self.cycle_target(+1))
        QShortcut(QKeySequence("Ctrl+Left"), self, lambda: self.cycle_target(-1))
        QShortcut(QKeySequence("Ctrl+M"), self, self._toggle_mode)

    # ---- mode ----
    def _toggle_mode(self):
        new = "copy" if self.settings.get("mode") == "move" else "move"
        self.settings["mode"] = new
        self.mode_btn.setChecked(new == "move")
        self._refresh_mode_btn()
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
            gt.newSubgroupRequested.connect(self.new_subgroup_in)
            gt.moveUpRequested.connect(self.move_group_up)
            gt.moveTopRequested.connect(self.move_group_top)
            gt.reparentRequested.connect(self.reparent_group)
            gt.foldersDroppedOnGroup.connect(self.add_folders_to_group)
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
                self.flow.addWidget(gt)
                gt.show()
        self._update_breadcrumb()
        self._update_selection_bar()
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
            "then drag images or videos onto its tile."
        )

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if self.empty_lbl.isVisible():
            self.empty_lbl.resize(self.grid_host.width(), 200)

    # ---- navigation ----
    def enter_group(self, group):
        self.current_group = group.id
        self.clear_selection()
        self._rebuild_grid()

    def go_home(self):
        self.current_group = None
        self.clear_selection()
        self._rebuild_grid()

    def go_up(self):
        g = self._group_by_id(self.current_group) if self.current_group else None
        self.current_group = g.parent if (g and g.parent) else None
        self.clear_selection()
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

    def clear_selection(self):
        had = bool(self.selected_ids)
        self.selected_ids.clear()
        if had:
            for t in self.tiles.values():
                t.set_selected(False)
        self._update_selection_bar()

    def _update_selection_bar(self):
        n = len(self.selected_ids)
        self.sel_label.setText(f"{n} selected")
        self.group_btn.setEnabled(n > 0)
        self.sel_bar.setVisible(n > 0)

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

    def _make_group(self, name, parent_pid):
        gid = uuid.uuid4().hex
        color = TILE_PALETTE[len(self.groups) % len(TILE_PALETTE)]
        self.groups.append(Group(id=gid, name=name, color=color, parent=parent_pid))
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
            new_ms = []
            for v in dlg.values():
                m = Mapping(id=uuid.uuid4().hex, name=v["name"], path=v["path"],
                            color=v.get("color", "#3b82f6"), category=v.get("category", ""))
                self.mappings.append(m)
                new_ms.append(m)
            if not new_ms:
                return
            if self.active_id is None:
                self.active_id = new_ms[0].id
            self._after_change()
            self.checker.check_many(new_ms)
            if len(new_ms) == 1:
                self.log(f"Added folder: {new_ms[0].name}")
            else:
                self.log(f"Added {len(new_ms)} folders: "
                         + ", ".join(m.name for m in new_ms))

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
        if QMessageBox.question(
            self, APP_NAME,
            f"Remove the tile for \u201c{mapping.name}\u201d?\n\n"
            f"This only removes it from {APP_NAME}. The folder and its files are not touched.",
        ) != QMessageBox.Yes:
            return
        self.mappings = [m for m in self.mappings if m.id != mapping.id]
        tile = self.tiles.pop(mapping.id, None)
        if tile:
            tile.setParent(None)
            tile.deleteLater()
        if self.active_id == mapping.id:
            self.active_id = self.mappings[0].id if self.mappings else None
        self._after_change()
        self.log(f"Removed folder: {mapping.name}")

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
        self._rebuild_grid()
        self._update_active_zone()
        self._save()

    # ---- the drop -> transfer ----
    def handle_drop(self, mapping, paths):
        files, skipped_dirs, skipped_type = [], 0, 0
        media_only = self.settings.get("media_only", True)
        for p in paths:
            if os.path.isdir(p):
                skipped_dirs += 1
                continue
            if media_only and not is_media(p):
                skipped_type += 1
                continue
            files.append(p)

        notes = []
        if skipped_dirs:
            notes.append(f"{skipped_dirs} folder(s) skipped")
        if skipped_type:
            notes.append(f"{skipped_type} non-media file(s) skipped")

        if not files:
            msg = "Nothing to file."
            if notes:
                msg += " (" + ", ".join(notes) + ")"
            self.statusBar().showMessage(msg, 4000)
            return

        if not is_path_reachable(mapping.path):
            tile = self.tiles.get(mapping.id)
            if tile:
                tile.set_reachable(False)
            self.log(f"ERROR: \u201c{mapping.name}\u201d not reachable ({mapping.path}) "
                     f"\u2014 {len(files)} file(s) not moved")
            QMessageBox.warning(
                self, "Drive not reachable",
                f"\u201c{mapping.name}\u201d could not be reached:\n\n{mapping.path}\n\n"
                f"The drive may be disconnected or the network share is offline. "
                f"No files were moved.",
            )
            return

        mode = self.settings.get("mode", "move")
        if self.settings.get("confirm_each", False):
            verb = "Move" if mode == "move" else "Copy"
            if QMessageBox.question(
                self, APP_NAME,
                f"{verb} {len(files)} file(s) to \u201c{mapping.name}\u201d?\n{mapping.path}",
            ) != QMessageBox.Yes:
                return

        if notes:
            self.statusBar().showMessage(", ".join(notes), 4000)

        self.progress.setRange(0, len(files))
        self.progress.setValue(0)
        self.progress.show()
        self._busy = True
        self.transfer.enqueue({
            "kind": "transfer",
            "files": files,
            "dest": mapping.path,
            "mode": mode,
            "collision": self.settings.get("collision", "rename"),
            "name": mapping.name,
        })
        self.log(f"{'Moving' if mode == 'move' else 'Copying'} "
                 f"{len(files)} file(s) -> {mapping.name}")

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
        tile = self.tiles.get(mid)
        if tile:
            tile.set_reachable(ok)
        if ok:
            m = self._mapping_by_id(mid)
            if m:
                self._request_cover(m)

    def _mapping_by_id(self, mid):
        return next((m for m in self.mappings if m.id == mid), None)

    def _request_cover(self, mapping):
        tile = self.tiles.get(mapping.id)
        have = bool(tile and tile._has_cover)
        self.thumbs.request(mapping.id, mapping.path, mapping.cover, have)

    def _on_thumb(self, mid, chosen, image):
        m = self._mapping_by_id(mid)
        if not m:
            return
        if m.cover != chosen:
            m.cover = chosen
            self._save()
        tile = self.tiles.get(mid)
        if not tile:
            return
        if image is not None and not image.isNull():
            pm = rounded_cover_pixmap(
                QPixmap.fromImage(image), COVER_W, COVER_H, COVER_RADIUS)
            tile.set_cover(pm)
        elif chosen == "":
            tile.clear_cover()
        # else: stored cover still valid and already shown -> keep as-is

    def refresh_cover(self, mapping):
        mapping.cover = ""
        tile = self.tiles.get(mapping.id)
        if tile:
            tile.clear_cover()
        self._save()
        self._request_cover(mapping)

    def _apply_timer(self):
        secs = int(self.settings.get("auto_check_seconds", 20))
        if secs > 0:
            self.timer.start(secs * 1000)
        else:
            self.timer.stop()

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
"""


def main():
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    win = MainWindow()
    win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()