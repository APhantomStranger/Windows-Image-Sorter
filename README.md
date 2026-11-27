# Windows Image Sorter

Creates a multi-tiled interface that links to different folders throughout your filesystem or even network drives. Instead of digging through Explorer windows, you drag images (and videos/audio) onto a folder tile, or onto a folder tree, and they're filed there in the background.

**Current version:** 3.3.0 · single file (`image-sorter.py`) · Python + PySide6 only

## Run it

Needs Python 3.10+.

```
py -3.12 -m pip install PySide6
py -3.12 image-sorter.py
```

(`python -m pip install PySide6` and `python image-sorter.py` work too if `python` points at a recent install.)

Settings and the activity log live in `%APPDATA%\ImageSorter\`.

## Two ways to work

Switch with the toolbar buttons or **Ctrl+I**.

### Original Mode: the tile dashboard
- Drag files or whole folders from Explorer onto folder tiles to **move** or **copy** them (toggle with Ctrl+M). Name collisions are auto-renamed.
- **Adding a folder imports its whole subfolder tree.** It becomes a group mirroring every subfolder, so you can double-click into it to reach anything below.
- Every tile shows a **random image from inside that folder**, re-picked each time you open a level. A folder holding only subfolders borrows a picture from them.
- Nested groups, favorites, multi-select (Ctrl+click), and network-drive scan roots that auto-map folder trees on launch.
- Unreachable network drives turn red and block drops with a clear message.

### Interactive Mode: one image at a time
- **Left:** the images sitting in your source folders (Desktop and Downloads by default), shown large. Step through them with the arrow keys, the mouse wheel, or Prev/Next.
- **Right:** every destination folder and its subfolders as a tree, with a filter box. Hovering over a collapsed folder while dragging opens it.
- Drag the big image onto a folder and it's filed. The next image appears automatically.
- **Single / Multiple toggle:** show up to 6 images at once (2 rows × 3 columns). Click to select, **Ctrl+click** or Shift+click to select several, then drag them onto a folder together.
- **Delete** (red trashcan button or the Delete key) sends the image to the Recycle Bin and moves on. Deleting several images always asks first.
- Previews JPEG, PNG, GIF (animated), WebP, BMP, TIFF, SVG and camera RAW (via the embedded preview). HEIC, AVIF and JXL show a placeholder card but can still be dragged.

Both modes use the same transfer engine: background copy/move with progress, **Ctrl+Z undo**, and a persistent activity log.
