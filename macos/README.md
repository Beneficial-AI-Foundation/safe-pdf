# macOS AppKit spike (task 11.1)

Plan.md §6 Phase 11: *"Spike first: a minimal Cocoa window (open, render, scroll, zoom) over
the C API; record the feel delta and the FFI surface in a Decisions entry before committing to
parity."* Plan.md §8: the shell is unverified and replaceable; the core as a library is the
deliverable. This directory is that spike. It is not parity with the Tk viewer (no toolbar,
sidebar, selection, search, links or annotations; that is 11.3).

## Files

| File | Role |
|---|---|
| `../SafePdf/Shell/Ffi.lean` | Lean side: `@[export safepdf_lean_*]` functions over `SafePdf.Api` (open, page count, page size, render, error text) |
| `safepdf_core.h` / `safepdf_core.c` | **The C API**: plain C, no Lean types; runtime initialisation, reference counting, copying pixels out |
| `main.m` | The AppKit app: `NSWindow` + `NSScrollView` (centring clip view) + a page view that draws every page stacked vertically; one render thread |
| `build.sh` | `lake build macosFfi`, then `clang` for the C and Objective-C files, then a link against Lean's runtime; writes `build/safepdf-mac` and `build/SafePdf.app` |
| `selftest.sh` | Headless self-test under a front-app watcher (below) |

## Build and run

```
macos/build.sh                      # needs elan's Lean and the Xcode command line tools only
macos/build/safepdf-mac FILE.pdf    # or without FILE: an Open panel
```

The Lake side is a non-default library `SafePdfFfi` (root `SafePdf.Shell.Ffi`) plus a custom
target `macosFfi`. That target takes the module's own link information, meaning its object
files and those of its whole import closure (the same list Lake links into an executable), and
packs them into `.lake/build/lib/libsafepdfffi.a`. The link line is Lake's executable link
line without the libraries the core does not use:
`-lleancpp -lInit -lStd -lleanrt -lcadical -lc++ -lgmp -luv -framework AppKit -Wl,-dead_strip`.
The default `lake build` is unchanged.

Keys: Cmd+O opens a file, Cmd+ / Cmd= zoom in (×1.25), Cmd- zooms out, Cmd-0 shows the
actual size. Pinch zooms with the trackpad, and scrolling uses the trackpad or mouse wheel.

## The C API (`safepdf_core.h`)

| Function | Contract |
|---|---|
| `int safepdf_init(void)` | Once, on the main thread, before anything else: `lean_initialize_runtime_module`, `initialize_safe_x2dpdf_SafePdf_Shell_Ffi(1)`, `lean_init_task_manager`, `lean_io_mark_end_initialization`. 0 = ok. |
| `void safepdf_thread_enter(void)` / `safepdf_thread_exit(void)` | Register or unregister any other thread that calls the API (`lean_initialize_thread` / `lean_finalize_thread`). |
| `safepdf_doc *safepdf_open(const char *path, char **error)` | The caller owns the result and releases it with `safepdf_close`. On failure it returns NULL and sets `*error` to a `malloc`ed string (the core's English message). The document is `lean_mark_mt`'d, so its object graph uses atomic reference counts and it may be used from several threads at once. Page sizes are read once, at open. |
| `void safepdf_close(safepdf_doc *)` | Drops the document's Lean reference. |
| `size_t safepdf_page_count(const safepdf_doc *)` | No Lean call. |
| `int safepdf_page_size(doc, page, double *w, double *h)` | Displayed CropBox size in points with `/Rotate` applied. Returns -1 when `page` is out of range. |
| `int safepdf_render(doc, page, uint32_t num, uint32_t den, safepdf_image *out, char **error)` | Renders at an exact zoom of `num/den` pixels per point. On success `out->rgba` holds `4·w·h` `malloc`ed bytes (RGBA, A = 255, rows from the top) that the caller owns. The call blocks the calling thread. |
| `void safepdf_image_free(safepdf_image *)` | Frees `rgba` and zeroes the struct. |

**Lean-level ownership** (inside `safepdf_core.c`): Lean v4.36 rejects `@&` (borrowed) parameters
on `@[export]` functions, so every exported Lean function **consumes** its object arguments.
The shim calls `lean_inc(handle)` before each call that passes the document, and `lean_dec`s
every result once it has copied the contents out. An error comes back as an `IO` error whose
text the shim reads with `safepdf_lean_error_text`.

The render path is the Tk viewer's: `Core.Raster.Glyph.renderDocPage` with the substitute
fonts found on the system (`Shell.Fonts.loadSubstFonts`), with no rotation and the default
optional-content state.

## Headless self-test

```
macos/selftest.sh FILE.pdf [OUTDIR]       # OUTDIR defaults to macos/build/selftest
```

`SAFEPDF_MACOS_SELFTEST=DIR` sets `NSApplicationActivationPolicyProhibited` before the core
starts, creates **no window**, and never calls `run` or `activate`. It does the following:

1. It checks the C API (open, page count and size, the error paths, page 1 rendered at 1× and
   2×, and the first 10 pages at 2× with timings).
2. It builds the real `NSScrollView` and page view off screen and drives them through the
   render thread and the main run loop at 1× and at a simulated 2× backing scale. It then sets
   the magnification to 1.5625, as two Cmd+ presses would, and scrolls to page 2.
3. It draws each state into an `NSBitmapImageRep` (`cacheDisplayInRect:`), writes the PNGs
   and `timings.txt` to DIR, and exits.

`selftest.sh` samples `lsappinfo front` every 0.5 s and checks `lsappinfo list` for a
Foreground registration. It kills only its own PID if either shows up.

Measured on this Mac (Apple Silicon, macOS 26), 2026-11-23:

| | arXiv 1706.03762 (15 p.) | NTSB AAR0701 (173 p.) |
|---|---|---|
| process start → core initialised | 57 ms | 42 ms |
| open | 4.2 ms | 5.6 ms |
| page 1 at 1× / 2× (C API) | 76 / 70 ms | 104 / 168 ms |
| pages 1–10 at 2×: mean / worst | 98 / 200 ms | 86 / 166 ms |
| view at 2×: first page drawn / all visible pages | 69 / 365 ms | 166 / 222 ms |
| re-render after zoom ×1.5625 at 2× backing | 186 ms | 289 ms |
| front-app leaks | 0 | 0 |

The sequential render thread explains why "all visible pages" in the view row is roughly the
sum of the page times.

## Feel delta against the Tk viewer

**What the self-test settles:** pages are drawn at backing scale × magnification pixels per
point, so they are sharp on Retina. The zoomed snapshot is rendered at 3.125 px/pt rather than
upscaled. Render latency is the core's (70–200 ms per page at 2× on these files), the same
renderer the Tk viewer uses. AppKit adds a `CGImage` wrap (zero-copy over the `malloc`ed
buffer) and one `memcpy` out of the Lean `ByteArray` (≈7.7 MB at 2× Letter). That copy is included in the timings above and was not measured
separately.

**What only a human can judge** (see the list below): scrolling smoothness, momentum and
rubber-banding, pinch feel, window-resize behaviour, how the app feels at startup, and whether
the blurry-then-sharp swap after a zoom is acceptable. This spike gives those to AppKit:
`NSScrollView` brings native momentum, elasticity and live magnification (the bitmap scales
during the pinch, and the pages are re-rendered when the gesture ends). The Tk viewer emulates
all of these in Tcl. Things to try:

* scroll fast through a long PDF with two-finger flicks (momentum, overscroll bounce, blank pages while renders catch up);
* pinch in and out, and hold mid-pinch (smoothness during the gesture, delay until sharp);
* Cmd+ / Cmd- repeatedly (zoom anchoring at the centre, re-render delay);
* drag the window between a Retina and a non-Retina display;
* resize the window (page centring, scroller behaviour);
* compare the time to first page against `lake exe viewer FILE`.

## Known spike limitations

* One render thread, no cancellation (a generation number only skips stale jobs before they
  start). Visible pages therefore render one after another.
* Opening a second document leaks the first: a queued job may still hold the raw pointer.
  11.2 needs reference-counted handles (`safepdf_retain`/`release`) or a close that drains the
  queue.
* No page labels, rotation, optional content, text, links, outline or annotations in the C API yet.
* `allowedFileTypes` is deprecated (warning suppressed). Use `UTType` in 11.3.

## Open questions for 11.2

1. **Where the shared logic lives.** View, Select, Links, Marks and Save are Lean today
   (`SafePdf/Shell/App/*`, Tk-free). They could be exported through the C API (one Lean
   source of truth: proofs such as the selection/search soundness carry over, but every UI
   event crosses the FFI), or the AppKit shell could reimplement them in Objective-C/Swift
   (natural with AppKit, but the logic is duplicated and the proofs no longer apply). A
   middle path: export *pure* functions (state in, state out, or plain data such as glyph
   boxes and hit tests) and keep the UI state machines native.
2. **A C API shape for structured data**: glyph lists, outline and annotations. One option is
   flat C structs owned by the caller, another is opaque handles with accessors, another is
   a serialised blob (JSON/CBOR).
3. **Zero-copy pixels**: hand out the Lean `ByteArray` behind a retain/release pair instead of
   `memcpy`ing it.
4. **Parallel rendering** with N render threads, all registered with the runtime, and with
   cancellation.
5. **Packaging**: the C API header and `libsafepdfffi.a` as the `safe-pdf-core` C deliverable
   (a `c/` or `include/` directory, plus an Xcode project or SwiftPM wrapper), versus
   keeping them under `macos/`. Code signing and notarisation for a distributable `.app`.
6. **Swift or Objective-C** for 11.3. The C header imports into Swift unchanged through a
   module map.
