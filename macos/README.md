# macOS: the C API v2 and the Swift app

The first part of this file is the C API v2 (current), then the Swift app (task 11.3b). Everything
from "History: the AppKit spike" on is the task 11.1 spike (`main.m`, since replaced by the Swift
app) and its v1 C calls, kept for reference and **superseded**.


## C API v2 (tasks 11.3a1 to 11.3a5)

The C API is four plain-C headers in this directory. No Lean type appears in any of them. The
sections below restate what the headers' own comments and the test programs in `tests/` say; where
a header is silent the text says so. When this text and a header differ, the header is right.

| Header | Implementation | Role | Test program |
|---|---|---|---|
| `safepdf_core.h` | `safepdf_core.c` | Document layer over the confined worker: open, reference counting, asynchronous requests (render, page index, links, outline, labels, attachments, layers), cancel, the v1 calls (deprecated) | `tests/core_test.c` (62 checks) |
| `safepdf_view.h` | `safepdf_view.c` | View and chrome logic: zoom, rotation, re-anchoring, spreads and page layout, zoom and view-mode drop-downs, page field, toolbar, commands, menus, key table, cursor | `tests/view_test.c` (174) |
| `safepdf_marks.h` | `safepdf_marks.c` | Marks store (highlight, note, free text, ink) with undo/redo, Save (incremental update bytes), XFDF import and export, dialog texts | `tests/marks_test.c` (105) |
| `safepdf_select.h` | `safepdf_select.c` | Text selection, copy and search over a page's index | `tests/select_test.c` (53) |

The Lean side is `SafePdf/Shell/Ffi.lean`, `Ffi/V2.lean`, `Ffi/Flat.lean`, `FfiView.lean`,
`FfiMarks.lean` and `FfiSelect.lean`; the headers call the Tk viewer's own Lean functions, so the
theorems and `#guard`s there hold for these results. Plain-C structs are copied out of Lean
objects; nothing with a theorem or `#guard` is reimplemented in C.

### Initialisation order

1. `safepdf_init()` (core), once, on the main thread, before anything else. Idempotent. 0 on
   success.
2. Then, once each and on the main thread, in any order: `safepdf_view_init()`,
   `safepdf_marks_init()`, `safepdf_select_init()`. All are idempotent and return 0 on success.
   `safepdf_marks_init` calls `safepdf_init` itself. The view header says that calls made before
   `safepdf_view_init` fail (-1, or 0 or an empty result for functions returning a value
   directly); `tests/view_test.c` checks that. The marks and select headers do not say what an
   uninitialised call does.

### Threads

* Core: after `safepdf_init`, any thread may call the API. A thread the Lean runtime does not know
  is registered on its first call and unregistered when it exits. `safepdf_thread_enter` and
  `safepdf_thread_exit` remain for v1 callers and are optional.
* View: the header sends other threads to core's rules (`safepdf_thread_enter` /
  `safepdf_thread_exit`). It says nothing more about concurrent calls.
* Marks: a store is locked on every call, so it may be used from several threads. The header asks
  that each such thread be registered with `safepdf_thread_enter`.
* Select: a page handle is immutable; any thread may call and use handles concurrently.
* Completion callbacks of core requests: see the next section.

### Requests, callbacks and dispatch queues (core)

* A document (`safepdf_document`) comes from `safepdf_doc_open_file` (capped read, at most
  `Limits.maxInputBytes + 1` bytes) or `safepdf_doc_open_bytes` (the buffer is copied). Both parse
  in this process, so `safepdf_doc_page_count`, `safepdf_doc_page_size`,
  `safepdf_doc_is_repaired` and `safepdf_doc_is_encrypted` are synchronous. Each document gets
  its own confined `worker` process, spawned on the first request and sent the bytes, never the
  path.
* `safepdf_open_options` (NULL means all defaults): `worker_path`, `deadline_ms` (0 means 20000),
  `strict` (the repair path never runs), `test_stall_ms` (tests only: the worker sleeps before
  each render).
* Every `safepdf_doc_<request>` call returns a request id greater than 0 and later calls its
  callback exactly once, on the dispatch queue the caller passed (`dispatch_async_f`). A call with
  a NULL document, queue or callback returns 0 and never calls back.
* The callback gets `SAFEPDF_STATUS_OK` (result non-NULL, owned by the callback),
  `SAFEPDF_STATUS_ERROR` (`error` is the English message, result NULL) or
  `SAFEPDF_STATUS_CANCELLED` (cancelled, superseded, or the document closed; result NULL).
  `error` is borrowed and valid only during the callback. `context` is passed through untouched.
  A callback never receives the document, so it can run after the document is gone.
* Callbacks run outside Lean, on the caller's queue, and may call the API again (for example to
  submit the next request).
* Worker requests are render, page index, links and outline: they have priorities
  (`SAFEPDF_PRIO_CURRENT` 0, `SAFEPDF_PRIO_VISIBLE` 1, `SAFEPDF_PRIO_THUMBNAIL` 2; oldest first among
  equals), cancel and a deadline. Page labels, attachments, attachment bytes and layers are
  computed in this process on a Lean task, because the worker protocol has no request for them;
  their priority is ignored. `safepdf_doc_raise` makes a queued worker request more urgent.
* `safepdf_layers_toggle` is synchronous (0, or -1 with `*error`).
* The view, marks and select functions are synchronous; they take no queue and call no callback.
* The header does not state a limit on the number of requests in flight or on queue length.

### Cancel, release, deadline

* `safepdf_doc_cancel(doc, id)`: a queued request is dropped (delivered as CANCELLED). A request in
  flight for more than 250 ms is stopped by killing its worker (delivered as CANCELLED; the next
  request starts a fresh worker). An id that was already delivered changes nothing.
* A request with no answer within the deadline kills the worker and is delivered as
  `SAFEPDF_STATUS_ERROR` "the document took too long (no answer within 20 s; its worker was
  stopped)". A crashed worker gives "the document worker stopped: ...". The next request spawns a
  fresh worker and sends the bytes again.
* `safepdf_doc_release` drops one reference. The last one closes the document: queued requests are
  cancelled, a request in flight is stopped, in-process requests that have not started are
  cancelled, and the call blocks until every outstanding request's callback has been enqueued (not
  run), so it may be called from a callback's own queue. Then the handle is freed.
* **Known gap** (ledger, task 11.3a1; the header does not mention it): release can block for up to
  the deadline while the worker is still starting or opening the document. A caller that must not
  block (for example the main thread) should release from a background queue.

### Worker path and environment

* The worker executable is, in order: `safepdf_open_options.worker_path`; else the path set by
  `safepdf_set_worker_path` (copied; NULL clears; 0 on success); else a file named `worker` next to
  the host executable. If the file does not exist the open fails with the error
  "no document worker at PATH" (`tests/core_test.c` checks this).
* The header does not mention the environment. From `SafePdf/Shell/Worker/Client.lean` and the
  ledger (12.2a, 12.2b): the worker is spawned with an empty environment and `/` as working
  directory, and refuses to run with a non-empty environment (exit code 3). The host's environment
  therefore never reaches it, and test settings reach it as command-line flags only (the tests use
  `test_stall_ms` for that). Build it with `lake build worker`; `lake build macosFfi` does not.

### Ownership and the `safepdf_free_*` functions

* Every struct a core callback delivers is heap-allocated and owned by the receiver with all its
  arrays and strings. One `safepdf_free_<type>` frees all of it; NULL is allowed. Strings in
  results are UTF-8 and NUL-terminated (a NUL in document text becomes U+FFFD) and live as long as
  the struct. Input pointers are borrowed for the duration of the call.
* Core: `safepdf_free_image`, `_page_index`, `_links`, `_outline`, `_labels`, `_attachments`,
  `_bytes` (frees the data and the struct), `_layers`. `safepdf_free_layers_state` frees the arrays
  of a `safepdf_layers_state` in caller storage (written by `safepdf_layers_toggle`) and zeroes it.
  The v1 `safepdf_image_free` is for caller-storage images and zeroes the struct.
* View: structs a call fills own their arrays and strings; each type has one free function
  (`safepdf_free_zoom_presets`, `_layout`, `_page_band`, `_view_choices`, `_commands`,
  `_menu_table`, `_key_table`, `_toolbar`, `_chrome_states`); NULL allowed, the struct is zeroed.
  Functions returning `char *` return a malloc'd string for the caller to `free()`.
* Marks: filled structs are released with `safepdf_free_mark_list`, `_save_result`,
  `_xfdf_import`, `_marks_bytes` (frees the data only, unlike core's `safepdf_free_bytes`); each
  zeroes its argument and allows NULL. Returned `char *` strings are `free()`d. The store is
  reference counted: create gives 1 reference; `safepdf_marks_retain` / `safepdf_marks_release`.
* Select: returned struct pointers are heap-allocated; free them with
  `safepdf_select_free_box_list`, `_copy_result`, `_hit_list` (NULL allowed). Returned `char *` are
  `free()`d. A page handle is reference counted (`safepdf_select_page_retain` / `_release`).
  `safepdf_select_page_new` converts a `safepdf_page_index` once; the index is borrowed for the
  call, so you may free it afterwards.
* Names that must not clash across the four headers: the double box `safepdf_box` is core's;
  marks' buffer is `safepdf_marks_bytes`; view's rationals are `safepdf_rat`, `safepdf_rat_box`,
  `safepdf_rat_point`, and its key actions are `safepdf_view_action` (core's
  `safepdf_action_kind` is the link action). `tests/all_headers.c` includes all four.

### Error strings

* Core: `char **error` out-parameters (open, `safepdf_layers_toggle`) are set on failure to a
  malloc'd English string; release it with `free()`. In callbacks, `error` is borrowed (above).
* Marks: `*error` is set only when the call fails and only when `error` is not NULL; malloc'd.
  Save returns `SAFEPDF_SAVE_OK` or a `SAFEPDF_SAVE_ERR_*` code, with `*error` set and `*out`
  zeroed on failure. Undo/redo with nothing to do fails with "nothing to undo" / "nothing to redo".
* Select: `safepdf_select_page_new` sets `*error` (malloc'd). Other functions report failure by -1
  or NULL (documented per function).
* View: no strings; failure is -1 (bad input, not initialised, out of memory, unrepresentable
  result), or NULL for `char *` results.

### Numbers and coordinates

* Core and select coordinates are page space in points (PDF user space, y up) as doubles converted
  from the core's exact rationals, for display only.
* View rationals cross as `safepdf_rat {num, den}` with `den > 0`; `den <= 0` is rejected, and a
  result that does not fit 64 bits is an error. `safepdf_rat_to_double` is for display only: the
  header says never to feed a rounded value back as a zoom.
* Marks coordinates must be finite with magnitude at most 2^32, else the call fails. Mark ids are
  greater than 0; 0 means none.

### v1 calls are deprecated

`safepdf_open`, `safepdf_close`, `safepdf_page_count`, `safepdf_page_size`, `safepdf_render` and
`safepdf_image_free` (with the `safepdf_doc` type) do an in-process open and a synchronous render
on the calling thread: no worker, no cancellation. The header keeps them until the spike app is
retired (task 11.3b) and says to use the v2 calls instead. The section "The v1 C API" below
describes them and is superseded.

### Building and running the C tests

All need macOS (they use `dispatch` and `clang`), the Lean toolchain, and the Xcode command line
tools. Never run two of them, or one of them and another `lake build`, at the same time in one
checkout. The scripts run `lake build macosFfi` (and `lake build worker` where the test starts a
worker) themselves, compile with `-O2 -Wall -Wextra -I "$(lean --print-prefix)/include"` (the view
and select scripts add `-Werror -I macos`), link against `.lake/build/lib/libsafepdfffi.a` and
Lean's runtime libraries, and print `NAME: N checks, 0 failures`.

| Command | What it does |
|---|---|
| `macos/tests/run.sh` | `macos/build.sh`, `lake build worker`, then `core_test WORKER Tests/golden`: open, async render byte-equal to v1, cancel (queued and in flight), release with pending requests, the 700 ms deadline against a 3 s stall and respawn, strict mode, error paths |
| `macos/tests/run_view.sh` | builds `safepdf_view.c` with the core shim, runs `view_test` (zoom, layout, drop-downs, commands, menus, keys, toolbar, cursors, the not-initialised failures) |
| `macos/tests/run_marks.sh` | runs `marks_test` on three goldens (plain, AES-128, RC4-128), writes `saved.pdf` and `export.xfdf` under `macos/build/marks-test/`, then `lake build inspect`, runs `inspect` on `saved.pdf`, and runs `qpdf --check` on it when `qpdf` is installed (skipped with a message otherwise) |
| `macos/tests/run_select.sh` | runs `select_test WORKER Tests/golden` (selection, copy, search, Find Next/Previous steps) |
| `macos/tests/run_all.sh` | compiles `tests/all_headers.c` (all four headers, `-Wall -Wextra -Werror`), runs the four scripts above in turn, then lists the global symbols the four `safepdf_*.o` objects define (`nm -g -U`) and fails on a duplicate. Prints one summary line; exit status is non-zero on any failure |

`lake build macosFfi` is also a step of the Linux CI `build` job, so the `#guard`s of
`FfiView.lean`, `FfiMarks.lean`, `FfiSelect.lean` and `Ffi/Flat.lean` run there. The C tests
themselves are not run in CI yet (task 11.4).

# The Swift app (task 11.3b)

Native AppKit shell in Swift 6 (strict concurrency) over the C API v2; unverified shell code that
only moves data between AppKit and the core. Its state is a scaffold: menubar and toolbar from the
exported tables, a document window with an empty sidebar, continuous vertical pages rendered
through the worker. Commands it does not implement yet stay disabled (`Commands.swift`).

## Sources (`macos/App/`)

| File | Role (from its header comment) |
|---|---|
| `main.swift` | Entry point: `SafePdf [FILE.pdf]`, or the headless self-test when `SAFEPDF_MACOS_SELFTEST=DIR` is set |
| `AppDelegate.swift` | Application life cycle: menubar, the document window, files from Finder and `open -a`, About and Quit |
| `ChromeTables.swift` | Swift copies of the exported chrome tables (every C struct copied into Swift values and freed at once) |
| `Commands.swift` | Which exported commands this shell implements yet; `pendingTask` names the task that implements the rest |
| `CoreBridge.swift` | Start-up of the C API and small conversions |
| `Document.swift` | An open PDF over the C API v2 (a `safepdf_document` reference, released with the object) |
| `DocumentToolbar.swift` | The unified toolbar built from the exported toolbar table |
| `DocumentWindowController.swift` | The document window: unified toolbar, split view with sidebar and page area, command routing and enabled states |
| `KeyEquivalents.swift` | Neutral keys (Menu.lean's key table) to AppKit key equivalents |
| `MainMenu.swift` | The menubar built from the exported menu table |
| `PageCanvasView.swift` | The pages, laid out by `safepdf_view_layout` and drawn from renders |
| `PageViewController.swift` | The content item: an `NSScrollView` over the page canvas |
| `Rendering.swift` | Asynchronous page renders through `safepdf_doc_render` |
| `SelfTest.swift` | The headless self-test (below) |
| `Sheets.swift` | Open and save panels and alerts as document-modal sheets |
| `SidebarViewController.swift` | The sidebar item with its four panels, empty for now |

Swift sees the C API through `module.modulemap`: one Clang module, `SafePdfC`, made of
`safepdf_core.h`, `safepdf_view.h`, `safepdf_marks.h` and `safepdf_select.h`; the sources say
`import SafePdfC`. `swiftc -I macos` finds the module map.

## Build

```
macos/build.sh        # needs elan's Lean and the Xcode command line tools only
```

`build.sh` runs `lake build macosFfi worker`, compiles the four C shims with `clang` at
`-mmacosx-version-min=14.0`, links `App/*.swift` with `swiftc` against the shims,
`libsafepdfffi.a` and Lean's runtime, and writes into `macos/build/`:

* `safepdf-mac`: the app binary, unbundled, with a copy of `worker` beside it;
* `SafePdf.app`: `Contents/MacOS/SafePdf`, the worker in `Contents/Helpers/worker`,
  `Contents/Resources/SafePdf.icns` (made with `iconutil` from `docs/branding/icon-*.png`),
  `Info.plist` (`CFBundleIdentifier` `org.safe-pdf.SafePDF`) and `PkgInfo`; the worker and the
  bundle are signed ad hoc (`codesign --sign -`). Distribution signing and notarisation are
  deferred;
* `core_test`: the C API v2 test program (run it with `macos/tests/run.sh`).

Scripts never launch the app.

## Running it by hand

```
open macos/build/SafePdf.app
macos/build/SafePdf.app/Contents/MacOS/SafePdf FILE.pdf
```

## Headless self-test

```
macos/selftest.sh FILE.pdf [OUTDIR]        # OUTDIR defaults to macos/build/selftest
SAFEPDF_SELFTEST_BUNDLE=1 macos/selftest.sh FILE.pdf    # the bundle's binary instead
```

`SAFEPDF_MACOS_SELFTEST=DIR` makes `main.swift` set the activation policy to Prohibited before
anything else; there is no window and the app never calls `run` or activates. `SelfTest.swift`
checks that the chrome tables build (every command in the menubar, every toolbar item), open and
its error path, page 1 through `safepdf_doc_render` at 1x and 2x, pages 1 to 10 at 2x, the real
scroll view and page canvas at 1x and 2x backing, scrolling to page 2 and dark mode; it writes
PNGs and `timings.txt` to DIR, prints `failures: N` and exits 0 when `N` is 0.

`selftest.sh` samples `lsappinfo front` every 0.5 s and checks `lsappinfo list` for a Foreground
registration, both only for the PID the script started (a copy launched by hand is ignored; the
match is by PID, so it covers the names `safepdf-mac`, `SafePdf` and `SafePDF`). It kills only
that PID if either shows up, and reports `leaks: N`.

## Known limitation (open question for the human)

`Info.plist` sets `LSMinimumSystemVersion` to 14.0 and `build.sh` compiles and links for macOS 14.0,
but the pinned Lean toolchain's runtime libraries (`libgmp.a`, `libuv.a`) are built for a newer
macOS (15). The linker warns once per object (counted by `build.sh`, full text in
`build/swift-link.log`). Whether the bundle runs on macOS 14 is therefore not established; whether
to raise the minimum is a decision for the human.


# History: the AppKit spike (task 11.1) — superseded

The spike was a single Objective-C file, `main.m` (an `NSWindow` with an `NSScrollView` and a page
view, one render thread), replaced by the Swift app above; `main.m` is no longer in this
directory. The sections below describe it and its v1 calls as they were.

Plan.md §6 Phase 11: *"Spike first: a minimal Cocoa window (open, render, scroll, zoom) over
the C API; record the feel delta and the FFI surface in a Decisions entry before committing to
parity."* Plan.md §8: the shell is unverified and replaceable; the core as a library is the
deliverable. The spike was not parity with the Tk viewer (no toolbar,
sidebar, selection, search, links or annotations; that is 11.3).

## The v1 C API (`safepdf_core.h`) — deprecated, superseded by the C API v2

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

## The spike's headless self-test

In the spike, `SAFEPDF_MACOS_SELFTEST=DIR` set `NSApplicationActivationPolicyProhibited` before the core
starts, creates **no window**, and never calls `run` or `activate`. It does the following:

1. It checks the C API (open, page count and size, the error paths, page 1 rendered at 1× and
   2×, and the first 10 pages at 2× with timings).
2. It builds the real `NSScrollView` and page view off screen and drives them through the
   render thread and the main run loop at 1× and at a simulated 2× backing scale. It then sets
   the magnification to 1.5625, as two Cmd+ presses would, and scrolls to page 2.
3. It draws each state into an `NSBitmapImageRep` (`cacheDisplayInRect:`), writes the PNGs
   and `timings.txt` to DIR, and exits.

`selftest.sh` samples `lsappinfo front` every 0.5 s and checks `lsappinfo list` for a
Foreground registration, both only for the PID the script started (a copy of the app launched by hand is ignored). It kills only that PID if either shows up.

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

## Known spike limitations (the v2 document layer answers the first two)

* One render thread, no cancellation (a generation number only skips stale jobs before they
  start). Visible pages therefore render one after another.
* Opening a second document leaks the first: a queued job may still hold the raw pointer.
  11.2 needs reference-counted handles (`safepdf_retain`/`release`) or a close that drains the
  queue.
* No page labels, rotation, optional content, text, links, outline or annotations in the C API yet.
* `allowedFileTypes` is deprecated (warning suppressed). Use `UTType` in 11.3.

## Open questions for 11.2

**All six answered 2026-11-24 in [docs/macos-design.md](../docs/macos-design.md) §3** (11.2's
Decisions entry): Lean logic exported (1), flat C structs (2), `memcpy` kept for now (3), the
document worker instead of in-process threads (4), packaging deferred (5), Swift (6).

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
