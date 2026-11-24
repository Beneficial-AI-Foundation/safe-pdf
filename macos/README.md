# macOS: the C API v2 and the Swift app

The first part of this file is the C API v2 (current), then the Swift app (tasks 11.3b–11.3f).
Everything from "History: the AppKit spike" on is the task 11.1 spike (`main.m`, since replaced by
the Swift app) and its v1 C calls (removed in task 11.3c1), kept for reference only.


## C API v2 (tasks 11.3a1 to 11.3e2)

The C API is four plain-C headers in this directory. No Lean type appears in any of them. The
sections below restate what the headers' own comments and the test programs in `tests/` say; where
a header is silent the text says so. When this text and a header differ, the header is right.

| Header | Implementation | Role | Test program |
|---|---|---|---|
| `safepdf_core.h` | `safepdf_core.c` | Document layer over the confined worker: open, reference counting, page geometry, open settings, asynchronous requests (render, page index, links, outline, labels, attachments, attachment bytes, layers), cancel; the sidebar's rules (11.3d2); the test-only in-process render | `tests/core_test.c` (144 checks) |
| `safepdf_view.h` | `safepdf_view.c` | View and chrome logic: zoom, rotation, re-anchoring, spreads and layout, zoom and view-mode drop-downs, page field, commands, menus, key table, toolbar, enabled states, cursor; wheel step, page text, history, page → screen (11.3c2) | `tests/view_test.c` (314) |
| `safepdf_marks.h` | `safepdf_marks.c` | Marks store (highlight, note, free text, ink) with undo/redo, Save (incremental update bytes), XFDF import and export, dialog texts; tool, bubble and pop-over rules (11.3e1); the preview, status texts and dialog helpers (11.3e2) | `tests/marks_test.c` (148) |
| `safepdf_select.h` | `safepdf_select.c` | Text selection, copy and search over a page's index; pointer, links and the search allowance (11.3d1) | `tests/select_test.c` (70) |

The Lean side is `SafePdf/Shell/Ffi.lean`, `Ffi/V2.lean`, `Ffi/Flat.lean`, `Ffi/Sidebar.lean`,
`FfiView.lean`, `FfiMarks.lean` and `FfiSelect.lean`; the headers call the Tk viewer's own Lean
functions, so the theorems and `#guard`s there hold for these results. Plain-C structs are copied
out of Lean objects; nothing with a theorem or `#guard` is reimplemented in C.

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
  `safepdf_thread_exit` remain and are optional. The sidebar rules are pure and synchronous, any
  thread after `safepdf_init`.
* View: the header sends other threads to core's rules (`safepdf_thread_enter` /
  `safepdf_thread_exit`). It says nothing more about concurrent calls.
* Marks: a store is locked on every call, so it may be used from several threads. The header asks
  that each such thread be registered with `safepdf_thread_enter`. `safepdf_marks_preview` works on
  a snapshot taken under the lock (its objects marked thread-shared first), so it may run on a
  background thread while the GUI edits.
* Select: a page handle is immutable; any thread may call and use handles concurrently.
* Completion callbacks of core requests: see the next section.

### Requests, callbacks and dispatch queues (core)

* A document (`safepdf_document`) comes from `safepdf_doc_open_file` (capped read, at most
  `Limits.maxInputBytes + 1` bytes) or `safepdf_doc_open_bytes` (the buffer is copied). Both parse
  in this process, so page count, sizes, geometry, open settings, the repaired and encrypted flags
  and `safepdf_doc_bytes` are synchronous. Each document gets its own confined `worker` process,
  spawned on the first request and sent the bytes, never the path.
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
  they take no priority. `safepdf_doc_raise` makes a queued worker request more urgent.
* `safepdf_layers_toggle` is synchronous (0, or -1 with `*error`).
* The view, marks, select and sidebar functions are synchronous; they take no queue and call no
  callback.
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
  block (for example the main thread) should release from a background queue (the app releases
  preview documents on a background queue).

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
  `_bytes` (frees the data and the struct), `_layers`, `_open_settings`.
  `safepdf_free_layers_state` frees the arrays of a `safepdf_layers_state` in caller storage
  (written by `safepdf_layers_toggle`) and zeroes it. The sidebar's `char *` results and the
  arrays of `safepdf_sidebar_thumbs_wanted` / `_thumb_evict` are `free()`d.
* View: structs a call fills own their arrays and strings; each type has one free function
  (`safepdf_free_zoom_presets`, `_layout`, `_page_band`, `_view_choices`, `_commands`,
  `_menu_table`, `_key_table`, `_toolbar`, `_chrome_states`, `_view_history`); NULL allowed, the
  struct is zeroed. Functions returning `char *` return a malloc'd string for the caller to
  `free()`.
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

* Core: `char **error` out-parameters (open, `safepdf_layers_toggle`, `safepdf_test_render_sync`)
  are set on failure to a malloc'd English string; release it with `free()`. In callbacks, `error`
  is borrowed (above).
* Marks: `*error` is set only when the call fails and only when `error` is not NULL; malloc'd.
  Save returns `SAFEPDF_SAVE_OK` or a `SAFEPDF_SAVE_ERR_*` code, with `*error` set and `*out`
  zeroed on failure. Undo/redo with nothing to do fails with "nothing to undo" / "nothing to redo".
* Select: `safepdf_select_page_new` sets `*error` (malloc'd). Other functions report failure by -1
  or NULL (documented per function).
* View: no strings; failure is -1 (bad input, not initialised, out of memory, unrepresentable
  result), or NULL for `char *` results.

### Numbers and coordinates

* Core and select coordinates are page space in points (PDF user space, y up) as doubles converted
  from the core's exact rationals, for display only. `safepdf_doc_page_geom` gives the exact
  rationals.
* View rationals cross as `safepdf_rat {num, den}` with `den > 0`; `den <= 0` is rejected, and a
  result that does not fit 64 bits is an error. `safepdf_rat_to_double` is for display only: the
  header says never to feed a rounded value back as a zoom.
* Marks coordinates must be finite with magnitude at most 2^32, else the call fails. Mark ids are
  greater than 0; 0 means none. `safepdf_marks_bubble_place` alone takes canvas rectangles with
  y down.

### Function reference

Every function the four headers declare, with its contract in one line (the header comment
abridged; Lean names in parentheses are the functions called). Return conventions as above unless
a line says otherwise.

#### `safepdf_core.h`

| Function | Contract |
|---|---|
| `safepdf_init` | Initialise the Lean runtime and the core's modules; 0 on success; idempotent |
| `safepdf_thread_enter` / `safepdf_thread_exit` | Register / unregister a non-main thread (optional: threads register on their first call) |
| `safepdf_set_worker_path` | Default worker executable for later opens (copied; NULL clears); 0 on success |
| `safepdf_doc_open_file` | Open a PDF path through the capped read; NULL with `*error` on failure |
| `safepdf_doc_open_bytes` | Open a PDF from a buffer (copied); NULL with `*error` on failure |
| `safepdf_doc_retain` / `safepdf_doc_release` | Add / drop a reference; the last release closes the document (cancels, drains, blocks until callbacks are enqueued) |
| `safepdf_doc_page_count` | Number of pages (synchronous) |
| `safepdf_doc_page_size` | Displayed size in points (CropBox with `/Rotate`); -1 out of range |
| `safepdf_doc_page_geom` | The effective CropBox as exact rationals and `/Rotate` in degrees (for `safepdf_view_layout`); -1 on a bad page or a coordinate beyond 64 bits |
| `safepdf_doc_is_repaired` / `safepdf_doc_is_encrypted` | Nonzero when the file opened only through repair / is encrypted (empty user password) |
| `safepdf_doc_open_settings` / `safepdf_free_open_settings` | The open settings (`Core.Doc.OpenSettings.read`, `View.modesOf`, `Links.jumpOf`, `Toolbar.zoomChoiceOf`): `/PageLayout` as view modes, `/Direction /R2L`, `/PageMode`, `/NonFullScreenPageMode`, the open destination and its zoom, the viewer preferences, the window title (`/DisplayDocTitle`), and the notes of what was not honoured; 0 / -1 |
| `safepdf_doc_bytes` | A copy of the bytes the document was opened from (the marks store is created from them); free with `safepdf_free_bytes` |
| `safepdf_doc_render` | Render a page at `zoom_num/zoom_den` px/pt with an extra clockwise rotation (quarter turns) under a layers state (NULL: default). Worker |
| `safepdf_doc_page_index` | The selection and search index of a page under a layers state. Worker |
| `safepdf_doc_links` | The links of a page. Worker |
| `safepdf_doc_outline` | The outline. Worker |
| `safepdf_doc_page_labels` | The page labels. In process |
| `safepdf_doc_attachments` | The attachments, listed (nothing decoded), with their annotations' icons. In process |
| `safepdf_doc_attachment_bytes` | The decoded bytes of attachment `index` (under the viewer's limits). In process |
| `safepdf_doc_layers` | The layers panel rows and the default layers state. In process |
| `safepdf_doc_cancel` | Cancel a request (queued: dropped; in flight over 250 ms: its worker killed) |
| `safepdf_doc_raise` | Make a queued worker request more urgent |
| `safepdf_layers_toggle` | Toggle a layers-panel row in a state (radio groups, locked groups, inert headings); the new state into caller storage; synchronous |
| `safepdf_sidebar_on_load` | The panel the sidebar opens with for a `/PageMode` (`Sidebar.onLoad`); `SAFEPDF_PANEL_NONE`: closed |
| `safepdf_sidebar_available` | Whether a panel's switcher button shows (`Sidebar.Panel.available`) |
| `safepdf_sidebar_pick` | The panel the toggle opens (`Sidebar.pick`): the last while available, else the outline, else the thumbnails |
| `safepdf_sidebar_constants` | The thumbnail constants (`thumbW`, `thumbTop`, `thumbLabelH`, `thumbGap`, `thumbMargin`, `thumbBudget`) |
| `safepdf_doc_thumb` | A page's thumbnail size at 1x and its render zoom, with the user's extra rotation (`Sidebar.thumbSize`) |
| `safepdf_sidebar_thumb_scale` | The 12.3b scale of a thumbnail image (0 full, 1 half, 2 quarter, 3 eighth) so that `thumbBudget` images fit the 32 MiB reserve |
| `safepdf_sidebar_thumb_layout` | The thumbnails' tops and the panel height (`Sidebar.thumbLayout`) |
| `safepdf_sidebar_thumbs_wanted` | The thumbnails to render for a visible band, nearest its middle first (`Sidebar.thumbsWanted`) |
| `safepdf_sidebar_thumb_evict` | The thumbnails to drop beyond `thumbBudget`, farthest first (`Sidebar.thumbEvict`) |
| `safepdf_sidebar_tree` | An outline tree's parents, disclosure and initial open state from depths (`Sidebar.rows`, `initialOpen`) |
| `safepdf_attachment_target_problem` | Why a file cannot take a saved attachment (`Attach.targetProblem`), NULL when it can |
| `safepdf_attachment_size_after` | The size column after a decode (`Attach.sizeColumn`: the decoded size, or "error"; the listed size first) |
| `safepdf_action_describe` | An outline action in words with labels and the page count (`Links.describe`) |
| `safepdf_identity_line` | The trusted full-screen identity line (`Viewer.identityLine`; controls and bidi overrides blanked; never `/Title`) |
| `safepdf_test_render_sync` | TESTS ONLY: renders in this process on the calling thread, as the worker would, for byte comparisons |
| `safepdf_free_image`, `_page_index`, `_links`, `_outline`, `_labels`, `_attachments`, `_bytes`, `_layers`, `_layers_state` | Free a delivered result (NULL allowed) |

The `safepdf_attachment` struct carries, besides name, file name, description, listed size, MIME
type, dates, page and problem, what the panel shows before decoding (11.3d2): `size_text`
(`Attach.sizeColumn`: "1.5 KB", "?", "—"), `tooltip` (`Attach.tooltip`, "" when nothing to say)
and `has_stream`. The list also carries `icons` (`safepdf_attachment_icon`: page, rectangle, row).

#### `safepdf_view.h`

| Function | Contract |
|---|---|
| `safepdf_view_init` | Initialise the view module (after `safepdf_init`); 0; idempotent |
| `safepdf_rat_to_double` | A rational as a double (display only) |
| `safepdf_view_get_constants` | Margin, page gap, zoom range, Automatic Zoom's ceiling, the per-page pixel cap, the renderer's side cap, the view pixel cap |
| `safepdf_view_zoom_steps` | The zoom steps in percent (`View.zoomSteps`) |
| `safepdf_view_quant` | Round a zoom down to a multiple of 1/64, at least 1/64 (`View.quant`) |
| `safepdf_view_pct_zoom` / `safepdf_view_zoom_pct` | Percentage → quantised zoom at a screen scale, and back (rounded) |
| `safepdf_view_step_in` / `safepdf_view_step_out` | Zoom In / Out on the effective zoom: 1 with the step, 0 at the end of the range (theorems `stepInZ_gt`, `stepOutZ_lt`) |
| `safepdf_view_fit_zoom` | The zoom fitting a box into a canvas less the margin (width only optional), quantised, in [1/16, 8] |
| `safepdf_view_cap_zoom` | A zoom lowered so the page image has at most N pixels (`View.capZoom`), with whether it was lowered |
| `safepdf_view_pixel_size` | Screen and rendered pixel sizes of a box at a zoom, and whether the renderer crops it |
| `safepdf_view_rotation` | Quarter-turn steps and the displayed size of a box at a rotation |
| `safepdf_view_reanchor` | Where the page point shown at `q` lies after a zoom / rotation change (C2; theorem `reanchor_self`) |
| `safepdf_view_spread` | A page's spread, the spread count and the pages Next / Previous go to |
| `safepdf_view_zoom_presets` / `safepdf_free_zoom_presets` | The zoom drop-down (`ZoomChoice.presets`) |
| `safepdf_view_zoom_label` / `safepdf_view_zoom_parse` | A zoom choice's label; a key ("auto", "150", …) to a choice |
| `safepdf_view_zoom_with` | A zoom choice's zoom for a page in a canvas (Automatic Zoom: page width when portrait, else page fit, capped) |
| `safepdf_view_layout` / `safepdf_free_layout` | Lay out the pages as the Tk viewer (`Viewer.computeLayout`): places, render zoom and rotation, capped / cropped flags |
| `safepdf_view_pages_in_band` / `safepdf_free_page_band` | Visible pages of a band and the wanted ones (one more each side) |
| `safepdf_view_page_at` | The page at (or nearest) a scroll-region point and the scroll tops that show it |
| `safepdf_view_view_choices` / `safepdf_free_view_choices` | The view-mode drop-down (`Toolbar.ViewChoice`) |
| `safepdf_view_choice_of_modes` / `safepdf_view_choice_modes` | The entry modes show; the modes an entry sets (a two-page choice keeps Even Spreads) |
| `safepdf_view_page_field` | The page field's text and its "of N" / "(k of N)" label |
| `safepdf_view_page_entry` | Return in the page field (`Toolbar.pageEntry`): 1 valid with the page, 0 invalid (revert) |
| `safepdf_view_commands` / `safepdf_view_actions` / `safepdf_free_commands` | The commands (`Menu.Cmd`, with macOS accelerators) and the key actions |
| `safepdf_view_app_name` / `safepdf_view_about_detail` | "SafePDF" and the About text |
| `safepdf_view_menubar` / `safepdf_view_overflow_menu` / `safepdf_free_menu_table` | The menubar (File, Edit, View, Go, Help) and the toolbar's overflow menu |
| `safepdf_view_keys` / `safepdf_free_key_table` | The main window's key bindings (`Menu.keyTable .aqua`) |
| `safepdf_view_toolbar` / `safepdf_free_toolbar` | The toolbar left to right (`Toolbar.layout`) |
| `safepdf_view_states` / `safepdf_free_chrome_states` | Enabled states per command and per toolbar item, visibility per item, from a `safepdf_ctx` |
| `safepdf_view_hit_of` / `safepdf_view_cursor_for` / `safepdf_view_mode_tool` | What lies under the pointer; the cursor for a mode over it; the tool pressed in a mode |
| `safepdf_view_wheel_step` | One wheel event on one axis (`View.wheelStep`): none, scroll to `*pos`, next or previous page |
| `safepdf_view_page_text` | "page k/n" or "page L (k/n)" (`Links.pageText`) |
| `safepdf_view_history_step` / `safepdf_free_view_history` | Push / back / forward on the history (`Links.History`, at most 100 per stack; theorem `History.back_push`): 1 done with the target, 0 nothing to go to |
| `safepdf_view_to_screen` | Where a page point shows, in pixels from the page image's top-left (`Geom.toScreen`) |

#### `safepdf_marks.h`

| Function | Contract |
|---|---|
| `safepdf_marks_init` | Initialise the marks module (calls `safepdf_init`); 0; idempotent |
| `safepdf_marks_create` | The store of a PDF's bytes, its saved marks listed as saved; NULL with `*error` |
| `safepdf_marks_retain` / `safepdf_marks_release` | Add / drop a reference |
| `safepdf_marks_get_state` | Counts, dirty flag, undo / redo availability |
| `safepdf_marks_list` / `safepdf_marks_list_all` / `safepdf_free_mark_list` | The marks of a page / of every page |
| `safepdf_marks_hit_at` | The topmost mark under a page point (note icons first); 0 none |
| `safepdf_marks_note_anchor` | Where a new note anchors (`Marks.noteAnchor`: the clicked point, the selection's quads, or none) |
| `safepdf_marks_note_close` | What closing a note popup without Save does: keep, save the text shown, or delete |
| `safepdf_marks_add_highlight` / `_add_note` / `_add_comment` / `_add_free_text` / `_add_ink` / `_add_stroke` | Add a mark (each one undo step; a comment reuses a highlight's existing note; a stroke joins a drawing) |
| `safepdf_marks_set_text` / `_recolor` / `_set_rgb` / `_set_size` / `_set_opacity` / `_translate` | Edit a mark; `merge` joins the current slider drag's undo step |
| `safepdf_marks_seal` | Close the open merge step (slider released) |
| `safepdf_marks_begin_group` / `safepdf_marks_end_group` | The edits between them are one undo step (11.6a: Paste re-creates a cut mark — a highlight and its comment, a drawing's strokes) |
| `safepdf_marks_delete` | Delete a mark (a highlight's comment goes with it) |
| `safepdf_marks_undo` / `safepdf_marks_redo` | One step; -1 "nothing to undo" / "nothing to redo" |
| `safepdf_marks_output_estimate` | Upper bound of the saved file's size |
| `safepdf_marks_save_build` / `safepdf_free_save_result` | Build the incremental update Save writes (64 fresh bytes needed for an encrypted file); `SAFEPDF_SAVE_OK` or an error code |
| `safepdf_marks_disk_state` | Whether the file on disk still holds the bytes the store came from |
| `safepdf_marks_save_route` | Save's route (`Save.route`) |
| `safepdf_marks_overwrite_question` / `_changed_question` / `_unsaved_question` | The dialogs' texts |
| `safepdf_marks_write_problem` / `_target_problem` | Why the opened file / a Save As or Export target cannot be written; NULL when it can |
| `safepdf_marks_default_target` / `safepdf_marks_with_ext` | `STEM-annotated.pdf` next to a path; a name with an extension unless it has it |
| `safepdf_marks_xfdf_estimate` / `safepdf_marks_xfdf_export` / `safepdf_free_marks_bytes` | Every mark as XFDF (upper bound; the export) |
| `safepdf_marks_xfdf_import` / `safepdf_free_xfdf_import` | Import XFDF with the bounded reader; marks already present are not added again; a refused file leaves the store unchanged |
| `safepdf_marks_tool_params` | The tools' parameters: the five highlight colours, the editor palette, font size, thickness and opacity ranges and defaults, free-text padding and line factor, the note icon size |
| `safepdf_marks_ui_step` | One step of the tool state (`Bubble.Ui`: tool click, toggle, editor, Select text, Escape); returns the mode and whether the Highlight button highlights the selection |
| `safepdf_marks_bubble_kind` | The bubble after a selection or on a selected highlight (`Bubble.kindFor`) |
| `safepdf_marks_bubble_layout` | A bubble's size and buttons with their commands and tooltips |
| `safepdf_marks_bubble_place` | Where a bubble goes for the selection rectangles (`Bubble.place`, theorem `place_inside`; y down) |
| `safepdf_marks_escape_closes` | What Escape closes among the open transients (`Toolbar.onEscape`: the topmost) |
| `safepdf_marks_preview` | The preview bytes (`Save.preview`): the document with only the changes of saved marks applied, empty when none; runs on a snapshot |
| `safepdf_marks_output_ceiling` | The save / export output ceiling (`Budget.ceilings.poolBytes`, 192 MiB) |
| `safepdf_marks_saved_status` / `safepdf_marks_import_status` | The status after a save / an import |
| `safepdf_marks_xfdf_target` | `STEM.xfdf` next to the PDF |
| `safepdf_marks_replace_question` / `safepdf_marks_opened_overwrite_question` | "NAME already exists. Replace it?"; Save As naming the opened file |
| `safepdf_marks_dialog_buttons` | A dialog's buttons in display order (`aqua`: the macOS order) |
| `safepdf_marks_unsaved_answer` | The unsaved-changes answer of a button key (anything else: Cancel) |
| `safepdf_marks_close_goes_on` | Whether a close / quit / open goes on (`Save.closeGoesOn`) |
| `safepdf_marks_dialog_dir` | The folder a file dialog starts in (`Save.dialogDir`) |
| `safepdf_marks_one_line` | A message on one line (`Save.oneLine`) |
| `safepdf_marks_tmp_name` | The temporary file name of a save (`Save.tmpName`) |

#### `safepdf_select.h`

| Function | Contract |
|---|---|
| `safepdf_select_init` | Initialise the selection module (after `safepdf_init`); 0; idempotent |
| `safepdf_select_page_new` / `_retain` / `_release` | A page index converted once into an immutable, reference-counted handle |
| `safepdf_select_cell_count` | Number of cells |
| `safepdf_select_nearest` | The cell nearest a point (`Select.nearest`, first on ties); -1 no cells or a refused coordinate |
| `safepdf_select_drag` | The range of a drag (`Select.dragRange`) |
| `safepdf_select_word_at` / `safepdf_select_line_at` | Double click: the word; triple click: the line |
| `safepdf_select_bands` | The selection bands (`Select.selBands`, task 10.18: one per line, consecutive lines meet) |
| `safepdf_select_range_boxes` | The highlight boxes of a range (`Select.rangeBoxes`: the quads of a highlight) |
| `safepdf_select_copy` | Copy a range: the text, its character count, how many come from unpainted glyphs, the status |
| `safepdf_select_normalize_query` | The query as the search sees it (`Select.normQuery`) |
| `safepdf_select_count` / `safepdf_select_find` | Hits on a page: their number; the hits with their boxes (`Select.findAll`, sound by `findAll_sound`) |
| `safepdf_select_find_doc` | The hits over several pages (highlight-all; NULL handles skipped) |
| `safepdf_select_next_hit` | Find Next / Previous over per-page counts (`Select.searchStep`): a hit, NEED a page's index, or none |
| `safepdf_select_over_text` | Whether a point lies in a glyph box (the cursor's text test) |
| `safepdf_select_link_at` | The topmost link containing a point (`Links.linkAt`); -1 none |
| `safepdf_select_link_describe` | A link's status text (`Links.describe`) |
| `safepdf_select_allowance_start` / `safepdf_select_allowance_spend` | A search's work allowance (`Budget.Allowance`: 400 pages, 60 s); spend one page, -1 when used up |
| `safepdf_select_free_box_list` / `_copy_result` / `_hit_list` | Free a result (NULL allowed) |

### v1 calls removed

`safepdf_open`, `safepdf_close`, `safepdf_page_count`, `safepdf_page_size`, `safepdf_render` and
`safepdf_image_free` (with the `safepdf_doc` type) did an in-process open and a synchronous render
on the calling thread. They were removed in task 11.3c1 once the Swift app replaced the spike;
the section "The v1 C API" below is history.

### Building and running the C tests

All need macOS (they use `dispatch` and `clang`), the Lean toolchain, and the Xcode command line
tools. Never run two of them, or one of them and another `lake build`, at the same time in one
checkout. The scripts run `lake build macosFfi` (and `lake build worker` where the test starts a
worker) themselves, compile with `-O2 -Wall -Wextra -I "$(lean --print-prefix)/include"` (the view
and select scripts add `-Werror -I macos`), link against `.lake/build/lib/libsafepdfffi.a` and
Lean's runtime libraries, and print `NAME: N checks, 0 failures`.

| Command | What it does |
|---|---|
| `macos/tests/run.sh` | `macos/build.sh`, `lake build worker`, then `core_test WORKER Tests/golden`: open, open settings on generated three-page files, page geometry (`tree.pdf` CropBoxes and `/Rotate` against `tree.pdf.expected`), async worker render byte-equal to the in-process render (`safepdf_test_render_sync`, rotations 0–3), cancel (queued and in flight), release with pending requests, the 700 ms deadline against a 3 s stall and respawn, strict mode, the sidebar rules, error paths |
| `macos/tests/run_view.sh` | builds `safepdf_view.c` with the core shim, runs `view_test` (zoom, layout, drop-downs, commands, menus, keys, toolbar, cursors, the not-initialised failures, wheel steps, page text, history, page → screen) |
| `macos/tests/run_marks.sh` | runs `marks_test` on three goldens (plain, AES-128, RC4-128), writes `saved.pdf` and `export.xfdf` under `macos/build/marks-test/`, then `lake build inspect`, runs `inspect` on `saved.pdf`, and runs `qpdf --check` on it when `qpdf` is installed (skipped with a message otherwise) |
| `macos/tests/run_select.sh` | runs `select_test WORKER Tests/golden` (selection, copy, search, Find Next/Previous steps, pointer and links, the allowance) |
| `macos/tests/run_all.sh` | compiles `tests/all_headers.c` (all four headers, `-Wall -Wextra -Werror`), runs the four scripts above in turn, then lists the global symbols the four `safepdf_*.o` objects define (`nm -g -U`) and fails on a duplicate. Prints one summary line; exit status is non-zero on any failure |

Counts on 2026-11-24 (task 11.3f, `macos/tests/run_all.sh`): `core_test: 144 checks, 0 failures`, `view_test: 314 checks, 0
failures`, `marks_test: 148 checks, 0 failures`, `select_test: 70 checks, 0 failures`, `no duplicate
global symbols (193 defined in 4 objects)`, `run_all.sh: ok`.

`lake build macosFfi` is also a step of the Linux CI `build` job, so the `#guard`s of
`FfiView.lean`, `FfiMarks.lean`, `FfiSelect.lean` and `Ffi/Flat.lean` run there. Since task 11.4 the
CI `macos` job runs `macos/tests/run_all.sh`.

# The Swift app (tasks 11.3b to 11.3f)

Native AppKit shell in Swift 6 (strict concurrency) over the C API v2; unverified shell code that
only moves data between AppKit and the core (Plan.md §8). Every rule with a theorem or a `#guard`
is a call into the Tk viewer's own Lean code through the four headers; Swift converts values,
keeps transient UI state and draws. Every exported command is implemented (`Commands.swift`:
none pending since 11.3e2).

## Sources (`macos/App/`)

| File | Role (from its header comment) |
|---|---|
| `main.swift` | Entry point: `SafePdf [FILE.pdf]`, or the headless self-test when `SAFEPDF_MACOS_SELFTEST=DIR` is set |
| `AppDelegate.swift` | Application life cycle: menubar, the document window, files from Finder and `open -a`, About and Quit; the unsaved-marks question before quitting and before opening another file |
| `ChromeTables.swift` | Swift copies of the exported chrome tables (every C struct copied into Swift values and freed at once) |
| `Commands.swift` | Which exported commands this shell implements (all since 11.3e2) |
| `CoreBridge.swift` | Start-up of the C API and small conversions |
| `Document.swift` | An open PDF over the C API v2 (a `safepdf_document` reference, released with the object): exact page geometry, open settings, page labels |
| `DocumentToolbar.swift` | The unified toolbar built from the exported toolbar table (SF Symbols, the Tk bar's order) |
| `DocumentWindowController.swift` | The document window: toolbar, split view with sidebar and page area, command routing and enabled states, zoom and rotation commands, view modes, page field, back/forward, open settings, subtitle, titlebar flags, Copy / Find, the sidebar and full screen, Save / Save As / XFDF and the unsaved-marks question |
| `FindController.swift` | Find, Find Next / Previous and highlight-all on the page view |
| `FullScreen.swift` | Native full screen with the trusted file-identity line |
| `KeyEquivalents.swift` | Neutral keys (Menu.lean's key table) to AppKit key equivalents |
| `LinkController.swift` | Following links on the page view; the external-link sheet (Copy Address / Cancel) |
| `MainMenu.swift` | The menubar built from the exported menu table |
| `MarksController.swift` | Marks on the page view: the tools, highlights and notes, free text and drawings, selecting, moving, recolouring and deleting marks, undo/redo, the selection bubble and Escape |
| `MarksModel.swift` | The marks store of one document over `safepdf_marks.h`, created from the document's bytes |
| `MarksPreview.swift` | The preview of edited saved marks: a second document over its own worker |
| `MarksViews.swift` | The views of the marks: the bubble and colour picker, the note editor, the free-text box, the tools' pop-overs |
| `PageCanvasView.swift` | The pages, laid out by `safepdf_view_layout` and drawn from renders; the keys the menu cannot carry |
| `PageViewController.swift` | The content item: an `NSScrollView` over the page canvas; zoom, pinch, rotation and the navigation rules |
| `Rendering.swift` | Asynchronous page renders through `safepdf_doc_render` (zero-copy into a `CGImage`) |
| `SaveController.swift` | Save, Save As…, the unsaved-marks question and XFDF import / export |
| `Selection.swift` | Text selection on the page view, Copy and Select All, the pointer's cursor |
| `SelfTest.swift` | The headless self-test (below) |
| `SelfTestNav.swift` | The self-test's checks of 11.3c2 (navigation, modes, page field, history, open settings, subtitle, pill, flags) |
| `SelfTestText.swift` | The self-test's checks of 11.3d1 (selection, copy, cursor, find, links) |
| `SelfTestSidebar.swift` | The self-test's checks of 11.3d2 and 11.3f (thumbnails, outline, attachments with the size probe and the icon click, layers, page modes, identity line) |
| `SelfTestMarks.swift` | The self-test's checks of 11.3e1 (marks on the page) |
| `SelfTestSave.swift` | The self-test's checks of 11.3e2 and 11.3f (Save, XFDF, the preview and the thumbnails following it) |
| `SelfTestCutPaste.swift` | The self-test's checks of 11.6a (page field width, ⌘X / ⌘V of marks, the highlighter cursor, sliding jumps) |
| `Sheets.swift` | Open and save panels and alerts as document-modal sheets |
| `SidebarViewController.swift` | The sidebar item with its four panels and the switcher; wires them to the page view |
| `SidebarModel.swift` | The sidebar's rules through the C API |
| `SidebarThumbnails.swift` | The thumbnails panel |
| `SidebarOutline.swift` | The outline panel and the tree both tree panels use |
| `SidebarAttachments.swift` | The attachments panel |
| `SidebarLayers.swift` | The layers panel |
| `StatusPill.swift` | The transient status pill: `NSGlassEffectView` on macOS 26, a material on 14/15 |
| `TextStore.swift` | The per-document cache of page text indexes and links |
| `ViewNav.swift` | View modes, spreads, wheel steps, history, page text and open settings through the C API |
| `ZoomModel.swift` | The zoom and rotation rules through `safepdf_view.h` |

Swift sees the C API through `module.modulemap`: one Clang module, `SafePdfC`, made of
`safepdf_core.h`, `safepdf_view.h`, `safepdf_marks.h` and `safepdf_select.h`; the sources say
`import SafePdfC`. `swiftc -I macos` finds the module map.

## Viewing (11.3c1, 11.3c2)

* **Zoom**: Zoom In / Out step through `View.stepInZ` / `stepOutZ` on the effective, quantised
  zoom; the toolbar's zoom drop-down offers the `ZoomChoice` presets (Automatic Zoom, Actual
  Size, Page Fit, Page Width, percentages). Every zoom or rotation change notes the page point
  under the anchor (the pointer, else the window centre) and scrolls so that `View.reanchor`'s
  image of it lies there again. ⌘-scroll zooms at the pointer (the Tk viewer's
  Command-MouseWheel binding).
* **Pinch**: live magnification (the bitmap scales during the gesture), committed to a quantised
  zoom at the gesture's end; smart magnify (two-finger double tap) is ignored. The sharp render
  cross-fades over the scaled image.
* **Rotation**: quarter turns clockwise and counter-clockwise, re-anchored as zoom.
* **View modes**: the view-mode drop-down's four choices (page or vertical scrolling, with or
  without two-page spreads) with odd / even spreads and `/Direction /R2L` mirroring; in the page scroll mode only the
  current spread is laid out and the wheel and Space / arrows turn pages at the edges
  (`View.wheelStep`). The current page is the page the viewer went to while the view stays there,
  else the page under the window centre.
* **Page field**: the toolbar field shows `Toolbar.entryText` with "of N" or "(k of N)" for page
  labels; Return goes there (`Toolbar.pageEntry`), an invalid entry reverts.
* **History**: Back / Forward over `Links.History` (at most 100 places each way); jumps from links,
  the outline, thumbnails and the page field are recorded.
* **Open settings**: every open starts afresh and applies the document's settings
  (`safepdf_doc_open_settings`): `/PageLayout`, `/Direction`, the `/OpenAction` destination and
  its zoom, the window title from `/DisplayDocTitle`, `/PageMode` for the sidebar; what is not
  honoured goes to the status pill.
* **Window and status**: title = document name with the proxy icon, subtitle `page k/n · zoom`
  (page labels as in Tk); the transient status pill (bottom centre, 4 s, then fades) shows notes
  and errors (the 10 Mpx per-page cap, open-settings notes, render errors); a titlebar accessory
  flags repaired and encrypted files.

## Text (11.3d1)

* **Selection**: a drag selects on the page it started on, from the glyph nearest the press point
  to the glyph nearest the pointer (`Select.dragRange`; as Tk); a double click selects the word,
  a triple click the line, shift-click extends from where the selection started. The selection is
  one band per line (`Select.selBands`) in the system accent colour at 35 %.
* **Copy** and **Select All**: Copy puts `Select.rangeText` on the clipboard and the pill shows
  `Select.copyStatus`, which counts text from glyphs the page does not paint (task 12.5).
* **Find**: the toolbar's search field (⌘F; ⌘G / ⇧⌘G for next / previous) with the Tk viewer's
  messages ("hit k/c on page p", per page as in Tk; "not found"; "search: empty query"); the
  order is `Select.searchStep`, pages are indexed as needed under the work allowance (400 pages,
  60 s); highlight-all draws every hit on the visible pages in yellow and the current one in
  orange.
* **Links**: a click in place follows the link under it (`Links.linkAt`): a destination in the
  document is a jump recorded in the history; **an external URI is never opened** — a
  document-modal sheet shows the exact address with **Copy Address** and **Cancel** (Copy Address
  only puts it on the clipboard); any other action (Launch, GoToR, JavaScript, an unknown
  destination) is described in the pill and not followed. The app makes no `NSWorkspace` call.
* **Cursor**: `Toolbar.cursorFor` over what lies under the pointer (text, link, mark). With the
  Highlight tool (11.6a) the page shows a highlighter cursor (the SF Symbol `highlighter`, black
  with a white outline, hot spot at the tip) where the rule gives the I-beam or the arrow; links
  and marks keep the pointing hand.
* **Cut and Paste of marks** (11.6a, Edit → Cut ⌘X / Paste ⌘V, the standard `cut:` / `paste:`
  actions: a focused text field takes them first): Cut removes the selected mark — highlight
  (with its comment), note, free text or drawing — in one undo step and keeps it on the app's
  mark clipboard; its text (a note's or free text's, or the highlighted text) goes on the
  pasteboard. Paste re-creates it through the add exports as a new, selected mark in one undo
  step: at the same place on its own page, else at the same page coordinates moved inside the
  current page's CropBox; it pastes again as often as wanted. The items are enabled only with a
  selected / a cut mark.
* **Sliding jumps** (11.6a): outline items, thumbnails, links, the page field and Back / Forward
  scroll to the destination with a 0.3 s ease-out slide (a display link on screen) instead of
  jumping, the destination's renders asked for first and the current page held at the target; a
  jump farther than 1.5 view heights first cuts to that distance. "Reduce motion" (and headless
  runs) jump at once; a wheel, a key scroll, a zoom or a relayout ends a slide at its target.

## Sidebar (11.3d2, 11.3f)

The sidebar (an `NSSplitViewController` sidebar item) has four panels switched by a segmented
control showing only the panels the document has (`Sidebar.buttons`: thumbnails always, the
outline, attachments and layers when present). When the outline, attachments and layers are
known, it opens as `/PageMode` says (`Sidebar.onLoad`: UseThumbs, UseOutlines, UseAttachments,
UseOC when the content exists; without a page mode the outline when there is one; UseNone and
FullScreen keep it closed); the toggle reopens the last panel chosen while the document has it
(`Sidebar.pick`).

* **Thumbnails**: laid out by `Sidebar.thumbLayout`; only the visible ones and `thumbMargin` more
  each side are rendered, through the worker at the thumbnail priority, at most 2 in flight;
  requests scrolled away are cancelled; at most `thumbBudget` (40) images are kept, rendered at
  ½–⅛ scale when needed to fit the 32 MiB reserve. The current page's thumbnail is highlighted
  and follows the view; a click (or Return on the keyboard selection) jumps. Thumbnails use the
  layers state of the page view and, while saved marks are edited, the same preview document as
  the pages (11.3f, as Tk's `State.view`); marks not yet saved are drawn only on the page view
  (as in Tk).
* **Outline**: an `NSOutlineView` tree (`Sidebar.rows`, `initialOpen`); a click activates the
  destination (a jump in the history; an external address goes to the same Copy Address sheet).
* **Attachments**: listed without decoding (name, the size known without decoding, a tooltip with
  description, type, dates, page, problem). Save Attachment As… (double-click, Return, the context
  menu) decodes, then asks with an `NSSavePanel` and refuses `Attach.targetProblem`'s targets.
  There is no open, open-with or Quick Look action: nothing launches an attachment. A click on a
  file attachment annotation's icon on the page opens the sidebar on this panel and selects its
  row (11.3f, `Viewer.attSelect`). When a row's tooltip is about to show and its size is unknown
  (a filtered stream, "?"), it is decoded once in the background and the size column shows the
  decoded size (11.3f, `Viewer.attProbe`; see the deviation under "Known limitations").
* **Layers**: the optional-content tree with checkboxes (`Sidebar.layerRows`); a click is
  `safepdf_layers_toggle` (radio groups, locked groups); pages and thumbnails re-render under the
  new state, which is never written to the file. Every open starts with the default state.

## Full screen (11.3d2)

Native full screen. While the window is in full screen a dark strip at the bottom of the page area
reads the trusted identity line (`safepdf_identity_line`: the cleaned file name and path, never
the document's `/Title`); the page view ends above it, so nothing the document draws can cover
it. A document's `/PageMode /FullScreen` enters full screen on open with the note "full screen
(Escape leaves)"; Escape leaves, and the sidebar then follows `/NonFullScreenPageMode`.

## Marks (11.3e1)

* **Tools**: Select text, Highlight, Add comment, Add text, Draw (exactly one pressed,
  `safepdf_marks_ui_step`); the Highlight and Add text / Draw pop-overs (`NSPopover`) set the
  colour, font size, thickness and opacity; Escape closes the topmost transient and keeps the tool
  (`safepdf_marks_escape_closes`).
* **Bubble**: after a selection a floating bar (glass on macOS 26, a material before) offers the
  five highlight colours and Comment (plus Copy, a native addition); on a selected highlight the
  edit bubble offers its colour (the picker), Comment and Delete. Placement is `Bubble.place`.
* **Notes**: Add comment anchors by `Marks.noteAnchor` (the clicked point, or the selection's
  quads); the note editor is an `NSPopover` with Delete, Cancel and Save (⌘Return); closing it
  without Save follows `safepdf_marks_note_close`.
* **Edit**: a click on a mark selects it; free text and drawings move by dragging; a double click
  edits a text box in place (Escape or a click elsewhere commits); a drawing session's strokes are
  one mark; a slider drag is one undo step. Delete removes the selected mark (a highlight's comment
  goes with it). Undo / Redo (⌘Z / ⇧⌘Z) step the store's history.
* Saved marks are painted by the renderer; new ones are drawn by the page view over it.

## Save, Save As, XFDF (11.3e2)

The Tk viewer's flow step for step, every rule and text from `safepdf_marks.h`: Save writes the
marks as an incremental update (the original bytes stay a prefix, C7); the first overwrite of the
opened file asks Overwrite / Save As… / Cancel; a file changed on disk since it was opened offers
Save As… / Cancel; Save As… proposes `STEM-annotated.pdf`, takes the opened file's own name
only after `Save.openedOverwriteQuestion` and refuses folders and read-only targets
(`Save.targetProblem`); the write is atomic (a temporary file in the
target's folder, read back, permissions copied, renamed). An encrypted file is saved only with 64
fresh bytes from `SecRandomCopyBytes`. After a save the file is reopened keeping view mode, zoom,
rotation, page and sidebar. Closing the window, quitting or opening another file with unsaved
marks asks Save / Don't Save / Cancel (a failed save aborts the close). Import XFDF adds the marks
not already present (one undo step; a refused file changes nothing); Export XFDF writes
`STEM.xfdf`. Output is capped at `safepdf_marks_output_ceiling` (half of it for an export).

## Preview of edited saved marks (11.3e2, 11.3f)

While saved marks are changed or deleted, the pages show the document as the next save will write
it: `safepdf_marks_preview` builds the bytes on a background queue from a snapshot of the store,
and they are opened with `safepdf_doc_open_bytes` as a **second document over its own confined
worker**. The page canvas and (11.3f) the thumbnails send their renders there; layout, text and
links stay with the opened document, as in Tk. A newer edit supersedes a preview still being
built; an error leaves the pages as they are and the pill says why; undoing back to the file's
state renders from the document itself again. Preview documents are released on a background
queue.

## Build

```
macos/build.sh            # needs elan's Lean and the Xcode command line tools only
lake build macosApp       # macOS only: macosFfi + worker, then macos/build.sh -> macos/build/SafePdf.app
lake build app            # the platform viewer: macosApp on macOS, the Tk viewer + worker elsewhere
lake build viewer worker  # the Tk viewer on Linux or macOS (needs Tk through pkg-config)
```

The Lake targets come from task 11.4 (`lakefile.lean`): `macosApp` builds `macosFfi` and `worker`
and then runs `macos/build.sh` with `SAFEPDF_MACOS_LAKE_DONE=1` (so the script does not build them
again). `macos/build.sh` still works on its own and builds `macosFfi` and `worker` itself. CI has
a `macos` job (runner `macos-26`) that runs `lake build`, `macosFfi` / `worker`, `macos/build.sh`,
`macos/tests/run_all.sh`, the headless self-test and `codesign`.

`build.sh` runs `lake build macosFfi worker`, compiles the four C shims with `clang` at
`-mmacosx-version-min=15.0`, links `App/*.swift` with `swiftc` (`-target …-macos15.0`) against the shims,
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
anything else; there is no window and the app never calls `run` or activates. Give `OUTDIR` as an
absolute path. `SelfTest.swift` checks that the chrome tables build (every command in the menubar,
every toolbar item), open and its error path, page 1 through `safepdf_doc_render` at 1x and 2x,
pages 1 to 10 at 2x, the real scroll view and page canvas at 1x and 2x backing, scrolling to page
2 and dark mode; zoom, pinch, rotation and backing changes (11.3c1); then, in order:

* `SelfTestNav.swift` (11.3c2): the current-page rule after Last page, every view-mode choice with
  its spreads, right to left, Next / Previous by spreads, the wheel and Space / Up turning pages in
  the page scroll mode, the page field (Return, an invalid entry), back / forward, the subtitle
  with the document's page labels, the 10 Mpx cap pill, the titlebar flags, and open settings on
  generated files written to `DIR/opensettings/` (the files of the Tk smoke case 1s);
* `SelfTestText.swift` (11.3d1): selection by drag, double / triple click and shift-click, the
  accent-coloured bands, Select All and Copy (onto a private pasteboard), the cursor, Find Next /
  Previous with wrap and highlight-all, the NEED path across pages, and links on
  `pages/tree.pdf` (an internal jump with history; an external address reaches the sheet, built,
  never shown or opened);
* `SelfTestSidebar.swift` (11.3d2, 11.3f): thumbnails (sizes, lazy rendering, cancellation, the
  budget on a generated 60-page file, the highlight, a click's jump), the outline of
  `pages/outline.pdf`, the attachments of a generated `att.pdf` (listing, saving, refused targets;
  11.3f: the tooltip's size probe of a filtered attachment — one probe, kept — and a click on the
  file attachment icon on page 2 opening the attachments panel with its row selected), the layers
  of a generated `oc.pdf`, the page modes' panels, and the identity line;
* `SelfTestMarks.swift` (11.3e1): highlights through the real pointer path and the bubble, the
  picker, comments and notes, free text, ink, undo / redo, the tools and cursors, the Edit
  commands' states, saved marks listed after a reopen;
* `SelfTestSave.swift` (11.3e2, 11.3f): Save on a copy in `DIR/save/` through the real controller
  with scripted dialogs (overwrite question, C7 prefix, reopen keeping the view, a second save
  appending, the preview after deleting a saved highlight — pixels — and, 11.3f, the thumbnails
  rendered from that preview and back from the file after the undo), encrypted files, the
  changed-on-disk check, the unsaved-marks question, XFDF export / import;
* `SelfTestCutPaste.swift` (11.6a): the page field's width (narrower than the old 56 pt box, "of
  N" right after it, wider for roman labels and many pages), ⌘X / ⌘V of a highlight with its
  comment, a note, free text and a drawing (same page and page 2, one undo step each, undo /
  redo, a second paste, the text on a private pasteboard, the Edit items), the highlighter
  cursor, and sliding jumps (a page jump and an outline click on a generated five-page file pass
  through intermediate positions and end exactly where the immediate jump lands; the Reduce
  motion rule).

It writes PNGs and `timings.txt` to DIR, prints `failures: N` and exits 0 when `N` is 0.

`selftest.sh` samples `lsappinfo front` every 0.5 s and checks `lsappinfo list` for a Foreground
registration, both only for the PID the script started (a copy launched by hand is ignored; the
match is by PID, so it covers the names `safepdf-mac`, `SafePdf` and `SafePDF`). It kills only
that PID if either shows up, and reports `leaks: N`. When `lsappinfo` reports no front
application at all (a session without a window server, as on a CI runner), it prints a SKIP line
for the watcher instead (task 11.4).

Results on 2026-11-24 (task 11.3f): `failures: 0` and `leaks: 0` on `text/latin.pdf`, `pages/tree.pdf` and
`pages/outline.pdf`, and on `text/latin.pdf` with `SAFEPDF_SELFTEST_BUNDLE=1`.

## Known limitations

* **Minimum macOS: 15** (the human's decision, task 11.6a). `Info.plist` sets
  `LSMinimumSystemVersion` to 15.0 and `build.sh` compiles and links for macOS 15.0, which the
  pinned Lean toolchain's `libgmp.a` / `libuv.a` are built for. The linker still warns once per
  object of `libsafepdfffi.a` (117 objects): Lake compiles the Lean-generated C without a
  deployment target, so those objects carry the build machine's macOS (26.0 on a macOS 26 host).
  `build.sh` counts the warnings (full text in `build/swift-link.log`); passing
  `-mmacosx-version-min=15.0` to Lake's C compiler (`moreLeancArgs` in `lakefile.lean`) would
  silence them.
* **Attachment size probe** (11.3f): the Tk viewer's tooltip probe lowers the per-stream decoding
  cap to 16 MB (`Attach.probeLimit`; a larger file shows "> 16 MB"). `safepdf_doc_attachment_bytes`
  has no cap parameter, so the app's probe decodes under the viewer's own limits (as Save
  Attachment As… does) and a larger file shows its decoded size. The tooltip text is the C API's
  (`Attach.tooltip` without a probe outcome), so a probed row's tooltip still names the stored
  size; the size column shows the decoded one. Matching Tk exactly needs a capped variant of the
  bytes request in `safepdf_core.h`.


# History: the AppKit spike (task 11.1) — superseded

The spike was a single Objective-C file, `main.m` (an `NSWindow` with an `NSScrollView` and a page
view, one render thread), replaced by the Swift app above; `main.m` is no longer in this
directory. The sections below describe it and its v1 calls as they were.

Plan.md §6 Phase 11: *"Spike first: a minimal Cocoa window (open, render, scroll, zoom) over
the C API; record the feel delta and the FFI surface in a Decisions entry before committing to
parity."* Plan.md §8: the shell is unverified and replaceable; the core as a library is the
deliverable. The spike was not parity with the Tk viewer (no toolbar,
sidebar, selection, search, links or annotations; that is 11.3).

## The v1 C API (`safepdf_core.h`) — removed (task 11.3c1)

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
