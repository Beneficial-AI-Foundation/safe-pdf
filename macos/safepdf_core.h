/*
 * safepdf_core.h — the C API over safe-pdf-core.
 *
 * v2 (task 11.3a1, the document layer over the worker; page geometry, task 11.3c1). The v1
 * calls of the 11.1 spike (safepdf_open, the synchronous safepdf_render, safepdf_image_free)
 * were retired in task 11.3c1. Plain C: no Lean types leak through. Implemented in
 * safepdf_core.c over the Lean exports of SafePdf/Shell/Ffi.lean, SafePdf/Shell/Ffi/V2.lean
 * and SafePdf/Shell/Ffi/Flat.lean; link
 * with libsafepdfffi.a (`lake build macosFfi`) and Lean's runtime libraries (macos/build.sh).
 * Design: docs/macos-design.md §3 (decisions 2 and 4).
 *
 * ===== v2: documents over the confined worker =====
 *
 * Documents
 *   safepdf_doc_open_file reads the file through the capped read (task 12.1: at most
 *   Limits.maxInputBytes + 1 bytes through a handle); safepdf_doc_open_bytes takes a caller
 *   buffer (copied; the caller keeps its buffer). Both parse the document in this process (page
 *   count and sizes are answered synchronously from that parse) and start the document's
 *   worker session: one confined `worker` process per document, spawned on the first request,
 *   sent the bytes (never the path).
 *   safepdf_doc_page_geom gives each page's CropBox as exact rationals and its /Rotate, in the
 *   safepdf_page_geom of safepdf_view.h (included here), ready for safepdf_view_layout.
 *
 * The worker executable
 *   safepdf_open_options.worker_path, else the path set by safepdf_set_worker_path, else
 *   `worker` next to the host executable. Opening fails (error "no document worker at …")
 *   when the file does not exist.
 *
 * Reference counting
 *   An open returns a document with one reference. safepdf_doc_retain adds one,
 *   safepdf_doc_release drops one. The LAST release closes the document: queued requests are
 *   cancelled, a request in flight is stopped (its worker is killed), in-process requests that
 *   have not started are cancelled — and release BLOCKS until every outstanding request's
 *   callback has been enqueued on its queue (it does not wait for the callbacks to run, so it
 *   may be called from a callback's own queue). Then the handle is freed. A callback never
 *   receives the document, so it may run after the document is gone.
 *
 * Requests (asynchronous)
 *   Every safepdf_doc_<request> call returns a request id (> 0) and later calls its callback
 *   EXACTLY ONCE, on the caller's dispatch queue (dispatch_async_f), with
 *     SAFEPDF_STATUS_OK        result non-NULL, owned by the callback: free it with the
 *                              matching safepdf_free_* (or keep it);
 *     SAFEPDF_STATUS_ERROR     `error` is the English message, result NULL;
 *     SAFEPDF_STATUS_CANCELLED cancelled, superseded or the document closed; result NULL.
 *   `error` is borrowed: valid only during the callback (copy it to keep it). `context` is
 *   passed through untouched. A call with a NULL document, queue or callback returns 0 and
 *   never calls back.
 *
 *   Where they run: render, page index, links and outline go to the worker (priorities,
 *   cancel, deadline). The worker protocol has no request for page labels, attachments or the
 *   layers configuration, so those (and an attachment's bytes) are computed from the
 *   in-process parse on a Lean task, as the Tk viewer does; their priority is ignored.
 *
 * Priorities (worker requests): 0 most urgent (the current page or spread, the outline),
 *   1 other visible pages and the prefetch, 2 thumbnails; oldest first among equals.
 *   safepdf_doc_raise makes a queued request more urgent.
 *
 * Cancel: safepdf_doc_cancel(doc, id). A queued request is dropped (CANCELLED); one in flight
 *   for more than 250 ms is stopped by killing its worker (CANCELLED; the next request starts
 *   a fresh worker). An id already delivered changes nothing.
 *
 * Worker crash or deadline: a request without an answer within the deadline
 *   (safepdf_open_options.deadline_ms, default 20000) kills the worker and is delivered as
 *   SAFEPDF_STATUS_ERROR "the document took too long (no answer within 20 s; its worker was
 *   stopped)"; a crashed worker gives "the document worker stopped: …". The next request
 *   spawns a fresh worker and sends the bytes again.
 *
 * Ownership of the structs
 *   Every result struct handed to a callback is heap-allocated and owned by the receiver,
 *   with all its arrays and strings: one safepdf_free_<type> frees all of it (NULL allowed).
 *   Strings inside results are UTF-8, NUL-terminated (a NUL in document text becomes
 *   U+FFFD) and live as long as the struct. safepdf_layers_state values written by
 *   safepdf_layers_toggle live in caller storage; release their arrays with
 *   safepdf_free_layers_state. Input pointers are borrowed for the duration of the call.
 *   Error strings from `char **error` out-parameters are malloc'd; release them with free().
 *
 * Coordinates: page space in points (PDF user space: origin at the lower left, y up), as
 *   doubles converted from the core's exact rationals (display only).
 *
 * Threads
 *   safepdf_init runs once, on the main thread, before anything else. Any thread may then call
 *   the API: a thread that is not registered with the Lean runtime is registered on its first
 *   call and unregistered when it exits (safepdf_thread_enter/exit remain optional).
 *   The worker session runs its own Lean task threads; completion is reported from one of them
 *   to the C shim (an @[extern] callback), which copies the result into the C structs and
 *   enqueues the caller's callback with dispatch_async_f. Callbacks therefore run outside Lean
 *   and may call the API again (e.g. submit the next request).
 *
 * Tests only
 *   safepdf_open_options.test_stall_ms and safepdf_test_render_sync exist for
 *   macos/tests/core_test.c; an application never calls them.
 */
#ifndef SAFEPDF_CORE_H
#define SAFEPDF_CORE_H

#include <stddef.h>
#include <stdint.h>
#include <dispatch/dispatch.h>

#include "safepdf_view.h" /* safepdf_rat_box, safepdf_page_geom */

#ifdef __cplusplus
extern "C" {
#endif

/* ----------------------------------------------------------------- common */

/** A rendered page: `height` rows of `stride` bytes, each pixel R, G, B, A (A = 255;
    white background), rows from the top. */
typedef struct {
    uint8_t *rgba;
    size_t width;
    size_t height;
    size_t stride;
} safepdf_image;

/** Initialise the Lean runtime and the core's modules. 0 on success. Idempotent. */
int safepdf_init(void);

/** Register / unregister the calling (non-main) thread with the Lean runtime. Optional
    (threads are registered on their first call). */
void safepdf_thread_enter(void);
void safepdf_thread_exit(void);

/* ----------------------------------------------------------------- v2: documents */

/** A document over the worker (opaque, reference counted). */
typedef struct safepdf_document safepdf_document;

/** A request id; 0 means "not submitted". */
typedef uint64_t safepdf_request_id;

/** How a request ended. */
typedef enum {
    SAFEPDF_STATUS_OK = 0,
    SAFEPDF_STATUS_ERROR = 1,
    SAFEPDF_STATUS_CANCELLED = 2
} safepdf_status;

/** Worker priorities (lower is more urgent). */
enum {
    SAFEPDF_PRIO_CURRENT = 0,
    SAFEPDF_PRIO_VISIBLE = 1,
    SAFEPDF_PRIO_THUMBNAIL = 2
};

/** Options of an open (NULL options: all defaults). */
typedef struct {
    /** The worker executable; NULL: safepdf_set_worker_path's, else `worker` next to the
        host executable. */
    const char *worker_path;
    /** Request deadline in ms; 0: 20000. */
    uint32_t deadline_ms;
    /** Nonzero: strict mode, the repair path never runs (task 12.1). */
    int strict;
    /** TESTS ONLY: the worker sleeps this many ms before each render (0: off). */
    uint32_t test_stall_ms;
} safepdf_open_options;

/** Set the default worker executable for later opens (copied; NULL clears). 0 on success. */
int safepdf_set_worker_path(const char *path);

/** Open the PDF at `path` (UTF-8) through the capped read. NULL on failure, `*error` set. */
safepdf_document *safepdf_doc_open_file(const char *path, const safepdf_open_options *opts,
                                        char **error);

/** Open a PDF from `len` bytes at `bytes` (copied). NULL on failure, `*error` set. */
safepdf_document *safepdf_doc_open_bytes(const uint8_t *bytes, size_t len,
                                         const safepdf_open_options *opts, char **error);

/** Add a reference; returns `doc`. NULL is allowed. */
safepdf_document *safepdf_doc_retain(safepdf_document *doc);

/** Drop a reference; the last one closes the document (see the header comment: cancels and
    drains pending requests, blocks until their callbacks are enqueued). NULL is allowed. */
void safepdf_doc_release(safepdf_document *doc);

/** Number of pages (synchronous). */
size_t safepdf_doc_page_count(const safepdf_document *doc);

/** Displayed size of page `page` (0-based) in points (CropBox, /Rotate applied; synchronous).
    0 on success, -1 when `page` is out of range. */
int safepdf_doc_page_size(const safepdf_document *doc, size_t page, double *width,
                          double *height);

/** The geometry of page `page` (0-based) for safepdf_view_layout (synchronous, read at open):
    `out->box` is the effective CropBox in page units as exact rationals (den > 0), the box the
    renderer draws; `out->rotate` the effective /Rotate in degrees (0, 90, 180, 270). Pass the
    user's extra rotation separately (safepdf_layout_params.user_rotation, and to
    safepdf_doc_render as quarter turns). 0 on success; -1 when `doc` or `out` is NULL, `page`
    is out of range, or a coordinate does not fit 64 bits (`*out` zeroed). */
int safepdf_doc_page_geom(const safepdf_document *doc, size_t page, safepdf_page_geom *out);

/** Nonzero when the file opened only through the repair path. */
int safepdf_doc_is_repaired(const safepdf_document *doc);

/** Nonzero when the file is encrypted (opened with the empty user password). */
int safepdf_doc_is_encrypted(const safepdf_document *doc);

/* ----------------------------------------------------------------- v2: open settings */

/** /PageMode and /NonFullScreenPageMode values (Core.Doc.OpenSettings.PageMode). */
typedef enum {
    SAFEPDF_PAGE_MODE_UNSET = -1, /* the document sets none */
    SAFEPDF_PAGE_MODE_USE_NONE = 0, SAFEPDF_PAGE_MODE_USE_OUTLINES = 1,
    SAFEPDF_PAGE_MODE_USE_THUMBS = 2, SAFEPDF_PAGE_MODE_FULL_SCREEN = 3,
    SAFEPDF_PAGE_MODE_USE_OC = 4, SAFEPDF_PAGE_MODE_USE_ATTACHMENTS = 5
} safepdf_page_mode;

/** The document's open settings (task 9.r8; Core.Doc.OpenSettings.read), as the Tk viewer
    applies them on every open (Viewer.applyOpenSettings; the view first resets to vertical
    scrolling, no spreads, left to right, Automatic Zoom, page 1). */
typedef struct {
    bool has_layout;      /* /PageLayout given: `scroll` and `spread` are its view modes
                             (View.modesOf); else they are the default (vertical, none) */
    uint32_t scroll;      /* safepdf_scroll_mode */
    uint32_t spread;      /* safepdf_spread_mode */
    bool rtl;             /* /ViewerPreferences /Direction /R2L: spreads mirrored */
    int32_t page_mode;    /* safepdf_page_mode (/PageMode; UNSET when absent) */
    bool has_dest;        /* /OpenAction is a destination (or a GoTo) on a page of the file */
    size_t dest_page;     /* its page (0-based) */
    bool has_left, has_top; /* its left / top in page units, when it gives them */
    safepdf_rat left, top;
    safepdf_zoom_choice zoom; /* the zoom to open at (Toolbar.zoomChoiceOf from Automatic
                                 Zoom; Automatic Zoom without a destination) */
    bool hide_toolbar, hide_menubar, hide_window_ui, fit_window, center_window,
        display_doc_title;
    int32_t non_full_screen_mode; /* /NonFullScreenPageMode (safepdf_page_mode) */
    char *title;          /* the window title (/DisplayDocTitle with a non-blank /Title), else
                             NULL */
    char **notes;         /* what was not honoured (Issue.message: an ignored JavaScript or URI
                             open action, an unresolved destination, a bad value, …) */
    size_t note_count;
} safepdf_open_settings;

/** The open settings of `doc` (synchronous, from the in-process parse; a few dictionary
    lookups). 0 on success (free with safepdf_free_open_settings), -1 on failure (`*out`
    zeroed). */
int safepdf_doc_open_settings(const safepdf_document *doc, safepdf_open_settings *out);
void safepdf_free_open_settings(safepdf_open_settings *s);

/* ----------------------------------------------------------------- v2: result structs */

/** A page-space box (points, y up). */
typedef struct { double llx, lly, urx, ury; } safepdf_box;

/** An optional content group (object number, generation). */
typedef struct { uint64_t num, gen; } safepdf_oc_key;

/** A layers state: the document's groups and those that are OFF. Input to renders and the
    page index (NULL: the document's default state). */
typedef struct {
    safepdf_oc_key *known;
    size_t known_count;
    safepdf_oc_key *off;
    size_t off_count;
} safepdf_layers_state;

/** One cell of a page's selection and search index (the Tk viewer's `Select.Cell`). */
typedef struct {
    const char *text;   /**< the glyph's text in reading order ("" for an overprinted duplicate) */
    const char *sep;    /**< the separator the layout puts before it ("", " " or "\n") */
    safepdf_box box;    /**< page-space box */
    size_t line;        /**< index of its line (into `line_dirs`) */
    int hidden;         /**< nonzero: the page does not paint it (Tr 3 / Tr 7) */
} safepdf_cell;

/** A page's selection and search index (the worker's `pageIndex` answer). */
typedef struct {
    safepdf_cell *cells;
    size_t cell_count;
    uint32_t *line_dirs;   /**< per line: baseline direction in quarter turns (0–3) */
    size_t line_count;
    char *strings_;        /**< internal: the string storage */
} safepdf_page_index;

/** What activating a link or an outline item does. */
typedef enum {
    SAFEPDF_ACTION_GOTO = 0,        /**< page, optional left/top */
    SAFEPDF_ACTION_URI = 1,         /**< text: the address as shown (percent-encoded) */
    SAFEPDF_ACTION_BAD_PAGE = 2,    /**< a destination whose page is not in the document */
    SAFEPDF_ACTION_UNRESOLVED = 3,  /**< text: a named destination that was not found */
    SAFEPDF_ACTION_OTHER = 4,       /**< text: another action type (never followed) */
    SAFEPDF_ACTION_NONE = 5
} safepdf_action_kind;

/** An action. */
typedef struct {
    safepdf_action_kind kind;
    size_t page;          /**< GOTO: 0-based page */
    int has_left;         /**< GOTO: `left` is given (page-space x of the left edge) */
    double left;
    int has_top;          /**< GOTO: `top` is given (page-space y of the top edge) */
    double top;
    const char *text;     /**< URI / UNRESOLVED / OTHER; "" otherwise */
} safepdf_action;

/** A link of a page (the Tk viewer's `Links.Link`). */
typedef struct { safepdf_box box; safepdf_action action; } safepdf_link;

/** A page's links. */
typedef struct {
    safepdf_link *links;
    size_t count;
    char *strings_;
} safepdf_link_list;

/** An outline row (preorder; each depth at most one more than the previous row's). */
typedef struct {
    const char *title;
    size_t depth;
    int is_open;          /**< starts expanded (/Count > 0) */
    safepdf_action action;
} safepdf_outline_item;

/** The outline. */
typedef struct {
    safepdf_outline_item *items;
    size_t count;
    char *strings_;
} safepdf_outline;

/** Page labels, one per page ("" where the document gives the page no label). */
typedef struct {
    const char **labels;
    size_t count;
    char *strings_;
} safepdf_label_list;

/** One attachment (Core.Doc.Attachments; nothing is decoded to list it). */
typedef struct {
    const char *name;          /**< display name */
    const char *file_name;     /**< default file name for saving */
    const char *description;   /**< NULL when absent */
    int has_size;
    uint64_t size;             /**< the listed size (/Params /Size, /DL, or stored unfiltered) */
    const char *mime;          /**< NULL when absent */
    const char *created;       /**< NULL when absent (PDF date string) */
    const char *modified;      /**< NULL when absent */
    int has_page;
    size_t page;               /**< page of its (first) file attachment annotation */
    int in_tree;               /**< from the /EmbeddedFiles name tree */
    int problem;               /**< 0 none; 1 not embedded; 2 bad /EF; 3 not a stream */
    const char *problem_text;  /**< "" when problem == 0 */
    /* task 11.3d2: what the attachments panel shows before decoding anything */
    const char *size_text;     /**< the size column (Attach.sizeColumn: "1.5 KB", "?", "—") */
    const char *tooltip;       /**< the row's tooltip (Attach.tooltip; "" when nothing to say) */
    int has_stream;            /**< it has an embedded file stream */
} safepdf_attachment;

/** A file attachment annotation's icon. */
typedef struct {
    size_t page;
    safepdf_box rect;
    size_t entry;              /**< index into `items` */
} safepdf_attachment_icon;

/** The document's attachments. */
typedef struct {
    safepdf_attachment *items;
    size_t count;
    safepdf_attachment_icon *icons;
    size_t icon_count;
    int truncated;             /**< entries beyond the cap were dropped */
    size_t warnings;           /**< problems skipped */
    char *strings_;
} safepdf_attachment_list;

/** Bytes (an attachment's decoded content). */
typedef struct {
    uint8_t *data;
    size_t len;
} safepdf_bytes;

/** A copy of the bytes the document was opened from (the capped read's, or the buffer given to
    safepdf_doc_open_bytes; task 11.3e1: the GUI creates the marks store from them, see
    safepdf_marks.h). NULL when `doc` is NULL or out of memory; free with safepdf_free_bytes. */
safepdf_bytes *safepdf_doc_bytes(const safepdf_document *doc);

/** A row of the layers panel (the Tk viewer's `Sidebar.layerRows`). */
typedef struct {
    size_t depth;
    const char *label;
    int has_group;          /**< 0 for a heading */
    safepdf_oc_key group;
    int italic;             /**< the "Additional Layers" heading */
    int locked;             /**< the checkbox is disabled */
    int on;                 /**< checked in `initial` */
} safepdf_layer_row;

/** The layers panel and the document's default state (no optional content: no rows, an
    empty state). */
typedef struct {
    safepdf_layer_row *rows;
    size_t count;
    safepdf_layers_state initial;
    char *strings_;
} safepdf_layers;

/* ----------------------------------------------------------------- v2: callbacks */

typedef void (*safepdf_render_fn)(void *context, safepdf_request_id id, safepdf_status status,
                                  const char *error, safepdf_image *image);
typedef void (*safepdf_page_index_fn)(void *context, safepdf_request_id id,
                                      safepdf_status status, const char *error,
                                      safepdf_page_index *index);
typedef void (*safepdf_links_fn)(void *context, safepdf_request_id id, safepdf_status status,
                                 const char *error, safepdf_link_list *links);
typedef void (*safepdf_outline_fn)(void *context, safepdf_request_id id, safepdf_status status,
                                   const char *error, safepdf_outline *outline);
typedef void (*safepdf_labels_fn)(void *context, safepdf_request_id id, safepdf_status status,
                                  const char *error, safepdf_label_list *labels);
typedef void (*safepdf_attachments_fn)(void *context, safepdf_request_id id,
                                       safepdf_status status, const char *error,
                                       safepdf_attachment_list *attachments);
typedef void (*safepdf_bytes_fn)(void *context, safepdf_request_id id, safepdf_status status,
                                 const char *error, safepdf_bytes *bytes);
typedef void (*safepdf_layers_fn)(void *context, safepdf_request_id id, safepdf_status status,
                                  const char *error, safepdf_layers *layers);

/* ----------------------------------------------------------------- v2: requests */

/** Render `page` at `zoom_num / zoom_den` pixels per point with an extra clockwise
    `rotation` (quarter turns, 0–3) under `layers` (NULL: the default state). Worker. */
safepdf_request_id safepdf_doc_render(safepdf_document *doc, size_t page, uint32_t zoom_num,
                                      uint32_t zoom_den, unsigned rotation,
                                      const safepdf_layers_state *layers, int priority,
                                      dispatch_queue_t queue, safepdf_render_fn fn,
                                      void *context);

/** The selection and search index of `page` under `layers` (NULL: default). Worker. */
safepdf_request_id safepdf_doc_page_index(safepdf_document *doc, size_t page,
                                          const safepdf_layers_state *layers, int priority,
                                          dispatch_queue_t queue, safepdf_page_index_fn fn,
                                          void *context);

/** The links of `page`. Worker. */
safepdf_request_id safepdf_doc_links(safepdf_document *doc, size_t page, int priority,
                                     dispatch_queue_t queue, safepdf_links_fn fn,
                                     void *context);

/** The outline. Worker. */
safepdf_request_id safepdf_doc_outline(safepdf_document *doc, int priority,
                                       dispatch_queue_t queue, safepdf_outline_fn fn,
                                       void *context);

/** The page labels. In process. */
safepdf_request_id safepdf_doc_page_labels(safepdf_document *doc, dispatch_queue_t queue,
                                           safepdf_labels_fn fn, void *context);

/** The attachments (listed, none decoded). In process. */
safepdf_request_id safepdf_doc_attachments(safepdf_document *doc, dispatch_queue_t queue,
                                           safepdf_attachments_fn fn, void *context);

/** The decoded bytes of attachment `index` (of safepdf_doc_attachments' list). In process
    (the worker protocol has no such request). */
safepdf_request_id safepdf_doc_attachment_bytes(safepdf_document *doc, size_t index,
                                                dispatch_queue_t queue, safepdf_bytes_fn fn,
                                                void *context);

/** The layers panel (optional content groups) and the default layers state. In process. */
safepdf_request_id safepdf_doc_layers(safepdf_document *doc, dispatch_queue_t queue,
                                      safepdf_layers_fn fn, void *context);

/** Cancel request `id` (see the header comment). */
void safepdf_doc_cancel(safepdf_document *doc, safepdf_request_id id);

/** Make queued worker request `id` more urgent (`priority` below its current one). */
void safepdf_doc_raise(safepdf_document *doc, safepdf_request_id id, int priority);

/** Toggle row `row` of the layers panel in state `current` (NULL: the default state), with
    the panel's rules (radio-button groups, locked groups unchanged, headings inert). Writes
    the new state to `*out` (caller storage; free with safepdf_free_layers_state).
    Synchronous. 0 on success, -1 on failure (`*error` set, `*out` zeroed). */
int safepdf_layers_toggle(safepdf_document *doc, const safepdf_layers_state *current,
                          size_t row, safepdf_layers_state *out, char **error);

/* ----------------------------------------------------------------- v2: the sidebar (11.3d2) */

/* The sidebar's rules (App.Sidebar, App.Attach, Viewer.identityLine; SafePdf/Shell/Ffi/Sidebar.lean).
 * Pure and synchronous, any thread after safepdf_init. */

/** A sidebar panel (Sidebar.panels order). */
typedef enum {
    SAFEPDF_PANEL_THUMBNAILS = 0, SAFEPDF_PANEL_OUTLINE = 1, SAFEPDF_PANEL_ATTACHMENTS = 2,
    SAFEPDF_PANEL_LAYERS = 3, SAFEPDF_PANEL_NONE = 4 /* the sidebar stays closed */
} safepdf_panel;

/** What a document has (Sidebar.Content). */
typedef struct {
    bool has_outline;
    bool has_attachments;
    bool has_layers;
} safepdf_sidebar_content;

/** The panel the sidebar opens with on load (Sidebar.onLoad) for `page_mode`
    (safepdf_page_mode, UNSET for none); SAFEPDF_PANEL_NONE: closed. */
safepdf_panel safepdf_sidebar_on_load(int32_t page_mode, safepdf_sidebar_content c);

/** Whether `panel`'s switcher button shows (Sidebar.Panel.available, Sidebar.buttons). */
bool safepdf_sidebar_available(safepdf_panel panel, safepdf_sidebar_content c);

/** The panel the sidebar toggle opens (Sidebar.pick): `last` while available, else the outline,
    else the thumbnails. */
safepdf_panel safepdf_sidebar_pick(safepdf_panel last, safepdf_sidebar_content c);

/** The thumbnail constants (Sidebar.thumbW, thumbTop, thumbLabelH, thumbGap, thumbMargin,
    thumbBudget), in pixels at 1x and counts. */
typedef struct {
    uint32_t width, top, label_h, gap, margin, budget;
} safepdf_thumb_constants;
int safepdf_sidebar_constants(safepdf_thumb_constants *out);

/** A page's thumbnail (the Tk viewer's pageSizeRot / Sidebar.thumbSize / thumbZoom): its size
    in pixels at 1x (`width` x `height`) and the zoom that renders it (pixels per point at 1x,
    thumbW / the rotated page width, `zoom_num / zoom_den`), with the user's extra rotation in
    quarter turns (0-3). 0 on success, -1 for a page out of range or a bad rotation (`*out`
    zeroed). */
typedef struct {
    uint32_t width, height;
    uint64_t zoom_num, zoom_den;
} safepdf_thumb;
int safepdf_doc_thumb(const safepdf_document *doc, size_t page, unsigned rotation,
                      safepdf_thumb *out);

/** The scale at which a thumbnail image of `w` x `h` pixels is rendered: 0 full, 1 half,
    2 quarter, 3 eighth zoom (task 12.3b's rule: thumbBudget such images fit the 32 MiB
    thumbnail reserve). */
unsigned safepdf_sidebar_thumb_scale(size_t w, size_t h);

/** The thumbnails laid out top to bottom (Sidebar.thumbLayout) from their `heights` (each
    `width` wide; pixels at 1x): `ys` (caller storage for `n`) receives each image's top, `*total`
    the panel's height. 0 on success. */
int safepdf_sidebar_thumb_layout(const uint32_t *heights, size_t n, uint32_t width, uint64_t *ys,
                                 uint64_t *total);

/** The thumbnails to render for the visible band [top, bottom) of a panel laid out by
    Sidebar.thumbLayout from `heights` (each `width` wide; pixels at 1x): Sidebar.thumbsWanted
    with thumbMargin, nearest the band's middle first. `*out` is malloc'd (free()), NULL when
    empty. 0 on success. */
int safepdf_sidebar_thumbs_wanted(const uint32_t *heights, size_t n, uint32_t width,
                                  uint64_t top, uint64_t bottom, size_t **out, size_t *count);

/** The thumbnails to drop (Sidebar.thumbEvict with thumbBudget) of `held` given `wanted` and
    the centre page, farthest first. `*out` malloc'd (free()), NULL when empty. 0 on success. */
int safepdf_sidebar_thumb_evict(const size_t *held, size_t nheld, const size_t *wanted,
                                size_t nwanted, size_t center, size_t **out, size_t *count);

/** A row of an outline tree (Sidebar.rows, Sidebar.initialOpen). */
typedef struct {
    int64_t parent;       /**< the parent row, -1 for none */
    bool has_kids;        /**< it has children (a disclosure triangle) */
    bool open;            /**< it starts expanded */
} safepdf_tree_row;

/** The tree of `n` entries given by their depths (each at most one more than the previous
    row's) and whether each starts open; `out` is caller storage for `n` rows. 0 on success. */
int safepdf_sidebar_tree(const size_t *depths, const bool *open, size_t n,
                         safepdf_tree_row *out);

/** Why `name` cannot take a saved attachment (Attach.targetProblem: a folder, the opened
    document, a read-only file, a folder that is not writable); NULL when it can. malloc'd. */
char *safepdf_attachment_target_problem(const char *name, bool is_dir, bool exists,
                                        bool file_writable, bool dir_writable, bool opened);

/** The size column of an attachment after it was decoded for saving (Attach.sizeColumn with
    the outcome: its decoded size when `ok`, "error" otherwise; the listed size first).
    malloc'd. */
char *safepdf_attachment_size_after(const safepdf_attachment *a, bool ok, uint64_t decoded);

/** What an outline item's action does, in words (Links.describe with the page labels and the
    page count): the status text of an item that is not followed. malloc'd. */
char *safepdf_action_describe(const safepdf_action *a, const char *const *labels, size_t nlabels,
                              size_t pages);

/** The trusted identity line (task 12.5, Viewer.identityLine): "SafePDF is showing NAME (PATH)
    - this line is drawn by SafePDF, never by the document", with controls and bidi overrides
    blanked; `path` NULL: no document. Never the document's /Title. malloc'd. */
char *safepdf_identity_line(const char *path, bool in_memory);

/* ----------------------------------------------------------------- tests only */

/** TESTS ONLY (macos/tests/core_test.c): renders `page` IN THIS PROCESS, on the calling thread
    (blocks), with the call the worker answers safepdf_doc_render with (same zoom, extra
    rotation, default layers state, substitute fonts), so a test can compare the two byte for
    byte. Returns an image to free with safepdf_free_image, or NULL with `*error` set. */
safepdf_image *safepdf_test_render_sync(safepdf_document *doc, size_t page, uint32_t zoom_num,
                                        uint32_t zoom_den, unsigned rotation, char **error);

/* ----------------------------------------------------------------- v2: frees */

/** Free a rendered image delivered to a callback (buffer and struct). NULL is allowed. */
void safepdf_free_image(safepdf_image *image);
void safepdf_free_page_index(safepdf_page_index *index);
void safepdf_free_links(safepdf_link_list *links);
void safepdf_free_outline(safepdf_outline *outline);
void safepdf_free_labels(safepdf_label_list *labels);
void safepdf_free_attachments(safepdf_attachment_list *attachments);
void safepdf_free_bytes(safepdf_bytes *bytes);
void safepdf_free_layers(safepdf_layers *layers);
/** Free the arrays of a layers state in caller storage and zero it. NULL is allowed. */
void safepdf_free_layers_state(safepdf_layers_state *state);

#ifdef __cplusplus
}
#endif

#endif /* SAFEPDF_CORE_H */
