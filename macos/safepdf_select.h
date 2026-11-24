/*
 * safepdf_select.h — C API v2: text selection, copy and search (task 11.3a4).
 *
 * The Tk viewer's selection and search (SafePdf/Shell/App/Select.lean) as pure functions over
 * a page's selection index. Implemented in safepdf_select.c over the Lean exports of
 * SafePdf/Shell/FfiSelect.lean; nothing with a theorem or a #guard is re-implemented in C
 * (docs/macos-design.md §3, decisions 1 and 2). Plain C: no Lean types leak through.
 *
 * Setup
 *   safepdf_init() (safepdf_core.h) first, then safepdf_select_init() once (idempotent).
 *
 * The page handle
 *   safepdf_select_page_new converts a safepdf_page_index (as safepdf_doc_page_index delivers
 *   it) ONCE into an immutable handle; every query below works on the handle, so the hit tests
 *   of a drag never re-marshal the cells. The index is borrowed for the call (free it when you
 *   like). Handles are reference counted (retain/release) and may be used from any thread
 *   concurrently: they are never modified.
 *
 * Cells and ranges
 *   Cells are numbered as in the index (`cells[i]`, reading order). A range is inclusive,
 *   `first <= last`; functions taking (a, b) accept either order and clamp to the cells.
 *
 * Coordinates
 *   Page space in points (y up), as in safepdf_page_index. Results are display doubles.
 *
 * Ownership
 *   Every returned struct pointer is heap-allocated and owned by the caller with all its
 *   arrays and strings: free it with its safepdf_select_free_* (NULL allowed). Returned
 *   `char *` strings are malloc'd: free() them. Input pointers are borrowed for the call.
 *
 * Threads
 *   Any thread may call (it is registered with the Lean runtime on its first call).
 */
#ifndef SAFEPDF_SELECT_H
#define SAFEPDF_SELECT_H

#include <stddef.h>
#include <stdint.h>

#include "safepdf_core.h"

#ifdef __cplusplus
extern "C" {
#endif

/** Initialise the selection module (after safepdf_init). 0 on success. Idempotent. */
int safepdf_select_init(void);

/** A page's selection handle (opaque, immutable, reference counted). */
typedef struct safepdf_select_page safepdf_select_page;

/** An inclusive cell range. */
typedef struct { size_t first, last; } safepdf_select_range;

/** Boxes (page space). */
typedef struct {
    safepdf_box *boxes;
    size_t count;
} safepdf_select_box_list;

/** What a copy puts on the clipboard (Select.rangeText) and the status line to show
    (Select.copyStatus, task 12.5: invisible text is copied, and counted). */
typedef struct {
    char *text;            /**< UTF-8, NUL-terminated */
    size_t chars;          /**< characters (Unicode scalar values) of `text` */
    size_t hidden_chars;   /**< of them, from glyphs the page does not paint (Tr 3 / Tr 7) */
    char *status;          /**< e.g. "copied 11 characters" */
} safepdf_select_copy_result;

/** A search hit: its page, its cells and its highlight boxes (one per line run). */
typedef struct {
    size_t page;           /**< safepdf_select_find: always 0; safepdf_select_find_doc: the page */
    safepdf_select_range range;
    safepdf_box *boxes;    /**< points into the list's storage */
    size_t box_count;
} safepdf_select_hit;

/** Search hits in order (page, then position on the page). */
typedef struct {
    safepdf_select_hit *hits;
    size_t count;
    safepdf_box *boxes_;   /**< internal: the boxes' storage */
} safepdf_select_hit_list;

/** Find Next / Previous: what to do next (Select.searchStep). */
typedef enum {
    SAFEPDF_SELECT_STEP_HIT = 0,   /**< show hit `index` of `count` on `page` */
    SAFEPDF_SELECT_STEP_NEED = 1,  /**< fetch the index of `page`, put its count in, step again */
    SAFEPDF_SELECT_STEP_NONE = 2   /**< no hit in the document */
} safepdf_select_step_kind;

/** A search step. */
typedef struct {
    safepdf_select_step_kind kind;
    size_t page;
    size_t index;          /**< HIT: the hit's index on `page` */
    size_t count;          /**< HIT: the hits on `page` */
    int wrapped;           /**< HIT: the search wrapped around the document */
} safepdf_select_step;

/* ---------------------------------------------------------------- the page handle */

/** The handle of a page's index (converted once). NULL on failure, `*error` set (malloc'd). */
safepdf_select_page *safepdf_select_page_new(const safepdf_page_index *index, char **error);

/** Add a reference; returns `page`. NULL is allowed. */
safepdf_select_page *safepdf_select_page_retain(safepdf_select_page *page);

/** Drop a reference; the last one frees the handle. NULL is allowed. */
void safepdf_select_page_release(safepdf_select_page *page);

/** Number of cells. */
size_t safepdf_select_cell_count(const safepdf_select_page *page);

/* ---------------------------------------------------------------- pointer */

/** Hit test (Select.nearest): the cell whose box is nearest to (x, y), the first on ties.
    0 with `*cell` set; -1 when the page has no cells or a coordinate is not finite (or beyond
    ±2^32). */
int safepdf_select_nearest(const safepdf_select_page *page, double x, double y, size_t *cell);

/** Drag from (x0, y0) to (x1, y1) (Select.dragRange). 0 with `*out` set; -1 as nearest. */
int safepdf_select_drag(const safepdf_select_page *page, double x0, double y0, double x1,
                        double y1, safepdf_select_range *out);

/** Double click on cell `cell` (Select.wordAt): its word; just the cell when its text is not
    a word character (or `cell` is out of range). */
safepdf_select_range safepdf_select_word_at(const safepdf_select_page *page, size_t cell);

/** Triple click on cell `cell` (Select.lineAt): its whole line. */
safepdf_select_range safepdf_select_line_at(const safepdf_select_page *page, size_t cell);

/* ---------------------------------------------------------------- drawing and copy */

/** The selection bands of cells a … b (Select.selBands, task 10.18): one per line in reading
    order, each covering its line's selected glyph boxes (shape_covers, bandAt_covers);
    consecutive lines of a paragraph meet (bandAt_meet). NULL only when out of memory. */
safepdf_select_box_list *safepdf_select_bands(const safepdf_select_page *page, size_t a,
                                              size_t b);

/** The highlight boxes of cells a … b (Select.rangeBoxes: one per line run; highlight quads). */
safepdf_select_box_list *safepdf_select_range_boxes(const safepdf_select_page *page, size_t a,
                                                    size_t b);

/** Copy cells a … b (the viewer's copySel). NULL only when out of memory. */
safepdf_select_copy_result *safepdf_select_copy(const safepdf_select_page *page, size_t a,
                                                size_t b);

/* ---------------------------------------------------------------- search */

/** The query as the search sees it (Select.normQuery: lower case, whitespace runs as one
    space, trimmed; "" means no search). malloc'd. */
char *safepdf_select_normalize_query(const char *query);

/** Number of hits of `query` on the page. */
size_t safepdf_select_count(const safepdf_select_page *page, const char *query);

/** The hits of `query` on the page (Select.findAll, sound by findAll_sound), with their boxes. */
safepdf_select_hit_list *safepdf_select_find(const safepdf_select_page *page, const char *query);

/** The hits of `query` on pages 0 … n-1 (highlight-all): `pages[p]` is page p's handle, NULL
    for a page whose index the caller does not have (skipped). */
safepdf_select_hit_list *safepdf_select_find_doc(const safepdf_select_page *const *pages,
                                                 size_t n, const char *query);

/** Find Next (`forward` nonzero) or Previous over `n` pages (the Tk viewer's nextHit order):
    `counts[p]` is page p's hit count (safepdf_select_count; 0 for a page without text or
    whose index failed), -1 while unknown; `current` is the current hit's index on page `page`,
    -1 for none. Writes the step to `*out`; -1 for bad arguments. */
int safepdf_select_next_hit(const int64_t *counts, size_t n, size_t page, int64_t current,
                            int forward, safepdf_select_step *out);

/* ---------------------------------------------------------------- frees */

void safepdf_select_free_box_list(safepdf_select_box_list *list);
void safepdf_select_free_copy_result(safepdf_select_copy_result *result);
void safepdf_select_free_hit_list(safepdf_select_hit_list *list);

#ifdef __cplusplus
}
#endif

#endif /* SAFEPDF_SELECT_H */
