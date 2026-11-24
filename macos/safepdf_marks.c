/*
 * safepdf_marks.c — the C API of safepdf_marks.h over the Lean exports of
 * SafePdf/Shell/FfiMarks.lean (task 11.3a3).
 *
 * Reference counting (as safepdf_core.c): Lean v4.36 `@[export]` functions take every object
 * argument as OWNED, so the store's handle gets a lean_inc before each call that passes it;
 * every object a Lean function returns is owned here and released with lean_dec once its
 * contents are copied out. Lean values are immutable: an edit returns a new handle, which
 * replaces the old one under the store's mutex.
 *
 * Result shapes (Lean's object layout): `Except ε α` is constructor 0 `error e` / 1 `ok a`
 * with one field; `α × β` is constructor 0 with two fields; scalars inside them (USize, small
 * Nat) are boxed; FloatArray / ByteArray are scalar arrays.
 */
#include "safepdf_marks.h"
#include "safepdf_core.h"

#include <lean/lean.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

extern lean_object *initialize_safe_x2dpdf_SafePdf_Shell_FfiMarks(uint8_t builtin);

/* Lean exports (SafePdf/Shell/FfiMarks.lean). */
extern lean_object *safepdf_marks_lean_create(lean_object *bytes);
extern size_t safepdf_marks_lean_page_count(lean_object *h);
extern lean_object *safepdf_marks_lean_list(lean_object *h, size_t page, uint8_t all);
extern lean_object *safepdf_marks_lean_add_highlight(lean_object *h, size_t page, uint8_t color,
                                                     lean_object *quads);
extern lean_object *safepdf_marks_lean_add_note(lean_object *h, size_t page, uint8_t color,
                                                lean_object *text, uint8_t anchor,
                                                lean_object *nums);
extern lean_object *safepdf_marks_lean_add_comment(lean_object *h, size_t id, lean_object *text);
extern lean_object *safepdf_marks_lean_add_free_text(lean_object *h, size_t page,
                                                     lean_object *text, double x, double y,
                                                     uint32_t size, uint32_t rgb);
extern lean_object *safepdf_marks_lean_add_ink(lean_object *h, size_t page, lean_object *pts,
                                               uint32_t width, uint32_t opacity, uint32_t rgb);
extern lean_object *safepdf_marks_lean_add_stroke(lean_object *h, size_t id, lean_object *pts);
extern lean_object *safepdf_marks_lean_set_text(lean_object *h, size_t id, lean_object *text);
extern lean_object *safepdf_marks_lean_recolor(lean_object *h, size_t id, uint8_t color);
extern lean_object *safepdf_marks_lean_set_rgb(lean_object *h, size_t id, uint32_t rgb,
                                               uint8_t merge);
extern lean_object *safepdf_marks_lean_set_size(lean_object *h, size_t id, uint32_t n,
                                                uint8_t merge);
extern lean_object *safepdf_marks_lean_set_opacity(lean_object *h, size_t id, uint32_t o,
                                                   uint8_t merge);
extern lean_object *safepdf_marks_lean_translate(lean_object *h, size_t id, double dx, double dy,
                                                 uint8_t merge);
extern lean_object *safepdf_marks_lean_seal(lean_object *h);
extern lean_object *safepdf_marks_lean_delete(lean_object *h, size_t id);
extern lean_object *safepdf_marks_lean_undo_redo(lean_object *h, uint8_t undo);
extern lean_object *safepdf_marks_lean_state(lean_object *h);
extern size_t safepdf_marks_lean_hit_at(lean_object *h, size_t page, double x, double y);
extern uint8_t safepdf_marks_lean_note_close(lean_object *h, size_t id, lean_object *shown);
extern uint8_t safepdf_marks_lean_note_anchor(lean_object *sel, uint8_t click, double x, double y);
extern size_t safepdf_marks_lean_output_estimate(lean_object *h);
extern lean_object *safepdf_marks_lean_save_build(lean_object *h, lean_object *seed,
                                                  lean_object *date, size_t max_out);
extern uint8_t safepdf_marks_lean_disk_state(lean_object *h, lean_object *disk, uint8_t readable);
extern uint8_t safepdf_marks_lean_route(uint8_t dirty, uint8_t library, uint8_t in_memory,
                                        uint8_t confirmed);
extern lean_object *safepdf_marks_lean_overwrite_question(lean_object *h, lean_object *name);
extern lean_object *safepdf_marks_lean_changed_question(lean_object *name, uint8_t st);
extern lean_object *safepdf_marks_lean_unsaved_question(lean_object *h, lean_object *name,
                                                        lean_object *what, uint8_t library,
                                                        uint8_t in_memory, uint8_t into);
extern lean_object *safepdf_marks_lean_write_problem(lean_object *name, uint8_t fw, uint8_t dw);
extern lean_object *safepdf_marks_lean_target_problem(lean_object *name, uint8_t is_dir,
                                                      uint8_t exists, uint8_t fw, uint8_t dw,
                                                      uint8_t opened);
extern lean_object *safepdf_marks_lean_default_target(lean_object *path);
extern lean_object *safepdf_marks_lean_with_ext(lean_object *name, lean_object *ext);
extern size_t safepdf_marks_lean_xfdf_estimate(lean_object *h);
extern lean_object *safepdf_marks_lean_xfdf_export(lean_object *h, lean_object *href,
                                                   lean_object *date, size_t max_out);
extern lean_object *safepdf_marks_lean_xfdf_import(lean_object *h, lean_object *bytes);
extern lean_object *safepdf_marks_lean_error_text(lean_object *e);
extern lean_object *safepdf_marks_lean_tool_params(uint8_t u);
extern lean_object *safepdf_marks_lean_ui_step(lean_object *ui, uint8_t op, uint8_t arg);
extern uint8_t safepdf_marks_lean_bubble_kind(uint8_t sel, uint8_t mark, uint8_t show_all);
extern lean_object *safepdf_marks_lean_bubble_layout(uint8_t kind);
extern lean_object *safepdf_marks_lean_bubble_place(lean_object *sel, double w, double h,
                                                    lean_object *area);
extern uint32_t safepdf_marks_lean_escape_closes(uint32_t opened);
extern lean_object *safepdf_marks_lean_preview(lean_object *h, lean_object *date);
extern size_t safepdf_marks_lean_output_ceiling(uint8_t u);
extern lean_object *safepdf_marks_lean_saved_status(lean_object *path, size_t marks, size_t appended,
                                                    size_t total, size_t deleted, lean_object *notes);
extern lean_object *safepdf_marks_lean_import_status(lean_object *name, size_t added, size_t dups,
                                                     size_t skipped, uint8_t has_first,
                                                     lean_object *elem, lean_object *reason);
extern lean_object *safepdf_marks_lean_xfdf_target(lean_object *path);
extern lean_object *safepdf_marks_lean_replace_question(lean_object *name);
extern lean_object *safepdf_marks_lean_opened_overwrite_question(lean_object *name);
extern lean_object *safepdf_marks_lean_dialog_buttons(uint8_t kind, uint8_t aqua);
extern uint8_t safepdf_marks_lean_unsaved_answer(lean_object *key);
extern uint8_t safepdf_marks_lean_close_goes_on(uint8_t dirty, uint8_t answer, uint8_t saved);
extern lean_object *safepdf_marks_lean_dialog_dir(lean_object *dir, uint8_t usable, lean_object *home);
extern lean_object *safepdf_marks_lean_one_line(lean_object *s);
extern lean_object *safepdf_marks_lean_tmp_name(lean_object *base, uint64_t stamp);

struct safepdf_marks {
    atomic_size_t refs;
    pthread_mutex_t lock;
    lean_object *handle; /* SafePdf.Shell.FfiMarks.Handle, one reference owned */
};

/* ---- Helpers --------------------------------------------------------------------------- */

static int marks_initialised = 0;

int safepdf_marks_init(void) {
    if (marks_initialised) return 0;
    if (safepdf_init() != 0) return -1;
    lean_object *res = initialize_safe_x2dpdf_SafePdf_Shell_FfiMarks(1 /* builtin */);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec(res);
        return -1;
    }
    lean_dec(res);
    marks_initialised = 1;
    return 0;
}

static void set_error(char **error, char *msg) {
    if (error) *error = msg; else free(msg);
}

static char *dup_lean_string(lean_object *s) { /* borrowed */
    size_t n = lean_string_size(s) - 1;
    char *out = malloc(n + 1);
    if (!out) return NULL;
    memcpy(out, lean_string_cstr(s), n);
    out[n] = 0;
    return out;
}

/* Copy and release an owned Lean string. */
static char *take_string(lean_object *s) {
    char *out = dup_lean_string(s);
    lean_dec(s);
    return out;
}

/* An owned Lean string, empty -> NULL. */
static char *take_optional(lean_object *s) {
    if (lean_string_size(s) <= 1) { lean_dec(s); return NULL; }
    return take_string(s);
}

static lean_object *mk_str(const char *s) { return lean_mk_string(s ? s : ""); }

static lean_object *mk_bytes(const uint8_t *p, size_t n) {
    lean_object *a = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(a), p, n);
    return a;
}

static lean_object *mk_floats(const double *p, size_t n) {
    lean_object *a = lean_alloc_sarray(sizeof(double), n, n);
    if (n) memcpy(lean_float_array_cptr(a), p, n * sizeof(double));
    return a;
}

static lean_object *mk_boxes(const safepdf_box *b, size_t n) {
    lean_object *a = lean_alloc_sarray(sizeof(double), 4 * n, 4 * n);
    double *d = lean_float_array_cptr(a);
    for (size_t i = 0; i < n; i++) {
        d[4 * i] = b[i].llx; d[4 * i + 1] = b[i].lly;
        d[4 * i + 2] = b[i].urx; d[4 * i + 3] = b[i].ury;
    }
    return a;
}

static lean_object *mk_points(const safepdf_point *p, size_t n) {
    lean_object *a = lean_alloc_sarray(sizeof(double), 2 * n, 2 * n);
    double *d = lean_float_array_cptr(a);
    for (size_t i = 0; i < n; i++) { d[2 * i] = p[i].x; d[2 * i + 1] = p[i].y; }
    return a;
}

/* A palette index as the Lean side's UInt8 (out of range: 255, which Lean refuses). */
static uint8_t color_code(int c) { return (c >= 0 && c <= 4) ? (uint8_t)c : 255; }

static void lock(safepdf_marks *m) { pthread_mutex_lock(&m->lock); }
static void unlock(safepdf_marks *m) { pthread_mutex_unlock(&m->lock); }

/* The handle with one more reference, for a call that consumes it (lock held). */
static lean_object *h_arg(safepdf_marks *m) { lean_inc(m->handle); return m->handle; }

/* Apply an `Except String (Handle × USize)` result (owned) to the store (lock held). */
static int apply_edit(safepdf_marks *m, lean_object *r, uint64_t *id, char **error) {
    if (lean_obj_tag(r) == 0) {
        set_error(error, dup_lean_string(lean_ctor_get(r, 0)));
        lean_dec(r);
        return -1;
    }
    lean_object *pair = lean_ctor_get(r, 0);
    lean_object *h = lean_ctor_get(pair, 0);
    size_t nid = lean_unbox_usize(lean_ctor_get(pair, 1));
    lean_inc(h);
    lean_dec(r);
    lean_dec(m->handle);
    m->handle = h;
    if (id) *id = nid;
    return 0;
}

/* ---- Lifetime -------------------------------------------------------------------------- */

safepdf_marks *safepdf_marks_create(const uint8_t *bytes, size_t len, char **error) {
    lean_object *r = safepdf_marks_lean_create(mk_bytes(bytes, len));
    if (lean_obj_tag(r) == 0) {
        set_error(error, dup_lean_string(lean_ctor_get(r, 0)));
        lean_dec(r);
        return NULL;
    }
    lean_object *h = lean_ctor_get(r, 0);
    lean_inc(h);
    lean_dec(r);
    safepdf_marks *m = calloc(1, sizeof *m);
    if (!m) { lean_dec(h); set_error(error, strdup("out of memory")); return NULL; }
    atomic_init(&m->refs, 1);
    pthread_mutex_init(&m->lock, NULL);
    m->handle = h;
    return m;
}

safepdf_marks *safepdf_marks_retain(safepdf_marks *m) {
    if (m) atomic_fetch_add(&m->refs, 1);
    return m;
}

void safepdf_marks_release(safepdf_marks *m) {
    if (!m) return;
    if (atomic_fetch_sub(&m->refs, 1) != 1) return;
    lean_dec(m->handle);
    pthread_mutex_destroy(&m->lock);
    free(m);
}

/* ---- Queries --------------------------------------------------------------------------- */

void safepdf_marks_get_state(safepdf_marks *m, safepdf_marks_state *out) {
    memset(out, 0, sizeof *out);
    lock(m);
    lean_object *a = safepdf_marks_lean_state(h_arg(m));
    unlock(m);
    double *d = lean_float_array_cptr(a);
    if (lean_sarray_size(a) >= 12) {
        out->can_undo = d[0] != 0; out->can_redo = d[1] != 0; out->dirty = d[2] != 0;
        out->pending = (size_t)d[3]; out->new_count = (size_t)d[4];
        out->changed_count = (size_t)d[5]; out->deleted_saved_count = (size_t)d[6];
        out->undo_depth = (size_t)d[7]; out->redo_depth = (size_t)d[8];
        out->encrypted = d[9] != 0; out->page_count = (size_t)d[10];
        out->mark_count = (size_t)d[11];
    }
    lean_dec(a);
}

void safepdf_free_mark_list(safepdf_mark_list *list) {
    if (!list) return;
    for (size_t i = 0; i < list->count; i++) {
        safepdf_mark *k = &list->marks[i];
        free(k->text); free(k->quads); free(k->stroke_lengths); free(k->points);
    }
    free(list->marks);
    memset(list, 0, sizeof *list);
}

/* Decode the list result `(Array USize × FloatArray × Array String)` (borrowed); the layout is
   FfiMarks.markNums. */
static int decode_list(lean_object *r, safepdf_mark_list *out) {
    lean_object *ids = lean_ctor_get(r, 0);
    lean_object *rest = lean_ctor_get(r, 1);
    lean_object *nums = lean_ctor_get(rest, 0);
    lean_object *texts = lean_ctor_get(rest, 1);
    size_t n = lean_array_size(ids);
    const double *d = lean_float_array_cptr(nums);
    size_t dn = lean_sarray_size(nums), at = 0;
    out->marks = calloc(n ? n : 1, sizeof(safepdf_mark));
    if (!out->marks) return -1;
    out->count = n;
#define NEXT() (at < dn ? d[at++] : 0.0)
    for (size_t i = 0; i < n; i++) {
        safepdf_mark *k = &out->marks[i];
        k->id = lean_unbox_usize(lean_array_get_core(ids, i));
        k->kind = (int)NEXT(); k->page = (size_t)NEXT(); k->color = (int)NEXT();
        k->r = (uint8_t)NEXT(); k->g = (uint8_t)NEXT(); k->b = (uint8_t)NEXT();
        k->state = (int)NEXT(); k->is_comment = NEXT() != 0;
        k->size = (uint32_t)NEXT(); k->opacity = (uint32_t)NEXT();
        k->has_point = NEXT() != 0; k->point.x = NEXT(); k->point.y = NEXT();
        k->has_rect = NEXT() != 0;
        k->rect.llx = NEXT(); k->rect.lly = NEXT(); k->rect.urx = NEXT(); k->rect.ury = NEXT();
        k->quad_count = (size_t)NEXT();
        k->quads = calloc(k->quad_count ? k->quad_count : 1, sizeof(safepdf_box));
        if (!k->quads) return -1;
        for (size_t q = 0; q < k->quad_count; q++) {
            k->quads[q].llx = NEXT(); k->quads[q].lly = NEXT();
            k->quads[q].urx = NEXT(); k->quads[q].ury = NEXT();
        }
        k->stroke_count = (size_t)NEXT();
        k->stroke_lengths = calloc(k->stroke_count ? k->stroke_count : 1, sizeof(size_t));
        if (!k->stroke_lengths) return -1;
        size_t pts = 0;
        for (size_t s = 0; s < k->stroke_count; s++) {
            k->stroke_lengths[s] = (size_t)NEXT();
            pts += k->stroke_lengths[s];
        }
        k->point_count = pts;
        k->points = calloc(pts ? pts : 1, sizeof(safepdf_point));
        if (!k->points) return -1;
        for (size_t p = 0; p < pts; p++) { k->points[p].x = NEXT(); k->points[p].y = NEXT(); }
        lean_object *t = lean_array_get_core(texts, i);
        k->text_len = lean_string_size(t) - 1;
        k->text = dup_lean_string(t);
        if (!k->text) return -1;
    }
#undef NEXT
    return 0;
}

static int list_impl(safepdf_marks *m, size_t page, uint8_t all, safepdf_mark_list *out,
                     char **error) {
    memset(out, 0, sizeof *out);
    lock(m);
    lean_object *r = safepdf_marks_lean_list(h_arg(m), page, all);
    unlock(m);
    int rc = decode_list(r, out);
    lean_dec(r);
    if (rc != 0) {
        safepdf_free_mark_list(out);
        set_error(error, strdup("out of memory"));
    }
    return rc;
}

int safepdf_marks_list(safepdf_marks *m, size_t page, safepdf_mark_list *out, char **error) {
    return list_impl(m, page, 0, out, error);
}

int safepdf_marks_list_all(safepdf_marks *m, safepdf_mark_list *out, char **error) {
    return list_impl(m, 0, 1, out, error);
}

uint64_t safepdf_marks_hit_at(safepdf_marks *m, size_t page, double x, double y) {
    lock(m);
    size_t id = safepdf_marks_lean_hit_at(h_arg(m), page, x, y);
    unlock(m);
    return id;
}

int safepdf_marks_note_anchor(const safepdf_box *sel, size_t sel_count,
                              const safepdf_point *click) {
    uint8_t r = safepdf_marks_lean_note_anchor(mk_boxes(sel, sel_count), click != NULL,
                                               click ? click->x : 0, click ? click->y : 0);
    return r == 255 ? -1 : r;
}

int safepdf_marks_note_close(safepdf_marks *m, uint64_t id, const char *shown) {
    lock(m);
    uint8_t r = safepdf_marks_lean_note_close(h_arg(m), id, mk_str(shown));
    unlock(m);
    return r;
}

/* ---- Edits ----------------------------------------------------------------------------- */

/* Run an edit export `call` (an expression using `h`, the consumed handle) under the lock. */
#define EDIT(m, id, error, call)                                     \
    do {                                                             \
        lock(m);                                                     \
        lean_object *h = h_arg(m);                                   \
        int rc_ = apply_edit((m), (call), (id), (error));            \
        unlock(m);                                                   \
        return rc_;                                                  \
    } while (0)

int safepdf_marks_add_highlight(safepdf_marks *m, size_t page, int color, const safepdf_box *quads,
                                size_t quad_count, uint64_t *id, char **error) {
    EDIT(m, id, error, safepdf_marks_lean_add_highlight(h, page, color_code(color),
                                                        mk_boxes(quads, quad_count)));
}

int safepdf_marks_add_note(safepdf_marks *m, size_t page, int color, const char *text, int anchor,
                           const safepdf_point *point, const safepdf_box *quads, size_t quad_count,
                           uint64_t *id, char **error) {
    lean_object *nums;
    uint8_t kind;
    if (anchor == SAFEPDF_ANCHOR_POINT && point) { kind = 0; nums = mk_points(point, 1); }
    else if (anchor == SAFEPDF_ANCHOR_QUADS) { kind = 1; nums = mk_boxes(quads, quad_count); }
    else { kind = 2; nums = mk_floats(NULL, 0); }
    EDIT(m, id, error, safepdf_marks_lean_add_note(h, page, color_code(color), mk_str(text), kind,
                                                   nums));
}

int safepdf_marks_add_comment(safepdf_marks *m, uint64_t highlight, const char *text, uint64_t *id,
                              char **error) {
    EDIT(m, id, error, safepdf_marks_lean_add_comment(h, highlight, mk_str(text)));
}

int safepdf_marks_add_free_text(safepdf_marks *m, size_t page, const char *text, double x, double y,
                                uint32_t size, uint32_t rgb, uint64_t *id, char **error) {
    EDIT(m, id, error, safepdf_marks_lean_add_free_text(h, page, mk_str(text), x, y, size, rgb));
}

int safepdf_marks_add_ink(safepdf_marks *m, size_t page, const safepdf_point *points, size_t count,
                          uint32_t width, uint32_t opacity, uint32_t rgb, uint64_t *id,
                          char **error) {
    EDIT(m, id, error, safepdf_marks_lean_add_ink(h, page, mk_points(points, count), width,
                                                  opacity, rgb));
}

int safepdf_marks_add_stroke(safepdf_marks *m, uint64_t id, const safepdf_point *points,
                             size_t count, char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_add_stroke(h, id, mk_points(points, count)));
}

int safepdf_marks_set_text(safepdf_marks *m, uint64_t id, const char *text, char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_set_text(h, id, mk_str(text)));
}

int safepdf_marks_recolor(safepdf_marks *m, uint64_t id, int color, char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_recolor(h, id, color_code(color)));
}

int safepdf_marks_set_rgb(safepdf_marks *m, uint64_t id, uint32_t rgb, int merge, char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_set_rgb(h, id, rgb, merge != 0));
}

int safepdf_marks_set_size(safepdf_marks *m, uint64_t id, uint32_t size, int merge, char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_set_size(h, id, size, merge != 0));
}

int safepdf_marks_set_opacity(safepdf_marks *m, uint64_t id, uint32_t opacity, int merge,
                              char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_set_opacity(h, id, opacity, merge != 0));
}

int safepdf_marks_translate(safepdf_marks *m, uint64_t id, double dx, double dy, int merge,
                            char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_translate(h, id, dx, dy, merge != 0));
}

void safepdf_marks_seal(safepdf_marks *m) {
    lock(m);
    lean_object *h = safepdf_marks_lean_seal(h_arg(m));
    lean_dec(m->handle);
    m->handle = h;
    unlock(m);
}

int safepdf_marks_delete(safepdf_marks *m, uint64_t id, char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_delete(h, id));
}

int safepdf_marks_undo(safepdf_marks *m, char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_undo_redo(h, 1));
}

int safepdf_marks_redo(safepdf_marks *m, char **error) {
    EDIT(m, NULL, error, safepdf_marks_lean_undo_redo(h, 0));
}

/* ---- Save ------------------------------------------------------------------------------ */

size_t safepdf_marks_output_estimate(safepdf_marks *m) {
    lock(m);
    size_t n = safepdf_marks_lean_output_estimate(h_arg(m));
    unlock(m);
    return n;
}

/* The text of the error of IO result `r` (borrowed), malloc'd. */
static char *io_error_of(lean_object *r) {
    lean_object *e = lean_io_result_get_error(r);
    lean_inc(e);
    return take_string(safepdf_marks_lean_error_text(e));
}

void safepdf_free_save_result(safepdf_save_result *r) {
    if (!r) return;
    free(r->bytes);
    for (size_t i = 0; i < r->note_count; i++) free(r->notes[i]);
    free(r->notes);
    memset(r, 0, sizeof *r);
}

int safepdf_marks_save_build(safepdf_marks *m, const uint8_t *iv_seed, size_t seed_len,
                             const char *date, size_t max_output, safepdf_save_result *out,
                             char **error) {
    memset(out, 0, sizeof *out);
    lock(m);
    lean_object *io = safepdf_marks_lean_save_build(h_arg(m), mk_bytes(iv_seed, iv_seed ? seed_len : 0),
                                                    mk_str(date), max_output);
    unlock(m);
    if (!lean_io_result_is_ok(io)) {
        set_error(error, io_error_of(io));
        lean_dec(io);
        return SAFEPDF_SAVE_ERR_BUILD;
    }
    lean_object *r = lean_io_result_get_value(io);
    if (lean_obj_tag(r) == 0) {
        lean_object *err = lean_ctor_get(r, 0);
        lean_object *code = lean_ctor_get(err, 0);
        int c = lean_is_scalar(code) ? (int)lean_unbox(code) : SAFEPDF_SAVE_ERR_BUILD;
        set_error(error, dup_lean_string(lean_ctor_get(err, 1)));
        lean_dec(io);
        return c;
    }
    lean_object *v = lean_ctor_get(r, 0);
    lean_object *bytes = lean_ctor_get(v, 0);
    lean_object *rest = lean_ctor_get(v, 1);
    lean_object *nums = lean_ctor_get(rest, 0);
    lean_object *notes = lean_ctor_get(rest, 1);
    size_t n = lean_sarray_size(bytes);
    size_t nn = lean_array_size(notes);
    out->bytes = malloc(n ? n : 1);
    out->notes = calloc(nn ? nn : 1, sizeof(char *));
    if (!out->bytes || !out->notes) goto oom;
    memcpy(out->bytes, lean_sarray_cptr(bytes), n);
    out->size = n;
    const double *d = lean_float_array_cptr(nums);
    if (lean_sarray_size(nums) >= 5) {
        out->marks_written = (size_t)d[0]; out->marks_total = (size_t)d[1];
        out->appended = (size_t)d[2]; out->flags = (uint32_t)d[3];
        out->deleted_saved = (size_t)d[4];
    }
    for (size_t i = 0; i < nn; i++) {
        out->notes[i] = dup_lean_string(lean_array_get_core(notes, i));
        if (!out->notes[i]) goto oom;
        out->note_count = i + 1;
    }
    lean_dec(io);
    return SAFEPDF_SAVE_OK;
oom:
    lean_dec(io);
    safepdf_free_save_result(out);
    set_error(error, strdup("out of memory"));
    return SAFEPDF_SAVE_ERR_NO_MEMORY;
}

int safepdf_marks_disk_state(safepdf_marks *m, const uint8_t *disk, size_t len) {
    lock(m);
    uint8_t r = safepdf_marks_lean_disk_state(h_arg(m), mk_bytes(disk, disk ? len : 0),
                                              disk != NULL);
    unlock(m);
    return r;
}

int safepdf_marks_save_route(int dirty, int library, int in_memory, int confirmed) {
    return safepdf_marks_lean_route(dirty != 0, library != 0, in_memory != 0, confirmed != 0);
}

char *safepdf_marks_overwrite_question(safepdf_marks *m, const char *name) {
    lock(m);
    lean_object *s = safepdf_marks_lean_overwrite_question(h_arg(m), mk_str(name));
    unlock(m);
    return take_string(s);
}

char *safepdf_marks_changed_question(const char *name, int disk_state) {
    return take_string(safepdf_marks_lean_changed_question(mk_str(name),
                                                           disk_state == SAFEPDF_DISK_MISSING ? 2 : 1));
}

char *safepdf_marks_unsaved_question(safepdf_marks *m, const char *name, const char *what,
                                     int library, int in_memory, int into) {
    lock(m);
    lean_object *s = safepdf_marks_lean_unsaved_question(h_arg(m), mk_str(name), mk_str(what),
                                                         library != 0, in_memory != 0, into != 0);
    unlock(m);
    return take_string(s);
}

char *safepdf_marks_write_problem(const char *name, int file_writable, int dir_writable) {
    return take_optional(safepdf_marks_lean_write_problem(mk_str(name), file_writable != 0,
                                                          dir_writable != 0));
}

char *safepdf_marks_target_problem(const char *name, int is_dir, int exists, int file_writable,
                                   int dir_writable, int is_opened_document) {
    return take_optional(safepdf_marks_lean_target_problem(mk_str(name), is_dir != 0, exists != 0,
                                                           file_writable != 0, dir_writable != 0,
                                                           is_opened_document != 0));
}

char *safepdf_marks_default_target(const char *path) {
    return take_string(safepdf_marks_lean_default_target(mk_str(path)));
}

char *safepdf_marks_with_ext(const char *name, const char *ext) {
    return take_string(safepdf_marks_lean_with_ext(mk_str(name), mk_str(ext)));
}

/* ---- XFDF ------------------------------------------------------------------------------ */

size_t safepdf_marks_xfdf_estimate(safepdf_marks *m) {
    lock(m);
    size_t n = safepdf_marks_lean_xfdf_estimate(h_arg(m));
    unlock(m);
    return n;
}

void safepdf_free_marks_bytes(safepdf_marks_bytes *b) {
    if (!b) return;
    free(b->data);
    memset(b, 0, sizeof *b);
}

int safepdf_marks_xfdf_export(safepdf_marks *m, const char *href, const char *date,
                              size_t max_output, safepdf_marks_bytes *out, char **error) {
    memset(out, 0, sizeof *out);
    lock(m);
    lean_object *io = safepdf_marks_lean_xfdf_export(h_arg(m), mk_str(href), mk_str(date),
                                                     max_output);
    unlock(m);
    if (!lean_io_result_is_ok(io)) {
        set_error(error, io_error_of(io));
        lean_dec(io);
        return -1;
    }
    lean_object *r = lean_io_result_get_value(io);
    if (lean_obj_tag(r) == 0) {
        set_error(error, dup_lean_string(lean_ctor_get(r, 0)));
        lean_dec(io);
        return -1;
    }
    lean_object *bytes = lean_ctor_get(r, 0);
    size_t n = lean_sarray_size(bytes);
    out->data = malloc(n ? n : 1);
    if (!out->data) { lean_dec(io); set_error(error, strdup("out of memory")); return -1; }
    memcpy(out->data, lean_sarray_cptr(bytes), n);
    out->size = n;
    lean_dec(io);
    return 0;
}

void safepdf_free_xfdf_import(safepdf_xfdf_import *r) {
    if (!r) return;
    for (size_t i = 0; i < r->skip_count; i++) {
        free(r->skip_elements[i]);
        free(r->skip_reasons[i]);
    }
    free(r->skip_elements);
    free(r->skip_reasons);
    memset(r, 0, sizeof *r);
}

int safepdf_marks_xfdf_import(safepdf_marks *m, const uint8_t *bytes, size_t len,
                              safepdf_xfdf_import *out, char **error) {
    memset(out, 0, sizeof *out);
    lock(m);
    lean_object *r = safepdf_marks_lean_xfdf_import(h_arg(m), mk_bytes(bytes, bytes ? len : 0));
    if (lean_obj_tag(r) == 0) {
        unlock(m);
        set_error(error, dup_lean_string(lean_ctor_get(r, 0)));
        lean_dec(r);
        return -1;
    }
    lean_object *v = lean_ctor_get(r, 0);
    lean_object *h = lean_ctor_get(v, 0);
    lean_inc(h);
    lean_dec(m->handle);
    m->handle = h;
    unlock(m);
    lean_object *rest = lean_ctor_get(v, 1);
    lean_object *nums = lean_ctor_get(rest, 0);
    lean_object *skips = lean_ctor_get(rest, 1);
    const double *d = lean_float_array_cptr(nums);
    if (lean_sarray_size(nums) >= 4) {
        out->added = (size_t)d[0]; out->already_present = (size_t)d[1];
        out->skipped = (size_t)d[2]; out->ignored = (size_t)d[3];
    }
    size_t k = lean_array_size(skips) / 2;
    out->skip_elements = calloc(k ? k : 1, sizeof(char *));
    out->skip_reasons = calloc(k ? k : 1, sizeof(char *));
    if (!out->skip_elements || !out->skip_reasons) goto oom;
    for (size_t i = 0; i < k; i++) {
        out->skip_elements[i] = dup_lean_string(lean_array_get_core(skips, 2 * i));
        out->skip_reasons[i] = dup_lean_string(lean_array_get_core(skips, 2 * i + 1));
        out->skip_count = i + 1;
        if (!out->skip_elements[i] || !out->skip_reasons[i]) goto oom;
    }
    lean_dec(r);
    return 0;
oom:
    /* The store is already updated (the import happened); only the report is lost. */
    lean_dec(r);
    safepdf_free_xfdf_import(out);
    set_error(error, strdup("out of memory (the marks were imported; the report was lost)"));
    return -1;
}

/* ---- Tools, bubble and pop-over parameters (task 11.3e1) ------------------------------- */

static uint32_t u32_of(double v) {
    if (!(v >= 0)) return 0;
    if (v > 4294967295.0) return UINT32_MAX;
    return (uint32_t)v;
}

int safepdf_marks_tool_params(safepdf_tool_params *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!marks_initialised) return -1;
    lean_object *a = safepdf_marks_lean_tool_params(0);
    size_t n = lean_sarray_size(a);
    double *d = lean_float_array_cptr(a);
    int rc = -1;
    if (n >= 16) {
        size_t i = 0;
        for (int c = 0; c < 5; c++)
            for (int k = 0; k < 3; k++) out->highlight_rgb[c][k] = (uint8_t)u32_of(d[i++]);
        size_t ec = (size_t)u32_of(d[i++]);
        if (ec <= 8 && n == i + 3 * ec + 12 + 2 + 3) {
            out->editor_count = ec;
            for (size_t c = 0; c < ec; c++)
                for (int k = 0; k < 3; k++) out->editor_rgb[c][k] = (uint8_t)u32_of(d[i++]);
            uint32_t *sl[12] = {&out->font_min, &out->font_max, &out->font_step, &out->font_default,
                                &out->width_min, &out->width_max, &out->width_step,
                                &out->width_default, &out->opacity_min, &out->opacity_max,
                                &out->opacity_step, &out->opacity_default};
            for (int k = 0; k < 12; k++) *sl[k] = u32_of(d[i++]);
            out->text_rgb_default = u32_of(d[i++]);
            out->ink_rgb_default = u32_of(d[i++]);
            out->ft_pad = d[i++];
            out->line_factor = d[i++];
            out->note_size = d[i++];
            rc = 0;
        }
    }
    lean_dec(a);
    if (rc != 0) memset(out, 0, sizeof *out);
    return rc;
}

int safepdf_marks_ui_step(const safepdf_tool_ui *in, int op, int arg, safepdf_tool_ui *out,
                          int *highlight) {
    if (!out || op < 0 || op > 255 || arg < 0 || arg > 255 || !marks_initialised) return -1;
    double v[12] = {0};
    if (in) {
        v[0] = in->tool != 0; v[1] = in->popover != 0; v[2] = in->show_all != 0;
        v[3] = in->picker != 0; v[4] = in->editor; v[5] = in->ed_pop != 0;
        v[6] = in->thickness; v[7] = in->ft_size; v[8] = in->ft_rgb; v[9] = in->ink_rgb;
        v[10] = in->ink_thick; v[11] = in->ink_opacity;
    }
    lean_object *a = safepdf_marks_lean_ui_step(mk_floats(v, in ? 12 : 0), (uint8_t)op,
                                                (uint8_t)arg);
    size_t n = lean_sarray_size(a);
    double *d = lean_float_array_cptr(a);
    if (n != 14) { lean_dec(a); return -1; }
    safepdf_tool_ui r;
    r.tool = d[0] != 0; r.popover = d[1] != 0; r.show_all = d[2] != 0; r.picker = d[3] != 0;
    r.editor = (int)u32_of(d[4]); r.ed_pop = d[5] != 0; r.thickness = u32_of(d[6]);
    r.ft_size = u32_of(d[7]); r.ft_rgb = u32_of(d[8]); r.ink_rgb = u32_of(d[9]);
    r.ink_thick = u32_of(d[10]); r.ink_opacity = u32_of(d[11]);
    int mode = (int)u32_of(d[12]);
    if (highlight) *highlight = d[13] != 0;
    lean_dec(a);
    *out = r;
    return mode;
}

int safepdf_marks_bubble_kind(int sel_here, int mark_here, int show_all) {
    if (!marks_initialised) return -1;
    uint8_t r = safepdf_marks_lean_bubble_kind(sel_here != 0, mark_here != 0, show_all != 0);
    return r == 255 ? -1 : r;
}

int safepdf_marks_bubble_layout(int kind, safepdf_bubble_layout *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (kind < 0 || kind > 255 || !marks_initialised) return -1;
    lean_object *r = safepdf_marks_lean_bubble_layout((uint8_t)kind);
    lean_object *nums = lean_ctor_get(r, 0), *tips = lean_ctor_get(r, 1);
    size_t n = lean_sarray_size(nums);
    double *d = lean_float_array_cptr(nums);
    size_t count = n >= 2 ? (n - 2) / 4 : 0;
    int rc = -1;
    if (n >= 2 && (n - 2) % 4 == 0 && count <= 4 && lean_array_size(tips) == count) {
        out->width = d[0];
        out->height = d[1];
        out->count = count;
        for (size_t i = 0; i < count; i++) {
            safepdf_bubble_button *b = &out->buttons[i];
            b->button = (int)u32_of(d[2 + 4 * i]);
            b->cmd = d[3 + 4 * i] < 0 ? -1 : (int)u32_of(d[3 + 4 * i]);
            b->x0 = d[4 + 4 * i];
            b->x1 = d[5 + 4 * i];
            lean_object *t = lean_array_get_core(tips, i);
            size_t len = lean_string_size(t) - 1;
            if (len >= sizeof b->tip) len = sizeof b->tip - 1;
            memcpy(b->tip, lean_string_cstr(t), len);
            b->tip[len] = 0;
        }
        rc = 0;
    }
    lean_dec(r);
    if (rc != 0) memset(out, 0, sizeof *out);
    return rc;
}

int safepdf_marks_bubble_place(const safepdf_box *sel, size_t n, double w, double h,
                               const safepdf_box *area, safepdf_box *out) {
    if (!area || !out || (!sel && n) || !marks_initialised) return -1;
    lean_object *a = safepdf_marks_lean_bubble_place(mk_boxes(sel, n), w, h, mk_boxes(area, 1));
    size_t k = lean_sarray_size(a);
    double *d = lean_float_array_cptr(a);
    int rc = 0;
    if (k == 4) {
        out->llx = d[0]; out->lly = d[1]; out->urx = d[2]; out->ury = d[3];
        rc = 1;
    }
    lean_dec(a);
    return rc;
}

uint32_t safepdf_marks_escape_closes(uint32_t opened) {
    if (!marks_initialised) return 0;
    return safepdf_marks_lean_escape_closes(opened);
}

/* ---- Preview, save texts and dialogs (task 11.3e2) ------------------------------------- */

int safepdf_marks_preview(safepdf_marks *m, const char *date, safepdf_marks_bytes *out,
                          char **error) {
    memset(out, 0, sizeof *out);
    /* A snapshot: handles are immutable, so the (long) build runs without the lock. Its objects
       are shared with the thread that edits the store meanwhile (which reads and increments the
       same document and marks), so they get atomic reference counts first (lean_mark_mt, as
       safepdf_core.c's documents), under the lock that serialises every other use. */
    lock(m);
    lean_mark_mt(m->handle);
    lean_object *h = h_arg(m);
    unlock(m);
    lean_object *io = safepdf_marks_lean_preview(h, mk_str(date));
    if (!lean_io_result_is_ok(io)) {
        set_error(error, io_error_of(io));
        lean_dec(io);
        return -1;
    }
    lean_object *r = lean_io_result_get_value(io);
    if (lean_obj_tag(r) == 0) {
        set_error(error, dup_lean_string(lean_ctor_get(r, 0)));
        lean_dec(io);
        return -1;
    }
    lean_object *bytes = lean_ctor_get(r, 0);
    size_t n = lean_sarray_size(bytes);
    if (n > 0) {
        out->data = malloc(n);
        if (!out->data) { lean_dec(io); set_error(error, strdup("out of memory")); return -1; }
        memcpy(out->data, lean_sarray_cptr(bytes), n);
        out->size = n;
    }
    lean_dec(io);
    return 0;
}

size_t safepdf_marks_output_ceiling(void) {
    if (!marks_initialised) return 0;
    return safepdf_marks_lean_output_ceiling(0);
}

char *safepdf_marks_saved_status(const char *path, const safepdf_save_result *r) {
    if (!r || !marks_initialised) return NULL;
    /* The notes are the protection notes, then the retention text when the flag is set. */
    size_t n = r->note_count;
    if ((r->flags & SAFEPDF_SAVE_NOTE_RETENTION) && n > 0) n--;
    lean_object *notes = lean_mk_empty_array();
    for (size_t i = 0; i < n; i++) notes = lean_array_push(notes, mk_str(r->notes ? r->notes[i] : NULL));
    return take_string(safepdf_marks_lean_saved_status(mk_str(path), r->marks_written, r->appended,
                                                       r->marks_total, r->deleted_saved, notes));
}

char *safepdf_marks_import_status(const char *name, const safepdf_xfdf_import *r) {
    if (!r || !marks_initialised) return NULL;
    int first = r->skip_count > 0 && r->skip_elements && r->skip_reasons;
    return take_string(safepdf_marks_lean_import_status(
        mk_str(name), r->added, r->already_present, r->skipped, (uint8_t)first,
        mk_str(first ? r->skip_elements[0] : NULL), mk_str(first ? r->skip_reasons[0] : NULL)));
}

char *safepdf_marks_xfdf_target(const char *path) {
    if (!marks_initialised) return NULL;
    return take_string(safepdf_marks_lean_xfdf_target(mk_str(path)));
}

char *safepdf_marks_replace_question(const char *name) {
    if (!marks_initialised) return NULL;
    return take_string(safepdf_marks_lean_replace_question(mk_str(name)));
}

char *safepdf_marks_opened_overwrite_question(const char *name) {
    if (!marks_initialised) return NULL;
    return take_string(safepdf_marks_lean_opened_overwrite_question(mk_str(name)));
}

int safepdf_marks_dialog_buttons(int dialog, int aqua, safepdf_dialog_buttons *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!marks_initialised || dialog < 0 || dialog > 2) return -1;
    lean_object *a = safepdf_marks_lean_dialog_buttons((uint8_t)dialog, aqua != 0);
    size_t k = lean_array_size(a) / 2;
    if (k > 3) k = 3;
    for (size_t i = 0; i < k; i++) {
        lean_object *key = lean_array_get_core(a, 2 * i);
        lean_object *label = lean_array_get_core(a, 2 * i + 1);
        size_t kl = lean_string_size(key) - 1, ll = lean_string_size(label) - 1;
        if (kl >= sizeof out->key[i]) kl = sizeof out->key[i] - 1;
        if (ll >= sizeof out->label[i]) ll = sizeof out->label[i] - 1;
        memcpy(out->key[i], lean_string_cstr(key), kl);
        memcpy(out->label[i], lean_string_cstr(label), ll);
    }
    out->count = k;
    lean_dec(a);
    return k > 0 ? 0 : -1;
}

int safepdf_marks_unsaved_answer(const char *key) {
    if (!marks_initialised) return SAFEPDF_ANSWER_CANCEL;
    return safepdf_marks_lean_unsaved_answer(mk_str(key));
}

int safepdf_marks_close_goes_on(int dirty, int answer, int saved) {
    if (!marks_initialised) return 0;
    uint8_t a = (answer == SAFEPDF_ANSWER_SAVE || answer == SAFEPDF_ANSWER_DONT_SAVE) ? (uint8_t)answer : 0;
    return safepdf_marks_lean_close_goes_on(dirty != 0, a, saved != 0);
}

char *safepdf_marks_dialog_dir(const char *dir, int usable, const char *home) {
    if (!marks_initialised) return NULL;
    return take_string(safepdf_marks_lean_dialog_dir(mk_str(dir), usable != 0, mk_str(home)));
}

char *safepdf_marks_one_line(const char *s) {
    if (!marks_initialised) return NULL;
    return take_string(safepdf_marks_lean_one_line(mk_str(s)));
}

char *safepdf_marks_tmp_name(const char *base, uint64_t stamp) {
    if (!marks_initialised) return NULL;
    return take_string(safepdf_marks_lean_tmp_name(mk_str(base), stamp));
}
