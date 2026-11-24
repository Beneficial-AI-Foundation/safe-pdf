/*
 * safepdf_select.c — the C API of safepdf_select.h over the Lean exports of
 * SafePdf/Shell/FfiSelect.lean (task 11.3a4).
 *
 * Reference counting (as safepdf_marks.c): Lean v4.36 `@[export]` functions take every object
 * argument as OWNED, so the page's handle gets a lean_inc before each call that passes it;
 * every object a Lean function returns is owned here and released with lean_dec once its
 * contents are copied out. The handle (a Select.PageIndex) is immutable and marked
 * thread-shared (lean_mark_mt), so any thread may query it concurrently.
 *
 * Numbers cross as FloatArrays (FfiSelect.lean documents each layout); counts and indices are
 * exact doubles (below 2^53). Result shapes: `Except ε α` is constructor 0 `error e` / 1
 * `ok a`; `α × β` is constructor 0 with two fields; `Option α` is box(0) / constructor 1.
 */
#include "safepdf_select.h"

#include <lean/lean.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

extern lean_object *initialize_safe_x2dpdf_SafePdf_Shell_FfiSelect(uint8_t builtin);

/* Lean exports (SafePdf/Shell/FfiSelect.lean). */
extern lean_object *safepdf_select_lean_page_new(lean_object *nums, lean_object *strs,
                                                 size_t n_cells, size_t n_lines);
extern size_t safepdf_select_lean_cell_count(lean_object *h);
extern size_t safepdf_select_lean_nearest(lean_object *h, double x, double y);
extern lean_object *safepdf_select_lean_drag(lean_object *h, double x0, double y0, double x1,
                                             double y1);
extern lean_object *safepdf_select_lean_word_at(lean_object *h, size_t i);
extern lean_object *safepdf_select_lean_line_at(lean_object *h, size_t i);
extern lean_object *safepdf_select_lean_bands(lean_object *h, size_t a, size_t b);
extern lean_object *safepdf_select_lean_range_boxes(lean_object *h, size_t a, size_t b);
extern lean_object *safepdf_select_lean_copy(lean_object *h, size_t a, size_t b);
extern lean_object *safepdf_select_lean_norm_query(lean_object *q);
extern size_t safepdf_select_lean_count(lean_object *h, lean_object *q);
extern lean_object *safepdf_select_lean_find(lean_object *h, lean_object *q);
extern lean_object *safepdf_select_lean_find_doc(lean_object *hs, lean_object *q);
extern lean_object *safepdf_select_lean_next_hit(lean_object *counts, size_t page, size_t cur,
                                                 uint8_t forward);

struct safepdf_select_page {
    atomic_size_t refs;
    lean_object *handle; /* SafePdf.Shell.App.Select.PageIndex, one reference owned, MT */
};

/* ---- Helpers --------------------------------------------------------------------------- */

static int select_initialised = 0;

int safepdf_select_init(void) {
    if (select_initialised) return 0;
    if (safepdf_init() != 0) return -1;
    lean_object *res = initialize_safe_x2dpdf_SafePdf_Shell_FfiSelect(1 /* builtin */);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec(res);
        return -1;
    }
    lean_dec(res);
    select_initialised = 1;
    return 0;
}

static void set_error(char **error, const char *msg) {
    if (error) *error = strdup(msg);
}

/* A malloc'd copy of a borrowed Lean string (all its bytes). */
static char *dup_lean_string(lean_object *s) {
    size_t n = lean_string_size(s) - 1;
    char *out = malloc(n + 1);
    if (!out) return NULL;
    memcpy(out, lean_string_cstr(s), n);
    out[n] = 0;
    return out;
}

/* The page's handle with one more reference, for a call that consumes it. */
static lean_object *h_arg(const safepdf_select_page *p) {
    lean_inc(p->handle);
    return p->handle;
}

static lean_object *mk_floats(size_t n) {
    return lean_alloc_sarray(sizeof(double), n, n);
}

static size_t fsize(lean_object *a) { return lean_sarray_size(a); }

/* Number i of a FloatArray as a size_t (0 past the end or when negative). */
static size_t fnat(lean_object *a, size_t i) {
    if (i >= fsize(a)) return 0;
    double d = lean_float_array_cptr(a)[i];
    return d > 0 ? (size_t)d : 0;
}

static double fval(lean_object *a, size_t i) {
    return i < fsize(a) ? lean_float_array_cptr(a)[i] : 0.0;
}

static safepdf_box box_at(lean_object *a, size_t i) {
    safepdf_box b = { fval(a, i), fval(a, i + 1), fval(a, i + 2), fval(a, i + 3) };
    return b;
}

/* A box list from an owned FloatArray of 4 numbers per box (released). */
static safepdf_select_box_list *take_boxes(lean_object *a) {
    safepdf_select_box_list *l = calloc(1, sizeof *l);
    size_t n = fsize(a) / 4;
    if (l && n) {
        l->boxes = malloc(n * sizeof *l->boxes);
        if (!l->boxes) { free(l); l = NULL; }
        else {
            for (size_t i = 0; i < n; i++) l->boxes[i] = box_at(a, 4 * i);
            l->count = n;
        }
    }
    lean_dec(a);
    return l;
}

/* A range from an owned FloatArray [first, last] (released). */
static safepdf_select_range take_range(lean_object *a) {
    safepdf_select_range r = { fnat(a, 0), fnat(a, 1) };
    lean_dec(a);
    return r;
}

/* ---- The page handle ------------------------------------------------------------------- */

safepdf_select_page *safepdf_select_page_new(const safepdf_page_index *x, char **error) {
    if (!select_initialised) { set_error(error, "safepdf_select_init was not called"); return NULL; }
    if (!x || (x->cell_count && !x->cells) || (x->line_count && !x->line_dirs)) {
        set_error(error, "no page index");
        return NULL;
    }
    safepdf_thread_enter();
    size_t n = x->cell_count, m = x->line_count;
    lean_object *nums = mk_floats(6 * n + m);
    double *d = lean_float_array_cptr(nums);
    lean_object *strs = lean_alloc_array(2 * n, 2 * n);
    for (size_t i = 0; i < n; i++) {
        const safepdf_cell *c = &x->cells[i];
        d[6 * i] = c->box.llx;
        d[6 * i + 1] = c->box.lly;
        d[6 * i + 2] = c->box.urx;
        d[6 * i + 3] = c->box.ury;
        d[6 * i + 4] = (double)c->line;
        d[6 * i + 5] = c->hidden ? 1.0 : 0.0;
        lean_array_cptr(strs)[2 * i] = lean_mk_string(c->text ? c->text : "");
        lean_array_cptr(strs)[2 * i + 1] = lean_mk_string(c->sep ? c->sep : "");
    }
    for (size_t j = 0; j < m; j++) d[6 * n + j] = (double)x->line_dirs[j];
    lean_object *r = safepdf_select_lean_page_new(nums, strs, n, m);
    if (lean_obj_tag(r) == 0) {
        char *msg = dup_lean_string(lean_ctor_get(r, 0));
        set_error(error, msg ? msg : "out of memory");
        free(msg);
        lean_dec(r);
        return NULL;
    }
    lean_object *h = lean_ctor_get(r, 0);
    lean_inc(h);
    lean_dec(r);
    safepdf_select_page *p = calloc(1, sizeof *p);
    if (!p) { lean_dec(h); set_error(error, "out of memory"); return NULL; }
    lean_mark_mt(h);
    atomic_init(&p->refs, 1);
    p->handle = h;
    return p;
}

safepdf_select_page *safepdf_select_page_retain(safepdf_select_page *p) {
    if (p) atomic_fetch_add(&p->refs, 1);
    return p;
}

void safepdf_select_page_release(safepdf_select_page *p) {
    if (!p) return;
    if (atomic_fetch_sub(&p->refs, 1) != 1) return;
    safepdf_thread_enter();
    lean_dec(p->handle);
    free(p);
}

size_t safepdf_select_cell_count(const safepdf_select_page *p) {
    if (!p) return 0;
    safepdf_thread_enter();
    return safepdf_select_lean_cell_count(h_arg(p));
}

/* ---- Pointer --------------------------------------------------------------------------- */

int safepdf_select_nearest(const safepdf_select_page *p, double x, double y, size_t *cell) {
    if (!p) return -1;
    safepdf_thread_enter();
    size_t r = safepdf_select_lean_nearest(h_arg(p), x, y);
    if (r == 0) return -1;
    if (cell) *cell = r - 1;
    return 0;
}

int safepdf_select_drag(const safepdf_select_page *p, double x0, double y0, double x1,
                        double y1, safepdf_select_range *out) {
    if (!p) return -1;
    safepdf_thread_enter();
    lean_object *a = safepdf_select_lean_drag(h_arg(p), x0, y0, x1, y1);
    int found = fval(a, 0) != 0;
    safepdf_select_range r = { fnat(a, 1), fnat(a, 2) };
    lean_dec(a);
    if (!found) return -1;
    if (out) *out = r;
    return 0;
}

safepdf_select_range safepdf_select_word_at(const safepdf_select_page *p, size_t cell) {
    if (!p) { safepdf_select_range r = { cell, cell }; return r; }
    safepdf_thread_enter();
    return take_range(safepdf_select_lean_word_at(h_arg(p), cell));
}

safepdf_select_range safepdf_select_line_at(const safepdf_select_page *p, size_t cell) {
    if (!p) { safepdf_select_range r = { cell, cell }; return r; }
    safepdf_thread_enter();
    return take_range(safepdf_select_lean_line_at(h_arg(p), cell));
}

/* ---- Drawing and copy ------------------------------------------------------------------ */

safepdf_select_box_list *safepdf_select_bands(const safepdf_select_page *p, size_t a, size_t b) {
    if (!p) return calloc(1, sizeof(safepdf_select_box_list));
    safepdf_thread_enter();
    return take_boxes(safepdf_select_lean_bands(h_arg(p), a, b));
}

safepdf_select_box_list *safepdf_select_range_boxes(const safepdf_select_page *p, size_t a,
                                                    size_t b) {
    if (!p) return calloc(1, sizeof(safepdf_select_box_list));
    safepdf_thread_enter();
    return take_boxes(safepdf_select_lean_range_boxes(h_arg(p), a, b));
}

safepdf_select_copy_result *safepdf_select_copy(const safepdf_select_page *p, size_t a,
                                                size_t b) {
    safepdf_select_copy_result *c = calloc(1, sizeof *c);
    if (!c) return NULL;
    if (!p) {
        c->text = strdup("");
        c->status = strdup("copied 0 characters");
    } else {
        safepdf_thread_enter();
        lean_object *r = safepdf_select_lean_copy(h_arg(p), a, b);
        lean_object *strs = lean_ctor_get(r, 0), *nums = lean_ctor_get(r, 1);
        if (lean_array_size(strs) >= 2) {
            c->text = dup_lean_string(lean_array_get_core(strs, 0));
            c->status = dup_lean_string(lean_array_get_core(strs, 1));
        }
        c->chars = fnat(nums, 0);
        c->hidden_chars = fnat(nums, 1);
        lean_dec(r);
    }
    if (!c->text || !c->status) { safepdf_select_free_copy_result(c); return NULL; }
    return c;
}

/* ---- Search ---------------------------------------------------------------------------- */

char *safepdf_select_normalize_query(const char *query) {
    if (!select_initialised) return strdup("");
    safepdf_thread_enter();
    lean_object *s = safepdf_select_lean_norm_query(lean_mk_string(query ? query : ""));
    char *out = dup_lean_string(s);
    lean_dec(s);
    return out;
}

size_t safepdf_select_count(const safepdf_select_page *p, const char *query) {
    if (!p) return 0;
    safepdf_thread_enter();
    return safepdf_select_lean_count(h_arg(p), lean_mk_string(query ? query : ""));
}

/* A hit list from an owned FloatArray: count, then per hit [page if with_page], first, last,
   number of boxes, the boxes (released). NULL when out of memory or malformed. */
static safepdf_select_hit_list *take_hits(lean_object *a, int with_page) {
    safepdf_select_hit_list *l = calloc(1, sizeof *l);
    if (!l) { lean_dec(a); return NULL; }
    size_t n = fnat(a, 0), total = 0, len = fsize(a);
    /* First pass: validate the layout and count the boxes. */
    size_t pos = 1;
    for (size_t i = 0; i < n; i++) {
        size_t hdr = with_page ? 4 : 3;
        if (pos + hdr > len) goto bad;
        size_t k = fnat(a, pos + hdr - 1);
        if (k > (len - pos - hdr) / 4) goto bad;
        total += k;
        pos += hdr + 4 * k;
    }
    if (n) {
        l->hits = calloc(n, sizeof *l->hits);
        if (!l->hits) goto bad;
    }
    if (total) {
        l->boxes_ = malloc(total * sizeof *l->boxes_);
        if (!l->boxes_) goto bad;
    }
    pos = 1;
    size_t used = 0;
    for (size_t i = 0; i < n; i++) {
        safepdf_select_hit *h = &l->hits[i];
        if (with_page) h->page = fnat(a, pos++);
        h->range.first = fnat(a, pos);
        h->range.last = fnat(a, pos + 1);
        h->box_count = fnat(a, pos + 2);
        pos += 3;
        h->boxes = h->box_count ? l->boxes_ + used : NULL;
        for (size_t j = 0; j < h->box_count; j++) h->boxes[j] = box_at(a, pos + 4 * j);
        used += h->box_count;
        pos += 4 * h->box_count;
    }
    l->count = n;
    lean_dec(a);
    return l;
bad:
    lean_dec(a);
    safepdf_select_free_hit_list(l);
    return NULL;
}

safepdf_select_hit_list *safepdf_select_find(const safepdf_select_page *p, const char *query) {
    if (!p) return calloc(1, sizeof(safepdf_select_hit_list));
    safepdf_thread_enter();
    return take_hits(safepdf_select_lean_find(h_arg(p), lean_mk_string(query ? query : "")), 0);
}

safepdf_select_hit_list *safepdf_select_find_doc(const safepdf_select_page *const *pages,
                                                 size_t n, const char *query) {
    if (!select_initialised || (n && !pages)) return calloc(1, sizeof(safepdf_select_hit_list));
    safepdf_thread_enter();
    lean_object *arr = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++) {
        lean_object *o = lean_box(0);
        if (pages[i]) {
            o = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(o, 0, h_arg(pages[i]));
        }
        lean_array_cptr(arr)[i] = o;
    }
    return take_hits(safepdf_select_lean_find_doc(arr, lean_mk_string(query ? query : "")), 1);
}

int safepdf_select_next_hit(const int64_t *counts, size_t n, size_t page, int64_t current,
                            int forward, safepdf_select_step *out) {
    if (!select_initialised || !out || (n && !counts)) return -1;
    safepdf_thread_enter();
    lean_object *c = mk_floats(n);
    double *d = lean_float_array_cptr(c);
    for (size_t i = 0; i < n; i++) d[i] = counts[i] < 0 ? -1.0 : (double)counts[i];
    size_t cur = current < 0 ? 0 : (size_t)current + 1;
    lean_object *r = safepdf_select_lean_next_hit(c, page, cur, forward ? 1 : 0);
    memset(out, 0, sizeof *out);
    size_t kind = fnat(r, 0);
    out->kind = kind == 0 ? SAFEPDF_SELECT_STEP_HIT
              : kind == 1 ? SAFEPDF_SELECT_STEP_NEED : SAFEPDF_SELECT_STEP_NONE;
    out->page = fnat(r, 1);
    out->index = fnat(r, 2);
    out->count = fnat(r, 3);
    out->wrapped = fval(r, 4) != 0;
    lean_dec(r);
    return 0;
}

/* ---- Frees ----------------------------------------------------------------------------- */

void safepdf_select_free_box_list(safepdf_select_box_list *l) {
    if (!l) return;
    free(l->boxes);
    free(l);
}

void safepdf_select_free_copy_result(safepdf_select_copy_result *c) {
    if (!c) return;
    free(c->text);
    free(c->status);
    free(c);
}

void safepdf_select_free_hit_list(safepdf_select_hit_list *l) {
    if (!l) return;
    free(l->hits);
    free(l->boxes_);
    free(l);
}
