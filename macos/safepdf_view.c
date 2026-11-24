/*
 * safepdf_view.c — the C API of safepdf_view.h over the Lean exports of
 * SafePdf/Shell/FfiView.lean (task 11.3a2).
 *
 * Internal wire format (FfiView.lean): numbers cross as a Lean ByteArray of little-endian
 * 64-bit two's complement integers; a rational is two of them (a result of 0/0 means "does
 * not fit 64 bits"); tables cross as a Lean structure {ints : ByteArray, strs : Array String}
 * with a fixed number of integers and strings per row.
 *
 * Reference counting: every Lean export consumes its object arguments (Lean v4.36 has no
 * borrowed parameters on @[export]); arguments built here are passed with their single
 * reference. Every result is owned here and released with lean_dec after copying out.
 */
#include "safepdf_view.h"

#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

extern lean_object *initialize_safe_x2dpdf_SafePdf_Shell_FfiView(uint8_t builtin);

/* Lean exports (SafePdf/Shell/FfiView.lean). */
extern lean_object *safepdf_lean_view_constants(lean_object *u);
extern lean_object *safepdf_lean_view_zoom_steps(lean_object *u);
extern lean_object *safepdf_lean_view_quant(lean_object *a);
extern lean_object *safepdf_lean_view_pct_zoom(lean_object *a);
extern lean_object *safepdf_lean_view_zoom_pct(lean_object *a);
extern lean_object *safepdf_lean_view_step_in(lean_object *a);
extern lean_object *safepdf_lean_view_step_out(lean_object *a);
extern lean_object *safepdf_lean_view_fit_zoom(lean_object *a);
extern lean_object *safepdf_lean_view_cap_zoom(lean_object *a);
extern lean_object *safepdf_lean_view_pixel_size(lean_object *a);
extern lean_object *safepdf_lean_view_rotate(lean_object *a);
extern lean_object *safepdf_lean_view_reanchor(lean_object *a);
extern lean_object *safepdf_lean_view_spread(lean_object *a);
extern lean_object *safepdf_lean_view_layout(lean_object *a);
extern lean_object *safepdf_lean_view_pages_in_band(lean_object *a);
extern lean_object *safepdf_lean_view_page_at(lean_object *a);
extern lean_object *safepdf_lean_view_zoom_presets(lean_object *u);
extern lean_object *safepdf_lean_view_zoom_label(uint32_t kind, uint32_t pct);
extern lean_object *safepdf_lean_view_zoom_parse(lean_object *key);
extern lean_object *safepdf_lean_view_zoom_with(lean_object *a);
extern lean_object *safepdf_lean_view_choices(lean_object *u);
extern lean_object *safepdf_lean_view_choice_modes(lean_object *a);
extern lean_object *safepdf_lean_view_page_field(lean_object *labels, size_t page, size_t n);
extern lean_object *safepdf_lean_view_page_entry(lean_object *labels, size_t n, size_t cur,
                                                 lean_object *input);
extern lean_object *safepdf_lean_view_toolbar(lean_object *u);
extern lean_object *safepdf_lean_view_states(lean_object *a);
extern uint32_t safepdf_lean_view_cursor_for(uint32_t mode, uint32_t hit);
extern uint32_t safepdf_lean_view_hit_of(uint8_t mark, uint8_t link, uint8_t text);
extern uint32_t safepdf_lean_view_mode_tool(uint32_t mode);
extern lean_object *safepdf_lean_view_commands(lean_object *u);
extern lean_object *safepdf_lean_view_menubar(lean_object *u);
extern lean_object *safepdf_lean_view_overflow(lean_object *u);
extern lean_object *safepdf_lean_view_keys(lean_object *u);
extern lean_object *safepdf_lean_view_actions(lean_object *u);
extern lean_object *safepdf_lean_view_app_strings(lean_object *u);

static int initialised = 0;

int safepdf_view_init(void) {
    if (initialised) return 0;
    lean_object *res = initialize_safe_x2dpdf_SafePdf_Shell_FfiView(1 /* builtin */);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec(res);
        return -1;
    }
    lean_dec(res);
    initialised = 1;
    return 0;
}

double safepdf_rat_to_double(safepdf_rat q) {
    return q.den == 0 ? 0.0 : (double)q.num / (double)q.den;
}

/* ---------------------------------------------------------------- wire helpers */

/** A growable list of int64 inputs. `bad` records an invalid rational or a failed
    allocation; calls check it before going to Lean. */
typedef struct { int64_t *v; size_t n, cap; int bad; } ints;

static void push(ints *b, int64_t x) {
    if (b->bad) return;
    if (b->n == b->cap) {
        size_t cap = b->cap ? 2 * b->cap : 32;
        int64_t *v = realloc(b->v, cap * sizeof *v);
        if (!v) { b->bad = 1; return; }
        b->v = v; b->cap = cap;
    }
    b->v[b->n++] = x;
}

static void push_rat(ints *b, safepdf_rat q) {
    if (q.den <= 0) b->bad = 1;
    push(b, q.num);
    push(b, q.den);
}

static void push_box(ints *b, const safepdf_rat_box *bx) {
    if (!bx) { b->bad = 1; return; }
    push_rat(b, bx->llx); push_rat(b, bx->lly); push_rat(b, bx->urx); push_rat(b, bx->ury);
}

/** Saturating conversion of an unsigned value to the wire (Lean reads it as a Nat). */
static int64_t u64(uint64_t x) { return x > (uint64_t)INT64_MAX ? INT64_MAX : (int64_t)x; }

/** The inputs as a Lean ByteArray (one reference, owned by the caller), freeing the list.
    NULL when the inputs are invalid or memory ran out. */
static lean_object *to_lean(ints *b) {
    if (b->bad || !initialised) { free(b->v); return NULL; }
    size_t bytes = 8 * b->n;
    lean_object *a = lean_alloc_sarray(1, bytes, bytes);
    uint8_t *p = lean_sarray_cptr(a);
    for (size_t i = 0; i < b->n; i++) {
        uint64_t u = (uint64_t)b->v[i];
        for (int k = 0; k < 8; k++) p[8 * i + k] = (uint8_t)(u >> (8 * k));
    }
    free(b->v);
    return a;
}

static size_t nums_len(lean_object *a) { return lean_sarray_size(a) / 8; }

static int64_t num(lean_object *a, size_t i) {
    if (i >= nums_len(a)) return 0;
    const uint8_t *p = lean_sarray_cptr(a) + 8 * i;
    uint64_t u = 0;
    for (int k = 0; k < 8; k++) u |= (uint64_t)p[k] << (8 * k);
    return (int64_t)u;
}

static uint64_t unum(lean_object *a, size_t i) {
    int64_t v = num(a, i);
    return v < 0 ? 0 : (uint64_t)v;
}

/** The rational at integers i, i + 1; -1 when it was unrepresentable (0/0). */
static int rat_at(lean_object *a, size_t i, safepdf_rat *out) {
    safepdf_rat q = { num(a, i), num(a, i + 1) };
    if (q.den <= 0) return -1;
    if (out) *out = q;
    return 0;
}

/** Calls `f` on the inputs; the result ByteArray (owned) or NULL. Checks it holds at least
    `want` integers. */
static lean_object *call(lean_object *(*f)(lean_object *), ints *in, size_t want) {
    lean_object *a = to_lean(in);
    if (!a) return NULL;
    lean_object *r = f(a);
    if (nums_len(r) < want) { lean_dec(r); return NULL; }
    return r;
}

/** A malloc'd copy of a Lean string. */
static char *dup_str(lean_object *s) {
    return strdup(lean_string_cstr(s));
}

/** A malloc'd copy of string i of a Lean `Array String` ("" past its end). */
static char *str_at(lean_object *arr, size_t i) {
    if (i >= lean_array_size(arr)) return strdup("");
    return dup_str(lean_array_get_core(arr, i));
}

/** A Lean `Array String` of C strings (one reference). */
static lean_object *mk_strings(const char *const *s, size_t n) {
    lean_object *arr = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++) lean_array_cptr(arr)[i] = lean_mk_string(s && s[i] ? s[i] : "");
    return arr;
}

/** Number of rows of a table with `k` integers and `m` strings per row; -1 if inconsistent. */
static long table_rows(lean_object *t, size_t k, size_t m) {
    lean_object *ints_ = lean_ctor_get(t, 0), *strs = lean_ctor_get(t, 1);
    size_t rows = nums_len(ints_) / k;
    if (nums_len(ints_) != rows * k || lean_array_size(strs) != rows * m) return -1;
    return (long)rows;
}

/* ---------------------------------------------------------------- constants */

int safepdf_view_get_constants(safepdf_view_constants *out) {
    if (!initialised || !out) return -1;
    lean_object *r = safepdf_lean_view_constants(lean_box(0));
    if (nums_len(r) < 8) { lean_dec(r); return -1; }
    out->margin = (uint32_t)unum(r, 0);
    out->page_gap = (uint32_t)unum(r, 1);
    out->min_pct = (uint32_t)unum(r, 2);
    out->max_pct = (uint32_t)unum(r, 3);
    out->auto_max_pct = (uint32_t)unum(r, 4);
    out->page_pixels = unum(r, 5);
    out->max_page_side = (uint32_t)unum(r, 6);
    out->max_view_pixels = unum(r, 7);
    lean_dec(r);
    return 0;
}

size_t safepdf_view_zoom_steps(uint32_t *out, size_t cap) {
    if (!initialised) return 0;
    lean_object *r = safepdf_lean_view_zoom_steps(lean_box(0));
    size_t n = nums_len(r);
    for (size_t i = 0; i < n && i < cap; i++) out[i] = (uint32_t)unum(r, i);
    lean_dec(r);
    return n;
}

/* ---------------------------------------------------------------- zoom */

/** Calls `f` and reads one rational result at integer 0. */
static int rat_call(lean_object *(*f)(lean_object *), ints *in, safepdf_rat *out) {
    lean_object *r = call(f, in, 2);
    if (!r) return -1;
    int rc = rat_at(r, 0, out);
    lean_dec(r);
    return rc;
}

int safepdf_view_quant(safepdf_rat z, safepdf_rat *out) {
    ints in = {0};
    push_rat(&in, z);
    return rat_call(safepdf_lean_view_quant, &in, out);
}

int safepdf_view_pct_zoom(uint32_t pct, safepdf_rat scaling, safepdf_rat *out) {
    ints in = {0};
    push(&in, pct); push_rat(&in, scaling);
    return rat_call(safepdf_lean_view_pct_zoom, &in, out);
}

int safepdf_view_zoom_pct(safepdf_rat z, safepdf_rat scaling, uint32_t *pct) {
    ints in = {0};
    push_rat(&in, z); push_rat(&in, scaling);
    lean_object *r = call(safepdf_lean_view_zoom_pct, &in, 1);
    if (!r) return -1;
    if (pct) *pct = (uint32_t)unum(r, 0);
    lean_dec(r);
    return 0;
}

static int step(lean_object *(*f)(lean_object *), safepdf_rat z, safepdf_rat scaling,
                uint32_t *pct) {
    ints in = {0};
    push_rat(&in, z); push_rat(&in, scaling);
    lean_object *r = call(f, &in, 2);
    if (!r) return -1;
    int found = num(r, 0) != 0;
    if (pct) *pct = (uint32_t)unum(r, 1);
    lean_dec(r);
    return found;
}

int safepdf_view_step_in(safepdf_rat z, safepdf_rat scaling, uint32_t *pct) {
    return step(safepdf_lean_view_step_in, z, scaling, pct);
}

int safepdf_view_step_out(safepdf_rat z, safepdf_rat scaling, uint32_t *pct) {
    return step(safepdf_lean_view_step_out, z, scaling, pct);
}

int safepdf_view_fit_zoom(bool width_only, uint32_t cw, uint32_t ch, safepdf_rat pw,
                          safepdf_rat ph, safepdf_rat *out) {
    ints in = {0};
    push(&in, width_only); push(&in, cw); push(&in, ch); push_rat(&in, pw); push_rat(&in, ph);
    return rat_call(safepdf_lean_view_fit_zoom, &in, out);
}

int safepdf_view_cap_zoom(uint64_t max_pixels, safepdf_rat z, uint32_t rotation,
                          const safepdf_rat_box *box, safepdf_rat *out, bool *lowered) {
    ints in = {0};
    push(&in, u64(max_pixels)); push_rat(&in, z); push(&in, rotation); push_box(&in, box);
    lean_object *r = call(safepdf_lean_view_cap_zoom, &in, 3);
    if (!r) return -1;
    int rc = rat_at(r, 0, out);
    if (lowered) *lowered = num(r, 2) != 0;
    lean_dec(r);
    return rc;
}

int safepdf_view_pixel_size(uint32_t side, safepdf_rat z, uint32_t rotation,
                            const safepdf_rat_box *box, safepdf_pixel_size *out) {
    ints in = {0};
    push(&in, side); push_rat(&in, z); push(&in, rotation); push_box(&in, box);
    lean_object *r = call(safepdf_lean_view_pixel_size, &in, 5);
    if (!r) return -1;
    if (out) {
        out->width = unum(r, 0); out->height = unum(r, 1);
        out->image_width = unum(r, 2); out->image_height = unum(r, 3);
        out->cropped = num(r, 4) != 0;
    }
    lean_dec(r);
    return 0;
}

/* ---------------------------------------------------------------- rotation, anchoring */

int safepdf_view_rotation(uint32_t rotation, const safepdf_rat_box *box, safepdf_rotation_info *out) {
    ints in = {0};
    push(&in, rotation); push_box(&in, box);
    lean_object *r = call(safepdf_lean_view_rotate, &in, 6);
    if (!r) return -1;
    safepdf_rotation_info info;
    info.cw = (uint32_t)unum(r, 0);
    info.ccw = (uint32_t)unum(r, 1);
    int rc = rat_at(r, 2, &info.width) | rat_at(r, 4, &info.height);
    lean_dec(r);
    if (rc) return -1;
    if (out) *out = info;
    return 0;
}

int safepdf_view_reanchor(safepdf_rat z, uint32_t rot, safepdf_rat z2, uint32_t rot2,
                          const safepdf_rat_box *box, safepdf_rat_point q, safepdf_rat_point *out) {
    ints in = {0};
    push_rat(&in, z); push(&in, rot); push_rat(&in, z2); push(&in, rot2); push_box(&in, box);
    push_rat(&in, q.x); push_rat(&in, q.y);
    lean_object *r = call(safepdf_lean_view_reanchor, &in, 4);
    if (!r) return -1;
    safepdf_rat_point p;
    int rc = rat_at(r, 0, &p.x) | rat_at(r, 2, &p.y);
    lean_dec(r);
    if (rc) return -1;
    if (out) *out = p;
    return 0;
}

/* ---------------------------------------------------------------- spreads */

int safepdf_view_spread(uint32_t spread, size_t n, size_t page, safepdf_spread_info *out) {
    ints in = {0};
    push(&in, spread); push(&in, u64(n)); push(&in, u64(page));
    lean_object *r = call(safepdf_lean_view_spread, &in, 7);
    if (!r) return -1;
    if (out) {
        out->spread = unum(r, 0); out->spread_count = unum(r, 1);
        out->next_page = unum(r, 2); out->prev_page = unum(r, 3);
        out->page_count = unum(r, 4); out->pages[0] = unum(r, 5); out->pages[1] = unum(r, 6);
    }
    lean_dec(r);
    return 0;
}

/* ---------------------------------------------------------------- zoom choices */

void safepdf_free_zoom_presets(safepdf_zoom_presets *p) {
    if (!p) return;
    for (size_t i = 0; i < p->count; i++) { free(p->items[i].label); free(p->items[i].key); }
    free(p->items);
    memset(p, 0, sizeof *p);
}

int safepdf_view_zoom_presets(safepdf_zoom_presets *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!initialised) return -1;
    lean_object *t = safepdf_lean_view_zoom_presets(lean_box(0));
    long rows = table_rows(t, 2, 2);
    if (rows < 0 || !(out->items = calloc(rows ? rows : 1, sizeof *out->items))) {
        lean_dec(t); return -1;
    }
    lean_object *in = lean_ctor_get(t, 0), *ss = lean_ctor_get(t, 1);
    for (long i = 0; i < rows; i++) {
        safepdf_zoom_preset *e = &out->items[i];
        e->choice.kind = (uint32_t)unum(in, 2 * i);
        e->choice.pct = (uint32_t)unum(in, 2 * i + 1);
        e->label = str_at(ss, 2 * i);
        e->key = str_at(ss, 2 * i + 1);
        out->count++;
    }
    lean_dec(t);
    return 0;
}

char *safepdf_view_zoom_label(safepdf_zoom_choice c) {
    if (!initialised) return NULL;
    lean_object *r = safepdf_lean_view_zoom_label(c.kind, c.pct);
    char *s = str_at(r, 0);
    lean_dec(r);
    return s;
}

int safepdf_view_zoom_parse(const char *key, safepdf_zoom_choice *out) {
    if (!initialised || !key) return -1;
    lean_object *r = safepdf_lean_view_zoom_parse(lean_mk_string(key));
    if (nums_len(r) < 3) { lean_dec(r); return -1; }
    int found = num(r, 0) != 0;
    if (found && out) { out->kind = (uint32_t)unum(r, 1); out->pct = (uint32_t)unum(r, 2); }
    lean_dec(r);
    return found;
}

int safepdf_view_zoom_with(safepdf_zoom_choice c, uint32_t cw, uint32_t ch, safepdf_rat scaling,
                           safepdf_rat pw, safepdf_rat ph, bool portrait, safepdf_rat *out) {
    ints in = {0};
    push(&in, c.kind); push(&in, c.pct); push(&in, cw); push(&in, ch);
    push_rat(&in, scaling); push_rat(&in, pw); push_rat(&in, ph); push(&in, portrait);
    return rat_call(safepdf_lean_view_zoom_with, &in, out);
}

/* ---------------------------------------------------------------- layout */

#define PLACE_INTS 10

void safepdf_free_layout(safepdf_layout *l) {
    if (!l) return;
    free(l->places);
    memset(l, 0, sizeof *l);
}

int safepdf_view_layout(const safepdf_page_geom *pages, size_t n,
                        const safepdf_layout_params *p, safepdf_layout *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!p || (n && !pages)) return -1;
    ints in = {0};
    push(&in, p->scroll); push(&in, p->spread); push(&in, p->user_rotation);
    push(&in, p->zoom.kind); push(&in, p->zoom.pct); push_rat(&in, p->scaling);
    push(&in, p->canvas_w); push(&in, p->canvas_h); push(&in, u64(p->page)); push(&in, p->rtl);
    for (size_t i = 0; i < n; i++) { push_box(&in, &pages[i].box); push(&in, pages[i].rotate); }
    lean_object *r = call(safepdf_lean_view_layout, &in, 5);
    if (!r) return -1;
    size_t count = unum(r, 4);
    if (rat_at(r, 0, &out->base_zoom) || nums_len(r) != 5 + PLACE_INTS * count ||
        !(out->places = calloc(count ? count : 1, sizeof *out->places))) {
        lean_dec(r); memset(out, 0, sizeof *out); return -1;
    }
    out->region_w = unum(r, 2);
    out->region_h = unum(r, 3);
    for (size_t i = 0; i < count; i++) {
        size_t o = 5 + PLACE_INTS * i;
        safepdf_place *pl = &out->places[i];
        pl->page = unum(r, o); pl->x = unum(r, o + 1); pl->y = unum(r, o + 2);
        pl->w = unum(r, o + 3); pl->h = unum(r, o + 4);
        if (rat_at(r, o + 5, &pl->zoom)) { lean_dec(r); safepdf_free_layout(out); return -1; }
        pl->rotation = (uint32_t)unum(r, o + 7);
        pl->capped = num(r, o + 8) != 0;
        pl->cropped = num(r, o + 9) != 0;
    }
    out->count = count;
    lean_dec(r);
    return 0;
}

/** Appends the places of `l` (page, x, y, w, h each). */
static void push_places(ints *in, const safepdf_layout *l) {
    for (size_t i = 0; i < l->count; i++) {
        const safepdf_place *pl = &l->places[i];
        push(in, u64(pl->page)); push(in, u64(pl->x)); push(in, u64(pl->y));
        push(in, u64(pl->w)); push(in, u64(pl->h));
    }
}

void safepdf_free_page_band(safepdf_page_band *b) {
    if (!b) return;
    free(b->visible);
    free(b->wanted);
    memset(b, 0, sizeof *b);
}

int safepdf_view_pages_in_band(const safepdf_layout *l, uint64_t top, uint64_t bottom,
                               safepdf_page_band *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!l) return -1;
    ints in = {0};
    push(&in, u64(top)); push(&in, u64(bottom)); push_places(&in, l);
    lean_object *r = call(safepdf_lean_view_pages_in_band, &in, 1);
    if (!r) return -1;
    size_t n = nums_len(r), nv = unum(r, 0);
    if (nv > n - 1) { lean_dec(r); return -1; }
    size_t nw = n - 1 - nv;
    out->visible = malloc((nv ? nv : 1) * sizeof(size_t));
    out->wanted = malloc((nw ? nw : 1) * sizeof(size_t));
    if (!out->visible || !out->wanted) { lean_dec(r); safepdf_free_page_band(out); return -1; }
    for (size_t i = 0; i < nv; i++) out->visible[i] = unum(r, 1 + i);
    for (size_t i = 0; i < nw; i++) out->wanted[i] = unum(r, 1 + nv + i);
    out->visible_count = nv;
    out->wanted_count = nw;
    lean_dec(r);
    return 0;
}

int safepdf_view_page_at(const safepdf_layout *l, uint64_t x, uint64_t y, uint64_t view_h,
                         safepdf_page_hit *out) {
    if (!l) return -1;
    ints in = {0};
    push(&in, u64(x)); push(&in, u64(y)); push(&in, u64(view_h)); push_places(&in, l);
    lean_object *r = call(safepdf_lean_view_page_at, &in, 4);
    if (!r) return -1;
    int found = num(r, 0) != 0;
    if (found && out) { out->page = unum(r, 1); out->top = unum(r, 2); out->bottom = unum(r, 3); }
    lean_dec(r);
    return found;
}

/* ---------------------------------------------------------------- view choices */

void safepdf_free_view_choices(safepdf_view_choices *c) {
    if (!c) return;
    for (size_t i = 0; i < c->count; i++) { free(c->items[i].label); free(c->items[i].key); }
    free(c->items);
    memset(c, 0, sizeof *c);
}

int safepdf_view_view_choices(safepdf_view_choices *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!initialised) return -1;
    lean_object *t = safepdf_lean_view_choices(lean_box(0));
    long rows = table_rows(t, 3, 2);
    if (rows < 0 || !(out->items = calloc(rows ? rows : 1, sizeof *out->items))) {
        lean_dec(t); return -1;
    }
    lean_object *in = lean_ctor_get(t, 0), *ss = lean_ctor_get(t, 1);
    for (long i = 0; i < rows; i++) {
        safepdf_view_choice_item *e = &out->items[i];
        e->choice = (uint32_t)unum(in, 3 * i);
        e->scroll = (uint32_t)unum(in, 3 * i + 1);
        e->spread = (uint32_t)unum(in, 3 * i + 2);
        e->label = str_at(ss, 2 * i);
        e->key = str_at(ss, 2 * i + 1);
        out->count++;
    }
    lean_dec(t);
    return 0;
}

/** ViewChoice.ofModes (index 0) and ViewChoice.modes (indices 1, 2) in one call. */
static lean_object *choice_call(uint32_t scroll, uint32_t spread, uint32_t choice) {
    ints in = {0};
    push(&in, scroll); push(&in, spread); push(&in, choice);
    return call(safepdf_lean_view_choice_modes, &in, 3);
}

uint32_t safepdf_view_choice_of_modes(uint32_t scroll, uint32_t spread) {
    lean_object *r = choice_call(scroll, spread, 0);
    if (!r) return 0;
    uint32_t c = (uint32_t)unum(r, 0);
    lean_dec(r);
    return c;
}

int safepdf_view_choice_modes(uint32_t choice, uint32_t spread_now, uint32_t *scroll,
                              uint32_t *spread) {
    lean_object *r = choice_call(0, spread_now, choice);
    if (!r) return -1;
    if (scroll) *scroll = (uint32_t)unum(r, 1);
    if (spread) *spread = (uint32_t)unum(r, 2);
    lean_dec(r);
    return 0;
}

/* ---------------------------------------------------------------- page field */

int safepdf_view_page_field(const char *const *labels, size_t nlabels, size_t page, size_t pages,
                            char **entry_text, char **of_text) {
    if (!initialised) return -1;
    lean_object *r = safepdf_lean_view_page_field(mk_strings(labels, nlabels), page, pages);
    char *a = str_at(r, 0), *b = str_at(r, 1);
    lean_dec(r);
    if (!a || !b) { free(a); free(b); return -1; }
    if (entry_text) *entry_text = a; else free(a);
    if (of_text) *of_text = b; else free(b);
    return 0;
}

int safepdf_view_page_entry(const char *const *labels, size_t nlabels, size_t pages,
                            size_t current, const char *input, size_t *page) {
    if (!initialised || !input) return -1;
    lean_object *r = safepdf_lean_view_page_entry(mk_strings(labels, nlabels), pages, current,
                                                  lean_mk_string(input));
    if (nums_len(r) < 2) { lean_dec(r); return -1; }
    if (page) *page = unum(r, 0);
    int ok = num(r, 1) != 0;
    lean_dec(r);
    return ok;
}

/* ---------------------------------------------------------------- commands */

void safepdf_free_commands(safepdf_commands *c) {
    if (!c) return;
    for (size_t i = 0; i < c->count; i++) {
        free(c->items[i].name); free(c->items[i].label);
        free(c->items[i].accel.key); free(c->items[i].accel.shown);
    }
    free(c->items);
    memset(c, 0, sizeof *c);
}

int safepdf_view_commands(safepdf_commands *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!initialised) return -1;
    lean_object *t = safepdf_lean_view_commands(lean_box(0));
    long rows = table_rows(t, 2, 4);
    if (rows < 0 || !(out->items = calloc(rows ? rows : 1, sizeof *out->items))) {
        lean_dec(t); return -1;
    }
    lean_object *in = lean_ctor_get(t, 0), *ss = lean_ctor_get(t, 1);
    for (long i = 0; i < rows; i++) {
        safepdf_command *e = &out->items[i];
        e->id = (uint32_t)unum(in, 2 * i);
        e->accel.mods = (uint32_t)unum(in, 2 * i + 1);
        e->name = str_at(ss, 4 * i);
        e->label = str_at(ss, 4 * i + 1);
        e->accel.key = str_at(ss, 4 * i + 2);
        e->accel.shown = str_at(ss, 4 * i + 3);
        out->count++;
    }
    lean_dec(t);
    return 0;
}

int safepdf_view_actions(safepdf_commands *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!initialised) return -1;
    lean_object *a = safepdf_lean_view_actions(lean_box(0));
    size_t rows = lean_array_size(a) / 2;
    if (!(out->items = calloc(rows ? rows : 1, sizeof *out->items))) { lean_dec(a); return -1; }
    for (size_t i = 0; i < rows; i++) {
        safepdf_command *e = &out->items[i];
        e->id = (uint32_t)i;
        e->name = str_at(a, 2 * i);
        e->label = str_at(a, 2 * i + 1);
        e->accel.key = strdup("");
        e->accel.shown = strdup("");
        out->count++;
    }
    lean_dec(a);
    return 0;
}

static char *app_string(size_t i) {
    if (!initialised) return NULL;
    lean_object *a = safepdf_lean_view_app_strings(lean_box(0));
    char *s = str_at(a, i);
    lean_dec(a);
    return s;
}

char *safepdf_view_app_name(void) { return app_string(0); }
char *safepdf_view_about_detail(void) { return app_string(1); }

/* ---------------------------------------------------------------- menus */

void safepdf_free_menu_table(safepdf_menu_table *t) {
    if (!t) return;
    for (size_t i = 0; i < t->menu_count; i++) free(t->menu_labels[i]);
    free(t->menu_labels);
    for (size_t i = 0; i < t->entry_count; i++) {
        safepdf_menu_entry *e = &t->entries[i];
        free(e->label); free(e->radio_value); free(e->accel.key); free(e->accel.shown);
    }
    free(t->entries);
    memset(t, 0, sizeof *t);
}

/** Fills `out` from a Lean (labels, table) pair (consumed). */
static int menu_table(lean_object *pair, safepdf_menu_table *out) {
    lean_object *labels = lean_ctor_get(pair, 0), *t = lean_ctor_get(pair, 1);
    size_t nm = lean_array_size(labels);
    long rows = table_rows(t, 5, 4);
    if (rows < 0 || !(out->menu_labels = calloc(nm ? nm : 1, sizeof(char *))) ||
        !(out->entries = calloc(rows ? rows : 1, sizeof *out->entries))) {
        lean_dec(pair); safepdf_free_menu_table(out); return -1;
    }
    for (size_t i = 0; i < nm; i++) { out->menu_labels[i] = str_at(labels, i); out->menu_count++; }
    lean_object *in = lean_ctor_get(t, 0), *ss = lean_ctor_get(t, 1);
    for (long i = 0; i < rows; i++) {
        safepdf_menu_entry *e = &out->entries[i];
        e->menu = (uint32_t)unum(in, 5 * i);
        e->kind = (uint32_t)unum(in, 5 * i + 1);
        e->cmd = (int32_t)num(in, 5 * i + 2);
        e->accel.mods = (uint32_t)unum(in, 5 * i + 3);
        e->radio_group = (uint32_t)unum(in, 5 * i + 4);
        e->label = str_at(ss, 4 * i);
        e->accel.key = str_at(ss, 4 * i + 1);
        e->accel.shown = str_at(ss, 4 * i + 2);
        e->radio_value = str_at(ss, 4 * i + 3);
        out->entry_count++;
    }
    lean_dec(pair);
    return 0;
}

int safepdf_view_menubar(safepdf_menu_table *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!initialised) return -1;
    return menu_table(safepdf_lean_view_menubar(lean_box(0)), out);
}

int safepdf_view_overflow_menu(safepdf_menu_table *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!initialised) return -1;
    return menu_table(safepdf_lean_view_overflow(lean_box(0)), out);
}

void safepdf_free_key_table(safepdf_key_table *t) {
    if (!t) return;
    for (size_t i = 0; i < t->count; i++) { free(t->items[i].key.key); free(t->items[i].key.shown); }
    free(t->items);
    memset(t, 0, sizeof *t);
}

int safepdf_view_keys(safepdf_key_table *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!initialised) return -1;
    lean_object *t = safepdf_lean_view_keys(lean_box(0));
    long rows = table_rows(t, 4, 2);
    if (rows < 0 || !(out->items = calloc(rows ? rows : 1, sizeof *out->items))) {
        lean_dec(t); return -1;
    }
    lean_object *in = lean_ctor_get(t, 0), *ss = lean_ctor_get(t, 1);
    for (long i = 0; i < rows; i++) {
        safepdf_key_binding *e = &out->items[i];
        e->target_kind = (uint32_t)unum(in, 4 * i);
        e->target = (uint32_t)unum(in, 4 * i + 1);
        e->key.mods = (uint32_t)unum(in, 4 * i + 2);
        e->x11 = num(in, 4 * i + 3) != 0;
        e->key.key = str_at(ss, 2 * i);
        e->key.shown = str_at(ss, 2 * i + 1);
        out->count++;
    }
    lean_dec(t);
    return 0;
}

/* ---------------------------------------------------------------- toolbar */

void safepdf_free_toolbar(safepdf_toolbar *t) {
    if (!t) return;
    for (size_t i = 0; i < t->count; i++) {
        free(t->items[i].id); free(t->items[i].icon); free(t->items[i].tooltip);
    }
    free(t->items);
    memset(t, 0, sizeof *t);
}

int safepdf_view_toolbar(safepdf_toolbar *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!initialised) return -1;
    lean_object *t = safepdf_lean_view_toolbar(lean_box(0));
    long rows = table_rows(t, 5, 3);
    if (rows < 0 || !(out->items = calloc(rows ? rows : 1, sizeof *out->items))) {
        lean_dec(t); return -1;
    }
    lean_object *in = lean_ctor_get(t, 0), *ss = lean_ctor_get(t, 1);
    for (long i = 0; i < rows; i++) {
        safepdf_toolbar_item *e = &out->items[i];
        e->group = (uint32_t)unum(in, 5 * i);
        e->kind = (uint32_t)unum(in, 5 * i + 1);
        e->action = (int32_t)num(in, 5 * i + 2);
        e->cmd = (int32_t)num(in, 5 * i + 3);
        e->tool = (int32_t)num(in, 5 * i + 4);
        e->id = str_at(ss, 3 * i);
        e->icon = str_at(ss, 3 * i + 1);
        e->tooltip = str_at(ss, 3 * i + 2);
        out->count++;
    }
    lean_dec(t);
    return 0;
}

void safepdf_free_chrome_states(safepdf_chrome_states *s) {
    if (!s) return;
    free(s->item_enabled);
    free(s->item_visible);
    memset(s, 0, sizeof *s);
}

int safepdf_view_states(const safepdf_ctx *c, safepdf_chrome_states *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!c) return -1;
    const bool bits[] = { c->has_doc, c->has_sel, c->has_outline, c->has_mark, c->can_back,
                          c->can_forward, c->dirty, c->can_undo, c->can_redo, c->on_first,
                          c->on_last };
    int64_t flags = 0;
    for (size_t i = 0; i < sizeof bits / sizeof bits[0]; i++) if (bits[i]) flags |= (int64_t)1 << i;
    ints in = {0};
    push(&in, flags); push(&in, u64(c->page)); push(&in, u64(c->pages));
    lean_object *r = call(safepdf_lean_view_states, &in, SAFEPDF_CMD_COUNT);
    if (!r) return -1;
    size_t n = nums_len(r), items = (n - SAFEPDF_CMD_COUNT) / 2;
    if (n != SAFEPDF_CMD_COUNT + 2 * items ||
        !(out->item_enabled = calloc(items ? items : 1, sizeof(bool))) ||
        !(out->item_visible = calloc(items ? items : 1, sizeof(bool)))) {
        lean_dec(r); safepdf_free_chrome_states(out); return -1;
    }
    for (size_t i = 0; i < SAFEPDF_CMD_COUNT; i++) out->command_enabled[i] = num(r, i) != 0;
    for (size_t i = 0; i < items; i++) {
        out->item_enabled[i] = num(r, SAFEPDF_CMD_COUNT + 2 * i) != 0;
        out->item_visible[i] = num(r, SAFEPDF_CMD_COUNT + 2 * i + 1) != 0;
    }
    out->item_count = items;
    lean_dec(r);
    return 0;
}

/* ---------------------------------------------------------------- pointer */

uint32_t safepdf_view_hit_of(bool mark, bool link, bool text) {
    if (!initialised) return SAFEPDF_HIT_EMPTY;
    return safepdf_lean_view_hit_of(mark, link, text);
}

uint32_t safepdf_view_cursor_for(uint32_t mode, uint32_t hit) {
    if (!initialised) return SAFEPDF_CURSOR_ARROW;
    return safepdf_lean_view_cursor_for(mode, hit);
}

uint32_t safepdf_view_mode_tool(uint32_t mode) {
    if (!initialised) return SAFEPDF_TOOL_SELECT;
    return safepdf_lean_view_mode_tool(mode);
}
