/*
 * safepdf_core.c — the C API of safepdf_core.h over the Lean exports of
 * SafePdf/Shell/Ffi.lean (the error text) and SafePdf/Shell/Ffi/V2.lean (v2, task 11.3a1; page
 * geometry and the test-only in-process render, task 11.3c1, which also retired v1).
 *
 * Reference counting: Lean v4.36 `@[export]` functions take every object argument as
 * OWNED (they consume one reference), so each call below that keeps using an object
 * afterwards first adds a reference with lean_inc. Every object a Lean function returns is
 * owned here and released with lean_dec once its contents are copied out.
 *
 * v2 delivery: Lean calls safepdf_c_deliver (an @[extern] of SafePdf.Shell.Ffi.V2) exactly
 * once per accepted request, from a Lean task thread, with a flat blob (SafePdf.Shell.Ffi.Flat:
 * tables of 64-bit little-endian cells and a NUL-terminated string pool). The shim copies the
 * blob into the public structs, enqueues the caller's callback with dispatch_async_f and
 * decrements the document's outstanding count; the callback itself runs outside Lean.
 */
#include "safepdf_core.h"

#include <lean/lean.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

/* Lean runtime and module initialisers (not declared in lean.h). */
extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern lean_object *initialize_safe_x2dpdf_SafePdf_Shell_Ffi(uint8_t builtin);

/* Lean exports (SafePdf/Shell/Ffi.lean). */
extern lean_object *safepdf_lean_error_text(lean_object *e);

/* Lean exports (SafePdf/Shell/Ffi/V2.lean, v2). */
extern lean_object *safepdf_lean_doc_open_bytes(lean_object *bytes, lean_object *worker,
                                                size_t deadline_ms, uint8_t strict,
                                                size_t stall_ms);
extern lean_object *safepdf_lean_doc_open_file(lean_object *path, lean_object *worker,
                                               size_t deadline_ms, uint8_t strict,
                                               size_t stall_ms);
extern size_t safepdf_lean_doc_page_count(lean_object *d);
extern lean_object *safepdf_lean_doc_page_size(lean_object *d, size_t i);
extern lean_object *safepdf_lean_doc_page_geom(lean_object *d, size_t i);
extern lean_object *safepdf_lean_doc_test_render(lean_object *d, size_t i, size_t num, size_t den,
                                                 uint8_t rot);
extern uint8_t safepdf_lean_doc_flags(lean_object *d);
extern lean_object *safepdf_lean_doc_bytes(lean_object *d);
extern lean_object *safepdf_lean_doc_submit(lean_object *d, size_t token, uint64_t cid,
                                            uint8_t kind, size_t page, size_t num, size_t den,
                                            uint8_t rot, lean_object *layers, uint8_t prio);
extern lean_object *safepdf_lean_doc_cancel(lean_object *d, uint64_t cid);
extern lean_object *safepdf_lean_doc_raise(lean_object *d, uint64_t cid, uint8_t prio);
extern lean_object *safepdf_lean_doc_shutdown(lean_object *d);
extern lean_object *safepdf_lean_doc_layers_toggle(lean_object *d, lean_object *state,
                                                   size_t row);
extern lean_object *safepdf_lean_doc_open_settings(lean_object *d);

/* Lean exports (SafePdf/Shell/Ffi/Sidebar.lean, task 11.3d2). */
extern uint32_t safepdf_lean_sidebar_on_load(uint32_t mode, uint32_t c);
extern uint8_t safepdf_lean_sidebar_available(uint32_t p, uint32_t c);
extern uint32_t safepdf_lean_sidebar_pick(uint32_t last, uint32_t c);
extern lean_object *safepdf_lean_sidebar_constants(lean_object *unit);
extern uint32_t safepdf_lean_sidebar_thumb_scale(size_t w, size_t h);
extern lean_object *safepdf_lean_doc_thumb(lean_object *d, size_t i, uint8_t q);
extern lean_object *safepdf_lean_sidebar_thumb_layout(lean_object *a);
extern lean_object *safepdf_lean_sidebar_thumbs_wanted(lean_object *a);
extern lean_object *safepdf_lean_sidebar_thumb_evict(lean_object *a);
extern lean_object *safepdf_lean_sidebar_tree(lean_object *a);
extern lean_object *safepdf_lean_attachment_target_problem(lean_object *name, uint32_t flags);
extern lean_object *safepdf_lean_attachment_size_after(uint8_t has, uint64_t listed,
                                                       uint8_t stream, uint8_t ok, uint64_t n);
extern lean_object *safepdf_lean_identity_line(lean_object *path, uint8_t has, uint8_t in_memory);
extern lean_object *safepdf_lean_action_describe(lean_object *labels, size_t n, uint8_t kind,
                                                 size_t page, lean_object *text);

/* ================================================================ runtime and threads */

static int initialised = 0;
static pthread_t init_thread;
static pthread_key_t reg_key;

/* A thread registered by ensure_thread is unregistered when it exits. */
static void reg_dtor(void *v) {
    if (v) lean_finalize_thread();
}

int safepdf_init(void) {
    if (initialised) return 0;
    lean_initialize_runtime_module();
    lean_object *res = initialize_safe_x2dpdf_SafePdf_Shell_Ffi(1 /* builtin */);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec(res);
        return -1;
    }
    lean_dec(res);
    lean_init_task_manager();
    lean_io_mark_end_initialization();
    if (pthread_key_create(&reg_key, reg_dtor) != 0) return -1;
    init_thread = pthread_self();
    initialised = 1;
    return 0;
}

/* Registers the calling thread with the Lean runtime unless it is the initialising thread or
   already registered (here or by safepdf_thread_enter). */
static void ensure_thread(void) {
    if (pthread_equal(pthread_self(), init_thread)) return;
    if (pthread_getspecific(reg_key)) return;
    lean_initialize_thread();
    pthread_setspecific(reg_key, (void *)1);
}

void safepdf_thread_enter(void) { ensure_thread(); }

void safepdf_thread_exit(void) {
    if (pthread_getspecific(reg_key)) {
        pthread_setspecific(reg_key, NULL);
        lean_finalize_thread();
    }
}

/* The text of the error in the IO result `r` (borrowed), malloc'd. */
static char *error_of(lean_object *r) {
    lean_object *e = lean_io_result_get_error(r);
    lean_inc(e);
    lean_object *s = safepdf_lean_error_text(e);
    char *out = strdup(lean_string_cstr(s));
    lean_dec(s);
    return out;
}

static void set_error(char **error, char *msg) {
    if (error) *error = msg; else free(msg);
}

/* ================================================================ v2: documents */

struct safepdf_document {
    lean_object *handle;   /* SafePdf.Shell.Ffi.V2.Handle, one reference owned, thread-shared */
    atomic_long refs;      /* C references (safepdf_doc_retain / release) */
    size_t pages;
    double *sizes;         /* 2 * pages: width, height in points (-1 when unknown) */
    safepdf_page_geom *geoms; /* per page: CropBox and /Rotate (den 0 when unknown) */
    uint8_t flags;         /* bit 0 repaired, bit 1 encrypted */
    pthread_mutex_t mu;
    pthread_cond_t drained;
    size_t outstanding;    /* requests submitted and not yet delivered (under mu) */
};

static pthread_mutex_t worker_mu = PTHREAD_MUTEX_INITIALIZER;
static char *worker_default = NULL;
static atomic_uint_fast64_t next_request_id = 1;

int safepdf_set_worker_path(const char *path) {
    char *copy = NULL;
    if (path && !(copy = strdup(path))) return -1;
    pthread_mutex_lock(&worker_mu);
    free(worker_default);
    worker_default = copy;
    pthread_mutex_unlock(&worker_mu);
    return 0;
}

/* The worker path of an open as a Lean string ("" : next to the host executable). */
static lean_object *worker_arg(const safepdf_open_options *opts) {
    if (opts && opts->worker_path) return lean_mk_string(opts->worker_path);
    pthread_mutex_lock(&worker_mu);
    lean_object *s = lean_mk_string(worker_default ? worker_default : "");
    pthread_mutex_unlock(&worker_mu);
    return s;
}

/* Eight little-endian bytes at `p`. */
static uint64_t rd64le(const uint8_t *p) {
    uint64_t v = 0;
    for (int i = 7; i >= 0; i--) v = (v << 8) | p[i];
    return v;
}

/* Wraps the Lean handle in the IO result `r` (consumed) into a document. */
static safepdf_document *doc_of_result(lean_object *r, char **error) {
    if (!lean_io_result_is_ok(r)) {
        set_error(error, error_of(r));
        lean_dec(r);
        return NULL;
    }
    lean_object *h = lean_io_result_get_value(r);
    lean_inc(h);
    lean_dec(r);
    /* Shared with the session's tasks and any caller thread: atomic reference counts. */
    lean_mark_mt(h);
    safepdf_document *doc = calloc(1, sizeof *doc);
    if (!doc) {
        lean_inc(h);
        lean_dec(safepdf_lean_doc_shutdown(h));
        lean_dec(h);
        set_error(error, strdup("out of memory"));
        return NULL;
    }
    doc->handle = h;
    atomic_init(&doc->refs, 1);
    pthread_mutex_init(&doc->mu, NULL);
    pthread_cond_init(&doc->drained, NULL);
    lean_inc(h);
    doc->pages = safepdf_lean_doc_page_count(h);
    lean_inc(h);
    doc->flags = safepdf_lean_doc_flags(h);
    doc->sizes = malloc(sizeof(double) * 2 * (doc->pages ? doc->pages : 1));
    for (size_t i = 0; i < doc->pages; i++) {
        lean_inc(h);
        lean_object *a = safepdf_lean_doc_page_size(h, i);
        if (doc->sizes && lean_sarray_size(a) == 2) {
            doc->sizes[2 * i] = lean_float_array_cptr(a)[0];
            doc->sizes[2 * i + 1] = lean_float_array_cptr(a)[1];
        } else if (doc->sizes) {
            doc->sizes[2 * i] = doc->sizes[2 * i + 1] = -1;
        }
        lean_dec(a);
    }
    doc->geoms = calloc(doc->pages ? doc->pages : 1, sizeof *doc->geoms);
    for (size_t i = 0; doc->geoms && i < doc->pages; i++) {
        lean_inc(h);
        lean_object *a = safepdf_lean_doc_page_geom(h, i);
        if (lean_sarray_size(a) == 9 * 8) {
            const uint8_t *b = lean_sarray_cptr(a);
            int64_t v[9];
            for (size_t k = 0; k < 9; k++) v[k] = (int64_t)rd64le(b + 8 * k);
            safepdf_page_geom *g = &doc->geoms[i];
            g->box.llx = (safepdf_rat){ v[0], v[1] };
            g->box.lly = (safepdf_rat){ v[2], v[3] };
            g->box.urx = (safepdf_rat){ v[4], v[5] };
            g->box.ury = (safepdf_rat){ v[6], v[7] };
            g->rotate = (uint32_t)v[8];
        } /* else: left zeroed (den 0), reported as -1 by safepdf_doc_page_geom */
        lean_dec(a);
    }
    return doc;
}

safepdf_document *safepdf_doc_open_file(const char *path, const safepdf_open_options *opts,
                                        char **error) {
    if (!path) { set_error(error, strdup("no path")); return NULL; }
    ensure_thread();
    lean_object *r = safepdf_lean_doc_open_file(
        lean_mk_string(path), worker_arg(opts), opts ? opts->deadline_ms : 0,
        (uint8_t)(opts && opts->strict), opts ? opts->test_stall_ms : 0);
    return doc_of_result(r, error);
}

safepdf_document *safepdf_doc_open_bytes(const uint8_t *bytes, size_t len,
                                         const safepdf_open_options *opts, char **error) {
    if (!bytes && len) { set_error(error, strdup("no bytes")); return NULL; }
    ensure_thread();
    lean_object *ba = lean_alloc_sarray(1, len, len);
    if (len) memcpy(lean_sarray_cptr(ba), bytes, len);
    lean_object *r = safepdf_lean_doc_open_bytes(
        ba, worker_arg(opts), opts ? opts->deadline_ms : 0, (uint8_t)(opts && opts->strict),
        opts ? opts->test_stall_ms : 0);
    return doc_of_result(r, error);
}

safepdf_document *safepdf_doc_retain(safepdf_document *doc) {
    if (doc) atomic_fetch_add(&doc->refs, 1);
    return doc;
}

void safepdf_doc_release(safepdf_document *doc) {
    if (!doc) return;
    if (atomic_fetch_sub(&doc->refs, 1) != 1) return;
    ensure_thread();
    lean_inc(doc->handle);
    lean_dec(safepdf_lean_doc_shutdown(doc->handle));
    pthread_mutex_lock(&doc->mu);
    while (doc->outstanding > 0) pthread_cond_wait(&doc->drained, &doc->mu);
    pthread_mutex_unlock(&doc->mu);
    lean_dec(doc->handle);
    pthread_cond_destroy(&doc->drained);
    pthread_mutex_destroy(&doc->mu);
    free(doc->sizes);
    free(doc->geoms);
    free(doc);
}

size_t safepdf_doc_page_count(const safepdf_document *doc) { return doc ? doc->pages : 0; }

int safepdf_doc_page_size(const safepdf_document *doc, size_t page, double *width,
                          double *height) {
    if (!doc || !doc->sizes || page >= doc->pages || doc->sizes[2 * page] < 0) return -1;
    if (width) *width = doc->sizes[2 * page];
    if (height) *height = doc->sizes[2 * page + 1];
    return 0;
}

int safepdf_doc_page_geom(const safepdf_document *doc, size_t page, safepdf_page_geom *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!doc || !doc->geoms || page >= doc->pages) return -1;
    const safepdf_page_geom *g = &doc->geoms[page];
    if (g->box.llx.den <= 0 || g->box.lly.den <= 0 || g->box.urx.den <= 0 || g->box.ury.den <= 0)
        return -1;
    *out = *g;
    return 0;
}

int safepdf_doc_is_repaired(const safepdf_document *doc) { return doc && (doc->flags & 1); }
int safepdf_doc_is_encrypted(const safepdf_document *doc) { return doc && (doc->flags & 2); }

safepdf_bytes *safepdf_doc_bytes(const safepdf_document *doc) {
    if (!doc) return NULL;
    ensure_thread();
    lean_inc(doc->handle);
    lean_object *a = safepdf_lean_doc_bytes(doc->handle);
    size_t n = lean_sarray_size(a);
    safepdf_bytes *out = calloc(1, sizeof *out);
    uint8_t *data = malloc(n ? n : 1);
    if (!out || !data) { free(out); free(data); lean_dec(a); return NULL; }
    if (n) memcpy(data, lean_sarray_cptr(a), n);
    lean_dec(a);
    out->data = data;
    out->len = n;
    return out;
}

/* ================================================================ v2: open settings */

void safepdf_free_open_settings(safepdf_open_settings *s) {
    if (!s) return;
    free(s->title);
    for (size_t i = 0; i < s->note_count; i++) free(s->notes[i]);
    free(s->notes);
    memset(s, 0, sizeof *s);
}

/* Integer i of an open-settings result (0 past its end). */
static int64_t os_int(lean_object *ints, size_t i) {
    if (8 * (i + 1) > lean_sarray_size(ints)) return 0;
    return (int64_t)rd64le(lean_sarray_cptr(ints) + 8 * i);
}

int safepdf_doc_open_settings(const safepdf_document *doc, safepdf_open_settings *out) {
    if (!out) return -1;
    memset(out, 0, sizeof *out);
    if (!doc) return -1;
    ensure_thread();
    lean_inc(doc->handle);
    lean_object *r = safepdf_lean_doc_open_settings(doc->handle);
    lean_object *ints = lean_ctor_get(r, 0), *strs = lean_ctor_get(r, 1);
    size_t nstr = lean_array_size(strs);
    if (lean_sarray_size(ints) != 22 * 8 || nstr < 1) { lean_dec(r); return -1; }
    out->has_layout = os_int(ints, 0) != 0;
    out->scroll = (uint32_t)os_int(ints, 1);
    out->spread = (uint32_t)os_int(ints, 2);
    out->rtl = os_int(ints, 3) != 0;
    out->page_mode = (int32_t)os_int(ints, 4);
    out->has_dest = os_int(ints, 5) != 0;
    out->dest_page = (size_t)os_int(ints, 6);
    out->has_left = os_int(ints, 7) != 0;
    out->left = (safepdf_rat){ os_int(ints, 8), os_int(ints, 9) };
    out->has_top = os_int(ints, 10) != 0;
    out->top = (safepdf_rat){ os_int(ints, 11), os_int(ints, 12) };
    out->zoom = (safepdf_zoom_choice){ (uint32_t)os_int(ints, 13), (uint32_t)os_int(ints, 14) };
    out->hide_toolbar = os_int(ints, 15) != 0;
    out->hide_menubar = os_int(ints, 16) != 0;
    out->hide_window_ui = os_int(ints, 17) != 0;
    out->fit_window = os_int(ints, 18) != 0;
    out->center_window = os_int(ints, 19) != 0;
    out->display_doc_title = os_int(ints, 20) != 0;
    out->non_full_screen_mode = (int32_t)os_int(ints, 21);
    int ok = 1;
    const char *title = lean_string_cstr(lean_array_get_core(strs, 0));
    if (title[0] && !(out->title = strdup(title))) ok = 0;
    if (ok && nstr > 1) {
        out->notes = calloc(nstr - 1, sizeof *out->notes);
        if (!out->notes) ok = 0;
        for (size_t i = 1; ok && i < nstr; i++) {
            if (!(out->notes[i - 1] = strdup(lean_string_cstr(lean_array_get_core(strs, i))))) ok = 0;
            else out->note_count = i;
        }
    }
    lean_dec(r);
    if (!ok) { safepdf_free_open_settings(out); return -1; }
    return 0;
}

/* ================================================================ tests only */

static void *copy_image(const uint8_t *p, size_t n, size_t w, size_t h);

safepdf_image *safepdf_test_render_sync(safepdf_document *doc, size_t page, uint32_t zoom_num,
                                        uint32_t zoom_den, unsigned rotation, char **error) {
    if (!doc) { set_error(error, strdup("no document")); return NULL; }
    if (rotation > 3) { set_error(error, strdup("rotation must be 0-3 quarter turns")); return NULL; }
    ensure_thread();
    lean_inc(doc->handle);
    lean_object *r = safepdf_lean_doc_test_render(doc->handle, page, zoom_num, zoom_den,
                                                  (uint8_t)rotation);
    if (!lean_io_result_is_ok(r)) {
        set_error(error, error_of(r));
        lean_dec(r);
        return NULL;
    }
    lean_object *a = lean_io_result_get_value(r);
    size_t n = lean_sarray_size(a);
    const uint8_t *b = lean_sarray_cptr(a);
    safepdf_image *img = NULL;
    if (n >= 16) {
        uint64_t w = rd64le(b), h = rd64le(b + 8);
        img = copy_image(b + 16, n - 16, (size_t)w, (size_t)h);
    }
    lean_dec(r);
    if (!img) set_error(error, strdup("malformed or oversized image"));
    return img;
}

/* ================================================================ v2: flat blobs */

/* One table of a blob: rows x cols cells of 8 bytes. */
typedef struct { size_t rows, cols; const uint8_t *cells; } ftab;

/* A parsed blob (layout: SafePdf/Shell/Ffi/Flat.lean). */
typedef struct {
    ftab t[3];
    const uint8_t *pool;
    size_t pool_len;
} fblob;

static uint64_t rd64(const uint8_t *p) {
    uint64_t v = 0;
    for (int i = 7; i >= 0; i--) v = (v << 8) | p[i];
    return v;
}

/* Parses `n` bytes at `p` as `nt` tables with the given column counts. 0 on success. */
static int fblob_parse(const uint8_t *p, size_t n, size_t nt, const size_t *cols, fblob *b) {
    memset(b, 0, sizeof *b);
    if (n < 8 || rd64(p) != nt || nt > 3) return -1;
    size_t off = 8;
    for (size_t i = 0; i < nt; i++) {
        if (n - off < 16) return -1;
        uint64_t rows = rd64(p + off), c = rd64(p + off + 8);
        off += 16;
        if (c != cols[i] || c == 0) return -1;
        if (rows > (n - off) / 8 / c) return -1;
        b->t[i].rows = (size_t)rows;
        b->t[i].cols = (size_t)c;
        b->t[i].cells = p + off;
        off += (size_t)rows * (size_t)c * 8;
    }
    b->pool = p + off;
    b->pool_len = n - off;
    if (b->pool_len > 0 && b->pool[b->pool_len - 1] != 0) return -1;
    return 0;
}

static uint64_t fu(const ftab *t, size_t r, size_t c) {
    return rd64(t->cells + 8 * (r * t->cols + c));
}

static double ff(const ftab *t, size_t r, size_t c) {
    uint64_t bits = fu(t, r, c);
    double d;
    memcpy(&d, &bits, sizeof d);
    return d;
}

/* The string of cell (r, c), a pointer into `pool` (the caller's copy of b->pool). */
static const char *fs(const fblob *b, const char *pool, const ftab *t, size_t r, size_t c) {
    uint64_t off = fu(t, r, c);
    return off < b->pool_len ? pool + off : "";
}

/* A copy of the pool (the strings of a result). */
static char *pool_copy(const fblob *b) {
    char *s = malloc(b->pool_len ? b->pool_len : 1);
    if (s && b->pool_len) memcpy(s, b->pool, b->pool_len);
    return s;
}

static safepdf_box box_at(const ftab *t, size_t r, size_t c) {
    safepdf_box x = { ff(t, r, c), ff(t, r, c + 1), ff(t, r, c + 2), ff(t, r, c + 3) };
    return x;
}

/* The seven action cells starting at column c (Flat.actionFields). */
static safepdf_action action_at(const fblob *b, const char *pool, const ftab *t, size_t r,
                                size_t c) {
    safepdf_action a;
    uint64_t k = fu(t, r, c);
    a.kind = k <= SAFEPDF_ACTION_NONE ? (safepdf_action_kind)k : SAFEPDF_ACTION_NONE;
    a.page = (size_t)fu(t, r, c + 1);
    a.has_left = fu(t, r, c + 2) != 0;
    a.left = ff(t, r, c + 3);
    a.has_top = fu(t, r, c + 4) != 0;
    a.top = ff(t, r, c + 5);
    a.text = fs(b, pool, t, r, c + 6);
    return a;
}

/* malloc of n items of size sz (at least one byte, overflow-checked). */
static void *alloc_n(size_t n, size_t sz) {
    if (n && sz > SIZE_MAX / n) return NULL;
    return calloc(n ? n : 1, sz);
}

/* Fills a layers state from two key tables of `b` (indices i and j). 0 on success. */
static int state_from(const fblob *b, size_t i, size_t j, safepdf_layers_state *st) {
    memset(st, 0, sizeof *st);
    st->known = alloc_n(b->t[i].rows, sizeof *st->known);
    st->off = alloc_n(b->t[j].rows, sizeof *st->off);
    if (!st->known || !st->off) { free(st->known); free(st->off); memset(st, 0, sizeof *st); return -1; }
    st->known_count = b->t[i].rows;
    st->off_count = b->t[j].rows;
    for (size_t r = 0; r < st->known_count; r++) {
        st->known[r].num = fu(&b->t[i], r, 0);
        st->known[r].gen = fu(&b->t[i], r, 1);
    }
    for (size_t r = 0; r < st->off_count; r++) {
        st->off[r].num = fu(&b->t[j], r, 0);
        st->off[r].gen = fu(&b->t[j], r, 1);
    }
    return 0;
}

static safepdf_page_index *build_page_index(const uint8_t *p, size_t n) {
    static const size_t cols[] = { 8, 1 };
    fblob b;
    if (fblob_parse(p, n, 2, cols, &b)) return NULL;
    safepdf_page_index *x = calloc(1, sizeof *x);
    if (!x) return NULL;
    x->strings_ = pool_copy(&b);
    x->cells = alloc_n(b.t[0].rows, sizeof *x->cells);
    x->line_dirs = alloc_n(b.t[1].rows, sizeof *x->line_dirs);
    if (!x->strings_ || !x->cells || !x->line_dirs) { safepdf_free_page_index(x); return NULL; }
    x->cell_count = b.t[0].rows;
    x->line_count = b.t[1].rows;
    for (size_t r = 0; r < x->cell_count; r++) {
        safepdf_cell *c = &x->cells[r];
        c->text = fs(&b, x->strings_, &b.t[0], r, 0);
        c->sep = fs(&b, x->strings_, &b.t[0], r, 1);
        c->box = box_at(&b.t[0], r, 2);
        c->line = (size_t)fu(&b.t[0], r, 6);
        c->hidden = fu(&b.t[0], r, 7) != 0;
    }
    for (size_t r = 0; r < x->line_count; r++) x->line_dirs[r] = (uint32_t)fu(&b.t[1], r, 0);
    return x;
}

static safepdf_link_list *build_links(const uint8_t *p, size_t n) {
    static const size_t cols[] = { 11 };
    fblob b;
    if (fblob_parse(p, n, 1, cols, &b)) return NULL;
    safepdf_link_list *x = calloc(1, sizeof *x);
    if (!x) return NULL;
    x->strings_ = pool_copy(&b);
    x->links = alloc_n(b.t[0].rows, sizeof *x->links);
    if (!x->strings_ || !x->links) { safepdf_free_links(x); return NULL; }
    x->count = b.t[0].rows;
    for (size_t r = 0; r < x->count; r++) {
        x->links[r].box = box_at(&b.t[0], r, 0);
        x->links[r].action = action_at(&b, x->strings_, &b.t[0], r, 4);
    }
    return x;
}

static safepdf_outline *build_outline(const uint8_t *p, size_t n) {
    static const size_t cols[] = { 10 };
    fblob b;
    if (fblob_parse(p, n, 1, cols, &b)) return NULL;
    safepdf_outline *x = calloc(1, sizeof *x);
    if (!x) return NULL;
    x->strings_ = pool_copy(&b);
    x->items = alloc_n(b.t[0].rows, sizeof *x->items);
    if (!x->strings_ || !x->items) { safepdf_free_outline(x); return NULL; }
    x->count = b.t[0].rows;
    for (size_t r = 0; r < x->count; r++) {
        x->items[r].title = fs(&b, x->strings_, &b.t[0], r, 0);
        x->items[r].depth = (size_t)fu(&b.t[0], r, 1);
        x->items[r].is_open = fu(&b.t[0], r, 2) != 0;
        x->items[r].action = action_at(&b, x->strings_, &b.t[0], r, 3);
    }
    return x;
}

static safepdf_label_list *build_labels(const uint8_t *p, size_t n) {
    static const size_t cols[] = { 1 };
    fblob b;
    if (fblob_parse(p, n, 1, cols, &b)) return NULL;
    safepdf_label_list *x = calloc(1, sizeof *x);
    if (!x) return NULL;
    x->strings_ = pool_copy(&b);
    x->labels = alloc_n(b.t[0].rows, sizeof *x->labels);
    if (!x->strings_ || !x->labels) { safepdf_free_labels(x); return NULL; }
    x->count = b.t[0].rows;
    for (size_t r = 0; r < x->count; r++) x->labels[r] = fs(&b, x->strings_, &b.t[0], r, 0);
    return x;
}

/* An optional string (present flag at column c, value at c + 1). */
static const char *opt_s(const fblob *b, const char *pool, const ftab *t, size_t r, size_t c) {
    return fu(t, r, c) ? fs(b, pool, t, r, c + 1) : NULL;
}

static safepdf_attachment_list *build_attachments(const uint8_t *p, size_t n) {
    static const size_t cols[] = { 20, 6, 2 };
    fblob b;
    if (fblob_parse(p, n, 3, cols, &b) || b.t[2].rows != 1) return NULL;
    safepdf_attachment_list *x = calloc(1, sizeof *x);
    if (!x) return NULL;
    x->strings_ = pool_copy(&b);
    x->items = alloc_n(b.t[0].rows, sizeof *x->items);
    x->icons = alloc_n(b.t[1].rows, sizeof *x->icons);
    if (!x->strings_ || !x->items || !x->icons) { safepdf_free_attachments(x); return NULL; }
    x->count = b.t[0].rows;
    x->icon_count = b.t[1].rows;
    const ftab *t = &b.t[0];
    for (size_t r = 0; r < x->count; r++) {
        safepdf_attachment *a = &x->items[r];
        a->name = fs(&b, x->strings_, t, r, 0);
        a->file_name = fs(&b, x->strings_, t, r, 1);
        a->description = opt_s(&b, x->strings_, t, r, 2);
        a->has_size = fu(t, r, 4) != 0;
        a->size = fu(t, r, 5);
        a->mime = opt_s(&b, x->strings_, t, r, 6);
        a->created = opt_s(&b, x->strings_, t, r, 8);
        a->modified = opt_s(&b, x->strings_, t, r, 10);
        a->has_page = fu(t, r, 12) != 0;
        a->page = (size_t)fu(t, r, 13);
        a->in_tree = fu(t, r, 14) != 0;
        a->problem = (int)fu(t, r, 15);
        a->problem_text = fs(&b, x->strings_, t, r, 16);
        a->size_text = fs(&b, x->strings_, t, r, 17);
        a->tooltip = fs(&b, x->strings_, t, r, 18);
        a->has_stream = fu(t, r, 19) != 0;
    }
    for (size_t r = 0; r < x->icon_count; r++) {
        x->icons[r].page = (size_t)fu(&b.t[1], r, 0);
        x->icons[r].rect = box_at(&b.t[1], r, 1);
        x->icons[r].entry = (size_t)fu(&b.t[1], r, 5);
    }
    x->truncated = fu(&b.t[2], 0, 0) != 0;
    x->warnings = (size_t)fu(&b.t[2], 0, 1);
    return x;
}

static safepdf_layers *build_layers(const uint8_t *p, size_t n) {
    static const size_t cols[] = { 8, 2, 2 };
    fblob b;
    if (fblob_parse(p, n, 3, cols, &b)) return NULL;
    safepdf_layers *x = calloc(1, sizeof *x);
    if (!x) return NULL;
    x->strings_ = pool_copy(&b);
    x->rows = alloc_n(b.t[0].rows, sizeof *x->rows);
    if (!x->strings_ || !x->rows || state_from(&b, 1, 2, &x->initial)) {
        safepdf_free_layers(x);
        return NULL;
    }
    x->count = b.t[0].rows;
    for (size_t r = 0; r < x->count; r++) {
        safepdf_layer_row *row = &x->rows[r];
        row->depth = (size_t)fu(&b.t[0], r, 0);
        row->label = fs(&b, x->strings_, &b.t[0], r, 1);
        row->has_group = fu(&b.t[0], r, 2) != 0;
        row->group.num = fu(&b.t[0], r, 3);
        row->group.gen = fu(&b.t[0], r, 4);
        row->italic = fu(&b.t[0], r, 5) != 0;
        row->locked = fu(&b.t[0], r, 6) != 0;
        row->on = fu(&b.t[0], r, 7) != 0;
    }
    return x;
}

static void *copy_bytes(const uint8_t *p, size_t n) {
    safepdf_bytes *x = calloc(1, sizeof *x);
    if (!x) return NULL;
    x->data = malloc(n ? n : 1);
    if (!x->data) { free(x); return NULL; }
    if (n) memcpy(x->data, p, n);
    x->len = n;
    return x;
}

static void *copy_image(const uint8_t *p, size_t n, size_t w, size_t h) {
    if (w && h > SIZE_MAX / 4 / w) return NULL;
    if (n != 4 * w * h) return NULL;
    safepdf_image *x = calloc(1, sizeof *x);
    if (!x) return NULL;
    x->rgba = malloc(n ? n : 1);
    if (!x->rgba) { free(x); return NULL; }
    if (n) memcpy(x->rgba, p, n);
    x->width = w;
    x->height = h;
    x->stride = 4 * w;
    return x;
}

/* The encoded layers state the Lean side reads (Flat.encodeState); NULL: empty (default). */
static lean_object *encode_state(const safepdf_layers_state *st) {
    if (!st) return lean_alloc_sarray(1, 0, 0);
    size_t n = 16 + 16 * (st->known_count + st->off_count);
    lean_object *a = lean_alloc_sarray(1, n, n);
    uint8_t *q = lean_sarray_cptr(a);
    size_t off = 0;
#define PUT(v) do { uint64_t v_ = (uint64_t)(v); for (int i_ = 0; i_ < 8; i_++) q[off++] = (uint8_t)(v_ >> (8 * i_)); } while (0)
    PUT(st->known_count);
    for (size_t i = 0; i < st->known_count; i++) { PUT(st->known[i].num); PUT(st->known[i].gen); }
    PUT(st->off_count);
    for (size_t i = 0; i < st->off_count; i++) { PUT(st->off[i].num); PUT(st->off[i].gen); }
#undef PUT
    return a;
}

/* ================================================================ v2: requests */

enum {
    K_RENDER = 0, K_PAGE_INDEX = 1, K_LINKS = 2, K_OUTLINE = 3, K_LABELS = 4,
    K_ATTACHMENTS = 5, K_ATTACHMENT_BYTES = 6, K_LAYERS = 7
};

/* One submitted request, from submit until its callback has run. */
typedef struct {
    safepdf_document *doc;      /* for the outstanding count only (until delivery) */
    safepdf_request_id id;
    int kind;
    dispatch_queue_t queue;     /* retained */
    union {
        safepdf_render_fn render;
        safepdf_page_index_fn page_index;
        safepdf_links_fn links;
        safepdf_outline_fn outline;
        safepdf_labels_fn labels;
        safepdf_attachments_fn attachments;
        safepdf_bytes_fn bytes;
        safepdf_layers_fn layers;
    } fn;
    void *context;
    safepdf_status status;
    char *error;                /* malloc'd; freed after the callback */
    void *result;               /* owned by the callback */
} request;

/* Runs on the caller's queue. */
static void trampoline(void *p) {
    request *r = p;
    const char *e = r->error;
    switch (r->kind) {
    case K_RENDER: r->fn.render(r->context, r->id, r->status, e, r->result); break;
    case K_PAGE_INDEX: r->fn.page_index(r->context, r->id, r->status, e, r->result); break;
    case K_LINKS: r->fn.links(r->context, r->id, r->status, e, r->result); break;
    case K_OUTLINE: r->fn.outline(r->context, r->id, r->status, e, r->result); break;
    case K_LABELS: r->fn.labels(r->context, r->id, r->status, e, r->result); break;
    case K_ATTACHMENTS: r->fn.attachments(r->context, r->id, r->status, e, r->result); break;
    case K_ATTACHMENT_BYTES: r->fn.bytes(r->context, r->id, r->status, e, r->result); break;
    case K_LAYERS: r->fn.layers(r->context, r->id, r->status, e, r->result); break;
    }
    free(r->error);
    dispatch_release(r->queue);
    free(r);
}

/* Enqueues the callback of `r` and counts it as delivered. */
static void finish(request *r) {
    safepdf_document *doc = r->doc;
    dispatch_async_f(r->queue, r, trampoline);
    pthread_mutex_lock(&doc->mu);
    if (--doc->outstanding == 0) pthread_cond_broadcast(&doc->drained);
    pthread_mutex_unlock(&doc->mu);
}

/* The result struct of a request of kind `k` from its blob (NULL: malformed). */
static void *build(int k, const uint8_t *p, size_t n, size_t w, size_t h) {
    switch (k) {
    case K_RENDER: return copy_image(p, n, w, h);
    case K_PAGE_INDEX: return build_page_index(p, n);
    case K_LINKS: return build_links(p, n);
    case K_OUTLINE: return build_outline(p, n);
    case K_LABELS: return build_labels(p, n);
    case K_ATTACHMENTS: return build_attachments(p, n);
    case K_ATTACHMENT_BYTES: return copy_bytes(p, n);
    case K_LAYERS: return build_layers(p, n);
    }
    return NULL;
}

/* The @[extern] callback of SafePdf.Shell.Ffi.V2.deliver; runs on a Lean task thread. */
LEAN_EXPORT lean_object *safepdf_c_deliver(size_t token, uint8_t status, b_lean_obj_arg msg,
                                           b_lean_obj_arg blob, size_t w, size_t h) {
    request *r = (request *)token;
    if (status == 0) {
        r->result = build(r->kind, lean_sarray_cptr(blob), lean_sarray_size(blob), w, h);
        if (r->result) {
            r->status = SAFEPDF_STATUS_OK;
        } else {
            r->status = SAFEPDF_STATUS_ERROR;
            r->error = strdup("internal error: malformed result (or out of memory)");
        }
    } else if (status == 1) {
        r->status = SAFEPDF_STATUS_ERROR;
        r->error = strdup(lean_string_cstr(msg));
    } else {
        r->status = SAFEPDF_STATUS_CANCELLED;
    }
    finish(r);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Submits a request; returns its id (0 for a NULL document, queue or callback). */
static safepdf_request_id submit(safepdf_document *doc, int kind, size_t page, size_t num,
                                 size_t den, unsigned rot, const safepdf_layers_state *layers,
                                 int prio, dispatch_queue_t queue, void (*fn)(void),
                                 void *context) {
    if (!doc || !queue || !fn) return 0;
    request *r = calloc(1, sizeof *r);
    if (!r) return 0;
    ensure_thread();
    safepdf_request_id id = atomic_fetch_add(&next_request_id, 1);
    r->doc = doc;
    r->id = id;
    r->kind = kind;
    r->queue = queue;
    dispatch_retain(queue);
    memcpy(&r->fn, &fn, sizeof fn);
    r->context = context;
    pthread_mutex_lock(&doc->mu);
    doc->outstanding++;
    pthread_mutex_unlock(&doc->mu);
    uint8_t p8 = prio < 0 ? 0 : prio > 255 ? 255 : (uint8_t)prio;
    uint8_t r8 = rot > 255 ? 255 : (uint8_t)rot;
    lean_inc(doc->handle);
    lean_object *res = safepdf_lean_doc_submit(doc->handle, (size_t)r, id, (uint8_t)kind, page,
                                               num, den, r8, encode_state(layers), p8);
    /* `r` may already be delivered (and freed) here: only `id` is used below. */
    if (!lean_io_result_is_ok(res)) {
        /* Unreachable (submit never throws); delivered here so the count drains. */
        r->status = SAFEPDF_STATUS_ERROR;
        r->error = error_of(res);
        finish(r);
    }
    lean_dec(res);
    return id;
}

typedef void (*generic_fn)(void);

safepdf_request_id safepdf_doc_render(safepdf_document *doc, size_t page, uint32_t zoom_num,
                                      uint32_t zoom_den, unsigned rotation,
                                      const safepdf_layers_state *layers, int priority,
                                      dispatch_queue_t queue, safepdf_render_fn fn,
                                      void *context) {
    return submit(doc, K_RENDER, page, zoom_num, zoom_den, rotation, layers, priority, queue,
                  (generic_fn)fn, context);
}

safepdf_request_id safepdf_doc_page_index(safepdf_document *doc, size_t page,
                                          const safepdf_layers_state *layers, int priority,
                                          dispatch_queue_t queue, safepdf_page_index_fn fn,
                                          void *context) {
    return submit(doc, K_PAGE_INDEX, page, 0, 0, 0, layers, priority, queue, (generic_fn)fn,
                  context);
}

safepdf_request_id safepdf_doc_links(safepdf_document *doc, size_t page, int priority,
                                     dispatch_queue_t queue, safepdf_links_fn fn,
                                     void *context) {
    return submit(doc, K_LINKS, page, 0, 0, 0, NULL, priority, queue, (generic_fn)fn, context);
}

safepdf_request_id safepdf_doc_outline(safepdf_document *doc, int priority,
                                       dispatch_queue_t queue, safepdf_outline_fn fn,
                                       void *context) {
    return submit(doc, K_OUTLINE, 0, 0, 0, 0, NULL, priority, queue, (generic_fn)fn, context);
}

safepdf_request_id safepdf_doc_page_labels(safepdf_document *doc, dispatch_queue_t queue,
                                           safepdf_labels_fn fn, void *context) {
    return submit(doc, K_LABELS, 0, 0, 0, 0, NULL, 0, queue, (generic_fn)fn, context);
}

safepdf_request_id safepdf_doc_attachments(safepdf_document *doc, dispatch_queue_t queue,
                                           safepdf_attachments_fn fn, void *context) {
    return submit(doc, K_ATTACHMENTS, 0, 0, 0, 0, NULL, 0, queue, (generic_fn)fn, context);
}

safepdf_request_id safepdf_doc_attachment_bytes(safepdf_document *doc, size_t index,
                                                dispatch_queue_t queue, safepdf_bytes_fn fn,
                                                void *context) {
    return submit(doc, K_ATTACHMENT_BYTES, index, 0, 0, 0, NULL, 0, queue, (generic_fn)fn,
                  context);
}

safepdf_request_id safepdf_doc_layers(safepdf_document *doc, dispatch_queue_t queue,
                                      safepdf_layers_fn fn, void *context) {
    return submit(doc, K_LAYERS, 0, 0, 0, 0, NULL, 0, queue, (generic_fn)fn, context);
}

void safepdf_doc_cancel(safepdf_document *doc, safepdf_request_id id) {
    if (!doc || !id) return;
    ensure_thread();
    lean_inc(doc->handle);
    lean_dec(safepdf_lean_doc_cancel(doc->handle, id));
}

void safepdf_doc_raise(safepdf_document *doc, safepdf_request_id id, int priority) {
    if (!doc || !id) return;
    ensure_thread();
    uint8_t p8 = priority < 0 ? 0 : priority > 255 ? 255 : (uint8_t)priority;
    lean_inc(doc->handle);
    lean_dec(safepdf_lean_doc_raise(doc->handle, id, p8));
}

int safepdf_layers_toggle(safepdf_document *doc, const safepdf_layers_state *current,
                          size_t row, safepdf_layers_state *out, char **error) {
    if (out) memset(out, 0, sizeof *out);
    if (!doc || !out) { set_error(error, strdup("no document or no output")); return -1; }
    ensure_thread();
    lean_inc(doc->handle);
    lean_object *r = safepdf_lean_doc_layers_toggle(doc->handle, encode_state(current), row);
    if (!lean_io_result_is_ok(r)) {
        set_error(error, error_of(r));
        lean_dec(r);
        return -1;
    }
    lean_object *blob = lean_io_result_get_value(r);
    static const size_t cols[] = { 2, 2 };
    fblob b;
    int rc = fblob_parse(lean_sarray_cptr(blob), lean_sarray_size(blob), 2, cols, &b);
    if (rc == 0) rc = state_from(&b, 0, 1, out);
    lean_dec(r);
    if (rc) { set_error(error, strdup("internal error: malformed layers state")); return -1; }
    return 0;
}

/* ================================================================ v2: the sidebar (11.3d2) */

static uint32_t content_bits(safepdf_sidebar_content c) {
    return (c.has_outline ? 1u : 0u) | (c.has_attachments ? 2u : 0u) | (c.has_layers ? 4u : 0u);
}

static safepdf_panel panel_of(uint32_t p) {
    return p <= SAFEPDF_PANEL_NONE ? (safepdf_panel)p : SAFEPDF_PANEL_NONE;
}

safepdf_panel safepdf_sidebar_on_load(int32_t page_mode, safepdf_sidebar_content c) {
    if (!initialised) return SAFEPDF_PANEL_NONE;
    ensure_thread();
    return panel_of(safepdf_lean_sidebar_on_load((uint32_t)page_mode, content_bits(c)));
}

bool safepdf_sidebar_available(safepdf_panel panel, safepdf_sidebar_content c) {
    if (!initialised) return false;
    ensure_thread();
    return safepdf_lean_sidebar_available((uint32_t)panel, content_bits(c)) != 0;
}

safepdf_panel safepdf_sidebar_pick(safepdf_panel last, safepdf_sidebar_content c) {
    if (!initialised) return SAFEPDF_PANEL_THUMBNAILS;
    ensure_thread();
    return panel_of(safepdf_lean_sidebar_pick((uint32_t)last, content_bits(c)));
}

/* A ByteArray of the 64-bit little-endian numbers `v` (Flat.getU64's layout). */
static lean_object *u64_array(const uint64_t *v, size_t n) {
    lean_object *a = lean_alloc_sarray(1, 8 * n, 8 * n);
    uint8_t *q = lean_sarray_cptr(a);
    for (size_t i = 0; i < n; i++)
        for (int k = 0; k < 8; k++) q[8 * i + k] = (uint8_t)(v[i] >> (8 * k));
    return a;
}

/* Number i of a result ByteArray (0 past its end). */
static uint64_t u64_at(lean_object *a, size_t i) {
    size_t n = lean_sarray_size(a);
    return 8 * i + 8 <= n ? rd64(lean_sarray_cptr(a) + 8 * i) : 0;
}

/* A malloc'd copy of a Lean string result (consumed). */
static char *take_string(lean_object *s) {
    char *out = strdup(lean_string_cstr(s));
    lean_dec(s);
    return out;
}

/* Copies a list (count, then numbers) from result `r` (consumed) into a malloc'd array. */
static int take_list(lean_object *r, size_t **out, size_t *count) {
    *out = NULL;
    *count = 0;
    uint64_t n = u64_at(r, 0);
    if (n > lean_sarray_size(r) / 8) { lean_dec(r); return -1; }
    if (n) {
        size_t *v = malloc((size_t)n * sizeof *v);
        if (!v) { lean_dec(r); return -1; }
        for (size_t i = 0; i < (size_t)n; i++) v[i] = (size_t)u64_at(r, 1 + i);
        *out = v;
        *count = (size_t)n;
    }
    lean_dec(r);
    return 0;
}

int safepdf_sidebar_constants(safepdf_thumb_constants *out) {
    if (!out || !initialised) return -1;
    ensure_thread();
    lean_object *r = safepdf_lean_sidebar_constants(lean_box(0));
    out->width = (uint32_t)u64_at(r, 0);
    out->top = (uint32_t)u64_at(r, 1);
    out->label_h = (uint32_t)u64_at(r, 2);
    out->gap = (uint32_t)u64_at(r, 3);
    out->margin = (uint32_t)u64_at(r, 4);
    out->budget = (uint32_t)u64_at(r, 5);
    lean_dec(r);
    return 0;
}

int safepdf_doc_thumb(const safepdf_document *doc, size_t page, unsigned rotation,
                      safepdf_thumb *out) {
    if (out) memset(out, 0, sizeof *out);
    if (!doc || !out || rotation > 3) return -1;
    ensure_thread();
    lean_inc(doc->handle);
    lean_object *r = safepdf_lean_doc_thumb(doc->handle, page, (uint8_t)rotation);
    int ok = lean_sarray_size(r) == 32;
    if (ok) {
        out->width = (uint32_t)u64_at(r, 0);
        out->height = (uint32_t)u64_at(r, 1);
        out->zoom_num = u64_at(r, 2);
        out->zoom_den = u64_at(r, 3);
        ok = out->zoom_den > 0;
    }
    lean_dec(r);
    if (!ok) { memset(out, 0, sizeof *out); return -1; }
    return 0;
}

unsigned safepdf_sidebar_thumb_scale(size_t w, size_t h) {
    if (!initialised) return 3;
    ensure_thread();
    return (unsigned)safepdf_lean_sidebar_thumb_scale(w, h);
}

int safepdf_sidebar_thumb_layout(const uint32_t *heights, size_t n, uint32_t width, uint64_t *ys,
                                 uint64_t *total) {
    if (!initialised || !total || (n && (!heights || !ys)) || n > (SIZE_MAX / 8 - 1) / 2) return -1;
    uint64_t *v = malloc((1 + 2 * n) * sizeof *v);
    if (!v) return -1;
    v[0] = n;
    for (size_t i = 0; i < n; i++) { v[1 + 2 * i] = width; v[2 + 2 * i] = heights[i]; }
    ensure_thread();
    lean_object *a = u64_array(v, 1 + 2 * n);
    free(v);
    lean_object *r = safepdf_lean_sidebar_thumb_layout(a);
    int rc = u64_at(r, 0) == n && lean_sarray_size(r) == 8 * (n + 2) ? 0 : -1;
    for (size_t i = 0; rc == 0 && i < n; i++) ys[i] = u64_at(r, 1 + i);
    if (rc == 0) *total = u64_at(r, 1 + n);
    lean_dec(r);
    return rc;
}

int safepdf_sidebar_thumbs_wanted(const uint32_t *heights, size_t n, uint32_t width,
                                  uint64_t top, uint64_t bottom, size_t **out, size_t *count) {
    if (!out || !count) return -1;
    *out = NULL;
    *count = 0;
    if (!initialised || (n && !heights) || n > (SIZE_MAX / 8 - 3) / 2) return -1;
    uint64_t *v = malloc((3 + 2 * n) * sizeof *v);
    if (!v) return -1;
    v[0] = n;
    for (size_t i = 0; i < n; i++) { v[1 + 2 * i] = width; v[2 + 2 * i] = heights[i]; }
    v[1 + 2 * n] = top;
    v[2 + 2 * n] = bottom;
    ensure_thread();
    lean_object *a = u64_array(v, 3 + 2 * n);
    free(v);
    return take_list(safepdf_lean_sidebar_thumbs_wanted(a), out, count);
}

int safepdf_sidebar_thumb_evict(const size_t *held, size_t nheld, const size_t *wanted,
                                size_t nwanted, size_t center, size_t **out, size_t *count) {
    if (!out || !count) return -1;
    *out = NULL;
    *count = 0;
    if (!initialised || (nheld && !held) || (nwanted && !wanted) ||
        nheld > SIZE_MAX / 16 || nwanted > SIZE_MAX / 16) return -1;
    size_t m = 3 + nheld + nwanted;
    uint64_t *v = malloc(m * sizeof *v);
    if (!v) return -1;
    size_t k = 0;
    v[k++] = nheld;
    for (size_t i = 0; i < nheld; i++) v[k++] = held[i];
    v[k++] = nwanted;
    for (size_t i = 0; i < nwanted; i++) v[k++] = wanted[i];
    v[k++] = center;
    ensure_thread();
    lean_object *a = u64_array(v, m);
    free(v);
    return take_list(safepdf_lean_sidebar_thumb_evict(a), out, count);
}

int safepdf_sidebar_tree(const size_t *depths, const bool *open, size_t n,
                         safepdf_tree_row *out) {
    if (!initialised || (n && (!depths || !open || !out)) || n > (SIZE_MAX / 8 - 1) / 2) return -1;
    if (n == 0) return 0;
    uint64_t *v = malloc((1 + 2 * n) * sizeof *v);
    if (!v) return -1;
    v[0] = n;
    for (size_t i = 0; i < n; i++) { v[1 + 2 * i] = depths[i]; v[2 + 2 * i] = open[i] ? 1 : 0; }
    ensure_thread();
    lean_object *a = u64_array(v, 1 + 2 * n);
    free(v);
    lean_object *r = safepdf_lean_sidebar_tree(a);
    int rc = lean_sarray_size(r) == 24 * n ? 0 : -1;
    for (size_t i = 0; rc == 0 && i < n; i++) {
        uint64_t p = u64_at(r, 3 * i);
        out[i].parent = p == 0 || p > n ? -1 : (int64_t)(p - 1);
        out[i].has_kids = u64_at(r, 3 * i + 1) != 0;
        out[i].open = u64_at(r, 3 * i + 2) != 0;
    }
    lean_dec(r);
    return rc;
}

char *safepdf_attachment_target_problem(const char *name, bool is_dir, bool exists,
                                        bool file_writable, bool dir_writable, bool opened) {
    if (!initialised) return strdup("the core is not initialised");
    ensure_thread();
    uint32_t flags = (is_dir ? 1u : 0u) | (exists ? 2u : 0u) | (file_writable ? 4u : 0u) |
                     (dir_writable ? 8u : 0u) | (opened ? 16u : 0u);
    char *s = take_string(safepdf_lean_attachment_target_problem(lean_mk_string(name ? name : ""),
                                                                 flags));
    if (s && !*s) { free(s); return NULL; }
    return s;
}

char *safepdf_attachment_size_after(const safepdf_attachment *a, bool ok, uint64_t decoded) {
    if (!a || !initialised) return NULL;
    ensure_thread();
    return take_string(safepdf_lean_attachment_size_after(a->has_size ? 1 : 0, a->size,
                                                          a->has_stream ? 1 : 0, ok ? 1 : 0,
                                                          decoded));
}

char *safepdf_action_describe(const safepdf_action *a, const char *const *labels, size_t nlabels,
                              size_t pages) {
    if (!a || !initialised) return NULL;
    ensure_thread();
    lean_object *arr = lean_alloc_array(nlabels, nlabels);
    for (size_t i = 0; i < nlabels; i++)
        lean_array_cptr(arr)[i] = lean_mk_string(labels && labels[i] ? labels[i] : "");
    return take_string(safepdf_lean_action_describe(arr, pages, (uint8_t)a->kind, a->page,
                                                    lean_mk_string(a->text ? a->text : "")));
}

char *safepdf_identity_line(const char *path, bool in_memory) {
    if (!initialised) return NULL;
    ensure_thread();
    return take_string(safepdf_lean_identity_line(lean_mk_string(path ? path : ""), path ? 1 : 0,
                                                  in_memory ? 1 : 0));
}

/* ================================================================ v2: frees */

void safepdf_free_image(safepdf_image *image) {
    if (!image) return;
    free(image->rgba);
    free(image);
}

void safepdf_free_page_index(safepdf_page_index *x) {
    if (!x) return;
    free(x->cells);
    free(x->line_dirs);
    free(x->strings_);
    free(x);
}

void safepdf_free_links(safepdf_link_list *x) {
    if (!x) return;
    free(x->links);
    free(x->strings_);
    free(x);
}

void safepdf_free_outline(safepdf_outline *x) {
    if (!x) return;
    free(x->items);
    free(x->strings_);
    free(x);
}

void safepdf_free_labels(safepdf_label_list *x) {
    if (!x) return;
    free((void *)x->labels);
    free(x->strings_);
    free(x);
}

void safepdf_free_attachments(safepdf_attachment_list *x) {
    if (!x) return;
    free(x->items);
    free(x->icons);
    free(x->strings_);
    free(x);
}

void safepdf_free_bytes(safepdf_bytes *x) {
    if (!x) return;
    free(x->data);
    free(x);
}

void safepdf_free_layers_state(safepdf_layers_state *st) {
    if (!st) return;
    free(st->known);
    free(st->off);
    memset(st, 0, sizeof *st);
}

void safepdf_free_layers(safepdf_layers *x) {
    if (!x) return;
    free(x->rows);
    safepdf_free_layers_state(&x->initial);
    free(x->strings_);
    free(x);
}
