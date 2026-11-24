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
extern lean_object *safepdf_lean_doc_submit(lean_object *d, size_t token, uint64_t cid,
                                            uint8_t kind, size_t page, size_t num, size_t den,
                                            uint8_t rot, lean_object *layers, uint8_t prio);
extern lean_object *safepdf_lean_doc_cancel(lean_object *d, uint64_t cid);
extern lean_object *safepdf_lean_doc_raise(lean_object *d, uint64_t cid, uint8_t prio);
extern lean_object *safepdf_lean_doc_shutdown(lean_object *d);
extern lean_object *safepdf_lean_doc_layers_toggle(lean_object *d, lean_object *state,
                                                   size_t row);

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
    static const size_t cols[] = { 17, 6, 2 };
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
