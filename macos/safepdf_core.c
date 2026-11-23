/*
 * safepdf_core.c — the C API of safepdf_core.h over the Lean exports of
 * SafePdf/Shell/Ffi.lean (task 11.1, AppKit spike).
 *
 * Reference counting: Lean v4.36 `@[export]` functions take every object argument as
 * OWNED (they consume one reference), so each call below that keeps using an object
 * afterwards first adds a reference with lean_inc. Every object a Lean function returns is
 * owned here and released with lean_dec once its contents are copied out.
 */
#include "safepdf_core.h"

#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

/* Lean runtime and module initialisers (not declared in lean.h). */
extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern lean_object *initialize_safe_x2dpdf_SafePdf_Shell_Ffi(uint8_t builtin);

/* Lean exports (SafePdf/Shell/Ffi.lean). */
extern lean_object *safepdf_lean_open(lean_object *path);
extern size_t safepdf_lean_page_count(lean_object *h);
extern lean_object *safepdf_lean_page_size(lean_object *h, size_t i);
extern lean_object *safepdf_lean_render(lean_object *h, size_t i, size_t num, size_t den);
extern size_t safepdf_lean_image_width(lean_object *img);
extern size_t safepdf_lean_image_height(lean_object *img);
extern lean_object *safepdf_lean_image_data(lean_object *img);
extern lean_object *safepdf_lean_error_text(lean_object *e);

struct safepdf_doc {
    lean_object *handle; /* SafePdf.Shell.Ffi.Handle, one reference owned, thread-shared */
    size_t pages;
    double *sizes;       /* 2 * pages: width, height in points (-1 when unknown) */
};

static int initialised = 0;

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
    initialised = 1;
    return 0;
}

void safepdf_thread_enter(void) { lean_initialize_thread(); }
void safepdf_thread_exit(void) { lean_finalize_thread(); }

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

safepdf_doc *safepdf_open(const char *path, char **error) {
    lean_object *r = safepdf_lean_open(lean_mk_string(path));
    if (!lean_io_result_is_ok(r)) {
        set_error(error, error_of(r));
        lean_dec(r);
        return NULL;
    }
    lean_object *h = lean_io_result_get_value(r);
    lean_inc(h);
    lean_dec(r);
    /* The document is shared with render threads: switch its whole object graph to
       atomic reference counts before any other thread can see it. */
    lean_mark_mt(h);
    safepdf_doc *doc = calloc(1, sizeof *doc);
    if (!doc) { lean_dec(h); set_error(error, strdup("out of memory")); return NULL; }
    doc->handle = h;
    lean_inc(h);
    doc->pages = safepdf_lean_page_count(h);
    doc->sizes = malloc(sizeof(double) * 2 * (doc->pages ? doc->pages : 1));
    for (size_t i = 0; i < doc->pages; i++) {
        lean_inc(h);
        lean_object *a = safepdf_lean_page_size(h, i);
        if (lean_sarray_size(a) == 2) {
            doc->sizes[2 * i] = lean_float_array_cptr(a)[0];
            doc->sizes[2 * i + 1] = lean_float_array_cptr(a)[1];
        } else {
            doc->sizes[2 * i] = doc->sizes[2 * i + 1] = -1;
        }
        lean_dec(a);
    }
    return doc;
}

void safepdf_close(safepdf_doc *doc) {
    if (!doc) return;
    lean_dec(doc->handle);
    free(doc->sizes);
    free(doc);
}

size_t safepdf_page_count(const safepdf_doc *doc) { return doc->pages; }

int safepdf_page_size(const safepdf_doc *doc, size_t page, double *width, double *height) {
    if (page >= doc->pages || doc->sizes[2 * page] < 0) return -1;
    if (width) *width = doc->sizes[2 * page];
    if (height) *height = doc->sizes[2 * page + 1];
    return 0;
}

int safepdf_render(const safepdf_doc *doc, size_t page, uint32_t zoom_num, uint32_t zoom_den,
                   safepdf_image *out, char **error) {
    memset(out, 0, sizeof *out);
    lean_inc(doc->handle);
    lean_object *r = safepdf_lean_render(doc->handle, page, zoom_num, zoom_den);
    if (!lean_io_result_is_ok(r)) {
        set_error(error, error_of(r));
        lean_dec(r);
        return -1;
    }
    lean_object *img = lean_io_result_get_value(r);
    lean_inc(img); lean_inc(img); lean_inc(img);
    lean_dec(r);
    size_t w = safepdf_lean_image_width(img);
    size_t h = safepdf_lean_image_height(img);
    lean_object *data = safepdf_lean_image_data(img); /* consumes the last reference */
    size_t n = lean_sarray_size(data);
    if (n != 4 * w * h) { /* renderPage_size: cannot happen */
        lean_dec(data);
        set_error(error, strdup("internal error: image size mismatch"));
        return -1;
    }
    uint8_t *buf = malloc(n ? n : 1);
    if (!buf) { lean_dec(data); set_error(error, strdup("out of memory")); return -1; }
    memcpy(buf, lean_sarray_cptr(data), n);
    lean_dec(data);
    out->rgba = buf;
    out->width = w;
    out->height = h;
    out->stride = 4 * w;
    return 0;
}

void safepdf_image_free(safepdf_image *img) {
    if (!img) return;
    free(img->rgba);
    memset(img, 0, sizeof *img);
}
