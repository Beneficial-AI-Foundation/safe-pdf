/*
 * safepdf_core.h — a first, minimal C API over safe-pdf-core (task 11.1, AppKit spike).
 *
 * Plain C: no Lean types leak through. Implemented in safepdf_core.c over the Lean
 * exports of SafePdf/Shell/Ffi.lean; link with libsafepdfffi.a (`lake build macosFfi`) and
 * Lean's runtime libraries (see macos/build.sh).
 *
 * Ownership rules
 *   - safepdf_open returns a document the caller owns; release it with safepdf_close.
 *   - safepdf_render fills a safepdf_image whose `rgba` buffer the caller owns (malloc'd);
 *     release it with safepdf_image_free (or free(img->rgba)).
 *   - Error strings (`char **error` out-parameters) are malloc'd; release with free().
 *     They are set only when the call fails, and only when `error` is not NULL.
 *   - Input strings and pointers are borrowed for the duration of the call.
 *
 * Threads
 *   - safepdf_init must run once, on the main thread, before any other call.
 *   - A document may be used from several threads at once (it is marked thread-shared).
 *   - Every thread other than the one that called safepdf_init must call
 *     safepdf_thread_enter before its first call and safepdf_thread_exit when done.
 *   - Each call runs on the calling thread and blocks until done (a render can take
 *     hundreds of milliseconds): call safepdf_render off the UI thread.
 */
#ifndef SAFEPDF_CORE_H
#define SAFEPDF_CORE_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/** An open document (opaque). */
typedef struct safepdf_doc safepdf_doc;

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

/** Register / unregister the calling (non-main) thread with the Lean runtime. */
void safepdf_thread_enter(void);
void safepdf_thread_exit(void);

/** Open the PDF at `path` (UTF-8). NULL on failure, with `*error` set. */
safepdf_doc *safepdf_open(const char *path, char **error);

/** Release a document. NULL is allowed. */
void safepdf_close(safepdf_doc *doc);

/** Number of pages. */
size_t safepdf_page_count(const safepdf_doc *doc);

/** Displayed size of page `page` (0-based) in points (CropBox, /Rotate applied).
    0 on success, -1 when `page` is out of range. */
int safepdf_page_size(const safepdf_doc *doc, size_t page, double *width, double *height);

/** Render page `page` at zoom `zoom_num / zoom_den` pixels per point (1 = 72 dpi).
    0 on success (`*out` filled), -1 on failure (`*error` set, `*out` zeroed). */
int safepdf_render(const safepdf_doc *doc, size_t page, uint32_t zoom_num, uint32_t zoom_den,
                   safepdf_image *out, char **error);

/** Release the buffer of a rendered image and zero it. NULL is allowed. */
void safepdf_image_free(safepdf_image *img);

#ifdef __cplusplus
}
#endif

#endif /* SAFEPDF_CORE_H */
