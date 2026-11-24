/*
 * safepdf_marks.h — C API v2: user marks, Save and XFDF (task 11.3a3).
 *
 * Plain C: no Lean types leak through. Implemented in safepdf_marks.c over the Lean exports
 * of SafePdf/Shell/FfiMarks.lean, which call the Tk viewer's own marks model
 * (SafePdf/Shell/App/Marks.lean), save flow (Save.lean, C7) and XFDF reader/writer (Xfdf.lean):
 * nothing is reimplemented here (docs/macos-design.md §3, decisions 1 and 2). Link with
 * libsafepdfffi.a (`lake build macosFfi`) and Lean's runtime (see macos/build.sh).
 *
 * The store
 *   A safepdf_marks is the marks store of one document: created from the document's bytes
 *   (the bytes the GUI read through its capped read; Lean does no file I/O here), it lists the
 *   marks already saved in the file as saved. Edits are recorded for undo/redo. It is
 *   reference counted (create = 1 reference; safepdf_marks_retain / safepdf_marks_release),
 *   and every call locks it, so it may be used from several threads (each registered with
 *   safepdf_thread_enter, see safepdf_core.h).
 *
 * Save stays in the GUI process
 *   safepdf_marks_save_build returns the bytes of the incremental update (the original bytes
 *   are a prefix, C7; checked by a strict reopen and read-back of every mark). The GUI writes
 *   them (atomically), then creates a new store from the written bytes (the Tk viewer reopens
 *   the written file the same way; undo history starts afresh). The GUI owns the output
 *   budget: pass a ceiling (`max_output`), compare with safepdf_marks_output_estimate first.
 *
 * Ownership
 *   - Every struct a call fills is owned by the caller and released with its safepdf_free_*
 *     function (one per struct type); returned `char *` strings and `*error` strings are
 *     malloc'd, release them with free(). `*error` is set only when the call fails and only
 *     when `error` is not NULL.
 *   - Input strings (UTF-8; invalid sequences become U+FFFD) and buffers are borrowed for the
 *     duration of the call.
 *
 * Coordinates are page space (points, origin bottom left, as the PDF). They must be finite
 * with magnitude at most 2^32 (else the call fails); they are taken exactly.
 * Mark ids are > 0; 0 means "none".
 */
#ifndef SAFEPDF_MARKS_H
#define SAFEPDF_MARKS_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/** The marks store of one document (opaque, reference counted). */
typedef struct safepdf_marks safepdf_marks;

/** Highlight palette (PDF.js's five colours, Marks.Color.all order). */
enum {
    SAFEPDF_COLOR_YELLOW = 0, /* #FFFF98 */
    SAFEPDF_COLOR_GREEN = 1,  /* #53FFBC */
    SAFEPDF_COLOR_BLUE = 2,   /* #80EBFF */
    SAFEPDF_COLOR_PINK = 3,   /* #FFCBE6 */
    SAFEPDF_COLOR_RED = 4     /* #FF4F5F */
};

/** Mark kinds. */
enum {
    SAFEPDF_MARK_HIGHLIGHT = 0,
    SAFEPDF_MARK_NOTE = 1,
    SAFEPDF_MARK_FREETEXT = 2,
    SAFEPDF_MARK_INK = 3
};

/** Whether a mark is in the file. */
enum {
    SAFEPDF_MARK_NEW = 0,          /* not saved yet */
    SAFEPDF_MARK_SAVED = 1,        /* in the file, unchanged */
    SAFEPDF_MARK_SAVED_CHANGED = 2 /* in the file, edited since (Save supersedes it) */
};

/** A page-space box. */
typedef struct { double llx, lly, urx, ury; } safepdf_box;

/** A page-space point. */
typedef struct { double x, y; } safepdf_point;

/** One mark, as listed. */
typedef struct {
    uint64_t id;
    int kind;              /* SAFEPDF_MARK_* */
    size_t page;           /* 0-based */
    int color;             /* SAFEPDF_COLOR_* (highlights and notes; free text/ink: unused) */
    uint8_t r, g, b;       /* the colour to draw it in (palette, or free text/ink's own) */
    int state;             /* SAFEPDF_MARK_NEW / _SAVED / _SAVED_CHANGED */
    int is_comment;        /* a note that is a highlight's comment (Save folds it into it) */
    char *text;            /* note / free text (UTF-8, NUL-terminated; "" for none) */
    size_t text_len;       /* bytes, without the terminator (text may contain NUL) */
    uint32_t size;         /* free text font size, ink thickness; else 0 */
    uint32_t opacity;      /* ink opacity percent; else 100 */
    int has_point;         /* note anchored at a point / free text's upper-left corner */
    safepdf_point point;
    int has_rect;          /* the /Rect Save writes: note icon box, quads' union, box */
    safepdf_box rect;
    safepdf_box *quads;    /* highlight quads, or the quads a note is anchored to */
    size_t quad_count;
    size_t *stroke_lengths; /* ink: points per stroke */
    size_t stroke_count;
    safepdf_point *points; /* ink: all strokes' points, in order */
    size_t point_count;
} safepdf_mark;

/** A list of marks, oldest first (later ones are drawn on top). */
typedef struct {
    safepdf_mark *marks;
    size_t count;
} safepdf_mark_list;

/** The store's state (title `*`, Undo/Redo menu enabling, Save enabling). */
typedef struct {
    int can_undo, can_redo;
    int dirty;              /* unsaved changes (new, changed or deleted saved marks) */
    size_t pending;         /* their number (new + changed + deleted) */
    size_t new_count, changed_count, deleted_saved_count;
    size_t undo_depth, redo_depth;
    int encrypted;          /* Save needs a 64-byte IV seed */
    size_t page_count;
    size_t mark_count;
} safepdf_marks_state;

/** A byte buffer. */
typedef struct {
    uint8_t *data;
    size_t size;
} safepdf_bytes;

/** Save note flags (safepdf_save_result.flags). */
enum {
    SAFEPDF_SAVE_NOTE_RC4 = 1,       /* legacy RC4 encryption kept (written with a note) */
    SAFEPDF_SAVE_NOTE_SIGNED = 2,    /* signed input: the signature covers the old revision */
    SAFEPDF_SAVE_NOTE_RETENTION = 4, /* deleted saved marks stay in the earlier revision */
    SAFEPDF_SAVE_NOTE_COPY = 8       /* nothing to write: the bytes are the original's */
};

/** Save results (safepdf_marks_save_build's return value). */
enum {
    SAFEPDF_SAVE_OK = 0,
    SAFEPDF_SAVE_ERR_BUILD = 1,        /* the update failed to build or its check failed */
    SAFEPDF_SAVE_ERR_CERTIFIED = 2,    /* /DocMDP P1/P2: refused, export XFDF instead */
    SAFEPDF_SAVE_ERR_NEED_SEED = 3,    /* encrypted document without 64 random IV bytes */
    SAFEPDF_SAVE_ERR_OUTPUT_LIMIT = 4, /* the estimate exceeds max_output */
    SAFEPDF_SAVE_ERR_NO_MEMORY = 5
};

/** What a save built. */
typedef struct {
    uint8_t *bytes;        /* the file to write (malloc'd) */
    size_t size;
    size_t marks_written;  /* marks added, changed or deleted by this update */
    size_t marks_total;    /* marks in the written file (read back) */
    size_t appended;       /* bytes appended to the original */
    uint32_t flags;        /* SAFEPDF_SAVE_NOTE_* */
    size_t deleted_saved;  /* saved marks deleted (the retention note's count) */
    char **notes;          /* the notes to show, in order (UTF-8) */
    size_t note_count;
} safepdf_save_result;

/** What an XFDF import did. The store is changed (one undo step) only when added > 0. */
typedef struct {
    size_t added, already_present, skipped, ignored;
    char **skip_elements;  /* the first skipped annotations (at most 100): element name */
    char **skip_reasons;   /* ... and why */
    size_t skip_count;
} safepdf_xfdf_import;

/** Disk states (safepdf_marks_disk_state). */
enum { SAFEPDF_DISK_SAME = 0, SAFEPDF_DISK_CHANGED = 1, SAFEPDF_DISK_MISSING = 2 };

/** Save routes (safepdf_marks_save_route). */
enum {
    SAFEPDF_ROUTE_NOTHING = 0,       /* nothing unsaved */
    SAFEPDF_ROUTE_LIBRARY = 1,       /* save to the library */
    SAFEPDF_ROUTE_SAVE_AS = 2,       /* opened from memory: Save As... */
    SAFEPDF_ROUTE_OVERWRITE = 3,     /* write into the opened file */
    SAFEPDF_ROUTE_OVERWRITE_ASK = 4  /* first ask Overwrite / Save As... / Cancel */
};

/** Note anchors (safepdf_marks_note_anchor, safepdf_marks_add_note). */
enum {
    SAFEPDF_ANCHOR_NONE = 0,  /* no selection, no click: the caller picks the window centre */
    SAFEPDF_ANCHOR_QUADS = 1, /* the selection's quads (a comment on that text) */
    SAFEPDF_ANCHOR_POINT = 2  /* the clicked point */
};

/** Closing a note popup without Save (safepdf_marks_note_close). */
enum { SAFEPDF_NOTE_KEEP = 0, SAFEPDF_NOTE_SAVE = 1, SAFEPDF_NOTE_DELETE = 2 };

/* ---- Lifetime ---------------------------------------------------------------------- */

/** Initialise the marks module (calls safepdf_init first, which is idempotent). Once, on the
    main thread. 0 on success. Idempotent. */
int safepdf_marks_init(void);

/** Create the store of the PDF `bytes` (its saved marks listed as saved). NULL on failure
    with `*error` set (the core's message). */
safepdf_marks *safepdf_marks_create(const uint8_t *bytes, size_t len, char **error);

/** Add a reference; returns `m`. */
safepdf_marks *safepdf_marks_retain(safepdf_marks *m);

/** Drop a reference (the last one frees the store). NULL is allowed. */
void safepdf_marks_release(safepdf_marks *m);

/* ---- Queries ------------------------------------------------------------------------- */

/** The store's state. */
void safepdf_marks_get_state(safepdf_marks *m, safepdf_marks_state *out);

/** The marks of `page`. 0 on success, -1 on failure (out of memory). */
int safepdf_marks_list(safepdf_marks *m, size_t page, safepdf_mark_list *out, char **error);

/** The marks of every page. */
int safepdf_marks_list_all(safepdf_marks *m, safepdf_mark_list *out, char **error);

/** Release a list's contents and zero it. NULL is allowed. */
void safepdf_free_mark_list(safepdf_mark_list *list);

/** The topmost mark of `page` under page point (x, y) (note icons first); 0 when none. */
uint64_t safepdf_marks_hit_at(safepdf_marks *m, size_t page, double x, double y);

/** Where a new note anchors (Marks.noteAnchor): `sel` the boxes of the current selection on
    the page in question (may be empty), `click` the clicked page point or NULL (menu / bubble).
    SAFEPDF_ANCHOR_*; -1 on bad numbers. Needs no store. */
int safepdf_marks_note_anchor(const safepdf_box *sel, size_t sel_count, const safepdf_point *click);

/** What closing note `id`'s popup without Save does when it shows `shown`: SAFEPDF_NOTE_KEEP,
    _SAVE (call safepdf_marks_set_text with `shown`) or _DELETE (safepdf_marks_delete). */
int safepdf_marks_note_close(safepdf_marks *m, uint64_t id, const char *shown);

/* ---- Edits (each one undo step; 0 on success, -1 with *error) ------------------------ */

/** Highlight over `quads` in palette colour `color`; `*id` the new mark (may be NULL). */
int safepdf_marks_add_highlight(safepdf_marks *m, size_t page, int color, const safepdf_box *quads,
                                size_t quad_count, uint64_t *id, char **error);

/** Note with `text`: `anchor` SAFEPDF_ANCHOR_POINT at `*point`, or SAFEPDF_ANCHOR_QUADS on
    `quads` (from safepdf_marks_note_anchor). */
int safepdf_marks_add_note(safepdf_marks *m, size_t page, int color, const char *text, int anchor,
                           const safepdf_point *point, const safepdf_box *quads, size_t quad_count,
                           uint64_t *id, char **error);

/** The comment of highlight `highlight`: its existing comment note (`*id`, nothing changes),
    else a new note with `text` on exactly its quads, in its colour. */
int safepdf_marks_add_comment(safepdf_marks *m, uint64_t highlight, const char *text, uint64_t *id,
                              char **error);

/** Free text with its box's upper-left corner at (x, y), font size 5..100, colour 0xRRGGBB. */
int safepdf_marks_add_free_text(safepdf_marks *m, size_t page, const char *text, double x, double y,
                                uint32_t size, uint32_t rgb, uint64_t *id, char **error);

/** Ink with one stroke (at least one point), thickness 1..20, opacity 0..100 %, 0xRRGGBB. */
int safepdf_marks_add_ink(safepdf_marks *m, size_t page, const safepdf_point *points, size_t count,
                          uint32_t width, uint32_t opacity, uint32_t rgb, uint64_t *id, char **error);

/** Append a stroke to ink `id` (one drawing session = one mark). */
int safepdf_marks_add_stroke(safepdf_marks *m, uint64_t id, const safepdf_point *points,
                             size_t count, char **error);

/** Replace the text of note or free text `id` (unchanged text: no undo step). */
int safepdf_marks_set_text(safepdf_marks *m, uint64_t id, const char *text, char **error);

/** Recolour highlight or note `id` (palette colour). */
int safepdf_marks_recolor(safepdf_marks *m, uint64_t id, int color, char **error);

/** Free text / ink: colour, size (font size or thickness), opacity (ink), move by (dx, dy).
    `merge` != 0 joins the current slider drag's undo step; safepdf_marks_seal ends it. */
int safepdf_marks_set_rgb(safepdf_marks *m, uint64_t id, uint32_t rgb, int merge, char **error);
int safepdf_marks_set_size(safepdf_marks *m, uint64_t id, uint32_t size, int merge, char **error);
int safepdf_marks_set_opacity(safepdf_marks *m, uint64_t id, uint32_t opacity, int merge,
                              char **error);
int safepdf_marks_translate(safepdf_marks *m, uint64_t id, double dx, double dy, int merge,
                            char **error);

/** Close the open merge step (slider released). */
void safepdf_marks_seal(safepdf_marks *m);

/** Delete mark `id` (a highlight's comment goes with it). */
int safepdf_marks_delete(safepdf_marks *m, uint64_t id, char **error);

/** Undo / redo one step; -1 with *error "nothing to undo" / "nothing to redo". */
int safepdf_marks_undo(safepdf_marks *m, char **error);
int safepdf_marks_redo(safepdf_marks *m, char **error);

/* ---- Save -------------------------------------------------------------------------- */

/** Upper bound of the saved file's size (the GUI's budget reservation). */
size_t safepdf_marks_output_estimate(safepdf_marks *m);

/** Build the file Save writes for the store's changes. `iv_seed`: fresh random bytes for the
    AES IVs, at least 64 for an encrypted document (else SAFEPDF_SAVE_ERR_NEED_SEED), ignored
    otherwise. `date`: a PDF date "D:YYYYMMDDHHmmSSZ", or NULL / "" for now. `max_output`: 0
    for no ceiling. Returns SAFEPDF_SAVE_OK with `*out` filled, else a SAFEPDF_SAVE_ERR_*
    code with `*error` set and `*out` zeroed. */
int safepdf_marks_save_build(safepdf_marks *m, const uint8_t *iv_seed, size_t seed_len,
                             const char *date, size_t max_output, safepdf_save_result *out,
                             char **error);

/** Release a save result's contents and zero it. NULL is allowed. */
void safepdf_free_save_result(safepdf_save_result *r);

/** Does the file on disk still hold the bytes the store was created from? `disk` the bytes
    the GUI read back (read at most the original size + 1), or NULL when it could not be read.
    SAFEPDF_DISK_*. */
int safepdf_marks_disk_state(safepdf_marks *m, const uint8_t *disk, size_t len);

/** Save's route (Save.route): SAFEPDF_ROUTE_*. `confirmed`: this session already wrote the
    file, or the user agreed in the unsaved-changes prompt. Needs no store. */
int safepdf_marks_save_route(int dirty, int library, int in_memory, int confirmed);

/** Dialog texts and checks (malloc'd; free()). */
char *safepdf_marks_overwrite_question(safepdf_marks *m, const char *name);
char *safepdf_marks_changed_question(const char *name, int disk_state);
char *safepdf_marks_unsaved_question(safepdf_marks *m, const char *name, const char *what,
                                     int library, int in_memory, int into);
/** NULL when the opened file can be overwritten. */
char *safepdf_marks_write_problem(const char *name, int file_writable, int dir_writable);
/** NULL when a Save As... / Export target can be written. */
char *safepdf_marks_target_problem(const char *name, int is_dir, int exists, int file_writable,
                                   int dir_writable, int is_opened_document);
/** STEM-annotated.pdf next to `path`. */
char *safepdf_marks_default_target(const char *path);
/** `name` with ".ext" unless it already ends so (any case). */
char *safepdf_marks_with_ext(const char *name, const char *ext);

/* ---- XFDF -------------------------------------------------------------------------- */

/** Upper bound of the export's size. */
size_t safepdf_marks_xfdf_estimate(safepdf_marks *m);

/** Every mark as XFDF (UTF-8). `href`: the PDF's file name for <f href> (NULL: none); `date`
    as for save (NULL: now); `max_output` 0: no ceiling. 0 on success, -1 with *error. */
int safepdf_marks_xfdf_export(safepdf_marks *m, const char *href, const char *date,
                              size_t max_output, safepdf_bytes *out, char **error);

/** Release a byte buffer and zero it. NULL is allowed. */
void safepdf_free_bytes(safepdf_bytes *b);

/** Import XFDF `bytes` (bounded reader: no DTDs or entities, limits on size, depth, nodes,
    marks; pages checked against the document). Marks already present are not added again.
    0 on success, -1 with *error when the file is refused (the store is unchanged). */
int safepdf_marks_xfdf_import(safepdf_marks *m, const uint8_t *bytes, size_t len,
                              safepdf_xfdf_import *out, char **error);

/** Release an import report's contents and zero it. NULL is allowed. */
void safepdf_free_xfdf_import(safepdf_xfdf_import *r);

#ifdef __cplusplus
}
#endif

#endif /* SAFEPDF_MARKS_H */
