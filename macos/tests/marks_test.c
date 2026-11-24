/*
 * marks_test.c — tests of the C API v2 for marks, Save and XFDF (task 11.3a3,
 * macos/safepdf_marks.h). Built and run by macos/tests/run_marks.sh:
 *
 *   marks_test PLAIN.pdf AES.pdf RC4.pdf OUTDIR
 *
 * Writes OUTDIR/saved.pdf (the first save, for an external `qpdf --check`) and
 * OUTDIR/export.xfdf. Exit status 0 when every check passes. Never opens a window.
 */
#include "../safepdf_marks.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;
static int checks = 0;

#define CHECK(cond, ...)                                              \
    do {                                                              \
        checks++;                                                     \
        if (!(cond)) {                                                \
            failures++;                                               \
            fprintf(stderr, "FAIL %s:%d: %s: ", __FILE__, __LINE__, #cond); \
            fprintf(stderr, __VA_ARGS__);                             \
            fprintf(stderr, "\n");                                    \
        }                                                             \
    } while (0)

static uint8_t *read_all(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); exit(2); }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *buf = malloc(n > 0 ? (size_t)n : 1);
    if (!buf || fread(buf, 1, (size_t)n, f) != (size_t)n) { perror(path); exit(2); }
    fclose(f);
    *len = (size_t)n;
    return buf;
}

static void write_all(const char *path, const uint8_t *p, size_t n) {
    FILE *f = fopen(path, "wb");
    if (!f || fwrite(p, 1, n, f) != n) { perror(path); exit(2); }
    fclose(f);
}

static const char *nz(const char *s) { return s ? s : "(null)"; }

static size_t count_all(safepdf_marks *m) {
    safepdf_mark_list l;
    char *err = NULL;
    if (safepdf_marks_list_all(m, &l, &err) != 0) { free(err); return (size_t)-1; }
    size_t n = l.count;
    safepdf_free_mark_list(&l);
    return n;
}

static const safepdf_mark *find(const safepdf_mark_list *l, uint64_t id) {
    for (size_t i = 0; i < l->count; i++)
        if (l->marks[i].id == id) return &l->marks[i];
    return NULL;
}

static const char *fixed_date = "D:20261124120000Z";

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "usage: %s PLAIN.pdf AES.pdf RC4.pdf OUTDIR\n", argv[0]);
        return 2;
    }
    char path[4096];
    CHECK(safepdf_marks_init() == 0, "init");
    CHECK(safepdf_marks_init() == 0, "init is idempotent");

    size_t plen;
    uint8_t *plain = read_all(argv[1], &plen);
    char *err = NULL;

    /* --- create, add a highlight + a note + a comment ---------------------------------- */
    safepdf_marks *m = safepdf_marks_create(plain, plen, &err);
    CHECK(m != NULL, "create: %s", nz(err));
    if (!m) return 1;
    safepdf_marks_state st;
    safepdf_marks_get_state(m, &st);
    CHECK(st.page_count >= 1 && st.mark_count == 0 && !st.dirty && !st.can_undo,
          "fresh state: pages %zu marks %zu", st.page_count, st.mark_count);
    CHECK(safepdf_marks_undo(m, &err) == -1 && err && strstr(err, "nothing to undo"),
          "undo on a fresh store: %s", nz(err));
    free(err); err = NULL;

    safepdf_box q = {100, 698, 166, 708};
    uint64_t hl = 0, note = 0, comment = 0;
    CHECK(safepdf_marks_add_highlight(m, 0, SAFEPDF_COLOR_GREEN, &q, 1, &hl, &err) == 0 && hl > 0,
          "add highlight: %s", nz(err));
    CHECK(safepdf_marks_add_highlight(m, 0, SAFEPDF_COLOR_GREEN, NULL, 0, NULL, &err) == -1,
          "a highlight without quads is refused");
    free(err); err = NULL;
    CHECK(safepdf_marks_add_highlight(m, 99999, SAFEPDF_COLOR_GREEN, &q, 1, NULL, &err) == -1,
          "a page beyond the document is refused");
    free(err); err = NULL;
    CHECK(safepdf_marks_add_highlight(m, 0, 7, &q, 1, NULL, &err) == -1,
          "a colour outside the palette is refused");
    free(err); err = NULL;

    /* note anchoring (Marks.noteAnchor) */
    safepdf_point inside = {120, 700}, outside = {300, 400};
    CHECK(safepdf_marks_note_anchor(&q, 1, &inside) == SAFEPDF_ANCHOR_QUADS, "click in selection");
    CHECK(safepdf_marks_note_anchor(&q, 1, &outside) == SAFEPDF_ANCHOR_POINT, "click elsewhere");
    CHECK(safepdf_marks_note_anchor(&q, 1, NULL) == SAFEPDF_ANCHOR_QUADS, "menu with selection");
    CHECK(safepdf_marks_note_anchor(NULL, 0, NULL) == SAFEPDF_ANCHOR_NONE, "nothing");
    int anc = safepdf_marks_note_anchor(NULL, 0, &outside);
    CHECK(anc == SAFEPDF_ANCHOR_POINT, "click without selection");
    CHECK(safepdf_marks_add_note(m, 0, SAFEPDF_COLOR_YELLOW, "hello \xc3\xa9", anc, &outside,
                                 NULL, 0, &note, &err) == 0 && note > hl,
          "add note: %s", nz(err));
    CHECK(safepdf_marks_add_comment(m, hl, "a comment", &comment, &err) == 0 && comment > note,
          "add comment: %s", nz(err));
    uint64_t again = 0;
    CHECK(safepdf_marks_add_comment(m, hl, "ignored", &again, &err) == 0 && again == comment,
          "the existing comment is returned");
    CHECK(safepdf_marks_add_comment(m, note, "x", NULL, &err) == -1, "a note has no comment");
    free(err); err = NULL;

    safepdf_mark_list l;
    CHECK(safepdf_marks_list(m, 0, &l, &err) == 0 && l.count == 3, "list page 0: %zu", l.count);
    const safepdf_mark *mh = find(&l, hl), *mn = find(&l, note), *mc = find(&l, comment);
    CHECK(mh && mh->kind == SAFEPDF_MARK_HIGHLIGHT && mh->quad_count == 1 &&
              mh->quads[0].llx == 100 && mh->quads[0].ury == 708 &&
              mh->color == SAFEPDF_COLOR_GREEN && mh->r == 0x53 && mh->g == 0xFF &&
              mh->state == SAFEPDF_MARK_NEW && mh->has_rect,
          "highlight listed");
    CHECK(mn && mn->kind == SAFEPDF_MARK_NOTE && mn->has_point && mn->point.x == 300 &&
              strcmp(mn->text, "hello \xc3\xa9") == 0 && mn->text_len == 8 && !mn->is_comment &&
              mn->has_rect && mn->rect.urx - mn->rect.llx == 20,
          "note listed");
    CHECK(mc && mc->is_comment && mc->quad_count == 1 && mc->color == SAFEPDF_COLOR_GREEN,
          "comment listed");
    safepdf_free_mark_list(&l);
    CHECK(safepdf_marks_hit_at(m, 0, 120, 700) == hl, "hit test on the highlight's quads");
    CHECK(safepdf_marks_hit_at(m, 0, 10, 10) == 0, "hit test on nothing");
    CHECK(safepdf_marks_note_close(m, note, "") == SAFEPDF_NOTE_KEEP, "note with text keeps it");

    /* --- undo / redo --------------------------------------------------------------------- */
    safepdf_marks_get_state(m, &st);
    CHECK(st.can_undo && !st.can_redo && st.undo_depth == 3 && st.dirty && st.pending == 3,
          "state after 3 adds: undo %zu pending %zu", st.undo_depth, st.pending);
    CHECK(safepdf_marks_undo(m, &err) == 0, "undo: %s", nz(err));
    CHECK(count_all(m) == 2, "undo removed the comment");
    CHECK(safepdf_marks_redo(m, &err) == 0, "redo: %s", nz(err));
    CHECK(count_all(m) == 3, "redo restored it");
    safepdf_marks_get_state(m, &st);
    CHECK(!st.can_redo && st.can_undo, "redo list empty again");

    /* --- free text, ink, slider merge, delete ------------------------------------------ */
    uint64_t ft = 0, ink = 0;
    CHECK(safepdf_marks_add_free_text(m, 0, "boxed", 200, 600, 12, 0xFF0000, &ft, &err) == 0,
          "free text: %s", nz(err));
    CHECK(safepdf_marks_add_free_text(m, 0, "x", 200, 600, 2, 0, NULL, &err) == -1,
          "font size 2 refused");
    free(err); err = NULL;
    safepdf_point stroke[3] = {{50, 50}, {60, 55}, {70, 52}};
    CHECK(safepdf_marks_add_ink(m, 0, stroke, 3, 2, 80, 0x0000FF, &ink, &err) == 0,
          "ink: %s", nz(err));
    CHECK(safepdf_marks_add_stroke(m, ink, stroke, 2, &err) == 0, "stroke: %s", nz(err));
    safepdf_marks_get_state(m, &st);
    size_t depth = st.undo_depth;
    CHECK(safepdf_marks_set_size(m, ink, 3, 1, &err) == 0 && safepdf_marks_set_size(m, ink, 4, 1, &err) == 0,
          "slider steps: %s", nz(err));
    safepdf_marks_seal(m);
    safepdf_marks_get_state(m, &st);
    CHECK(st.undo_depth == depth + 1, "one slider drag is one undo step (%zu -> %zu)", depth,
          st.undo_depth);
    CHECK(safepdf_marks_translate(m, ft, 1.5, -2.25, 0, &err) == 0, "move: %s", nz(err));
    CHECK(safepdf_marks_list(m, 0, &l, &err) == 0, "list");
    const safepdf_mark *mi = find(&l, ink), *mf = find(&l, ft);
    CHECK(mi && mi->kind == SAFEPDF_MARK_INK && mi->stroke_count == 2 && mi->point_count == 5 &&
              mi->size == 4 && mi->opacity == 80 && mi->b == 255,
          "ink listed");
    CHECK(mf && mf->kind == SAFEPDF_MARK_FREETEXT && mf->point.x == 201.5 && mf->point.y == 597.75 &&
              mf->r == 255 && mf->size == 12,
          "free text listed");
    safepdf_free_mark_list(&l);
    CHECK(safepdf_marks_delete(m, ink, &err) == 0 && safepdf_marks_delete(m, ft, &err) == 0,
          "delete editors: %s", nz(err));
    CHECK(safepdf_marks_delete(m, 424242, &err) == -1, "delete of a missing id refused");
    free(err); err = NULL;
    CHECK(count_all(m) == 3, "back to three marks");

    /* --- save --------------------------------------------------------------------------- */
    safepdf_save_result sr;
    CHECK(safepdf_marks_save_build(m, NULL, 0, fixed_date, 10, &sr, &err) ==
              SAFEPDF_SAVE_ERR_OUTPUT_LIMIT,
          "a ceiling below the estimate is refused");
    free(err); err = NULL;
    CHECK(safepdf_marks_output_estimate(m) > plen, "estimate covers the original");
    int rc = safepdf_marks_save_build(m, NULL, 0, fixed_date, 0, &sr, &err);
    CHECK(rc == SAFEPDF_SAVE_OK, "save: %d %s", rc, nz(err));
    CHECK(sr.size > plen && memcmp(sr.bytes, plain, plen) == 0 && sr.appended == sr.size - plen,
          "the original bytes are a prefix (C7)");
    CHECK(sr.marks_written == 3 && sr.marks_total == 3 && sr.flags == 0 && sr.note_count == 0,
          "save counts: written %zu total %zu flags %u", sr.marks_written, sr.marks_total,
          sr.flags);
    snprintf(path, sizeof path, "%s/saved.pdf", argv[4]);
    write_all(path, sr.bytes, sr.size);

    /* disk state and route (the overwrite decision) */
    CHECK(safepdf_marks_disk_state(m, plain, plen) == SAFEPDF_DISK_SAME, "disk same");
    CHECK(safepdf_marks_disk_state(m, sr.bytes, sr.size) == SAFEPDF_DISK_CHANGED, "disk changed");
    CHECK(safepdf_marks_disk_state(m, NULL, 0) == SAFEPDF_DISK_MISSING, "disk missing");
    CHECK(safepdf_marks_save_route(1, 0, 0, 0) == SAFEPDF_ROUTE_OVERWRITE_ASK, "route ask");
    CHECK(safepdf_marks_save_route(1, 0, 0, 1) == SAFEPDF_ROUTE_OVERWRITE, "route confirmed");
    CHECK(safepdf_marks_save_route(0, 0, 0, 0) == SAFEPDF_ROUTE_NOTHING, "route nothing");
    char *s = safepdf_marks_overwrite_question(m, "t.pdf");
    CHECK(s && strstr(s, "Save 3 new or changed mark(s) into t.pdf?"), "overwrite question: %s", nz(s));
    free(s);
    s = safepdf_marks_write_problem("t.pdf", 1, 1);
    CHECK(s == NULL, "writable");
    s = safepdf_marks_write_problem("t.pdf", 0, 1);
    CHECK(s && strstr(s, "read-only"), "read-only: %s", nz(s));
    free(s);
    s = safepdf_marks_default_target("/tmp/x/paper.pdf");
    CHECK(s && strcmp(s, "/tmp/x/paper-annotated.pdf") == 0, "default target: %s", nz(s));
    free(s);

    /* --- re-create from the saved bytes: the marks are listed as saved ------------------- */
    safepdf_marks *m2 = safepdf_marks_create(sr.bytes, sr.size, &err);
    CHECK(m2 != NULL, "create from saved bytes: %s", nz(err));
    if (m2) {
        CHECK(safepdf_marks_list_all(m2, &l, &err) == 0 && l.count == 3, "three saved marks");
        int all_saved = 1;
        for (size_t i = 0; i < l.count; i++) all_saved &= l.marks[i].state == SAFEPDF_MARK_SAVED;
        CHECK(all_saved, "all listed as saved");
        mh = find(&l, hl); mn = find(&l, note); mc = find(&l, comment);
        CHECK(mh && mn && mc && mc->is_comment && strcmp(mc->text, "a comment") == 0 &&
                  strcmp(mn->text, "hello \xc3\xa9") == 0,
              "ids and texts survive the save");
        safepdf_free_mark_list(&l);
        safepdf_marks_get_state(m2, &st);
        CHECK(!st.dirty && !st.can_undo, "a fresh store of the saved file is clean");
        /* edit a saved mark: listed as changed */
        CHECK(safepdf_marks_recolor(m2, hl, SAFEPDF_COLOR_RED, &err) == 0, "recolour saved");
        CHECK(safepdf_marks_list(m2, 0, &l, &err) == 0, "list");
        mh = find(&l, hl);
        CHECK(mh && mh->state == SAFEPDF_MARK_SAVED_CHANGED, "recoloured saved mark is changed");
        safepdf_free_mark_list(&l);
        /* task 11.3e2: the preview shows the recoloured saved highlight */
        safepdf_marks_bytes pv;
        CHECK(safepdf_marks_preview(m2, fixed_date, &pv, &err) == 0 && pv.size > sr.size &&
                  memcmp(pv.data, sr.bytes, sr.size) == 0,
              "preview of a recoloured saved mark: %zu bytes %s", pv.size, nz(err));
        safepdf_marks *mp = pv.size ? safepdf_marks_create(pv.data, pv.size, &err) : NULL;
        CHECK(mp != NULL, "the preview opens: %s", nz(err));
        if (mp) {
            CHECK(safepdf_marks_list(mp, 0, &l, &err) == 0, "list preview");
            mh = find(&l, hl);
            CHECK(mh && mh->color == SAFEPDF_COLOR_RED && mh->state == SAFEPDF_MARK_SAVED,
                  "the preview holds the highlight in red");
            safepdf_free_mark_list(&l);
            safepdf_marks_release(mp);
        }
        safepdf_free_marks_bytes(&pv);
        CHECK(safepdf_marks_undo(m2, &err) == 0, "undo recolour");
        safepdf_marks_get_state(m2, &st);
        CHECK(!st.dirty, "undo back to the file's state is clean");
        CHECK(safepdf_marks_preview(m2, NULL, &pv, &err) == 0 && pv.size == 0 && pv.data == NULL,
              "no preview without changed or deleted saved marks");
        /* delete a saved highlight (its comment goes too): the retention note */
        CHECK(safepdf_marks_delete(m2, hl, &err) == 0, "delete saved highlight");
        CHECK(count_all(m2) == 1, "highlight and its comment deleted");
        CHECK(safepdf_marks_preview(m2, NULL, &pv, &err) == 0 && pv.size > 0, "preview after delete");
        mp = pv.size ? safepdf_marks_create(pv.data, pv.size, &err) : NULL;
        CHECK(mp && count_all(mp) == 1, "the preview no longer holds the deleted marks");
        safepdf_marks_release(mp);
        safepdf_free_marks_bytes(&pv);
        safepdf_save_result sr2;
        rc = safepdf_marks_save_build(m2, NULL, 0, NULL, 0, &sr2, &err);
        CHECK(rc == SAFEPDF_SAVE_OK, "save after delete: %d %s", rc, nz(err));
        CHECK((sr2.flags & SAFEPDF_SAVE_NOTE_RETENTION) && sr2.deleted_saved == 2 &&
                  sr2.note_count == 1 && strstr(sr2.notes[0], "earlier revision"),
              "retention note: flags %u deleted %zu", sr2.flags, sr2.deleted_saved);
        CHECK(sr2.size > sr.size && memcmp(sr2.bytes, sr.bytes, sr.size) == 0,
              "second update appends again");
        s = safepdf_marks_saved_status("/d/t.pdf", &sr2);
        CHECK(s && strstr(s, "saved 2 new, changed or deleted mark(s) as an incremental update") &&
                  strstr(s, "to /d/t.pdf; 1 marks in the file, the original bytes unchanged at its start; note: the 2 deleted mark(s)"),
              "saved status with the retention note: %s", nz(s));
        free(s);
        safepdf_marks *m3 = safepdf_marks_create(sr2.bytes, sr2.size, &err);
        CHECK(m3 && count_all(m3) == 1, "deleted marks are gone after reopening");
        safepdf_marks_release(m3);
        safepdf_free_save_result(&sr2);
        safepdf_marks_release(m2);
    }
    free(err); err = NULL;
    safepdf_free_save_result(&sr);

    /* --- XFDF round trip ----------------------------------------------------------------- */
    safepdf_marks_bytes x;
    CHECK(safepdf_marks_xfdf_export(m, "paper.pdf", fixed_date, 10, &x, &err) == -1,
          "export ceiling refused");
    free(err); err = NULL;
    CHECK(safepdf_marks_xfdf_export(m, "paper.pdf", fixed_date, 0, &x, &err) == 0,
          "export: %s", nz(err));
    CHECK(x.size > 0 && strstr((const char *)x.data, "<highlight") != NULL, "export has a highlight");
    snprintf(path, sizeof path, "%s/export.xfdf", argv[4]);
    write_all(path, x.data, x.size);
    safepdf_marks *mx = safepdf_marks_create(plain, plen, &err);
    CHECK(mx != NULL, "create for import");
    if (mx) {
        safepdf_xfdf_import ir;
        CHECK(safepdf_marks_xfdf_import(mx, x.data, x.size, &ir, &err) == 0, "import: %s", nz(err));
        CHECK(ir.added == 3 && ir.already_present == 0 && ir.skipped == 0, "imported %zu", ir.added);
        safepdf_free_xfdf_import(&ir);
        CHECK(safepdf_marks_list_all(mx, &l, &err) == 0 && l.count == 3, "three imported marks");
        mh = find(&l, hl); mc = find(&l, comment);
        CHECK(mh && mc && mc->is_comment && mh->state == SAFEPDF_MARK_NEW, "ids kept, unsaved");
        safepdf_free_mark_list(&l);
        CHECK(safepdf_marks_xfdf_import(mx, x.data, x.size, &ir, &err) == 0 && ir.added == 0 &&
                  ir.already_present == 3,
              "re-import is idempotent");
        safepdf_free_xfdf_import(&ir);
        safepdf_marks_get_state(mx, &st);
        CHECK(st.undo_depth == 1, "an import is one undo step");
        /* malformed and hostile XFDF: an error, never a crash, the store unchanged */
        const char *bad[] = {
            "<xfdf><annots><highlight page=\"0\"",
            ("<?xml version=\"1.0\"?><!DOCTYPE x [<!ENTITY a \"aaaa\"><!ENTITY b \"&a;&a;&a;\">]>"
             "<xfdf>&b;</xfdf>"),
            "<notxfdf/>",
            "\xff\xfe<x/>",
            "",
        };
        for (size_t i = 0; i < sizeof bad / sizeof bad[0]; i++) {
            char *e = NULL;
            int r2 = safepdf_marks_xfdf_import(mx, (const uint8_t *)bad[i], strlen(bad[i]), &ir, &e);
            CHECK(r2 == -1 && e != NULL, "malformed XFDF %zu refused (%s)", i, nz(e));
            free(e);
        }
        CHECK(count_all(mx) == 3, "store unchanged by refused imports");
        /* a skipped annotation is reported */
        const char *skip = "<xfdf xmlns=\"http://ns.adobe.com/xfdf/\"><annots>"
                           "<underline page=\"0\" coords=\"0,0,1,1,0,0,1,1\"/></annots></xfdf>";
        CHECK(safepdf_marks_xfdf_import(mx, (const uint8_t *)skip, strlen(skip), &ir, &err) == 0 &&
                  ir.skipped == 1 && ir.skip_count == 1 && strcmp(ir.skip_elements[0], "underline") == 0,
              "skip reported");
        safepdf_free_xfdf_import(&ir);
        safepdf_marks_release(mx);
    }
    safepdf_free_marks_bytes(&x);

    /* --- encrypted documents: IV seed required; RC4 note -------------------------------- */
    size_t alen, rlen;
    uint8_t *aes = read_all(argv[2], &alen);
    safepdf_marks *me = safepdf_marks_create(aes, alen, &err);
    CHECK(me != NULL, "create encrypted: %s", nz(err));
    if (me) {
        safepdf_marks_get_state(me, &st);
        CHECK(st.encrypted, "encrypted flag");
        CHECK(safepdf_marks_add_highlight(me, 0, SAFEPDF_COLOR_BLUE, &q, 1, NULL, &err) == 0, "hl");
        rc = safepdf_marks_save_build(me, NULL, 0, fixed_date, 0, &sr, &err);
        CHECK(rc == SAFEPDF_SAVE_ERR_NEED_SEED && err, "encrypted without seed refused: %d", rc);
        free(err); err = NULL;
        uint8_t seed[64];
        for (int i = 0; i < 64; i++) seed[i] = (uint8_t)(i * 37 + 11);
        rc = safepdf_marks_save_build(me, seed, 32, fixed_date, 0, &sr, &err);
        CHECK(rc == SAFEPDF_SAVE_ERR_NEED_SEED, "32 bytes are not enough: %d", rc);
        free(err); err = NULL;
        rc = safepdf_marks_save_build(me, seed, 64, fixed_date, 0, &sr, &err);
        CHECK(rc == SAFEPDF_SAVE_OK && memcmp(sr.bytes, aes, alen) == 0, "AES save: %d %s", rc, nz(err));
        CHECK(sr.flags == 0, "AES: no note (flags %u)", sr.flags);
        safepdf_marks *me2 = rc == 0 ? safepdf_marks_create(sr.bytes, sr.size, &err) : NULL;
        CHECK(me2 && count_all(me2) == 1, "AES saved mark reads back");
        safepdf_marks_release(me2);
        safepdf_free_save_result(&sr);
        safepdf_marks_release(me);
    }
    free(err); err = NULL;
    uint8_t *rc4 = read_all(argv[3], &rlen);
    safepdf_marks *mr = safepdf_marks_create(rc4, rlen, &err);
    CHECK(mr != NULL, "create RC4: %s", nz(err));
    if (mr) {
        uint8_t seed[64] = {1};
        CHECK(safepdf_marks_add_highlight(mr, 0, SAFEPDF_COLOR_PINK, &q, 1, NULL, &err) == 0, "hl");
        rc = safepdf_marks_save_build(mr, seed, 64, fixed_date, 0, &sr, &err);
        CHECK(rc == SAFEPDF_SAVE_OK && (sr.flags & SAFEPDF_SAVE_NOTE_RC4) && sr.note_count == 1 &&
                  strstr(sr.notes[0], "RC4"),
              "RC4 written with a note: %d flags %u %s", rc, sr.flags, nz(err));
        safepdf_free_save_result(&sr);
        safepdf_marks_release(mr);
    }
    free(err); err = NULL;

    /* --- tools, bubble, pop-over parameters (task 11.3e1) ------------------------------- */
    safepdf_tool_params tp;
    CHECK(safepdf_marks_tool_params(&tp) == 0, "tool params");
    CHECK(tp.highlight_rgb[0][0] == 0xFF && tp.highlight_rgb[0][2] == 0x98 &&
              tp.highlight_rgb[4][1] == 0x4F && tp.editor_count == 6 && tp.editor_rgb[0][0] == 0,
          "palettes");
    CHECK(tp.font_min == 5 && tp.font_max == 100 && tp.font_default == 10 && tp.width_min == 1 &&
              tp.width_max == 20 && tp.opacity_step == 5 && tp.opacity_default == 100 &&
              tp.ft_pad == 2 && tp.line_factor == 1.35 && tp.note_size == 20,
          "sliders and metrics");
    safepdf_tool_ui ui;
    int hlnow = -1;
    CHECK(safepdf_marks_ui_step(NULL, SAFEPDF_UI_INIT, 0, &ui, NULL) == 0 && ui.show_all &&
              !ui.tool && ui.ft_size == 10 && ui.ink_opacity == 100,
          "initial tool state");
    CHECK(safepdf_marks_ui_step(&ui, SAFEPDF_UI_TOOL_CLICK, 1, &ui, &hlnow) == 0 && hlnow == 1 &&
              !ui.tool,
          "Highlight button with a selection highlights");
    CHECK(safepdf_marks_ui_step(&ui, SAFEPDF_UI_TOOL_CLICK, 0, &ui, &hlnow) == 1 && hlnow == 0 &&
              ui.tool && ui.popover,
          "Highlight button without a selection: the tool and its pop-over");
    CHECK(safepdf_marks_ui_step(&ui, SAFEPDF_UI_SELECT_EDITOR, SAFEPDF_EDITOR_DRAW, &ui, NULL) == 3 &&
              !ui.tool && ui.ed_pop,
          "Draw: the Highlight tool off");
    CHECK(safepdf_marks_ui_step(&ui, SAFEPDF_UI_ESCAPE, 0, &ui, NULL) == 3 && !ui.ed_pop,
          "Escape closes the pop-over, the mode stays");
    CHECK(safepdf_marks_ui_step(&ui, SAFEPDF_UI_SELECT_TOOL, 0, &ui, NULL) == 0 &&
              ui.editor == SAFEPDF_EDITOR_NONE,
          "Select text");
    CHECK(safepdf_marks_ui_step(&ui, 99, 0, &ui, NULL) == -1, "unknown op");
    CHECK(safepdf_marks_bubble_kind(1, 1, 1) == SAFEPDF_BUBBLE_FLOAT &&
              safepdf_marks_bubble_kind(0, 1, 1) == SAFEPDF_BUBBLE_EDIT &&
              safepdf_marks_bubble_kind(0, 1, 0) == -1 && safepdf_marks_bubble_kind(0, 0, 1) == -1,
          "bubble kinds");
    safepdf_bubble_layout bl;
    CHECK(safepdf_marks_bubble_layout(SAFEPDF_BUBBLE_FLOAT, &bl) == 0 && bl.count == 2 &&
              bl.width == 67 && bl.height == 34 && bl.buttons[0].button == SAFEPDF_BTN_HIGHLIGHT &&
              bl.buttons[0].cmd == 11 /* SAFEPDF_CMD_HIGHLIGHT */ && bl.buttons[1].x0 == 36 &&
              strcmp(bl.buttons[1].tip, "Add comment") == 0,
          "float bubble layout");
    CHECK(safepdf_marks_bubble_layout(SAFEPDF_BUBBLE_EDIT, &bl) == 0 && bl.count == 3 &&
              bl.buttons[0].cmd == -1 && bl.buttons[2].button == SAFEPDF_BTN_DELETE,
          "edit bubble layout");
    CHECK(safepdf_marks_bubble_layout(9, &bl) == -1, "unknown bubble");
    safepdf_box sels[2] = {{100, 100, 400, 120}, {100, 122, 300, 142}}, area = {0, 0, 1000, 800},
                placed;
    CHECK(safepdf_marks_bubble_place(sels, 2, 112, 34, &area, &placed) == 1 && placed.llx == 188 &&
              placed.lly == 148 && placed.urx == 300 && placed.ury == 182,
          "bubble placed (Bubble.place #guard)");
    CHECK(safepdf_marks_bubble_place(NULL, 0, 112, 34, &area, &placed) == 0, "no selection");
    CHECK(safepdf_marks_escape_closes(SAFEPDF_TRANSIENT_NOTE | SAFEPDF_TRANSIENT_HL_POP) ==
                  SAFEPDF_TRANSIENT_NOTE &&
              safepdf_marks_escape_closes(0) == 0,
          "Escape closes the topmost transient");

    /* --- task 11.3e2: preview, ceiling, texts and dialog rules --------------------------- */
    {
        safepdf_marks_bytes pv;
        CHECK(safepdf_marks_preview(m, NULL, &pv, &err) == 0 && pv.size == 0,
              "a store without saved marks has no preview");
        CHECK(safepdf_marks_output_ceiling() == (size_t)192 * 1024 * 1024, "output ceiling 192 MiB");
        safepdf_save_result fake = {0};
        fake.marks_written = 0; fake.marks_total = 4;
        char *t = safepdf_marks_saved_status("a.pdf", &fake);
        CHECK(t && strcmp(t, "saved a copy (no changed marks) to a.pdf; 4 marks in the file, the original bytes unchanged at its start") == 0,
              "copy status: %s", nz(t));
        free(t);
        safepdf_xfdf_import ir = {0};
        ir.added = 3; ir.already_present = 1;
        t = safepdf_marks_import_status("a.xfdf", &ir);
        CHECK(t && strcmp(t, "a.xfdf: 3 imported, 1 already present, 0 skipped") == 0, "import status: %s", nz(t));
        free(t);
        char *el[1] = {"ink"}, *re[1] = {"no page"};
        ir.skipped = 2; ir.skip_count = 1; ir.skip_elements = el; ir.skip_reasons = re;
        t = safepdf_marks_import_status("a.xfdf", &ir);
        CHECK(t && strstr(t, "2 skipped (first skipped: <ink>: no page)"), "import status with a skip: %s", nz(t));
        free(t);
        t = safepdf_marks_xfdf_target("/tmp/x/paper.pdf");
        CHECK(t && strcmp(t, "/tmp/x/paper.xfdf") == 0, "xfdf target: %s", nz(t));
        free(t);
        t = safepdf_marks_replace_question("a.pdf");
        CHECK(t && strcmp(t, "a.pdf already exists. Replace it?") == 0, "replace question: %s", nz(t));
        free(t);
        t = safepdf_marks_opened_overwrite_question("a.pdf");
        CHECK(t && strstr(t, "Overwrite the opened file a.pdf?"), "opened overwrite: %s", nz(t));
        free(t);
        safepdf_dialog_buttons b;
        CHECK(safepdf_marks_dialog_buttons(SAFEPDF_DIALOG_UNSAVED, 1, &b) == 0 && b.count == 3 &&
                  strcmp(b.key[0], "dontsave") == 0 && strcmp(b.label[2], "Save") == 0,
              "unsaved buttons, aqua order");
        CHECK(safepdf_marks_dialog_buttons(SAFEPDF_DIALOG_OVERWRITE, 0, &b) == 0 && b.count == 3 &&
                  strcmp(b.key[0], "overwrite") == 0 && strcmp(b.label[1], "Save As\xe2\x80\xa6") == 0,
              "overwrite buttons, X11 order");
        CHECK(safepdf_marks_dialog_buttons(SAFEPDF_DIALOG_CHANGED, 1, &b) == 0 && b.count == 2 &&
                  strcmp(b.key[1], "saveas") == 0,
              "changed buttons");
        CHECK(safepdf_marks_dialog_buttons(7, 1, &b) == -1 && b.count == 0, "unknown dialog");
        CHECK(safepdf_marks_unsaved_answer("save") == SAFEPDF_ANSWER_SAVE &&
                  safepdf_marks_unsaved_answer("dontsave") == SAFEPDF_ANSWER_DONT_SAVE &&
                  safepdf_marks_unsaved_answer("cancel") == SAFEPDF_ANSWER_CANCEL &&
                  safepdf_marks_unsaved_answer(NULL) == SAFEPDF_ANSWER_CANCEL,
              "unsaved answers");
        CHECK(safepdf_marks_close_goes_on(0, SAFEPDF_ANSWER_CANCEL, 0) == 1 &&
                  safepdf_marks_close_goes_on(1, SAFEPDF_ANSWER_DONT_SAVE, 0) == 1 &&
                  safepdf_marks_close_goes_on(1, SAFEPDF_ANSWER_SAVE, 1) == 1 &&
                  safepdf_marks_close_goes_on(1, SAFEPDF_ANSWER_SAVE, 0) == 0 &&
                  safepdf_marks_close_goes_on(1, SAFEPDF_ANSWER_CANCEL, 1) == 0,
              "close goes on (Save.closeGoesOn)");
        t = safepdf_marks_dialog_dir("/d", 0, "/h");
        CHECK(t && strcmp(t, "/h") == 0, "dialog dir: %s", nz(t));
        free(t);
        t = safepdf_marks_dialog_dir("/d", 1, NULL);
        CHECK(t && strcmp(t, "/d") == 0, "dialog dir usable: %s", nz(t));
        free(t);
        t = safepdf_marks_tmp_name("a.pdf", 7);
        CHECK(t && strcmp(t, ".a.pdf.safepdf-7.tmp") == 0, "tmp name: %s", nz(t));
        free(t);
        t = safepdf_marks_one_line("a\n  b");
        CHECK(t && strcmp(t, "a b") == 0, "one line: %s", nz(t));
        free(t);
    }

    /* --- reference counting -------------------------------------------------------------- */
    safepdf_marks_retain(m);
    safepdf_marks_release(m);
    CHECK(count_all(m) == 3, "store alive after retain/release");
    safepdf_marks_release(m);
    safepdf_marks_release(NULL);

    CHECK(safepdf_marks_create((const uint8_t *)"not a pdf", 9, &err) == NULL && err,
          "garbage refused");
    free(err);

    free(plain); free(aes); free(rc4);
    printf("marks_test: %d checks, %d failures\n", checks, failures);
    return failures ? 1 : 0;
}
