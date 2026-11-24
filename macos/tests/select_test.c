/*
 * select_test.c — test of the selection/search C API (task 11.3a4, macos/safepdf_select.h)
 * on Tests/golden/text/latin.pdf through the real confined worker.
 *
 *   select_test WORKER GOLDEN_DIR     (macos/tests/run_select.sh passes .lake/build/bin/worker
 *                                      and Tests/golden)
 *
 * Headless: no window, no AppKit. The page index arrives through safepdf_doc_page_index on a
 * private serial queue and signals a semaphore the main thread waits on. The checks restate
 * what the Lean side proves or #guards (bands cover the selected glyph boxes, consecutive
 * lines of a paragraph meet, search hits are matches) as sanity checks of the C boundary, not
 * as proofs. Exit status 0 iff every check passed.
 */
#include "../safepdf_core.h"
#include "../safepdf_select.h"

#include <ctype.h>
#include <dispatch/dispatch.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int checks = 0, failures = 0;

#define CHECK(cond, ...) do { \
    checks++; \
    if (!(cond)) { failures++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } \
} while (0)

static const char *golden;
static dispatch_queue_t q;

typedef struct {
    dispatch_semaphore_t done;
    safepdf_status status;
    char error[512];
    safepdf_page_index *index;
} reply;

static void on_index(void *c, safepdf_request_id id, safepdf_status s, const char *e,
                     safepdf_page_index *x) {
    (void)id;
    reply *r = c;
    r->status = s;
    r->index = x;
    if (e) snprintf(r->error, sizeof r->error, "%s", e);
    dispatch_semaphore_signal(r->done);
}

static uint8_t *read_all(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *b = malloc(n > 0 ? (size_t)n : 1);
    *len = fread(b, 1, (size_t)n, f);
    fclose(f);
    return b;
}

/* The page index of page 0 of `rel` (under GOLDEN_DIR), through the worker. */
static safepdf_page_index *index_of(const char *rel) {
    char path[4096];
    snprintf(path, sizeof path, "%s/%s", golden, rel);
    size_t len = 0;
    uint8_t *b = read_all(path, &len);
    char *err = NULL;
    safepdf_document *d = b ? safepdf_doc_open_bytes(b, len, NULL, &err) : NULL;
    free(b);
    if (!d) { printf("open %s failed: %s\n", path, err ? err : "(cannot read)"); free(err); return NULL; }
    reply r;
    memset(&r, 0, sizeof r);
    r.done = dispatch_semaphore_create(0);
    safepdf_doc_page_index(d, 0, NULL, SAFEPDF_PRIO_CURRENT, q, on_index, &r);
    int came = dispatch_semaphore_wait(r.done, dispatch_time(DISPATCH_TIME_NOW, 30000000000L)) == 0;
    CHECK(came && r.status == SAFEPDF_STATUS_OK && r.index, "page index of %s (%s)", rel, r.error);
    safepdf_doc_release(d);
    return came ? r.index : NULL;
}

/* The text of cells a … b as the layout puts it (first text, then separator + text). */
static char *cells_text(const safepdf_page_index *x, size_t a, size_t b) {
    size_t n = 1;
    for (size_t i = a; i <= b && i < x->cell_count; i++) n += strlen(x->cells[i].sep) + strlen(x->cells[i].text);
    char *s = malloc(n);
    s[0] = 0;
    for (size_t i = a; i <= b && i < x->cell_count; i++) {
        if (i > a) strcat(s, x->cells[i].sep);
        strcat(s, x->cells[i].text);
    }
    return s;
}

static size_t utf8_chars(const char *s) {
    size_t n = 0;
    for (; *s; s++) if (((unsigned char)*s & 0xC0) != 0x80) n++;
    return n;
}

static int inside(safepdf_box a, safepdf_box b) {
    const double e = 1e-9;
    return b.llx <= a.llx + e && b.lly <= a.lly + e && a.urx <= b.urx + e && a.ury <= b.ury + e;
}

static int contains_pt(safepdf_box b, double x, double y) {
    return b.llx <= x && x <= b.urx && b.lly <= y && y <= b.ury;
}

/* The first hit's range of `query`; 0 when found. */
static int first_hit(const safepdf_select_page *p, const char *query, safepdf_select_range *r) {
    safepdf_select_hit_list *l = safepdf_select_find(p, query);
    int ok = l && l->count > 0;
    if (ok) *r = l->hits[0].range;
    safepdf_select_free_hit_list(l);
    return ok ? 0 : -1;
}

static char *copy_text(const safepdf_select_page *p, safepdf_select_range r) {
    safepdf_select_copy_result *c = safepdf_select_copy(p, r.first, r.last);
    char *t = strdup(c ? c->text : "");
    safepdf_select_free_copy_result(c);
    return t;
}

/* ---- hit test and drag ---- */
static void test_pointer(const safepdf_page_index *x, const safepdf_select_page *p) {
    size_t bad = 0, missed = 0;
    for (size_t i = 0; i < x->cell_count; i++) {
        safepdf_box b = x->cells[i].box;
        double cx = (b.llx + b.urx) / 2, cy = (b.lly + b.ury) / 2;
        size_t j;
        if (safepdf_select_nearest(p, cx, cy, &j) != 0 || j >= x->cell_count) { missed++; continue; }
        /* The nearest box contains the point (distance 0), and no earlier cell does. */
        if (!contains_pt(x->cells[j].box, cx, cy)) bad++;
        for (size_t k = 0; k < j; k++) if (contains_pt(x->cells[k].box, cx, cy)) { bad++; break; }
    }
    CHECK(missed == 0 && bad == 0, "hit test on every cell centre (%zu missed, %zu wrong)", missed, bad);
    size_t j0;
    CHECK(safepdf_select_nearest(p, -1e6, 1e6, &j0) == 0, "hit test far away still finds a cell");
    CHECK(safepdf_select_nearest(p, 0.0 / 0.0, 1, &j0) == -1, "NaN point -> no cell");

    /* Drag between two cell centres: the nearest cells, ordered. */
    size_t n = x->cell_count, a = n / 5, b = (4 * n) / 5;
    safepdf_box ba = x->cells[a].box, bb = x->cells[b].box;
    double ax = (ba.llx + ba.urx) / 2, ay = (ba.lly + ba.ury) / 2;
    double bx = (bb.llx + bb.urx) / 2, by = (bb.lly + bb.ury) / 2;
    size_t na = 0, nb = 0;
    safepdf_select_nearest(p, ax, ay, &na);
    safepdf_select_nearest(p, bx, by, &nb);
    safepdf_select_range r1, r2;
    CHECK(safepdf_select_drag(p, bx, by, ax, ay, &r1) == 0 &&
          r1.first == (na < nb ? na : nb) && r1.last == (na < nb ? nb : na),
          "drag backwards = ordered nearest cells (%zu..%zu vs %zu, %zu)", r1.first, r1.last, na, nb);
    CHECK(safepdf_select_drag(p, ax, ay, bx, by, &r2) == 0 && r2.first == r1.first && r2.last == r1.last,
          "drag forwards = drag backwards");

    /* Many hit tests from other threads at once (registration, thread-shared handle). */
    __block size_t disagree = 0;
    dispatch_apply(16, dispatch_get_global_queue(QOS_CLASS_DEFAULT, 0), ^(size_t t) {
        for (size_t i = t; i < x->cell_count; i += 16) {
            safepdf_box bx2 = x->cells[i].box;
            size_t j1 = 0, j2 = 0;
            safepdf_select_nearest(p, (bx2.llx + bx2.urx) / 2, (bx2.lly + bx2.ury) / 2, &j1);
            safepdf_select_nearest(p, (bx2.llx + bx2.urx) / 2, (bx2.lly + bx2.ury) / 2, &j2);
            if (j1 != j2) __atomic_fetch_add(&disagree, 1, __ATOMIC_RELAXED);
        }
    });
    CHECK(disagree == 0, "concurrent hit tests agree");
}

/* ---- double and triple click ---- */
static void test_word_line(const safepdf_select_page *p) {
    safepdf_select_range h;
    if (first_hit(p, "paragraph", &h) != 0) { CHECK(0, "\"paragraph\" found"); return; }
    safepdf_select_range w1 = safepdf_select_word_at(p, h.first);
    safepdf_select_range w2 = safepdf_select_word_at(p, h.last);
    safepdf_select_range w3 = safepdf_select_word_at(p, (h.first + h.last) / 2);
    CHECK(w1.first == h.first && w1.last == h.last && w2.first == h.first && w2.last == h.last &&
          w3.first == h.first && w3.last == h.last, "double click selects the word \"paragraph\"");
    char *t = copy_text(p, w1);
    CHECK(strcmp(t, "paragraph") == 0, "word text \"%s\"", t);
    free(t);
    safepdf_select_range l = safepdf_select_line_at(p, h.first);
    t = copy_text(p, l);
    CHECK(strcmp(t, "After a paragraph gap.") == 0, "triple click selects the line (\"%s\")", t);
    free(t);
    safepdf_select_range l2 = safepdf_select_line_at(p, l.last);
    CHECK(l2.first == l.first && l2.last == l.last, "line of the line's last cell is the same line");
}

/* ---- selection bands ---- */
static void test_bands(const safepdf_page_index *x, const safepdf_select_page *p) {
    size_t n = x->cell_count;
    size_t ranges[][2] = { { 0, n - 1 }, { 3, n / 2 }, { n / 3, (2 * n) / 3 }, { 5, 5 }, { n - 1, 0 } };
    size_t uncovered = 0, nbands = 0, wrongcount = 0;
    for (size_t r = 0; r < sizeof ranges / sizeof ranges[0]; r++) {
        size_t a = ranges[r][0], b = ranges[r][1];
        size_t lo = a < b ? a : b, hi = a < b ? b : a;
        safepdf_select_box_list *bs = safepdf_select_bands(p, a, b);
        if (!bs) { CHECK(0, "bands"); continue; }
        nbands += bs->count;
        size_t runs = 0;
        for (size_t i = lo; i <= hi; i++) {
            if (i == lo || x->cells[i].line != x->cells[i - 1].line) runs++;
            int any = 0;
            for (size_t k = 0; k < bs->count && !any; k++) any = inside(x->cells[i].box, bs->boxes[k]);
            if (!any) uncovered++;
        }
        if (runs != bs->count) wrongcount++;
        safepdf_select_free_box_list(bs);
    }
    CHECK(uncovered == 0, "every selected glyph box lies in a band (%zu do not)", uncovered);
    CHECK(wrongcount == 0, "one band per line run");

    /* Select-all: consecutive horizontal lines joined by a plain line break whose bands do
       not overlap meet exactly; lines after a paragraph break never do. */
    safepdf_select_box_list *bs = safepdf_select_bands(p, 0, n - 1);
    size_t met = 0, para_met = 0, k = 0;
    for (size_t i = 1; i < n && bs; i++) {
        if (x->cells[i].line == x->cells[i - 1].line) continue;
        if (k + 1 >= bs->count) break;
        safepdf_box u = bs->boxes[k], w = bs->boxes[k + 1];
        int horiz = x->line_dirs[x->cells[i].line] == 0 && x->line_dirs[x->cells[i - 1].line] == 0;
        if (horiz && strcmp(x->cells[i].sep, "\n") == 0 && u.lly == w.ury) met++;
        if (strcmp(x->cells[i].sep, "\n\n") == 0 && u.lly == w.ury) para_met++;
        k++;
    }
    CHECK(bs && met >= 1, "consecutive lines of a paragraph meet (%zu pairs)", met);
    CHECK(para_met == 0, "no bands meet across a paragraph break");
    /* The first two lines ("First line of text." / "Word gap…") are one paragraph. */
    if (bs && bs->count >= 2)
        CHECK(bs->boxes[0].lly == bs->boxes[1].ury, "first two lines meet (%g vs %g)",
              bs->boxes[0].lly, bs->boxes[1].ury);
    printf("bands: %zu bands over 5 selections; select-all %zu bands, %zu joined pairs\n",
           nbands, bs ? bs->count : 0, met);
    safepdf_select_free_box_list(bs);
}

/* ---- copy ---- */
static void test_copy(const safepdf_page_index *x, const safepdf_select_page *p) {
    size_t n = x->cell_count;
    safepdf_select_copy_result *c = safepdf_select_copy(p, 0, n - 1);
    char *want = cells_text(x, 0, n - 1);
    CHECK(c && strcmp(c->text, want) == 0, "select-all copy = the page text");
    CHECK(c && c->chars == utf8_chars(c->text) && c->chars == 147, "147 characters (%zu)", c ? c->chars : 0);
    CHECK(c && c->hidden_chars == 19, "19 invisible characters (%zu)", c ? c->hidden_chars : 0);
    CHECK(c && strcmp(c->status, "copied 147 characters; the copied text includes 19 characters "
                      "that are not visible on the page (invisible text, e.g. an OCR layer)") == 0,
          "status \"%s\"", c ? c->status : "");
    safepdf_select_free_copy_result(c);
    free(want);
    c = safepdf_select_copy(p, n - 1, 0);
    CHECK(c && c->hidden_chars == 19, "copy in either order");
    safepdf_select_free_copy_result(c);
    safepdf_select_range h;
    if (first_hit(p, "First line", &h) == 0) {
        c = safepdf_select_copy(p, h.first, h.last);
        CHECK(c && strcmp(c->text, "First line") == 0 && c->hidden_chars == 0 &&
              strcmp(c->status, "copied 10 characters") == 0, "visible copy status (%s)", c ? c->status : "");
        safepdf_select_free_copy_result(c);
    } else CHECK(0, "\"First line\" found");
}

/* ---- search ---- */
static void test_search(const safepdf_select_page *p) {
    char *nq = safepdf_select_normalize_query("  Hello \n  WORLD ");
    CHECK(nq && strcmp(nq, "hello world") == 0, "normalised query \"%s\"", nq ? nq : "");
    free(nq);
    CHECK(safepdf_select_count(p, "paragraph") == 1, "paragraph x1");
    CHECK(safepdf_select_count(p, "first LINE") == 1, "first line x1 (case-insensitive)");
    CHECK(safepdf_select_count(p, "invisible   OCR") == 1, "invisible OCR x1 (whitespace)");
    CHECK(safepdf_select_count(p, "zzz") == 0, "zzz x0");
    CHECK(safepdf_select_count(p, "   ") == 0, "empty query x0");
    size_t ne = safepdf_select_count(p, "e");
    safepdf_select_hit_list *l = safepdf_select_find(p, "E");
    CHECK(l && l->count == ne && ne > 5, "find E = count e (%zu)", ne);
    size_t bad = 0, badboxes = 0;
    for (size_t i = 0; l && i < l->count; i++) {
        char *t = copy_text(p, l->hits[i].range);
        if (!(strlen(t) == 1 && tolower((unsigned char)t[0]) == 'e')) bad++;
        free(t);
        safepdf_select_box_list *bs = safepdf_select_range_boxes(p, l->hits[i].range.first, l->hits[i].range.last);
        if (!bs || bs->count != l->hits[i].box_count ||
            (bs->count && memcmp(bs->boxes, l->hits[i].boxes, bs->count * sizeof *bs->boxes) != 0)) badboxes++;
        safepdf_select_free_box_list(bs);
    }
    CHECK(bad == 0, "every hit of e is an e (%zu not)", bad);
    CHECK(badboxes == 0, "hit boxes = range boxes");
    safepdf_select_free_hit_list(l);

    /* Over a document: pages 0 and 2 indexed, page 1 not. */
    const safepdf_select_page *pages[3] = { p, NULL, p };
    size_t nl = safepdf_select_count(p, "line");
    l = safepdf_select_find_doc(pages, 3, "line");
    CHECK(l && nl >= 1 && l->count == 2 * nl, "find_doc: %zu hits (want %zu)", l ? l->count : 0, 2 * nl);
    if (l && l->count == 2 * nl)
        CHECK(l->hits[0].page == 0 && l->hits[nl].page == 2 && l->hits[0].box_count >= 1,
              "find_doc pages and boxes");
    safepdf_select_free_hit_list(l);

    /* Find Next / Previous over three pages (1 has no hit), fetching counts on demand. */
    int64_t counts[3] = { -1, -1, -1 };
    size_t c = safepdf_select_count(p, "e");
    safepdf_select_step s;
    safepdf_select_next_hit(counts, 3, 0, -1, 1, &s);
    CHECK(s.kind == SAFEPDF_SELECT_STEP_NEED && s.page == 0, "step: need page 0");
    counts[0] = (int64_t)c;
    safepdf_select_next_hit(counts, 3, 0, -1, 1, &s);
    CHECK(s.kind == SAFEPDF_SELECT_STEP_HIT && s.page == 0 && s.index == 0 && s.count == c && !s.wrapped, "step: hit 0/0");
    safepdf_select_next_hit(counts, 3, 0, (int64_t)c - 1, 1, &s);
    CHECK(s.kind == SAFEPDF_SELECT_STEP_NEED && s.page == 1, "step: need page 1");
    counts[1] = 0;
    safepdf_select_next_hit(counts, 3, 0, (int64_t)c - 1, 1, &s);
    CHECK(s.kind == SAFEPDF_SELECT_STEP_NEED && s.page == 2, "step: need page 2");
    counts[2] = (int64_t)c;
    safepdf_select_next_hit(counts, 3, 0, (int64_t)c - 1, 1, &s);
    CHECK(s.kind == SAFEPDF_SELECT_STEP_HIT && s.page == 2 && s.index == 0 && !s.wrapped, "step: hit on page 2");
    safepdf_select_next_hit(counts, 3, 2, (int64_t)c - 1, 1, &s);
    CHECK(s.kind == SAFEPDF_SELECT_STEP_HIT && s.page == 0 && s.index == 0 && s.wrapped, "step: wraps to page 0");
    safepdf_select_next_hit(counts, 3, 0, 0, 0, &s);
    CHECK(s.kind == SAFEPDF_SELECT_STEP_HIT && s.page == 2 && s.index == c - 1 && s.wrapped, "step: previous wraps to page 2's last");
    int64_t none[2] = { 0, 0 };
    safepdf_select_next_hit(none, 2, 0, -1, 1, &s);
    CHECK(s.kind == SAFEPDF_SELECT_STEP_NONE, "step: no hit");
    CHECK(safepdf_select_next_hit(NULL, 2, 0, -1, 1, &s) == -1, "step: NULL counts refused");
}

/* ---- edges ---- */
static void test_edges(void) {
    char *err = NULL;
    CHECK(safepdf_select_page_new(NULL, &err) == NULL && err, "NULL index refused");
    free(err);
    safepdf_page_index empty;
    memset(&empty, 0, sizeof empty);
    safepdf_select_page *p = safepdf_select_page_new(&empty, NULL);
    CHECK(p && safepdf_select_cell_count(p) == 0, "empty page");
    size_t j;
    CHECK(safepdf_select_nearest(p, 1, 1, &j) == -1, "empty: no hit");
    safepdf_select_range r;
    CHECK(safepdf_select_drag(p, 0, 0, 1, 1, &r) == -1, "empty: no drag");
    safepdf_select_box_list *bs = safepdf_select_bands(p, 0, 3);
    CHECK(bs && bs->count == 0, "empty: no bands");
    safepdf_select_free_box_list(bs);
    safepdf_select_copy_result *c = safepdf_select_copy(p, 0, 3);
    CHECK(c && c->text[0] == 0 && c->chars == 0, "empty: empty copy");
    safepdf_select_free_copy_result(c);
    CHECK(safepdf_select_page_retain(p) == p, "retain");
    safepdf_select_page_release(p);
    CHECK(safepdf_select_cell_count(p) == 0, "alive after one release");
    safepdf_select_page_release(p);
    safepdf_select_page_release(NULL);
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: %s WORKER GOLDEN_DIR\n", argv[0]);
        return 2;
    }
    golden = argv[2];
    if (safepdf_init() != 0) { fprintf(stderr, "init failed\n"); return 1; }
    CHECK(safepdf_select_init() == 0 && safepdf_select_init() == 0, "select init (twice)");
    safepdf_set_worker_path(argv[1]);
    q = dispatch_queue_create("org.safe-pdf.select-test", DISPATCH_QUEUE_SERIAL);

    safepdf_page_index *x = index_of("text/latin.pdf");
    if (!x || x->cell_count < 10) {
        printf("select_test: no page index\n");
        return 1;
    }
    char *err = NULL;
    safepdf_select_page *p = safepdf_select_page_new(x, &err);
    CHECK(p != NULL, "page handle (%s)", err ? err : "");
    free(err);
    if (p) {
        CHECK(safepdf_select_cell_count(p) == x->cell_count, "cell count %zu", x->cell_count);
        test_pointer(x, p);
        test_word_line(p);
        test_bands(x, p);
        test_copy(x, p);
        test_search(p);
        safepdf_select_page_release(p);
    }
    safepdf_free_page_index(x);
    test_edges();
    printf("select_test: %d checks, %d failures\n", checks, failures);
    return failures ? 1 : 0;
}
