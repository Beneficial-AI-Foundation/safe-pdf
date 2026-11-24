/*
 * core_test.c — end-to-end test of the C API v2 (task 11.3a1) on the goldens under
 * Tests/golden/, through the real confined worker.
 *
 *   core_test WORKER GOLDEN_DIR      (macos/tests/run.sh passes .lake/build/bin/worker and
 *                                     Tests/golden)
 *
 * Headless: no window, no AppKit. Every callback runs on a private serial dispatch queue and
 * signals a semaphore the main thread waits on (with a timeout, so a lost callback fails the
 * test instead of hanging it). Exit status 0 iff every check passed.
 */
#include "../safepdf_core.h"

#include <dispatch/dispatch.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static int checks = 0, failures = 0;

#define CHECK(cond, ...) do { \
    checks++; \
    if (!(cond)) { failures++; printf("FAIL %s:%d: ", __FILE__, __LINE__); printf(__VA_ARGS__); printf("\n"); } \
} while (0)

static const char *worker;
static const char *golden;
static dispatch_queue_t q;

static double now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e3 + ts.tv_nsec / 1e6;
}

static char *path_of(const char *rel) {
    size_t n = strlen(golden) + strlen(rel) + 2;
    char *p = malloc(n);
    snprintf(p, n, "%s/%s", golden, rel);
    return p;
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

/* What a callback reports back to the waiting test. */
typedef struct {
    dispatch_semaphore_t done;
    safepdf_request_id id;
    safepdf_status status;
    char error[512];
    void *result;
    int calls;
} reply;

static void reply_init(reply *r) {
    memset(r, 0, sizeof *r);
    r->done = dispatch_semaphore_create(0);
}

static void got(void *ctx, safepdf_request_id id, safepdf_status st, const char *err, void *res) {
    reply *r = ctx;
    r->id = id;
    r->status = st;
    r->result = res;
    r->calls++;
    if (err) snprintf(r->error, sizeof r->error, "%s", err);
    dispatch_semaphore_signal(r->done);
}

static void on_image(void *c, safepdf_request_id i, safepdf_status s, const char *e, safepdf_image *x) { got(c, i, s, e, x); }
static void on_index(void *c, safepdf_request_id i, safepdf_status s, const char *e, safepdf_page_index *x) { got(c, i, s, e, x); }
static void on_links(void *c, safepdf_request_id i, safepdf_status s, const char *e, safepdf_link_list *x) { got(c, i, s, e, x); }
static void on_outline(void *c, safepdf_request_id i, safepdf_status s, const char *e, safepdf_outline *x) { got(c, i, s, e, x); }
static void on_labels(void *c, safepdf_request_id i, safepdf_status s, const char *e, safepdf_label_list *x) { got(c, i, s, e, x); }
static void on_atts(void *c, safepdf_request_id i, safepdf_status s, const char *e, safepdf_attachment_list *x) { got(c, i, s, e, x); }
static void on_bytes(void *c, safepdf_request_id i, safepdf_status s, const char *e, safepdf_bytes *x) { got(c, i, s, e, x); }
static void on_layers(void *c, safepdf_request_id i, safepdf_status s, const char *e, safepdf_layers *x) { got(c, i, s, e, x); }

/* Waits for the callback (at most `ms`); 0 when it came. */
static int wait_for(reply *r, long ms) {
    return dispatch_semaphore_wait(r->done, dispatch_time(DISPATCH_TIME_NOW, ms * 1000000L)) == 0 ? 0 : -1;
}

static safepdf_document *open_golden(const char *rel, const safepdf_open_options *o) {
    char *p = path_of(rel);
    size_t len = 0;
    uint8_t *b = read_all(p, &len);
    char *err = NULL;
    safepdf_document *d = b ? safepdf_doc_open_bytes(b, len, o, &err) : NULL;
    if (!d) printf("open %s failed: %s\n", p, err ? err : "(cannot read)");
    free(err);
    free(b);
    free(p);
    return d;
}

/* Renders `page` of `d` through the worker and in process (safepdf_test_render_sync, the same
   renderer call) and checks the two images are equal byte for byte. */
static void check_render_equal(safepdf_document *d, const char *name, size_t page, uint32_t num,
                               uint32_t den, unsigned rot) {
    reply r;
    reply_init(&r);
    safepdf_request_id id = safepdf_doc_render(d, page, num, den, rot, NULL, SAFEPDF_PRIO_CURRENT,
                                               q, on_image, &r);
    CHECK(id > 0, "render id");
    CHECK(wait_for(&r, 30000) == 0, "render callback");
    CHECK(r.status == SAFEPDF_STATUS_OK && r.id == id, "%s p%zu render status %d (%s)", name, page,
          r.status, r.error);
    char *err = NULL;
    safepdf_image *b = safepdf_test_render_sync(d, page, num, den, rot, &err);
    CHECK(b != NULL, "%s p%zu in-process render: %s", name, page, err ? err : "");
    safepdf_image *a = r.result;
    if (a && b) {
        CHECK(a->width == b->width && a->height == b->height && a->stride == b->stride,
              "%s p%zu sizes %zux%zu vs %zux%zu", name, page, a->width, a->height, b->width, b->height);
        CHECK(a->width == b->width && a->height == b->height &&
                  memcmp(a->rgba, b->rgba, 4 * a->width * a->height) == 0,
              "%s p%zu rot %u: worker render equals the in-process render byte for byte", name, page, rot);
        printf("render %s p%zu at %u/%u rot %u: %zux%zu, worker == in-process\n", name, page, num, den,
               rot, a->width, a->height);
    }
    safepdf_free_image(a);
    safepdf_free_image(b);
    free(err);
}

/* ---- open from bytes, page count and size; the worker's render equals the in-process one
   (task 11.3c1: replaces the comparison with the retired v1 synchronous render) ---- */
static void test_render_equal(void) {
    safepdf_document *d = open_golden("text/latin.pdf", NULL);
    CHECK(d != NULL, "open latin.pdf from bytes");
    if (!d) return;
    CHECK(safepdf_doc_page_count(d) >= 1, "page count %zu", safepdf_doc_page_count(d));
    double w = 0, h = 0;
    CHECK(safepdf_doc_page_size(d, 0, &w, &h) == 0 && w > 0 && h > 0, "page size %gx%g", w, h);
    CHECK(safepdf_doc_page_size(d, 100000, &w, &h) == -1, "page size out of range");

    check_render_equal(d, "latin.pdf", 0, 3, 2, 0);
    check_render_equal(d, "latin.pdf", 0, 1, 1, 1);

    /* The test render's own error path. */
    char *err = NULL;
    CHECK(safepdf_test_render_sync(d, 9999, 1, 1, 0, &err) == NULL && err != NULL,
          "in-process render of a bad page -> error");
    free(err);

    /* Bad arguments are delivered as errors, not crashes. */
    reply r;
    reply_init(&r);
    safepdf_doc_render(d, 0, 0, 1, 0, NULL, 0, q, on_image, &r);
    CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_ERROR, "zero zoom -> error (%s)", r.error);
    reply_init(&r);
    safepdf_doc_render(d, 9999, 1, 1, 0, NULL, 0, q, on_image, &r);
    CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_ERROR, "bad page -> error (%s)", r.error);
    CHECK(safepdf_doc_render(NULL, 0, 1, 1, 0, NULL, 0, q, on_image, &r) == 0, "NULL doc -> 0");
    safepdf_doc_release(d);
}

/* ---- page geometry (task 11.3c1): exact CropBox and /Rotate, as Tests/golden/pages/tree.pdf's
   expected inspector output lists them ---- */
static int rat_is(safepdf_rat q, int64_t num, int64_t den) { return q.num == num && q.den == den; }

static double rat_d(safepdf_rat q) { return (double)q.num / (double)q.den; }

static void test_geom(void) {
    safepdf_document *d = open_golden("pages/tree.pdf", NULL);
    CHECK(d != NULL, "open tree.pdf");
    if (!d) return;
    CHECK(safepdf_doc_page_count(d) == 4, "tree.pdf has 4 pages (%zu)", safepdf_doc_page_count(d));
    /* crop [0 0 595.276 841.89] rotate 270; [0 0 300.5 400] 180; [0 0 595.276 841.89] 0;
       [0 0 612 792] 90 (tree.pdf.expected). */
    static const int64_t want[4][9] = {
        { 0, 1, 0, 1, 148819, 250, 84189, 100, 270 },
        { 0, 1, 0, 1, 601, 2, 400, 1, 180 },
        { 0, 1, 0, 1, 148819, 250, 84189, 100, 0 },
        { 0, 1, 0, 1, 612, 1, 792, 1, 90 },
    };
    for (size_t p = 0; p < 4 && p < safepdf_doc_page_count(d); p++) {
        safepdf_page_geom g;
        int rc = safepdf_doc_page_geom(d, p, &g);
        CHECK(rc == 0, "page_geom %zu", p);
        const int64_t *e = want[p];
        CHECK(rat_is(g.box.llx, e[0], e[1]) && rat_is(g.box.lly, e[2], e[3]) &&
                  rat_is(g.box.urx, e[4], e[5]) && rat_is(g.box.ury, e[6], e[7]) && g.rotate == e[8],
              "page %zu geom [%lld/%lld %lld/%lld %lld/%lld %lld/%lld] rot %u", p,
              (long long)g.box.llx.num, (long long)g.box.llx.den, (long long)g.box.lly.num,
              (long long)g.box.lly.den, (long long)g.box.urx.num, (long long)g.box.urx.den,
              (long long)g.box.ury.num, (long long)g.box.ury.den, g.rotate);
        /* Consistent with the displayed size (/Rotate swaps the sides). */
        double w = 0, h = 0;
        double bw = rat_d(g.box.urx) - rat_d(g.box.llx), bh = rat_d(g.box.ury) - rat_d(g.box.lly);
        safepdf_doc_page_size(d, p, &w, &h);
        int swap = g.rotate == 90 || g.rotate == 270;
        CHECK(fabs((swap ? bh : bw) - w) < 1e-6 && fabs((swap ? bw : bh) - h) < 1e-6,
              "page %zu size %gx%g vs geom %gx%g rot %u", p, w, h, bw, bh, g.rotate);
    }
    printf("geom: tree.pdf pages 0-3 match tree.pdf.expected (crop boxes exact, /Rotate 270 180 0 90)\n");
    safepdf_page_geom g;
    CHECK(safepdf_doc_page_geom(d, 4, &g) == -1 && g.box.llx.den == 0, "page_geom out of range -> -1, zeroed");
    CHECK(safepdf_doc_page_geom(NULL, 0, &g) == -1, "page_geom NULL doc -> -1");
    CHECK(safepdf_doc_page_geom(d, 0, NULL) == -1, "page_geom NULL out -> -1");

    /* Rotated pages render the same through the worker and in process, with and without an
       extra rotation. */
    check_render_equal(d, "tree.pdf", 1, 1, 2, 0);
    check_render_equal(d, "tree.pdf", 0, 1, 2, 3);
    check_render_equal(d, "tree.pdf", 3, 1, 2, 1);
    safepdf_doc_release(d);
}

/* ---- page index non-empty on a text page; in-process requests ---- */
static void test_text(void) {
    safepdf_document *d = open_golden("text/latin.pdf", NULL);
    if (!d) { CHECK(0, "open latin.pdf"); return; }
    reply r;
    reply_init(&r);
    safepdf_doc_page_index(d, 0, NULL, SAFEPDF_PRIO_CURRENT, q, on_index, &r);
    CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_OK, "page index (%s)", r.error);
    safepdf_page_index *x = r.result;
    if (x) {
        CHECK(x->cell_count > 0 && x->line_count > 0, "cells %zu lines %zu", x->cell_count, x->line_count);
        size_t chars = 0, badline = 0, badbox = 0;
        for (size_t i = 0; i < x->cell_count; i++) {
            chars += strlen(x->cells[i].text);
            if (x->cells[i].line >= x->line_count) badline++;
            if (!(x->cells[i].box.llx <= x->cells[i].box.urx)) badbox++;
        }
        CHECK(chars > 0, "cell text present");
        CHECK(badline == 0 && badbox == 0, "cells consistent (%zu bad lines, %zu bad boxes)", badline, badbox);
        printf("page index: %zu cells, %zu lines, first \"%s\"\n", x->cell_count, x->line_count,
               x->cell_count ? x->cells[0].text : "");
    }
    safepdf_free_page_index(x);

    reply_init(&r);
    safepdf_doc_attachments(d, q, on_atts, &r);
    CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_OK, "attachments (%s)", r.error);
    safepdf_attachment_list *al = r.result;
    CHECK(al && al->count == 0 && al->icon_count == 0, "no attachments in latin.pdf");
    safepdf_free_attachments(al);

    reply_init(&r);
    safepdf_doc_attachment_bytes(d, 0, q, on_bytes, &r);
    CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_ERROR, "attachment 0 -> error (%s)", r.error);

    reply_init(&r);
    safepdf_doc_layers(d, q, on_layers, &r);
    CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_OK, "layers (%s)", r.error);
    safepdf_layers *ly = r.result;
    CHECK(ly && ly->count == 0 && ly->initial.known_count == 0, "no layers in latin.pdf");
    safepdf_free_layers(ly);

    safepdf_layers_state st;
    char *err = NULL;
    CHECK(safepdf_layers_toggle(d, NULL, 0, &st, &err) == 0 && st.known_count == 0, "toggle without layers");
    safepdf_free_layers_state(&st);
    free(err);

    /* A page index under an explicit (empty) layers state. */
    safepdf_layers_state empty = { 0 };
    reply_init(&r);
    safepdf_doc_page_index(d, 0, &empty, 0, q, on_index, &r);
    CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_OK, "page index with a layers state (%s)", r.error);
    safepdf_free_page_index(r.result);
    safepdf_doc_release(d);
}

/* ---- links, labels and outline on files that have them ---- */
static void test_nav(void) {
    safepdf_document *d = open_golden("pages/outline.pdf", NULL);
    CHECK(d != NULL, "open outline.pdf");
    if (d) {
        reply r;
        reply_init(&r);
        safepdf_doc_outline(d, SAFEPDF_PRIO_CURRENT, q, on_outline, &r);
        CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_OK, "outline (%s)", r.error);
        safepdf_outline *o = r.result;
        CHECK(o && o->count > 0, "outline has items");
        if (o) {
            int depth_ok = 1;
            for (size_t i = 0; i < o->count; i++) {
                if (i == 0 ? o->items[i].depth != 0 : o->items[i].depth > o->items[i - 1].depth + 1) depth_ok = 0;
                if (!o->items[i].title || !o->items[i].action.text) depth_ok = 0;
            }
            CHECK(depth_ok, "outline depths clamped, strings present");
            printf("outline: %zu items, first \"%s\" (action %d page %zu)\n", o->count,
                   o->count ? o->items[0].title : "", o->count ? (int)o->items[0].action.kind : -1,
                   o->count ? o->items[0].action.page : 0);
        }
        safepdf_free_outline(o);
        safepdf_doc_release(d);
    }

    d = open_golden("pages/tree.pdf", NULL);
    CHECK(d != NULL, "open tree.pdf");
    if (!d) return;
    size_t n = safepdf_doc_page_count(d), total = 0;
    for (size_t p = 0; p < n; p++) {
        reply r;
        reply_init(&r);
        safepdf_doc_links(d, p, SAFEPDF_PRIO_VISIBLE, q, on_links, &r);
        CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_OK, "links of page %zu (%s)", p, r.error);
        safepdf_link_list *l = r.result;
        if (l) {
            total += l->count;
            for (size_t i = 0; i < l->count; i++)
                printf("link p%zu: [%g %g %g %g] kind %d page %zu text \"%s\"\n", p, l->links[i].box.llx,
                       l->links[i].box.lly, l->links[i].box.urx, l->links[i].box.ury,
                       (int)l->links[i].action.kind, l->links[i].action.page, l->links[i].action.text);
        }
        safepdf_free_links(l);
    }
    CHECK(total > 0, "tree.pdf has links (%zu)", total);

    reply r;
    reply_init(&r);
    safepdf_doc_page_labels(d, q, on_labels, &r);
    CHECK(wait_for(&r, 30000) == 0 && r.status == SAFEPDF_STATUS_OK, "labels (%s)", r.error);
    safepdf_label_list *lb = r.result;
    CHECK(lb && lb->count == n, "one label per page");
    if (lb) {
        size_t named = 0;
        for (size_t i = 0; i < lb->count; i++) if (lb->labels[i][0]) named++;
        CHECK(named > 0, "tree.pdf has page labels");
        printf("labels: %zu pages, first \"%s\"\n", lb->count, lb->count ? lb->labels[0] : "");
    }
    safepdf_free_labels(lb);
    safepdf_doc_release(d);
}

/* ---- cancel a queued request and one in flight ---- */
static void test_cancel(void) {
    safepdf_open_options o = { .test_stall_ms = 4000 };
    safepdf_document *d = open_golden("text/latin.pdf", &o);
    if (!d) { CHECK(0, "open with stall"); return; }
    reply a, b;
    reply_init(&a);
    reply_init(&b);
    safepdf_request_id ia = safepdf_doc_render(d, 0, 1, 1, 0, NULL, SAFEPDF_PRIO_CURRENT, q, on_image, &a);
    usleep(1000 * 1000); /* the worker is spawned and A is in flight (stalled for 4 s) */
    CHECK(dispatch_semaphore_wait(a.done, DISPATCH_TIME_NOW) != 0, "A still running");
    safepdf_request_id ib = safepdf_doc_render(d, 0, 2, 1, 0, NULL, SAFEPDF_PRIO_THUMBNAIL, q, on_image, &b);
    double t0 = now_ms();
    safepdf_doc_cancel(d, ib);
    safepdf_doc_cancel(d, ia);
    CHECK(wait_for(&a, 30000) == 0, "in-flight cancel delivered");
    CHECK(wait_for(&b, 30000) == 0, "queued cancel delivered");
    double dt = now_ms() - t0;
    CHECK(a.status == SAFEPDF_STATUS_CANCELLED && a.result == NULL, "in flight -> cancelled (%d %s)", a.status, a.error);
    CHECK(b.status == SAFEPDF_STATUS_CANCELLED && b.result == NULL, "queued -> cancelled (%d %s)", b.status, b.error);
    CHECK(dt < 2000, "cancel did not wait for the stalled render (%.0f ms)", dt);
    printf("cancel: in-flight and queued delivered %.0f ms after the cancel\n", dt);

    /* The next request works (fresh worker): a page index is not stalled. */
    reply c;
    reply_init(&c);
    safepdf_doc_page_index(d, 0, NULL, 0, q, on_index, &c);
    CHECK(wait_for(&c, 30000) == 0 && c.status == SAFEPDF_STATUS_OK, "request after a cancel (%s)", c.error);
    safepdf_free_page_index(c.result);

    /* raise: harmless on queued and unknown ids. */
    safepdf_doc_raise(d, 999999, 0);
    safepdf_doc_cancel(d, 999999);
    safepdf_doc_release(d);
}

/* ---- release while a request is pending; retain/release ---- */
static void test_release_pending(void) {
    safepdf_open_options o = { .test_stall_ms = 5000 };
    safepdf_document *d = open_golden("text/latin.pdf", &o);
    if (!d) { CHECK(0, "open with stall"); return; }
    CHECK(safepdf_doc_retain(d) == d, "retain");
    safepdf_doc_release(d); /* back to one reference: nothing closes */
    reply a, b;
    reply_init(&a);
    reply_init(&b);
    safepdf_doc_render(d, 0, 1, 1, 0, NULL, 0, q, on_image, &a);
    safepdf_doc_render(d, 0, 2, 1, 0, NULL, 1, q, on_image, &b);
    usleep(1000 * 1000); /* A in flight (stalled for 5 s), B queued */
    CHECK(dispatch_semaphore_wait(a.done, DISPATCH_TIME_NOW) != 0, "A still running");
    double t0 = now_ms();
    safepdf_doc_release(d);
    double dt = now_ms() - t0;
    CHECK(wait_for(&a, 5000) == 0 && wait_for(&b, 5000) == 0, "pending callbacks delivered after release");
    CHECK(a.status == SAFEPDF_STATUS_CANCELLED && b.status == SAFEPDF_STATUS_CANCELLED,
          "pending -> cancelled (%d %d)", a.status, b.status);
    CHECK(a.calls == 1 && b.calls == 1, "exactly once");
    CHECK(dt < 4000, "release drained without waiting for the stalled render (%.0f ms)", dt);
    printf("release with 2 pending: %.0f ms\n", dt);
}

/* ---- the deadline kills the worker; the next request respawns it ---- */
static void test_deadline(void) {
    safepdf_open_options o = { .test_stall_ms = 3000, .deadline_ms = 700 };
    safepdf_document *d = open_golden("text/latin.pdf", &o);
    if (!d) { CHECK(0, "open with deadline"); return; }
    reply a;
    reply_init(&a);
    safepdf_doc_render(d, 0, 1, 1, 0, NULL, 0, q, on_image, &a);
    CHECK(wait_for(&a, 30000) == 0, "deadline delivered");
    CHECK(a.status == SAFEPDF_STATUS_ERROR && strstr(a.error, "too long"), "deadline -> error (%d %s)", a.status, a.error);
    printf("deadline: \"%s\"\n", a.error);
    reply b;
    reply_init(&b);
    safepdf_doc_page_index(d, 0, NULL, 0, q, on_index, &b);
    CHECK(wait_for(&b, 30000) == 0 && b.status == SAFEPDF_STATUS_OK, "respawned after the deadline (%s)", b.error);
    safepdf_free_page_index(b.result);
    safepdf_doc_release(d);
}

/* ---- the API from a callback (a GCD thread the runtime has not seen) ---- */
typedef struct { safepdf_document *d; reply inner; dispatch_semaphore_t done; } chain;

static void chain_first(void *c, safepdf_request_id i, safepdf_status s, const char *e, safepdf_image *x) {
    (void)i; (void)s; (void)e;
    chain *ch = c;
    safepdf_free_image(x);
    safepdf_doc_page_index(ch->d, 0, NULL, 0, q, on_index, &ch->inner);
    dispatch_semaphore_signal(ch->done);
}

static void test_chain(void) {
    safepdf_document *d = open_golden("text/latin.pdf", NULL);
    if (!d) { CHECK(0, "open"); return; }
    chain ch = { .d = d, .done = dispatch_semaphore_create(0) };
    reply_init(&ch.inner);
    dispatch_queue_t other = dispatch_get_global_queue(QOS_CLASS_UTILITY, 0);
    safepdf_doc_render(d, 0, 1, 2, 0, NULL, 0, other, chain_first, &ch);
    CHECK(dispatch_semaphore_wait(ch.done, dispatch_time(DISPATCH_TIME_NOW, 30000000000L)) == 0, "first callback");
    CHECK(wait_for(&ch.inner, 30000) == 0 && ch.inner.status == SAFEPDF_STATUS_OK,
          "request submitted from a callback (%s)", ch.inner.error);
    safepdf_free_page_index(ch.inner.result);
    safepdf_doc_release(d);
}

/* ---- malformed and missing files: errors, not crashes ---- */
static void test_errors(void) {
    char *err = NULL;
    const char junk[] = "this is not a PDF at all";
    safepdf_document *d = safepdf_doc_open_bytes((const uint8_t *)junk, sizeof junk - 1, NULL, &err);
    CHECK(d == NULL && err != NULL, "garbage bytes -> error");
    printf("garbage: \"%s\"\n", err ? err : "");
    free(err);
    err = NULL;
    d = open_golden("header/missing-header.bin", NULL);
    CHECK(d == NULL, "missing header -> error");
    char *p = path_of("header/broken-startxref.pdf");
    d = safepdf_doc_open_file(p, NULL, &err);
    printf("broken-startxref: %s%s\n", d ? "opened (repaired: " : "error: ", d ? (safepdf_doc_is_repaired(d) ? "yes)" : "no)") : (err ? err : ""));
    safepdf_doc_release(d);
    free(err);
    err = NULL;
    safepdf_open_options strict = { .strict = 1 };
    d = safepdf_doc_open_file(p, &strict, &err);
    CHECK(d == NULL || !safepdf_doc_is_repaired(d), "strict mode never repairs");
    safepdf_doc_release(d);
    free(err);
    err = NULL;
    free(p);
    d = safepdf_doc_open_file("/nonexistent/file.pdf", NULL, &err);
    CHECK(d == NULL && err != NULL, "missing file -> error");
    free(err);
    err = NULL;
    p = path_of("text/latin.pdf");
    d = safepdf_doc_open_file(p, NULL, &err);
    CHECK(d != NULL, "open_file latin.pdf (%s)", err ? err : "");
    safepdf_doc_release(d);
    free(err);
    err = NULL;
    safepdf_open_options nowk = { .worker_path = "/nonexistent/worker" };
    d = safepdf_doc_open_file(p, &nowk, &err);
    CHECK(d == NULL && err && strstr(err, "no document worker"), "missing worker -> error (%s)", err ? err : "");
    free(err);
    free(p);
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: %s WORKER GOLDEN_DIR\n", argv[0]);
        return 2;
    }
    worker = argv[1];
    golden = argv[2];
    if (safepdf_init() != 0) { fprintf(stderr, "init failed\n"); return 1; }
    safepdf_set_worker_path(worker);
    q = dispatch_queue_create("org.safe-pdf.core-test", DISPATCH_QUEUE_SERIAL);
    double t0 = now_ms();
    test_render_equal();
    test_geom();
    test_text();
    test_nav();
    test_cancel();
    test_release_pending();
    test_deadline();
    test_chain();
    test_errors();
    printf("core_test: %d checks, %d failures (%.0f ms)\n", checks, failures, now_ms() - t0);
    return failures ? 1 : 0;
}
