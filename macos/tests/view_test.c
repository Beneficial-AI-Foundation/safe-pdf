/*
 * view_test.c — checks of the view/chrome C API (safepdf_view.h, task 11.3a2) against values
 * the Lean side also checks (#guards in SafePdf/Shell/App/View.lean, Toolbar.lean, Menu.lean
 * and SafePdf/Shell/FfiView.lean). Prints one line per failed check and a summary; exit
 * status 0 when everything passed. Built and run by macos/tests/run_view.sh.
 */
#include "safepdf_core.h"
#include "safepdf_view.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int checks = 0, failures = 0;

#define CHECK(cond) do { checks++; if (!(cond)) { failures++; \
    fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond); } } while (0)

static safepdf_rat R(int64_t n, int64_t d) { safepdf_rat q = { n, d }; return q; }
static int req(safepdf_rat a, int64_t n, int64_t d) { return a.num == n && a.den == d; }
static safepdf_rat_box box(int64_t w, int64_t h) {
    safepdf_rat_box b = { R(0, 1), R(0, 1), R(w, 1), R(h, 1) };
    return b;
}

static void test_zoom(void) {
    safepdf_rat z;
    /* View.lean: quant (4/3) = 85/64, quant 0 = 1/64. */
    CHECK(safepdf_view_quant(R(4, 3), &z) == 0 && req(z, 85, 64));
    CHECK(safepdf_view_quant(R(0, 1), &z) == 0 && req(z, 1, 64));
    CHECK(safepdf_view_quant(R(1, 0), &z) == -1); /* den 0 rejected */
    /* The 10.11 collision at tk scaling 1.334 (View.lean #guards). */
    safepdf_rat s = R(1334, 1000);
    CHECK(safepdf_view_pct_zoom(125, s, &z) == 0 && req(z, 53, 32)); /* 106/64 */
    uint32_t pct = 0;
    CHECK(safepdf_view_zoom_pct(R(106, 64), s, &pct) == 0 && pct == 124);
    CHECK(safepdf_view_step_in(R(106, 64), s, &pct) == 1 && pct == 150);
    safepdf_rat z150;
    CHECK(safepdf_view_pct_zoom(150, s, &z150) == 0);
    CHECK(safepdf_view_step_out(z150, s, &pct) == 1 && pct == 125);
    CHECK(safepdf_view_step_in(R(1, 1), R(1, 1), &pct) == 1 && pct == 125);
    CHECK(safepdf_view_step_out(R(1, 1), R(1, 1), &pct) == 1 && pct == 75);
    CHECK(safepdf_view_step_in(R(9, 1), R(1, 1), &pct) == 0);
    CHECK(safepdf_view_step_out(R(1, 64), R(1, 1), &pct) == 0);
    /* fitZoom #guards. */
    CHECK(safepdf_view_fit_zoom(true, 216, 216, R(100, 1), R(200, 1), &z) == 0 && req(z, 2, 1));
    CHECK(safepdf_view_fit_zoom(false, 216, 216, R(100, 1), R(200, 1), &z) == 0 && req(z, 1, 1));
    CHECK(safepdf_view_fit_zoom(false, 100, 100, R(10000, 1), R(10000, 1), &z) == 0 &&
          req(z, 1, 16));
    /* capZoom #guards. */
    safepdf_rat_box b100 = box(100, 100);
    bool lowered = true;
    CHECK(safepdf_view_cap_zoom(10000, R(1, 1), 0, &b100, &z, &lowered) == 0 && req(z, 1, 1) &&
          !lowered);
    CHECK(safepdf_view_cap_zoom(2500, R(1, 1), 0, &b100, &z, &lowered) == 0 && lowered);
    safepdf_pixel_size px;
    CHECK(safepdf_view_pixel_size(16384, z, 0, &b100, &px) == 0 &&
          px.width * px.height <= 2500 && px.width * px.height >= 2000);
    safepdf_rat_box tall = box(100, 20000);
    CHECK(safepdf_view_pixel_size(16384, R(1, 1), 0, &tall, &px) == 0 && px.cropped &&
          px.image_height == 16384 && px.height == 20000);
    uint32_t steps[32];
    size_t n = safepdf_view_zoom_steps(steps, 32);
    CHECK(n == 13 && steps[0] == 25 && steps[12] == 800);
    safepdf_view_constants c;
    CHECK(safepdf_view_get_constants(&c) == 0 && c.margin == 8 && c.page_gap == 10 &&
          c.min_pct == 25 && c.max_pct == 800 && c.auto_max_pct == 125 &&
          c.page_pixels == 10485760 && c.max_page_side == 16384 &&
          c.max_view_pixels == (1u << 26));
}

static void test_rotation(void) {
    safepdf_rat_box letter = box(612, 792);
    safepdf_rotation_info ri;
    CHECK(safepdf_view_rotation(270, &letter, &ri) == 0 && ri.cw == 0 && ri.ccw == 180 &&
          req(ri.width, 792, 1) && req(ri.height, 612, 1));
    CHECK(safepdf_view_rotation(90, &letter, &ri) == 0 && ri.cw == 180 && ri.ccw == 0);
    /* View.lean: reanchor 1 .r0 2 .r90 Letter (306, 396) = (792, 612); (100, 50) → (200, 100). */
    safepdf_rat_point q = { R(306, 1), R(396, 1) }, p;
    CHECK(safepdf_view_reanchor(R(1, 1), 0, R(2, 1), 90, &letter, q, &p) == 0 &&
          req(p.x, 792, 1) && req(p.y, 612, 1));
    safepdf_rat_point q2 = { R(100, 1), R(50, 1) };
    CHECK(safepdf_view_reanchor(R(1, 1), 0, R(2, 1), 0, &letter, q2, &p) == 0 &&
          req(p.x, 200, 1) && req(p.y, 100, 1));
    /* reanchor_self: nothing changed, the point stays. */
    safepdf_rat_point q3 = { R(7, 3), R(-5, 2) };
    CHECK(safepdf_view_reanchor(R(85, 64), 180, R(85, 64), 180, &letter, q3, &p) == 0 &&
          req(p.x, 7, 3) && req(p.y, -5, 2));
}

static void test_spreads_layout(void) {
    /* View.lean: nextPage .odd 5 = [2, 2, 4, 4, 4]; prevPage .even = [0, 0, 0, 1, 1];
       spreads .even 5 = [[0], [1, 2], [3, 4]]. */
    const size_t next_odd[5] = { 2, 2, 4, 4, 4 }, prev_even[5] = { 0, 0, 0, 1, 1 };
    safepdf_spread_info si;
    for (size_t pg = 0; pg < 5; pg++) {
        CHECK(safepdf_view_spread(SAFEPDF_SPREAD_ODD, 5, pg, &si) == 0 && si.next_page == next_odd[pg]);
        CHECK(safepdf_view_spread(SAFEPDF_SPREAD_EVEN, 5, pg, &si) == 0 && si.prev_page == prev_even[pg]);
    }
    CHECK(safepdf_view_spread(SAFEPDF_SPREAD_EVEN, 5, 2, &si) == 0 && si.spread == 1 &&
          si.spread_count == 3 && si.page_count == 2 && si.pages[0] == 1 && si.pages[1] == 2);
    CHECK(safepdf_view_spread(SAFEPDF_SPREAD_EVEN, 5, 0, &si) == 0 && si.page_count == 1 &&
          si.pages[0] == 0);

    /* Four 100 × 200 pages at 100 % in a 300 × 300 canvas, vertical (FfiView.lean #guard and
       View.lean's layoutRows / visiblePages / wantedPages / pageAt / topFor #guards). */
    safepdf_page_geom pages[4];
    for (int i = 0; i < 4; i++) { pages[i].box = box(100, 200); pages[i].rotate = 0; }
    safepdf_layout_params lp = { SAFEPDF_SCROLL_VERTICAL, SAFEPDF_SPREAD_NONE, 0,
                                 { SAFEPDF_ZOOM_PERCENT, 100 }, R(1, 1), 300, 300, 0, false };
    safepdf_layout l;
    CHECK(safepdf_view_layout(pages, 4, &lp, &l) == 0);
    CHECK(l.count == 4 && req(l.base_zoom, 1, 1) && l.region_w == 300 && l.region_h == 846);
    const uint64_t ys[4] = { 8, 218, 428, 638 };
    for (size_t i = 0; i < l.count && i < 4; i++)
        CHECK(l.places[i].page == i && l.places[i].x == 100 && l.places[i].y == ys[i] &&
              l.places[i].w == 100 && l.places[i].h == 200 && req(l.places[i].zoom, 1, 1) &&
              !l.places[i].capped && !l.places[i].cropped);
    safepdf_page_band band;
    CHECK(safepdf_view_pages_in_band(&l, 0, 300, &band) == 0 && band.visible_count == 2 &&
          band.visible[0] == 0 && band.visible[1] == 1 && band.wanted_count == 3 &&
          band.wanted[2] == 2);
    safepdf_free_page_band(&band);
    CHECK(safepdf_view_pages_in_band(&l, 400, 600, &band) == 0 && band.visible_count == 2 &&
          band.visible[0] == 1 && band.wanted_count == 4);
    safepdf_free_page_band(&band);
    safepdf_page_hit hit;
    CHECK(safepdf_view_page_at(&l, 150, 300, 300, &hit) == 1 && hit.page == 1);
    CHECK(safepdf_view_page_at(&l, 0, 9999, 300, &hit) == 1 && hit.page == 3);
    CHECK(safepdf_view_page_at(&l, 150, 430, 300, &hit) == 1 && hit.page == 2 &&
          hit.top == 420 && hit.bottom == 336);
    safepdf_free_layout(&l);
    CHECK(l.places == NULL && l.count == 0);

    /* Page scroll mode, odd spreads: only the current spread (pages 2|3 of 5). */
    safepdf_page_geom five[5];
    for (int i = 0; i < 5; i++) { five[i].box = box(100, 200); five[i].rotate = 0; }
    lp.scroll = SAFEPDF_SCROLL_PAGE; lp.spread = SAFEPDF_SPREAD_ODD; lp.page = 2;
    CHECK(safepdf_view_layout(five, 5, &lp, &l) == 0 && l.count == 2 &&
          l.places[0].page == 2 && l.places[1].page == 3 && l.places[0].x < l.places[1].x);
    safepdf_free_layout(&l);
    lp.rtl = true; /* right-to-left: the first page of the spread on the right */
    CHECK(safepdf_view_layout(five, 5, &lp, &l) == 0 && l.count == 2 &&
          l.places[0].page == 2 && l.places[0].x > l.places[1].x);
    safepdf_free_layout(&l);

    /* Automatic Zoom on a Letter page in a wide window: 125 % at 4/3 (Toolbar.lean #guard). */
    safepdf_page_geom letter = { box(612, 792), 0 };
    safepdf_layout_params la = { SAFEPDF_SCROLL_VERTICAL, SAFEPDF_SPREAD_NONE, 0,
                                 { SAFEPDF_ZOOM_AUTO, 0 }, R(4, 3), 1900, 900, 0, false };
    safepdf_rat z125;
    CHECK(safepdf_view_pct_zoom(125, R(4, 3), &z125) == 0);
    CHECK(safepdf_view_layout(&letter, 1, &la, &l) == 0 && l.count == 1 &&
          l.base_zoom.num == z125.num && l.base_zoom.den == z125.den &&
          l.places[0].rotation == 0);
    safepdf_free_layout(&l);
    letter.rotate = 90; la.user_rotation = 90;
    CHECK(safepdf_view_layout(&letter, 1, &la, &l) == 0 && l.count == 1 &&
          l.places[0].rotation == 180);
    safepdf_free_layout(&l);
    CHECK(safepdf_view_layout(NULL, 0, &la, &l) == 0 && l.count == 0);
    safepdf_free_layout(&l);
}

static void test_zoom_choices(void) {
    static const char *labels[] = { "Automatic Zoom", "Actual Size", "Page Fit", "Page Width",
        "50%", "75%", "100%", "125%", "150%", "200%", "300%", "400%" };
    safepdf_zoom_presets zp;
    CHECK(safepdf_view_zoom_presets(&zp) == 0 && zp.count == 12);
    for (size_t i = 0; i < zp.count && i < 12; i++) CHECK(strcmp(zp.items[i].label, labels[i]) == 0);
    if (zp.count == 12) {
        CHECK(zp.items[0].choice.kind == SAFEPDF_ZOOM_AUTO && strcmp(zp.items[0].key, "auto") == 0);
        CHECK(zp.items[8].choice.kind == SAFEPDF_ZOOM_PERCENT && zp.items[8].choice.pct == 150 &&
              strcmp(zp.items[8].key, "150") == 0);
    }
    safepdf_free_zoom_presets(&zp);
    safepdf_zoom_choice zc = { SAFEPDF_ZOOM_PERCENT, 33 };
    char *lab = safepdf_view_zoom_label(zc);
    CHECK(lab && strcmp(lab, "33%") == 0);
    free(lab);
    CHECK(safepdf_view_zoom_parse("33", &zc) == 1 && zc.kind == SAFEPDF_ZOOM_PERCENT && zc.pct == 33);
    CHECK(safepdf_view_zoom_parse("page-fit", &zc) == 1 && zc.kind == SAFEPDF_ZOOM_PAGE_FIT);
    CHECK(safepdf_view_zoom_parse("5", &zc) == 0 && safepdf_view_zoom_parse("9000", &zc) == 0 &&
          safepdf_view_zoom_parse("x", &zc) == 0);
    /* ZoomChoice.auto.zoom 400 900 (4/3) 612 792 = fitZoom true 400 900 612 792. */
    safepdf_zoom_choice autoz = { SAFEPDF_ZOOM_AUTO, 0 };
    safepdf_rat a, f;
    CHECK(safepdf_view_zoom_with(autoz, 400, 900, R(4, 3), R(612, 1), R(792, 1), true, &a) == 0 &&
          safepdf_view_fit_zoom(true, 400, 900, R(612, 1), R(792, 1), &f) == 0 &&
          a.num == f.num && a.den == f.den);

    safepdf_view_choices vc;
    static const char *vlabels[] = { "Single Page", "Vertical Scrolling", "Two Pages",
                                     "Two Pages Scrolling" };
    CHECK(safepdf_view_view_choices(&vc) == 0 && vc.count == 4);
    for (size_t i = 0; i < vc.count && i < 4; i++)
        CHECK(vc.items[i].choice == i && strcmp(vc.items[i].label, vlabels[i]) == 0);
    safepdf_free_view_choices(&vc);
    CHECK(safepdf_view_choice_of_modes(SAFEPDF_SCROLL_VERTICAL, SAFEPDF_SPREAD_NONE) == SAFEPDF_VIEW_VERTICAL);
    CHECK(safepdf_view_choice_of_modes(SAFEPDF_SCROLL_PAGE, SAFEPDF_SPREAD_EVEN) == SAFEPDF_VIEW_TWO);
    uint32_t sc, sp;
    CHECK(safepdf_view_choice_modes(SAFEPDF_VIEW_TWO, SAFEPDF_SPREAD_EVEN, &sc, &sp) == 0 &&
          sc == SAFEPDF_SCROLL_PAGE && sp == SAFEPDF_SPREAD_EVEN);
    CHECK(safepdf_view_choice_modes(SAFEPDF_VIEW_TWO, SAFEPDF_SPREAD_NONE, &sc, &sp) == 0 &&
          sp == SAFEPDF_SPREAD_ODD);

    /* Page field (Toolbar.lean #guards). */
    const char *roman[] = { "i", "ii", "1" };
    char *e = NULL, *o = NULL;
    CHECK(safepdf_view_page_field(roman, 3, 1, 3, &e, &o) == 0 && strcmp(e, "ii") == 0 &&
          strcmp(o, "(2 of 3)") == 0);
    free(e); free(o);
    CHECK(safepdf_view_page_field(NULL, 0, 4, 9, &e, &o) == 0 && strcmp(e, "5") == 0 &&
          strcmp(o, "of 9") == 0);
    free(e); free(o);
    size_t pg = 99;
    CHECK(safepdf_view_page_entry(roman, 3, 3, 0, "II", &pg) == 1 && pg == 1);
    CHECK(safepdf_view_page_entry(roman, 3, 3, 0, "1", &pg) == 1 && pg == 2);
    const char *nums[] = { "1", "2", "3" };
    CHECK(safepdf_view_page_entry(nums, 3, 3, 1, "4", &pg) == 0 && pg == 1);
    CHECK(safepdf_view_page_entry(nums, 3, 3, 0, " 2 ", &pg) == 1 && pg == 1);
}

static void test_chrome(void) {
    /* Command enum ↔ Lean constructor names. */
    static const char *names[SAFEPDF_CMD_COUNT] = { "openFile", "save", "saveAs", "importXfdf",
        "exportXfdf", "close", "quit", "undo", "redo", "copy", "selectAll", "highlight",
        "addNote", "deleteMark", "hlTool", "showAll", "find", "outline", "zoomIn", "zoomOut",
        "actualSize", "fitPage", "fitWidth", "rotateCw", "rotateCcw", "scrollPage",
        "scrollVertical", "spreadNone", "spreadOdd", "spreadEven", "prevPage", "nextPage",
        "firstPage", "lastPage", "gotoPage", "back", "forward", "about" };
    safepdf_commands cmds;
    CHECK(safepdf_view_commands(&cmds) == 0 && cmds.count == SAFEPDF_CMD_COUNT);
    for (size_t i = 0; i < cmds.count && i < SAFEPDF_CMD_COUNT; i++)
        CHECK(cmds.items[i].id == i && strcmp(cmds.items[i].name, names[i]) == 0);
    if (cmds.count == SAFEPDF_CMD_COUNT) {
        safepdf_command *g = &cmds.items[SAFEPDF_CMD_GOTO_PAGE];
        CHECK(g->accel.mods == (SAFEPDF_MOD_COMMAND | SAFEPDF_MOD_OPTION) &&
              strcmp(g->accel.key, "g") == 0);
        safepdf_command *sb = &cmds.items[SAFEPDF_CMD_OUTLINE];
        CHECK(sb->accel.mods == (SAFEPDF_MOD_COMMAND | SAFEPDF_MOD_CONTROL) &&
              strcmp(sb->accel.key, "s") == 0 && strcmp(sb->label, "Sidebar") == 0);
        CHECK(cmds.items[SAFEPDF_CMD_SAVE_AS].accel.mods == (SAFEPDF_MOD_COMMAND | SAFEPDF_MOD_SHIFT));
        CHECK(cmds.items[SAFEPDF_CMD_BACK].accel.mods == SAFEPDF_MOD_COMMAND &&
              strcmp(cmds.items[SAFEPDF_CMD_BACK].accel.key, "bracketleft") == 0);
        CHECK(cmds.items[SAFEPDF_CMD_PREV_PAGE].accel.mods == 0 &&
              strcmp(cmds.items[SAFEPDF_CMD_PREV_PAGE].accel.key, "Prior") == 0);
        CHECK(strcmp(cmds.items[SAFEPDF_CMD_ABOUT].label, "About SafePDF") == 0 &&
              strcmp(cmds.items[SAFEPDF_CMD_ABOUT].accel.key, "") == 0);
    }
    safepdf_free_commands(&cmds);
    CHECK(safepdf_view_actions(&cmds) == 0 && cmds.count == SAFEPDF_ACTION_COUNT &&
          strcmp(cmds.items[SAFEPDF_ACTION_FIND_NEXT].name, "findNext") == 0 &&
          strcmp(cmds.items[SAFEPDF_ACTION_FIND_PREV].label, "Find previous") == 0);
    safepdf_free_commands(&cmds);
    char *app = safepdf_view_app_name();
    CHECK(app && strcmp(app, "SafePDF") == 0);
    free(app);

    /* Menubar (Menu.lean: labels; locate .quit = (file, 9); locate .zoomIn = (view, 2)). */
    safepdf_menu_table mt;
    CHECK(safepdf_view_menubar(&mt) == 0 && mt.menu_count == 5);
    static const char *menus[] = { "File", "Edit", "View", "Go", "Help" };
    for (size_t i = 0; i < mt.menu_count && i < 5; i++) CHECK(strcmp(mt.menu_labels[i], menus[i]) == 0);
    size_t idx[5] = { 0 }, cmd_entries = 0;
    int quit_at = -1, zoomin_at = -1, colors = 0, radios = 0;
    for (size_t i = 0; i < mt.entry_count; i++) {
        safepdf_menu_entry *e = &mt.entries[i];
        if (e->menu >= 5) { CHECK(e->menu < 5); continue; }
        if (e->cmd == SAFEPDF_CMD_QUIT) { quit_at = (int)idx[e->menu]; CHECK(e->menu == 0); }
        if (e->cmd == SAFEPDF_CMD_ZOOM_IN) { zoomin_at = (int)idx[e->menu]; CHECK(e->menu == 2); }
        if (e->kind == SAFEPDF_ENTRY_COLORS) colors++;
        if (e->radio_group != SAFEPDF_RADIO_NONE) radios++;
        if (e->cmd >= 0) cmd_entries++;
        idx[e->menu]++;
    }
    CHECK(quit_at == 9 && zoomin_at == 2 && colors == 1 && radios == 5);
    CHECK(cmd_entries == SAFEPDF_CMD_COUNT); /* every command exactly once (Menu.lean #guard) */
    safepdf_free_menu_table(&mt);
    CHECK(safepdf_view_overflow_menu(&mt) == 0 && mt.menu_count == 1 &&
          strcmp(mt.menu_labels[0], "Tools") == 0 && mt.entry_count == 19 &&
          mt.entries[0].cmd == SAFEPDF_CMD_OPEN_FILE && mt.entries[3].kind == SAFEPDF_ENTRY_SEPARATOR);
    safepdf_free_menu_table(&mt);

    /* Key table: ⌘G is Find next; ⌥⌘G Go to page; Ctrl+G (X11 column) Go to page too. */
    safepdf_key_table kt;
    CHECK(safepdf_view_keys(&kt) == 0 && kt.count > 0);
    int find_next = 0, goto_mac = 0, goto_x11 = 0;
    for (size_t i = 0; i < kt.count; i++) {
        safepdf_key_binding *k = &kt.items[i];
        if (strcmp(k->key.key, "g") != 0) continue;
        if (!k->x11 && k->key.mods == SAFEPDF_MOD_COMMAND && k->target_kind == 1 &&
            k->target == SAFEPDF_ACTION_FIND_NEXT) find_next++;
        if (!k->x11 && k->key.mods == (SAFEPDF_MOD_COMMAND | SAFEPDF_MOD_OPTION) &&
            k->target_kind == 0 && k->target == SAFEPDF_CMD_GOTO_PAGE) goto_mac++;
        if (k->x11 && k->key.mods == SAFEPDF_MOD_CONTROL && k->target_kind == 0 &&
            k->target == SAFEPDF_CMD_GOTO_PAGE) goto_x11++;
    }
    CHECK(find_next == 1 && goto_mac == 1 && goto_x11 == 1);
    safepdf_free_key_table(&kt);

    /* Toolbar (Toolbar.lean #guards: 14 buttons; enabled sets). */
    safepdf_toolbar tb;
    CHECK(safepdf_view_toolbar(&tb) == 0);
    size_t buttons = 0;
    for (size_t i = 0; i < tb.count; i++) if (tb.items[i].kind == SAFEPDF_ITEM_BUTTON) buttons++;
    CHECK(buttons == 14 && tb.count > 0 && strcmp(tb.items[0].id, "sidebar") == 0 &&
          tb.items[0].cmd == SAFEPDF_CMD_OUTLINE && strcmp(tb.items[tb.count - 1].id, "more") == 0 &&
          tb.items[tb.count - 1].action == SAFEPDF_ACT_MORE);
    for (size_t i = 0; i < tb.count; i++)
        if (strcmp(tb.items[i].id, "save") == 0)
            CHECK(strcmp(tb.items[i].tooltip, "Save (\xe2\x8c\x98S)") == 0); /* ⌘S */
    safepdf_ctx none;
    memset(&none, 0, sizeof none);
    safepdf_chrome_states st;
    CHECK(safepdf_view_states(&none, &st) == 0 && st.item_count == tb.count);
    size_t en = 0;
    for (size_t i = 0; i < SAFEPDF_CMD_COUNT; i++) en += st.command_enabled[i];
    CHECK(en == 3 && st.command_enabled[SAFEPDF_CMD_OPEN_FILE] && st.command_enabled[SAFEPDF_CMD_QUIT] &&
          st.command_enabled[SAFEPDF_CMD_ABOUT]);
    char got[512] = "";
    for (size_t i = 0; i < st.item_count && i < tb.count; i++)
        if (tb.items[i].kind == SAFEPDF_ITEM_BUTTON && st.item_enabled[i]) {
            strncat(got, tb.items[i].id, sizeof got - strlen(got) - 2); strcat(got, " ");
        }
    CHECK(strcmp(got, "more ") == 0);
    CHECK(!st.item_visible[0]); /* the sidebar toggle hides without a document */
    safepdf_free_chrome_states(&st);
    safepdf_ctx first = none;
    first.has_doc = true; first.page = 0; first.pages = 3; first.has_outline = true;
    CHECK(safepdf_view_states(&first, &st) == 0);
    got[0] = 0;
    for (size_t i = 0; i < st.item_count && i < tb.count; i++)
        if (tb.items[i].kind == SAFEPDF_ITEM_BUTTON && st.item_enabled[i]) {
            strncat(got, tb.items[i].id, sizeof got - strlen(got) - 2); strcat(got, " ");
        }
    CHECK(strcmp(got, "sidebar next zout zin select highlight comment text draw more ") == 0);
    CHECK(!st.command_enabled[SAFEPDF_CMD_PREV_PAGE] && st.command_enabled[SAFEPDF_CMD_NEXT_PAGE] &&
          !st.command_enabled[SAFEPDF_CMD_SAVE]);
    safepdf_free_chrome_states(&st);
    first.dirty = true;
    CHECK(safepdf_view_states(&first, &st) == 0 && st.command_enabled[SAFEPDF_CMD_SAVE]);
    safepdf_free_chrome_states(&st);
    safepdf_free_toolbar(&tb);

    /* Cursor table (Toolbar.lean #guards) and hit order. */
    CHECK(safepdf_view_cursor_for(SAFEPDF_MODE_SELECT, SAFEPDF_HIT_TEXT) == SAFEPDF_CURSOR_IBEAM);
    CHECK(safepdf_view_cursor_for(SAFEPDF_MODE_SELECT, SAFEPDF_HIT_LINK) == SAFEPDF_CURSOR_POINTING_HAND);
    CHECK(safepdf_view_cursor_for(SAFEPDF_MODE_SELECT, SAFEPDF_HIT_EMPTY) == SAFEPDF_CURSOR_ARROW);
    CHECK(safepdf_view_cursor_for(SAFEPDF_MODE_TEXT, SAFEPDF_HIT_LINK) == SAFEPDF_CURSOR_IBEAM);
    CHECK(safepdf_view_cursor_for(SAFEPDF_MODE_TEXT, SAFEPDF_HIT_MARK) == SAFEPDF_CURSOR_POINTING_HAND);
    for (uint32_t h = 0; h < 4; h++)
        CHECK(safepdf_view_cursor_for(SAFEPDF_MODE_DRAW, h) == SAFEPDF_CURSOR_CROSSHAIR);
    CHECK(safepdf_view_hit_of(true, true, true) == SAFEPDF_HIT_MARK &&
          safepdf_view_hit_of(false, true, true) == SAFEPDF_HIT_LINK &&
          safepdf_view_hit_of(false, false, true) == SAFEPDF_HIT_TEXT &&
          safepdf_view_hit_of(false, false, false) == SAFEPDF_HIT_EMPTY);
    CHECK(safepdf_view_mode_tool(SAFEPDF_MODE_DRAW) == SAFEPDF_TOOL_DRAW &&
          safepdf_view_mode_tool(SAFEPDF_MODE_HIGHLIGHT) == SAFEPDF_TOOL_HIGHLIGHT);
}

/* Task 11.3c2: the wheel, page text, history and page-to-screen exports. */
static void test_viewing_parity(void) {
    /* View.wheelStep (FfiView.lean #guards): 100 px down from the top scrolls to 100. */
    safepdf_wheel w0, w;
    memset(&w0, 0, sizeof w0);
    uint64_t pos = 0;
    CHECK(safepdf_view_wheel_step(&w0, SAFEPDF_WHEEL_PIXEL, -100, true, 1000, 0, 500, 1000, &w,
                                  &pos) == SAFEPDF_WHEEL_SCROLL && pos == 100);
    /* At the bottom a 30 px push beyond the 25 px threshold turns the page (page mode only);
       the 5 px beyond the threshold are owed to the new page. */
    CHECK(safepdf_view_wheel_step(&w0, SAFEPDF_WHEEL_PIXEL, -30, true, 1000, 500, 500, 1000, &w,
                                  &pos) == SAFEPDF_WHEEL_NEXT && req(w.acc, 5, 1));
    CHECK(safepdf_view_wheel_step(&w0, SAFEPDF_WHEEL_PIXEL, -30, false, 1000, 500, 500, 1000, &w,
                                  &pos) == SAFEPDF_WHEEL_NONE);
    /* A push below the threshold accumulates, the next event turns (in place: out == w). */
    w = w0;
    CHECK(safepdf_view_wheel_step(&w, SAFEPDF_WHEEL_PIXEL, -20, true, 1000, 500, 500, 1000, &w,
                                  &pos) == SAFEPDF_WHEEL_NONE && req(w.push, 20, 1));
    CHECK(safepdf_view_wheel_step(&w, SAFEPDF_WHEEL_PIXEL, -10, true, 1010, 500, 500, 1000, &w,
                                  &pos) == SAFEPDF_WHEEL_NEXT);
    /* Up at the top: previous page; a line of a 500 px view is 50 px. */
    CHECK(safepdf_view_wheel_step(&w0, SAFEPDF_WHEEL_LINE, 1, true, 1000, 0, 500, 1000, &w,
                                  &pos) == SAFEPDF_WHEEL_PREV);
    CHECK(safepdf_view_wheel_step(&w0, SAFEPDF_WHEEL_LINE, -1, true, 1000, 0, 500, 1000, &w,
                                  &pos) == SAFEPDF_WHEEL_SCROLL && pos == 50);
    CHECK(safepdf_view_wheel_step(&w0, 7, -1, true, 1000, 0, 500, 1000, &w, &pos) == -1);

    /* Links.pageText #guards. */
    const char *roman[] = { "i", "ii", "iii" };
    char *t = safepdf_view_page_text(roman, 3, 2, 120);
    CHECK(t && strcmp(t, "page iii (3/120)") == 0);
    free(t);
    t = safepdf_view_page_text(NULL, 0, 1, 2);
    CHECK(t && strcmp(t, "page 2/2") == 0);
    free(t);

    /* Links.History (theorem back_push): a jump from a, back from b returns to a, forward
       from a returns to b. */
    safepdf_view_loc a = { 0, R(0, 1), R(1, 4) }, b = { 5, R(0, 1), R(1, 2) }, tgt;
    safepdf_view_history h0, h1, h2, h3;
    memset(&h0, 0, sizeof h0);
    CHECK(safepdf_view_history_step(SAFEPDF_HISTORY_BACK, &h0, a, &h1, &tgt) == 0 &&
          h1.back_count == 0 && tgt.page == 0);
    safepdf_free_view_history(&h1);
    CHECK(safepdf_view_history_step(SAFEPDF_HISTORY_PUSH, &h0, a, &h1, &tgt) == 1 &&
          h1.back_count == 1 && h1.fwd_count == 0 && h1.back[0].page == 0 &&
          req(h1.back[0].y, 1, 4));
    CHECK(safepdf_view_history_step(SAFEPDF_HISTORY_BACK, &h1, b, &h2, &tgt) == 1 &&
          tgt.page == 0 && req(tgt.y, 1, 4) && h2.back_count == 0 && h2.fwd_count == 1 &&
          h2.fwd[0].page == 5);
    CHECK(safepdf_view_history_step(SAFEPDF_HISTORY_FORWARD, &h2, tgt, &h3, &tgt) == 1 &&
          tgt.page == 5 && req(tgt.y, 1, 2) && h3.back_count == 1 && h3.fwd_count == 0);
    safepdf_free_view_history(&h1);
    safepdf_free_view_history(&h2);
    /* A new jump clears the forward stack; at most 100 entries are kept. */
    safepdf_view_history big;
    memset(&big, 0, sizeof big);
    for (size_t i = 0; i < 120; i++) {
        safepdf_view_loc l = { i, R(0, 1), R(0, 1) };
        safepdf_view_history next;
        CHECK(safepdf_view_history_step(SAFEPDF_HISTORY_PUSH, &big, l, &next, NULL) == 1);
        safepdf_free_view_history(&big);
        big = next;
    }
    CHECK(big.back_count == 100 && big.back[0].page == 119 && big.fwd_count == 0);
    safepdf_free_view_history(&big);
    safepdf_free_view_history(&h3);
    safepdf_view_loc bad = { 0, R(0, 0), R(0, 1) };
    CHECK(safepdf_view_history_step(SAFEPDF_HISTORY_PUSH, &h0, bad, &h1, &tgt) == -1);

    /* Geom.toScreen (FfiView.lean #guards): the top-left corner of a 612 x 792 page is (0, 0);
       (100, 692) at zoom 3/2 is (150, 150); rotated a quarter turn the top-left of the page
       goes to the top-right of the image. */
    safepdf_rat_box letter = box(612, 792);
    safepdf_rat_point p = { R(0, 1), R(792, 1) }, q;
    CHECK(safepdf_view_to_screen(R(1, 1), 0, &letter, p, &q) == 0 && req(q.x, 0, 1) &&
          req(q.y, 0, 1));
    safepdf_rat_point p2 = { R(100, 1), R(692, 1) };
    CHECK(safepdf_view_to_screen(R(3, 2), 0, &letter, p2, &q) == 0 && req(q.x, 150, 1) &&
          req(q.y, 150, 1));
    CHECK(safepdf_view_to_screen(R(1, 1), 90, &letter, p, &q) == 0 && req(q.x, 792, 1) &&
          req(q.y, 0, 1));
    CHECK(safepdf_view_to_screen(R(1, 0), 0, &letter, p, &q) == -1);
}

int main(void) {
    /* Before safepdf_view_init every call fails cleanly. */
    safepdf_rat z;
    CHECK(safepdf_view_quant(R(1, 1), &z) == -1);
    if (safepdf_init() != 0 || safepdf_view_init() != 0 || safepdf_view_init() != 0) {
        fprintf(stderr, "init failed\n");
        return 1;
    }
    test_zoom();
    test_rotation();
    test_spreads_layout();
    test_zoom_choices();
    test_chrome();
    test_viewing_parity();
    printf("view_test: %d checks, %d failures\n", checks, failures);
    return failures ? 1 : 0;
}
