/*
 * safepdf_view.h — C API v2, view and chrome logic (task 11.3a2; docs/macos-design.md §3).
 *
 * The pure viewing rules and chrome tables of the Tk viewer, for the native macOS shell:
 * zoom (quantised steps, fit and automatic zoom, the per-page pixel cap), rotation, C2
 * re-anchoring, spreads and page layout, the zoom and view-mode drop-downs, the page field,
 * the toolbar (items, enabled and visible rules), the pointer cursor, the commands, the
 * menubar and overflow menu, and the key table. Every function calls the Lean function that
 * the Tk viewer uses (SafePdf/Shell/FfiView.lean over App/View, App/Toolbar, App/Menu), so the
 * theorems and #guards there hold for these results. Plain C: no Lean types leak through.
 *
 * Initialisation
 *   - safepdf_init (safepdf_core.h) must run first; then safepdf_view_init, once, on the
 *     same (main) thread. Both are idempotent. Other threads follow safepdf_core.h's rules
 *     (safepdf_thread_enter / safepdf_thread_exit). Calls before safepdf_view_init fail
 *     (-1, or 0 / an empty result for functions that return a value directly).
 *
 * Numbers
 *   - Rationals cross exactly as safepdf_rat {num, den} with den > 0 (zooms, page units,
 *     scaling). An input with den <= 0 is rejected (-1); a result whose numerator or
 *     denominator does not fit 64 bits is reported as an error (-1). safepdf_rat_to_double
 *     is for display only; never feed a rounded value back as a zoom.
 *   - Zoom is pixels per page unit (1 = 72 dpi at screen scale 1). `scaling` is the screen's
 *     pixels per point (an input, never a constant: 1 for a standard display, 2 for Retina in
 *     backing pixels, whatever the shell measures).
 *   - Rotations are degrees, 0/90/180/270 (other values are rounded down to a quarter turn,
 *     modulo 360). Pixel positions and sizes are whole pixels (uint64_t).
 *
 * Ownership
 *   - Structs filled by a call own their arrays and strings (malloc'd); release each with
 *     the one safepdf_free_* function of its type (NULL allowed; the struct is zeroed).
 *   - Functions returning `char *` return a malloc'd UTF-8 string the caller free()s.
 *   - Input pointers are borrowed for the duration of the call.
 *
 * Return values: 0 success, -1 failure (bad input, not initialised, out of memory,
 * unrepresentable result) unless stated otherwise.
 *
 * Keys are neutral: a modifier mask (SAFEPDF_MOD_*) and the key's X11/Tk keysym name
 * (`o`, `plus`, `bracketleft`, `Up`, `Prior`, `F9`, `Delete`; letters in lower case except
 * `R` with Shift), plus the name shown in labels. Translating them into AppKit key
 * equivalents is the shell's job.
 */
#ifndef SAFEPDF_VIEW_H
#define SAFEPDF_VIEW_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/** Initialise the view module (SafePdf.Shell.FfiView). Requires safepdf_init first.
    0 on success; idempotent. */
int safepdf_view_init(void);

/* ---------------------------------------------------------------- numbers */

/** An exact rational num / den, den > 0. */
typedef struct { int64_t num; int64_t den; } safepdf_rat;
/** A page box in page units (CropBox: lower-left, upper-right). */
typedef struct { safepdf_rat llx, lly, urx, ury; } safepdf_box;
/** A point (screen pixels or page units, as the function says). */
typedef struct { safepdf_rat x, y; } safepdf_point;

/** num / den as a double (display only). */
double safepdf_rat_to_double(safepdf_rat q);

/** The view constants (App/View, App/Toolbar, App/Budget, Core/Limits). */
typedef struct {
    uint32_t margin;          /* View.margin: pixels around the content */
    uint32_t page_gap;        /* View.pageGap: pixels between pages and spread halves */
    uint32_t min_pct;         /* View.minPct: smallest zoom step, percent */
    uint32_t max_pct;         /* View.maxPct: largest zoom step, percent */
    uint32_t auto_max_pct;    /* Toolbar.autoMaxPct: Automatic Zoom's ceiling, percent */
    uint64_t page_pixels;     /* Budget.ceilings.pagePixels: per-page pixel cap (capZoom) */
    uint32_t max_page_side;   /* Limits.maxPageSide: the renderer crops longer sides */
    uint64_t max_view_pixels; /* View.maxViewPixels */
} safepdf_view_constants;

int safepdf_view_get_constants(safepdf_view_constants *out);

/** The zoom steps in percent (View.zoomSteps): copies at most `cap` into `out` (may be
    NULL when cap is 0) and returns the number of steps (0 when not initialised). */
size_t safepdf_view_zoom_steps(uint32_t *out, size_t cap);

/* ---------------------------------------------------------------- zoom */

/** View.quant: rounds down to a multiple of 1/64, at least 1/64. */
int safepdf_view_quant(safepdf_rat z, safepdf_rat *out);
/** View.pctZoom: the (quantised) zoom of a percentage at screen scale `scaling`. */
int safepdf_view_pct_zoom(uint32_t pct, safepdf_rat scaling, safepdf_rat *out);
/** View.zoomPct: the percentage shown for zoom `z`, rounded to the nearest integer. */
int safepdf_view_zoom_pct(safepdf_rat z, safepdf_rat scaling, uint32_t *pct);
/** View.stepInZ / stepOutZ (Zoom In / Out on the effective, quantised zoom `z`; task 10.12):
    1 with `*pct` the step to go to, 0 at the end of the range (leave the zoom alone), -1 on
    error. The result's zoom is strictly larger (smaller) than `z` (theorems stepInZ_gt,
    stepOutZ_lt). */
int safepdf_view_step_in(safepdf_rat z, safepdf_rat scaling, uint32_t *pct);
int safepdf_view_step_out(safepdf_rat z, safepdf_rat scaling, uint32_t *pct);
/** View.fitZoom: the zoom fitting a pw × ph box (page units) into a cw × ch canvas less the
    margin (width only when `width_only`), quantised and kept in [1/16, 8]. */
int safepdf_view_fit_zoom(bool width_only, uint32_t cw, uint32_t ch, safepdf_rat pw,
                          safepdf_rat ph, safepdf_rat *out);
/** View.capZoom: `z` lowered so the page image has at most `max_pixels` pixels;
    `*lowered` says whether it was. The Tk viewer uses constants.page_pixels. */
int safepdf_view_cap_zoom(uint64_t max_pixels, safepdf_rat z, uint32_t rotation,
                          const safepdf_box *box, safepdf_rat *out, bool *lowered);

/** Pixel sizes of a page box at a zoom. */
typedef struct {
    uint64_t width, height;             /* View.pixelSize: ceil of the screen size */
    uint64_t image_width, image_height; /* Clip.pageSize: as rendered, sides capped at `side` */
    bool cropped;                       /* View.cropped: a side exceeds `side` */
} safepdf_pixel_size;

/** Pixel sizes at zoom `z`; `side` is the renderer's side cap (constants.max_page_side). */
int safepdf_view_pixel_size(uint32_t side, safepdf_rat z, uint32_t rotation,
                            const safepdf_box *box, safepdf_pixel_size *out);

/* ---------------------------------------------------------------- rotation, anchoring */

/** Rotation steps and the displayed size of a box. */
typedef struct {
    uint32_t cw;              /* View.rotCw: degrees after a quarter turn clockwise */
    uint32_t ccw;             /* View.rotCcw: after a quarter turn counter-clockwise */
    safepdf_rat width, height; /* View.boxSize: displayed size in page units */
} safepdf_rotation_info;

int safepdf_view_rotation(uint32_t rotation, const safepdf_box *box, safepdf_rotation_info *out);

/** View.reanchor (C2): the screen position, in the view (z2, rot2), of the page point shown
    at `q` (screen pixels relative to the page image's top-left) in the view (z, rot). With
    nothing changed it is `q` (theorem reanchor_self). Zoom about the pointer: scroll so that
    the result lies under the pointer again. */
int safepdf_view_reanchor(safepdf_rat z, uint32_t rot, safepdf_rat z2, uint32_t rot2,
                          const safepdf_box *box, safepdf_point q, safepdf_point *out);

/* ---------------------------------------------------------------- view modes, spreads */

/** View.ScrollMode. */
typedef enum { SAFEPDF_SCROLL_PAGE = 0, SAFEPDF_SCROLL_VERTICAL = 1 } safepdf_scroll_mode;
/** View.SpreadMode. */
typedef enum {
    SAFEPDF_SPREAD_NONE = 0, SAFEPDF_SPREAD_ODD = 1, SAFEPDF_SPREAD_EVEN = 2
} safepdf_spread_mode;

/** The spread of a page and the pages Next / Previous go to. */
typedef struct {
    size_t spread;       /* View.spreadOf */
    size_t spread_count; /* View.spreadCount */
    size_t next_page;    /* View.nextPage (the page itself at the end) */
    size_t prev_page;    /* View.prevPage (the page itself in the first spread) */
    size_t page_count;   /* pages in this spread (View.spreadPages), 1 or 2 (0: no such page) */
    size_t pages[2];     /* those pages, left to right before right-to-left mirroring */
} safepdf_spread_info;

int safepdf_view_spread(uint32_t spread, size_t n, size_t page, safepdf_spread_info *out);

/* ---------------------------------------------------------------- zoom choices */

/** Toolbar.ZoomChoice kinds. */
typedef enum {
    SAFEPDF_ZOOM_AUTO = 0, SAFEPDF_ZOOM_ACTUAL = 1, SAFEPDF_ZOOM_PAGE_FIT = 2,
    SAFEPDF_ZOOM_PAGE_WIDTH = 3, SAFEPDF_ZOOM_PERCENT = 4
} safepdf_zoom_kind;

/** A zoom choice: `pct` is used by SAFEPDF_ZOOM_PERCENT only. */
typedef struct { uint32_t kind; uint32_t pct; } safepdf_zoom_choice;

/** One entry of the zoom drop-down. */
typedef struct { safepdf_zoom_choice choice; char *label; char *key; } safepdf_zoom_preset;
/** The zoom drop-down, top to bottom (Toolbar.ZoomChoice.presets). */
typedef struct { safepdf_zoom_preset *items; size_t count; } safepdf_zoom_presets;

int safepdf_view_zoom_presets(safepdf_zoom_presets *out);
void safepdf_free_zoom_presets(safepdf_zoom_presets *p);

/** ZoomChoice.label (e.g. "Automatic Zoom", "33%"); NULL on failure. */
char *safepdf_view_zoom_label(safepdf_zoom_choice c);
/** ZoomChoice.ofKey ("auto", "page-fit", "150", …): 1 found, 0 not a choice, -1 error. */
int safepdf_view_zoom_parse(const char *key, safepdf_zoom_choice *out);
/** ZoomChoice.zoomWith: the zoom of choice `c` for a pw × ph box in a cw × ch canvas;
    Automatic Zoom is page width when `portrait`, page fit otherwise, at most auto_max_pct. */
int safepdf_view_zoom_with(safepdf_zoom_choice c, uint32_t cw, uint32_t ch, safepdf_rat scaling,
                           safepdf_rat pw, safepdf_rat ph, bool portrait, safepdf_rat *out);

/* ---------------------------------------------------------------- layout */

/** A page's geometry: its CropBox and /Rotate (degrees). */
typedef struct { safepdf_box box; uint32_t rotate; } safepdf_page_geom;

/** Layout parameters (the Tk viewer's state). */
typedef struct {
    uint32_t scroll;        /* safepdf_scroll_mode */
    uint32_t spread;        /* safepdf_spread_mode */
    uint32_t user_rotation; /* degrees, added to every page's /Rotate */
    safepdf_zoom_choice zoom;
    safepdf_rat scaling;    /* screen pixels per point */
    uint32_t canvas_w, canvas_h;
    size_t page;            /* current page: its size picks the zoom; its spread is shown in
                               the page scroll mode */
    bool rtl;               /* /Direction /R2L: spreads mirrored */
} safepdf_layout_params;

/** A laid-out page: its rectangle in the scroll region (pixels) and render parameters. */
typedef struct {
    size_t page;
    uint64_t x, y, w, h;
    safepdf_rat zoom;  /* render at this zoom (the base zoom, capped per page) */
    uint32_t rotation; /* render with this rotation (page /Rotate + user rotation), degrees */
    bool capped;       /* the pixel cap lowered the zoom (say "zoom limited") */
    bool cropped;      /* the renderer crops this page */
} safepdf_place;

/** A layout: places in page order (only the shown spread in the page scroll mode). */
typedef struct {
    safepdf_rat base_zoom;       /* the zoom choice's zoom for the current page */
    uint64_t region_w, region_h; /* the scroll region (at least the canvas) */
    safepdf_place *places;
    size_t count;
} safepdf_layout;

/** Lays out `n` pages as the Tk viewer does (Viewer.computeLayout over View.layoutRows,
    ZoomChoice.zoomWith, View.capZoom, Clip.pageSize, View.mirrorPlace). */
int safepdf_view_layout(const safepdf_page_geom *pages, size_t n,
                        const safepdf_layout_params *params, safepdf_layout *out);
void safepdf_free_layout(safepdf_layout *l);

/** The pages meeting a view band [top, bottom) of the scroll region. */
typedef struct {
    size_t *visible; size_t visible_count; /* View.visiblePages */
    size_t *wanted;  size_t wanted_count;  /* View.wantedPages: visible plus one each side */
} safepdf_page_band;

int safepdf_view_pages_in_band(const safepdf_layout *l, uint64_t top, uint64_t bottom,
                               safepdf_page_band *out);
void safepdf_free_page_band(safepdf_page_band *b);

/** The page at a point and the scroll positions that show it. */
typedef struct {
    size_t page;
    uint64_t top;    /* View.topFor: scroll top showing the page from its top */
    uint64_t bottom; /* View.bottomFor: scroll top showing the page down to its bottom */
} safepdf_page_hit;

/** View.pageAt: the page containing scroll-region point (x, y), else the nearest one.
    1 found, 0 no pages, -1 error. `view_h` is the view height (for `bottom`). */
int safepdf_view_page_at(const safepdf_layout *l, uint64_t x, uint64_t y, uint64_t view_h,
                         safepdf_page_hit *out);

/* ---------------------------------------------------------------- view-mode drop-down */

/** Toolbar.ViewChoice. */
typedef enum {
    SAFEPDF_VIEW_SINGLE = 0, SAFEPDF_VIEW_VERTICAL = 1, SAFEPDF_VIEW_TWO = 2,
    SAFEPDF_VIEW_TWO_SCROLL = 3
} safepdf_view_choice;

/** One entry: the choice, the modes it sets (from spread mode none), label, key (also the
    Tk icon name suffix). */
typedef struct {
    uint32_t choice; uint32_t scroll; uint32_t spread; char *label; char *key;
} safepdf_view_choice_item;
typedef struct { safepdf_view_choice_item *items; size_t count; } safepdf_view_choices;

int safepdf_view_view_choices(safepdf_view_choices *out);
void safepdf_free_view_choices(safepdf_view_choices *c);

/** ViewChoice.ofModes: the entry the modes show (checked in the drop-down). */
uint32_t safepdf_view_choice_of_modes(uint32_t scroll, uint32_t spread);
/** ViewChoice.modes: the modes choosing `choice` sets when the spread mode is `spread_now`
    (a two-page choice keeps Even Spreads). */
int safepdf_view_choice_modes(uint32_t choice, uint32_t spread_now, uint32_t *scroll,
                              uint32_t *spread);

/* ---------------------------------------------------------------- page field */

/** Toolbar.entryText / ofText: the page field's text and the label after it ("of N" or
    "(k of N)" with page labels). `labels` holds `nlabels` page labels (may be 0). */
int safepdf_view_page_field(const char *const *labels, size_t nlabels, size_t page, size_t pages,
                            char **entry_text, char **of_text);
/** Toolbar.pageEntry: Enter in the page field. 1 valid (`*page` the page to show), 0 invalid
    (`*page` = current: revert the field), -1 error. */
int safepdf_view_page_entry(const char *const *labels, size_t nlabels, size_t pages,
                            size_t current, const char *input, size_t *page);

/* ---------------------------------------------------------------- commands */

/** Menu.Cmd, in Menu.Cmd.all order. */
typedef enum {
    SAFEPDF_CMD_OPEN_FILE, SAFEPDF_CMD_SAVE, SAFEPDF_CMD_SAVE_AS, SAFEPDF_CMD_IMPORT_XFDF,
    SAFEPDF_CMD_EXPORT_XFDF, SAFEPDF_CMD_CLOSE, SAFEPDF_CMD_QUIT, SAFEPDF_CMD_UNDO,
    SAFEPDF_CMD_REDO, SAFEPDF_CMD_COPY, SAFEPDF_CMD_SELECT_ALL, SAFEPDF_CMD_HIGHLIGHT,
    SAFEPDF_CMD_ADD_NOTE, SAFEPDF_CMD_DELETE_MARK, SAFEPDF_CMD_HL_TOOL, SAFEPDF_CMD_SHOW_ALL,
    SAFEPDF_CMD_FIND, SAFEPDF_CMD_OUTLINE, SAFEPDF_CMD_ZOOM_IN, SAFEPDF_CMD_ZOOM_OUT,
    SAFEPDF_CMD_ACTUAL_SIZE, SAFEPDF_CMD_FIT_PAGE, SAFEPDF_CMD_FIT_WIDTH, SAFEPDF_CMD_ROTATE_CW,
    SAFEPDF_CMD_ROTATE_CCW, SAFEPDF_CMD_SCROLL_PAGE, SAFEPDF_CMD_SCROLL_VERTICAL,
    SAFEPDF_CMD_SPREAD_NONE, SAFEPDF_CMD_SPREAD_ODD, SAFEPDF_CMD_SPREAD_EVEN,
    SAFEPDF_CMD_PREV_PAGE, SAFEPDF_CMD_NEXT_PAGE, SAFEPDF_CMD_FIRST_PAGE, SAFEPDF_CMD_LAST_PAGE,
    SAFEPDF_CMD_GOTO_PAGE, SAFEPDF_CMD_BACK, SAFEPDF_CMD_FORWARD, SAFEPDF_CMD_ABOUT,
    SAFEPDF_CMD_COUNT
} safepdf_cmd;

/** Menu.Action (keys that are not menu commands), in Menu.Action.all order. */
typedef enum { SAFEPDF_ACTION_FIND_NEXT, SAFEPDF_ACTION_FIND_PREV, SAFEPDF_ACTION_COUNT } safepdf_action;

/** Modifier mask bits. */
enum {
    SAFEPDF_MOD_COMMAND = 1, SAFEPDF_MOD_SHIFT = 2, SAFEPDF_MOD_OPTION = 4,
    SAFEPDF_MOD_CONTROL = 8
};

/** A key: modifiers, keysym ("" = no key), the name shown in labels. */
typedef struct { uint32_t mods; char *key; char *shown; } safepdf_key;

/** A command (or action): its enum value, constructor name ("openFile"), label, and its
    macOS accelerator (Cmd.keyOn .aqua; none for actions). */
typedef struct { uint32_t id; char *name; char *label; safepdf_key accel; } safepdf_command;
typedef struct { safepdf_command *items; size_t count; } safepdf_commands;

/** The commands, in safepdf_cmd order. */
int safepdf_view_commands(safepdf_commands *out);
/** The key actions, in safepdf_action order (label = Action.name). */
int safepdf_view_actions(safepdf_commands *out);
void safepdf_free_commands(safepdf_commands *c);

/** Menu.appName ("SafePDF") and Menu.aboutDetail; NULL on failure. */
char *safepdf_view_app_name(void);
char *safepdf_view_about_detail(void);

/* ---------------------------------------------------------------- menus */

/** Menu entry kinds. */
typedef enum {
    SAFEPDF_ENTRY_COMMAND = 0, SAFEPDF_ENTRY_CHECK = 1, /* a check item (Sidebar, tools) */
    SAFEPDF_ENTRY_COLORS = 2,                          /* the highlight-colour submenu */
    SAFEPDF_ENTRY_SEPARATOR = 3
} safepdf_entry_kind;

/** Radio groups (the view-mode entries: checked while the mode is on). */
typedef enum { SAFEPDF_RADIO_NONE = 0, SAFEPDF_RADIO_SCROLL = 1, SAFEPDF_RADIO_SPREAD = 2 } safepdf_radio;

/** A menu entry: its menu (index into menu_labels), kind, command (-1 none), macOS
    accelerator, radio group and value (the mode's key: "page", "vertical", "none", "odd",
    "even"), label. */
typedef struct {
    uint32_t menu; uint32_t kind; int32_t cmd; safepdf_key accel;
    uint32_t radio_group; char *radio_value; char *label;
} safepdf_menu_entry;

/** Menus and their entries, top to bottom. */
typedef struct {
    char **menu_labels; size_t menu_count;
    safepdf_menu_entry *entries; size_t entry_count;
} safepdf_menu_table;

/** The menubar (Menu.menubar): File, Edit, View, Go, Help. */
int safepdf_view_menubar(safepdf_menu_table *out);
/** The toolbar's overflow menu (Toolbar.overflow): one menu, labelled as the overflow
    button's tooltip. */
int safepdf_view_overflow_menu(safepdf_menu_table *out);
void safepdf_free_menu_table(safepdf_menu_table *t);

/** One key binding of the main window (Menu.keyTable .aqua, row by row): what it runs
    (target_kind 0 command, 1 action), the key, and whether it is from the X11 column (Ctrl
    keys the Tk viewer keeps on macOS) or the macOS column. */
typedef struct { uint32_t target_kind; uint32_t target; safepdf_key key; bool x11; } safepdf_key_binding;
typedef struct { safepdf_key_binding *items; size_t count; } safepdf_key_table;

int safepdf_view_keys(safepdf_key_table *out);
void safepdf_free_key_table(safepdf_key_table *t);

/* ---------------------------------------------------------------- toolbar */

/** Toolbar.Tool, in toolbar order. */
typedef enum {
    SAFEPDF_TOOL_SELECT, SAFEPDF_TOOL_HIGHLIGHT, SAFEPDF_TOOL_COMMENT, SAFEPDF_TOOL_TEXT,
    SAFEPDF_TOOL_DRAW, SAFEPDF_TOOL_IMAGE, SAFEPDF_TOOL_PRINT, SAFEPDF_TOOL_COUNT
} safepdf_tool;

/** Toolbar item kinds. */
typedef enum {
    SAFEPDF_ITEM_BUTTON = 0, SAFEPDF_ITEM_SEPARATOR = 1, SAFEPDF_ITEM_PAGE_FIELD = 2,
    SAFEPDF_ITEM_ZOOM_BOX = 3, SAFEPDF_ITEM_VIEW_BOX = 4
} safepdf_item_kind;

/** Button actions. */
typedef enum {
    SAFEPDF_ACT_NONE = -1, SAFEPDF_ACT_COMMAND = 0, SAFEPDF_ACT_TOOL = 1, SAFEPDF_ACT_MORE = 2
} safepdf_act;

/** A toolbar item: group (0 left, 1 centre, 2 right), kind, action (buttons), command or
    tool (-1 when not that action), id (the Tk path without ".bar."; "page", "zoom", "view"
    for the controls), Tk icon name, tooltip (with ⌘ glyphs). */
typedef struct {
    uint32_t group; uint32_t kind; int32_t action; int32_t cmd; int32_t tool;
    char *id; char *icon; char *tooltip;
} safepdf_toolbar_item;
typedef struct { safepdf_toolbar_item *items; size_t count; } safepdf_toolbar;

/** The toolbar, left to right (Toolbar.layout). */
int safepdf_view_toolbar(safepdf_toolbar *out);
void safepdf_free_toolbar(safepdf_toolbar *t);

/** What the enabled rules look at (Menu.Ctx). */
typedef struct {
    bool has_doc; size_t page; size_t pages; bool has_sel; bool has_outline; bool has_mark;
    bool can_back; bool can_forward; bool dirty; bool can_undo; bool can_redo;
    bool on_first; bool on_last;
} safepdf_ctx;

/** Enabled states: per command (Cmd.enabled; menus and overflow entries use their command's),
    per toolbar item (Button.enabled / Button.visible; non-buttons enabled and visible). */
typedef struct {
    bool command_enabled[SAFEPDF_CMD_COUNT];
    bool *item_enabled; bool *item_visible; size_t item_count; /* safepdf_view_toolbar order */
} safepdf_chrome_states;

int safepdf_view_states(const safepdf_ctx *ctx, safepdf_chrome_states *out);
void safepdf_free_chrome_states(safepdf_chrome_states *s);

/* ---------------------------------------------------------------- pointer */

/** Toolbar.Mode: the active tool. */
typedef enum {
    SAFEPDF_MODE_SELECT = 0, SAFEPDF_MODE_HIGHLIGHT = 1, SAFEPDF_MODE_TEXT = 2, SAFEPDF_MODE_DRAW = 3
} safepdf_tool_mode;
/** Toolbar.Hit: what lies under the pointer. */
typedef enum { SAFEPDF_HIT_TEXT = 0, SAFEPDF_HIT_LINK = 1, SAFEPDF_HIT_MARK = 2, SAFEPDF_HIT_EMPTY = 3 } safepdf_hit;
/** Cursors (Toolbar.cursorFor's Tk names: "" arrow, xterm, hand2, crosshair). */
typedef enum {
    SAFEPDF_CURSOR_ARROW = 0, SAFEPDF_CURSOR_IBEAM = 1, SAFEPDF_CURSOR_POINTING_HAND = 2,
    SAFEPDF_CURSOR_CROSSHAIR = 3
} safepdf_cursor;

/** Toolbar.hitOf: the hit when the pointer is over a mark, a link, text (any of them). */
uint32_t safepdf_view_hit_of(bool mark, bool link, bool text);
/** Toolbar.cursorFor: the page cursor for a mode over a hit. */
uint32_t safepdf_view_cursor_for(uint32_t mode, uint32_t hit);
/** Toolbar.Mode.tool: the tool whose button shows pressed in a mode. */
uint32_t safepdf_view_mode_tool(uint32_t mode);

#ifdef __cplusplus
}
#endif

#endif /* SAFEPDF_VIEW_H */
