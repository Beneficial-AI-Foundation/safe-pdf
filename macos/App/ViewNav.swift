// ViewNav.swift — the navigation rules of the Tk viewer through the C API (task 11.3c2): view
// modes and spreads, page-at-a-time wheel steps, back/forward history, the page as text, the
// document's open settings. Plan.md §6 Phase 11; docs/macos-design.md §1 ("the view modes
// (single / continuous / facing / continuous-facing, odd/even spreads), page-at-a-time wheel
// rules, ... back/forward history, document open settings (9.r8: every open starts afresh)") and
// §3 decision 1: every rule is one call into the Lean function the Tk viewer uses
// (safepdf_view.h, safepdf_core.h); Swift only converts values.

import Foundation
import SafePdfC

/// The view modes (View.ScrollMode, View.SpreadMode) and the reading direction.
struct ViewModes: Equatable {
    var scroll: UInt32 = SAFEPDF_SCROLL_VERTICAL.rawValue
    var spread: UInt32 = SAFEPDF_SPREAD_NONE.rawValue
    /// `/Direction /R2L`: spreads mirrored (only from a document's open settings).
    var rtl = false

    /// Continuous vertical scrolling without spreads, left to right: where every open starts.
    static let start = ViewModes()

    var continuous: Bool { scroll == SAFEPDF_SCROLL_VERTICAL.rawValue }

    /// The view-mode drop-down's entry these modes show (Toolbar.ViewChoice.ofModes).
    var choice: UInt32 { safepdf_view_choice_of_modes(scroll, spread) }

    /// The modes after choosing a drop-down entry (Toolbar.ViewChoice.modes: a two-page choice
    /// keeps Even Spreads).
    func choosing(_ choice: UInt32) -> ViewModes? {
        var sc: UInt32 = 0, sp: UInt32 = 0
        guard safepdf_view_choice_modes(choice, spread, &sc, &sp) == 0 else { return nil }
        return ViewModes(scroll: sc, spread: sp, rtl: rtl)
    }
}

/// The spread of a page and where Next / Previous go (View.spreadOf, nextPage, prevPage).
@MainActor enum Spreads {
    static func info(_ spread: UInt32, pages n: Int, page: Int) -> safepdf_spread_info? {
        guard n > 0 else { return nil }
        var info = safepdf_spread_info()
        return safepdf_view_spread(spread, n, min(page, n - 1), &info) == 0 ? info : nil
    }
}

/// Links.pageText: "page k/n", or "page L (k/n)" with page labels.
@MainActor enum PageText {
    static func of(labels: [String], page: Int, pages: Int) -> String {
        withCStrings(labels) { ptrs, n in
            Core.take(safepdf_view_page_text(ptrs, n, page, pages))
        } ?? "page \(page + 1)/\(pages)"
    }

    /// Toolbar.entryText / ofText: the page field's text and the label after it.
    static func field(labels: [String], page: Int, pages: Int) -> (entry: String, of: String) {
        withCStrings(labels) { ptrs, n in
            var e: UnsafeMutablePointer<CChar>? = nil
            var o: UnsafeMutablePointer<CChar>? = nil
            let rc = safepdf_view_page_field(ptrs, n, page, pages, &e, &o)
            let entry = Core.take(e), of = Core.take(o)
            guard rc == 0, let entry, let of else { return nil }
            return (entry, of)
        } ?? ("\(page + 1)", "of \(pages)")
    }

    /// Toolbar.pageEntry: the page an entry names (nil: not a page; the field reverts).
    static func entry(labels: [String], pages: Int, current: Int, input: String) -> Int? {
        withCStrings(labels) { ptrs, n in
            var p = 0
            return safepdf_view_page_entry(ptrs, n, pages, current, input, &p) == 1 ? p : nil
        }
    }

    /// Calls `body` with the strings as a borrowed C array (NULL when empty).
    static func withCStrings<T>(_ ss: [String],
                                _ body: (UnsafePointer<UnsafePointer<CChar>?>?, Int) -> T?) -> T? {
        if ss.isEmpty { return body(nil, 0) }
        let dups = ss.map { strdup($0) }
        defer { dups.forEach { free($0) } }
        guard !dups.contains(where: { $0 == nil }) else { return nil }
        let ptrs: [UnsafePointer<CChar>?] = dups.map { UnsafePointer($0) }
        return ptrs.withUnsafeBufferPointer { body($0.baseAddress, ss.count) }
    }
}

/// A place in the document for the history (Links.Loc): page and the scroll fractions of the
/// view's top-left in the scroll region, as exact rationals (pixels over the region's size).
struct NavLoc: Equatable {
    let page: Int
    let x: safepdf_rat
    let y: safepdf_rat

    var c: safepdf_view_loc { safepdf_view_loc(page: page, x: x, y: y) }

    init(page: Int, x: safepdf_rat, y: safepdf_rat) {
        self.page = page
        self.x = x
        self.y = y
    }

    init(_ l: safepdf_view_loc) { self.init(page: l.page, x: l.x, y: l.y) }

    static func == (a: NavLoc, b: NavLoc) -> Bool {
        a.page == b.page && a.x.num == b.x.num && a.x.den == b.x.den && a.y.num == b.y.num && a.y.den == b.y.den
    }
}

/// The back/forward history (Links.History through safepdf_view_history_step): the stacks are
/// Swift arrays; every step goes through the C call.
@MainActor final class NavHistory {
    private(set) var back: [NavLoc] = []
    private(set) var forward: [NavLoc] = []

    var canBack: Bool { !back.isEmpty }
    var canForward: Bool { !forward.isEmpty }

    func clear() {
        back = []
        forward = []
    }

    /// History.push: a jump from `cur` (links, outline, page field, Go to page).
    func push(_ cur: NavLoc) { _ = step(SAFEPDF_HISTORY_PUSH, cur) }

    /// History.goBack / goForward from `cur`: where to go, nil when there is nothing.
    func go(back b: Bool, from cur: NavLoc) -> NavLoc? {
        step(b ? SAFEPDF_HISTORY_BACK : SAFEPDF_HISTORY_FORWARD, cur)
    }

    private func step(_ op: safepdf_history_op, _ cur: NavLoc) -> NavLoc? {
        var bs = back.map(\.c), fs = forward.map(\.c)
        var out = safepdf_view_history()
        var target = safepdf_view_loc()
        let rc = bs.withUnsafeMutableBufferPointer { bp in
            fs.withUnsafeMutableBufferPointer { fp in
                var h = safepdf_view_history(back: bp.baseAddress, back_count: bp.count,
                                             fwd: fp.baseAddress, fwd_count: fp.count)
                return safepdf_view_history_step(op.rawValue, &h, cur.c, &out, &target)
            }
        }
        defer { safepdf_free_view_history(&out) }
        guard rc >= 0 else { return nil }
        var nb: [NavLoc] = [], nf: [NavLoc] = []
        if let p = out.back { for i in 0..<out.back_count { nb.append(NavLoc(p[i])) } }
        if let p = out.fwd { for i in 0..<out.fwd_count { nf.append(NavLoc(p[i])) } }
        back = nb
        forward = nf
        return rc == 1 ? NavLoc(target) : nil
    }
}

/// One axis's wheel state (View.Wheel) and its step (View.wheelStep through
/// safepdf_view_wheel_step).
struct WheelAxis {
    var state = safepdf_wheel()

    /// One event: the action and the scroll position (pixels) for SAFEPDF_WHEEL_SCROLL.
    mutating func step(kind: safepdf_wheel_kind, delta: Int64, cross: Bool, nowMs: UInt64,
                       top: UInt64, view: UInt64, region: UInt64) -> (safepdf_wheel_act, UInt64) {
        var out = safepdf_wheel()
        var pos: UInt64 = 0
        let act = safepdf_view_wheel_step(&state, kind.rawValue, delta, cross, nowMs, top, view, region,
                                          &out, &pos)
        guard act >= 0 else { return (SAFEPDF_WHEEL_NONE, 0) }
        state = out
        return (safepdf_wheel_act(rawValue: UInt32(act)), pos)
    }

    /// A turn at an end of the document went nowhere: it owes nothing (Viewer.wheel).
    mutating func dropOwed() { state.acc = safepdf_rat(num: 0, den: 1) }
}

/// The document's open settings (task 9.r8; safepdf_doc_open_settings), copied into Swift.
struct OpenSettings {
    var hasLayout = false
    var modes = ViewModes.start
    var pageMode: Int32 = SAFEPDF_PAGE_MODE_UNSET.rawValue
    /// The open destination: page and position (page units), when the document gives one.
    var destPage: Int?
    var left: safepdf_rat?
    var top: safepdf_rat?
    var zoom = safepdf_zoom_choice(kind: SAFEPDF_ZOOM_AUTO.rawValue, pct: 0)
    var hideToolbar = false, hideMenubar = false, hideWindowUI = false
    var fitWindow = false, centerWindow = false
    var nonFullScreenMode: Int32 = SAFEPDF_PAGE_MODE_USE_NONE.rawValue
    /// The window title from `/Title` (`/DisplayDocTitle`), when shown.
    var title: String?
    /// What the core could not honour (Issue.message).
    var notes: [String] = []

    /// No settings: where every open starts.
    static let none = OpenSettings()

    /// Reads them (nil when the C call fails).
    @MainActor static func read(_ doc: Document) -> OpenSettings? {
        var c = safepdf_open_settings()
        guard safepdf_doc_open_settings(doc.handle, &c) == 0 else { return nil }
        defer { safepdf_free_open_settings(&c) }
        var s = OpenSettings()
        s.hasLayout = c.has_layout
        s.modes = ViewModes(scroll: c.scroll, spread: c.spread, rtl: c.rtl)
        s.pageMode = c.page_mode
        if c.has_dest, c.dest_page < doc.pageCount {
            s.destPage = c.dest_page
            s.left = c.has_left && c.left.den > 0 ? c.left : nil
            s.top = c.has_top && c.top.den > 0 ? c.top : nil
        }
        s.zoom = c.zoom
        s.hideToolbar = c.hide_toolbar
        s.hideMenubar = c.hide_menubar
        s.hideWindowUI = c.hide_window_ui
        s.fitWindow = c.fit_window
        s.centerWindow = c.center_window
        s.nonFullScreenMode = c.non_full_screen_mode
        s.title = c.title.map { String(cString: $0) }
        if let ns = c.notes {
            for i in 0..<c.note_count { if let n = ns[i] { s.notes.append(String(cString: n)) } }
        }
        return s
    }

    /// Notes for what this shell does not honour yet (the Tk viewer does): the hiding
    /// preferences, full screen, fitting the window, and the sidebar panel a page mode opens
    /// (the sidebar is task 11.3d).
    var shellNotes: [String] {
        var out: [String] = []
        if hideToolbar || hideMenubar || hideWindowUI {
            out.append("the document asks to hide parts of the window (not honoured)")
        }
        if pageMode == SAFEPDF_PAGE_MODE_FULL_SCREEN.rawValue {
            out.append("the document asks for full screen (not honoured)")
        }
        if fitWindow { out.append("the document asks to fit the window to the page (not honoured)") }
        let panelModes: [Int32] = [SAFEPDF_PAGE_MODE_USE_OUTLINES.rawValue, SAFEPDF_PAGE_MODE_USE_THUMBS.rawValue,
                                   SAFEPDF_PAGE_MODE_USE_OC.rawValue, SAFEPDF_PAGE_MODE_USE_ATTACHMENTS.rawValue]
        if panelModes.contains(pageMode) {
            out.append("the document's sidebar panel is not opened yet")
        }
        return out
    }
}
