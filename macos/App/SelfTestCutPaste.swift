// SelfTestCutPaste.swift — the self-test's checks of task 11.6a (the human's manual check of
// the app): the page field's width ("of N" right after a field sized for the document's widest
// entry), ⌘X / ⌘V of every mark kind (same page and another page, one undo step each, a
// highlight's comment travelling with it, the text on a private pasteboard, the menu items'
// validation), the Highlight tool's cursor, and sliding jumps (an outline / link / page-field
// jump passes through intermediate scroll positions and ends exactly at the target; without a
// slide — Reduce motion, or headless — it jumps). Plan.md §6 Phase 11; docs/macos-design.md.
// Headless like SelfTest.swift: no window; the pasteboard is a private one.

import AppKit
import SafePdfC

extension SelfTest {
    static func polishChecks(_ doc: Document, _ pv: PageViewController, dir: String) {
        pageFieldWidth(doc)
        cutPaste(doc, pv)
        highlightCursor(doc, pv)
        slidingJumps(doc, pv)
        outlineSlide(pv, dir: dir)
    }

    /// An outline click slides (the generated five-page fixture with an outline: "Four" goes to
    /// page 4 through SidebarOutline.activate → PageViewController.jump).
    private static func outlineSlide(_ pv: PageViewController, dir: String) {
        let path = "\(dir)/outline-slide.pdf"
        guard (try? settingsPDF("", title: "Outline slide").write(to: URL(fileURLWithPath: path))) != nil,
              let doc = try? Document(url: URL(fileURLWithPath: path)) else {
            check(false, "outline slide fixture")
            return
        }
        let sb = SidebarViewController()
        sb.view.frame = NSRect(x: 0, y: 0, width: 220, height: 600)
        var loaded = false
        sb.onLoaded = { _ in loaded = true }
        pv.setZoom(ZoomModel.auto)
        pv.show(doc)
        sb.show(doc, pages: pv)
        pump(limit: 30) { loaded }
        sb.onLoaded = nil
        let ol = sb.outline
        guard let i = ol.rows.firstIndex(where: { $0.title == "Four" }) else {
            check(false, "outline slide: no \"Four\" item (\(ol.rows.map(\.title)))")
            return
        }
        // Where the jump lands without a slide, then the same click sliding.
        pv.slideOverride = false
        ol.activate(i)
        let dest = pv.scrollView.contentView.bounds.origin
        pv.show(page: 0, .top)
        pv.history.clear()
        pv.slideOverride = true
        ol.activate(i)
        check(pv.isSliding && pv.canvas.currentPage == 3 && pv.history.back.count == 1,
              "an outline click slides to page 4, recorded once")
        var ys: [CGFloat] = []
        pump(limit: 5) {
            ys.append(pv.scrollView.contentView.bounds.origin.y)
            return !pv.isSliding
        }
        let end = pv.scrollView.contentView.bounds.origin
        let mid = Set(ys.filter { abs($0 - dest.y) > 0.5 }).count
        check(end == dest && pv.canvas.currentPage == 3, "the outline slide ends exactly at its destination (\(end) vs \(dest))")
        check(mid >= 2, "the outline slide passes through intermediate positions (\(mid))")
        pv.slideOverride = nil
        say("outline slide: \"Four\" -> page 4 at y \(dest.y), \(mid) intermediate positions")
    }

    // MARK: page field

    private static func pageFieldWidth(_ doc: Document) {
        guard let tb = DocumentToolbar(identifier: "org.safe-pdf.selftest.field") else {
            check(false, "toolbar for the page field")
            return
        }
        for id in tb.identifiers where id != .flexibleSpace && id != .sidebarTrackingSeparator { _ = tb.makeItem(id) }
        let n = doc.pageCount
        tb.fitPageField(labels: doc.labels, pages: n)
        let f = PageText.field(labels: doc.labels, page: 0, pages: n)
        tb.setPage(entry: f.entry, of: f.of)
        let m = tb.pageFieldMetrics
        check(m.width < 56, "the page field is narrower than the old 56 pt box: \(m.width)")
        check(m.gap >= 0 && m.gap <= DocumentToolbar.pageGap + 1, "\"of N\" follows the field: gap \(m.gap)")
        // Labels and many pages widen it (up to its maximum); a short document keeps it small.
        tb.fitPageField(labels: ["i", "ii", "xviii", "xxviii"], pages: 4)
        let roman = tb.pageFieldMetrics.width
        tb.fitPageField(labels: [], pages: 12345)
        let big = tb.pageFieldMetrics.width
        tb.fitPageField(labels: [], pages: 9)
        let small = tb.pageFieldMetrics.width
        check(small <= roman && roman <= big && big <= DocumentToolbar.pageFieldMax && small >= 20,
              "page field widths: 9 pages \(small), roman labels \(roman), 12345 pages \(big)")
        say("page field: \(m.width) pt wide, gap \(m.gap) to \"\(f.of)\"; 9 pages \(small), xxviii \(roman), 12345 pages \(big)")
    }

    // MARK: cut and paste

    private static func index(_ t: TextController, _ p: Int) -> SelectPage? {
        var done: TextOutcome<SelectPage>? = nil
        t.store.withIndex(p, priority: Int32(SAFEPDF_PRIO_CURRENT)) { done = $0 }
        pump(limit: 60) { done != nil }
        if case .ready(let sp)? = done { return sp }
        return nil
    }

    private static func sameGeometry(_ a: Mark, _ b: Mark, dx: Double = 0, dy: Double = 0) -> Bool {
        func eq(_ x: Double, _ y: Double) -> Bool { abs(x - y) <= 1e-6 }
        let quads = a.quads.count == b.quads.count && zip(a.quads, b.quads).allSatisfy {
            eq($0.llx + dx, $1.llx) && eq($0.lly + dy, $1.lly) && eq($0.urx + dx, $1.urx) && eq($0.ury + dy, $1.ury)
        }
        let point = (a.point == nil) == (b.point == nil)
            && (a.point.map { p in b.point.map { eq(p.x + dx, $0.x) && eq(p.y + dy, $0.y) } ?? false } ?? true)
        let strokes = a.strokes.count == b.strokes.count && zip(a.strokes, b.strokes).allSatisfy { s, t in
            s.count == t.count && zip(s, t).allSatisfy { eq($0.x + dx, $1.x) && eq($0.y + dy, $1.y) }
        }
        return a.kind == b.kind && a.color == b.color && a.rgb == b.rgb && a.text == b.text && a.size == b.size
            && a.opacity == b.opacity && quads && point && strokes
    }

    private static func centre(_ mk: Mark) -> CGPoint {
        if mk.isNote, let b = mk.rect { return CGPoint(x: (b.llx + b.urx) / 2, y: (b.lly + b.ury) / 2) }
        if let r = MarksController.extent(mk) { return CGPoint(x: r.midX, y: r.midY) }
        return .zero
    }

    /// Cuts mark `id` (selected by a click at its centre) and pastes it back on the current page;
    /// returns the pasted mark.
    private static func cutAndPaste(_ mc: MarksController, _ m: MarksModel, _ pb: NSPasteboard, _ id: UInt64,
                                    label: String, wantText: String?) -> Mark? {
        guard let mk = m.find(id) else { check(false, "\(label): mark missing"); return nil }
        guard mc.selectMark(page: mk.page, at: centre(mk), openIt: false), mc.markSel == id else {
            check(false, "\(label): a click at its centre selects it (\(mc.markSel ?? 0) vs \(id))")
            return nil
        }
        check(mc.canCut, "\(label): Cut enabled with the mark selected")
        let d0 = m.state.undo_depth
        pb.clearContents()
        mc.cutSelected()
        check(m.find(id) == nil && m.state.undo_depth == d0 + 1, "\(label): Cut removed it in one undo step")
        check(MarksController.clipboard?.mark.id == id && mc.canPaste, "\(label): on the mark clipboard, Paste enabled")
        if let want = wantText {
            check(pb.string(forType: .string) == want, "\(label): its text on the pasteboard: \(pb.string(forType: .string) ?? "nil")")
        }
        let before = m.listAll().count
        mc.paste()
        guard let new = mc.markSel, let pm = m.find(new) else { check(false, "\(label): Paste made no mark"); return nil }
        check(new != id && m.listAll().count == before + 1 + (mk.isHighlight && MarksController.clipboard?.comment != nil ? 1 : 0)
              && m.state.undo_depth == d0 + 2, "\(label): Paste is one undo step")
        return pm
    }

    private static func cutPaste(_ doc: Document, _ pv: PageViewController) {
        let mc = pv.marks
        let t = pv.text
        let pb = NSPasteboard(name: NSPasteboard.Name("org.safe-pdf.selftest.cut.\(getpid())"))
        defer { pb.releaseGlobally(); t.pasteboard = .general }
        t.pasteboard = pb
        pv.canvas.scaleOverride = 2
        pv.show(doc)
        waitRenders(pv)
        mc.tool(Int32(SAFEPDF_TOOL_SELECT.rawValue))
        guard let m = mc.model, let box = doc.geometry.first?.box else { check(false, "cut/paste: no store"); return }
        MarksController.clipboard = nil
        check(!mc.canCut && !mc.canPaste, "nothing selected, nothing cut: Cut and Paste disabled")
        // The menu items: the window controller validates the standard cut: / paste: actions.
        if let (menu, _) = MainMenu.build() {
            let edit = menu.items.first { $0.submenu?.title == "Edit" }?.submenu
            let cut = edit?.items.first { $0.action == #selector(NSText.cut(_:)) }
            let paste = edit?.items.first { $0.action == #selector(NSText.paste(_:)) }
            check(cut?.keyEquivalent == "x" && paste?.keyEquivalent == "v" && cut?.isHidden == false && paste?.isHidden == false,
                  "Edit has Cut (⌘X) and Paste (⌘V)")
            if let e = edit, let ci = e.items.firstIndex(where: { $0.action == #selector(NSText.cut(_:)) }),
               let pi = e.items.firstIndex(where: { $0.action == #selector(NSText.paste(_:)) }) {
                check(pi == ci + 2 && e.items[ci + 1].tag == Commands.id(SAFEPDF_CMD_COPY), "Cut, Copy, Paste in order")
            }
        }
        let x0 = ZoomModel.double(box.llx), y0 = ZoomModel.double(box.lly)
        let x1 = ZoomModel.double(box.urx), y1 = ZoomModel.double(box.ury)
        let cx = (x0 + x1) / 2, cy = (y0 + y1) / 2
        var log: [String] = []

        // 1. A highlight with its comment (over the page's first words when it has text).
        var quads = [safepdf_box(llx: cx - 60, lly: cy + 100, urx: cx + 20, ury: cy + 112)]
        var hlText: String? = nil
        if let sp = index(t, 0), sp.cellCount >= 6,
           let l = safepdf_select_range_boxes(sp.handle, 0, min(sp.cellCount - 1, 12)) {
            var qs: [safepdf_box] = []
            if let bs = l.pointee.boxes { for i in 0..<l.pointee.count { qs.append(bs[i]) } }
            safepdf_select_free_box_list(l)
            if !qs.isEmpty {
                quads = qs
                if let c = safepdf_select_copy(sp.handle, 0, min(sp.cellCount - 1, 12)) {
                    hlText = Core.string(c.pointee.text)
                    safepdf_select_free_copy_result(c)
                }
            }
        }
        if case .success(let hl) = m.addHighlight(page: 0, color: Int32(SAFEPDF_COLOR_GREEN), quads: quads),
           case .success(let cm) = m.addComment(hl, text: "travels with it"), let hm = m.find(hl) {
            _ = m.recolor(cm, Int32(SAFEPDF_COLOR_PINK))
            if let pm = cutAndPaste(mc, m, pb, hl, label: "highlight", wantText: hlText) {
                check(sameGeometry(hm, pm), "highlight pasted at the same place with its colour")
                let comments = m.list(0).filter { $0.isNote && $0.isComment && $0.quads.count == pm.quads.count
                    && zip($0.quads, pm.quads).allSatisfy { MarksModel.same($0.0, $0.1) } }
                check(comments.count == 1 && comments.first?.text == "travels with it"
                      && comments.first?.color == Int32(SAFEPDF_COLOR_PINK), "the comment travelled with its highlight")
                // Undo takes the paste (highlight and comment) back at once; redo brings both.
                let n = m.listAll().count
                mc.undoRedo(undo: true)
                check(m.listAll().count == n - 2 && m.find(pm.id) == nil, "undo removed the pasted highlight and comment")
                mc.undoRedo(undo: false)
                check(m.listAll().count == n && m.find(pm.id) != nil, "redo restored them")
                // Paste works again: a second copy.
                mc.paste()
                check(m.listAll().count == n + 2, "a second Paste adds another copy")
                mc.undoRedo(undo: true)
                log.append("highlight + comment")
            }
        } else {
            check(false, "cut/paste: a highlight with a comment")
        }

        // 2. A note at a point, 3. free text, 4. a drawing of two strokes.
        if case .success(let id) = m.addNote(page: 0, color: Int32(SAFEPDF_COLOR_BLUE), text: "a note",
                                             anchor: Int32(SAFEPDF_ANCHOR_POINT), point: CGPoint(x: cx - min(150, abs(x1 - x0) / 4), y: cy), quads: []),
           let before = m.find(id), let pm = cutAndPaste(mc, m, pb, id, label: "note", wantText: "a note") {
            check(sameGeometry(before, pm), "note pasted at the same place, colour and text kept")
            log.append("note")
        }
        if case .success(let id) = m.addFreeText(page: 0, text: "free text", at: CGPoint(x: cx, y: cy - 50), size: 18, rgb: 0x2050C0),
           let before = m.find(id), let pm = cutAndPaste(mc, m, pb, id, label: "free text", wantText: "free text") {
            check(sameGeometry(before, pm), "free text pasted at the same place, size and colour kept")
            log.append("free text")
        }
        var inkMark: Mark? = nil
        if case .success(let id) = m.addInk(page: 0, points: [CGPoint(x: cx - 40, y: cy - 150), CGPoint(x: cx + 40, y: cy - 140)],
                                            width: 6, opacity: 70, rgb: 0xC02020) {
            m.addStroke(id, points: [CGPoint(x: cx - 40, y: cy - 160), CGPoint(x: cx + 40, y: cy - 170), CGPoint(x: cx, y: cy - 180)])
            if let before = m.find(id), let pm = cutAndPaste(mc, m, pb, id, label: "drawing", wantText: nil) {
                check(sameGeometry(before, pm) && pm.strokes.count == 2, "drawing pasted with both strokes, width, opacity, colour")
                inkMark = pm
                log.append("drawing")
            }
        }

        // 5. Another page: the same page coordinates, moved inside the page box.
        if doc.pageCount > 1, let ink = inkMark {
            pv.goTo(1)
            let n = m.listAll().count, d0 = m.state.undo_depth
            mc.paste()
            if let id = mc.markSel, let pm = m.find(id) {
                let tb = doc.geometry[1].box
                let d = MarksController.pasteOffset(ink, into: tb)
                check(pm.page == 1 && sameGeometry(ink, pm, dx: Double(d.dx), dy: Double(d.dy)),
                      "pasted on page 2 at the same coordinates (moved by \(d.dx), \(d.dy) into its box)")
                if let e = MarksController.extent(pm) {
                    let bx0 = ZoomModel.double(tb.llx), by0 = ZoomModel.double(tb.lly)
                    let bx1 = ZoomModel.double(tb.urx), by1 = ZoomModel.double(tb.ury)
                    check(e.minX >= min(bx0, bx1) - 1e-6 && e.maxX <= max(bx0, bx1) + 1e-6
                          && e.minY >= min(by0, by1) - 1e-6 && e.maxY <= max(by0, by1) + 1e-6, "inside page 2's box")
                }
                check(m.listAll().count == n + 1 && m.state.undo_depth == d0 + 1, "one undo step on page 2")
                log.append("drawing on page 2")
            } else {
                check(false, "paste on page 2")
            }
            pv.goTo(0)
        }
        // A mark far outside: clamped into the box (the offset's rule).
        if let mk = m.listAll().first {
            var far = mk
            far = Mark(copying: far, shiftedBy: 1e5)
            let d = MarksController.pasteOffset(far, into: box)
            if let e = MarksController.extent(far) {
                let moved = e.offsetBy(dx: d.dx, dy: d.dy)
                check(moved.maxX <= max(x0, x1) + 1e-6 && moved.maxY <= max(y0, y1) + 1e-6, "a mark beyond the page is moved inside")
            }
        }
        say("cut/paste: \(log.joined(separator: ", ")); \(m.listAll().count) marks, undo depth \(m.state.undo_depth)")
        MarksController.clipboard = nil
    }

    // MARK: the Highlight tool's cursor

    private static func highlightCursor(_ doc: Document, _ pv: PageViewController) {
        let mc = pv.marks, t = pv.text
        guard mc.model != nil, let r = pv.canvas.rect(ofPage: pv.canvas.currentPage) else { return }
        let vis = r.intersection(pv.canvas.visibleRect)
        guard !vis.isNull else { return }
        let at = CGPoint(x: vis.maxX - 12, y: vis.maxY - 12)
        mc.tool(Int32(SAFEPDF_TOOL_SELECT.rawValue))
        t.updateCursor(at: at)
        check(!t.showsHighlighter, "Select text: no highlighter cursor")
        mc.tool(Int32(SAFEPDF_TOOL_HIGHLIGHT.rawValue))
        check(mc.mode == SAFEPDF_MODE_HIGHLIGHT.rawValue, "the Highlight tool is on")
        t.updateCursor(at: at)
        check(t.showsHighlighter, "Highlight tool over the page: the highlighter cursor (rule gave \(t.cursor))")
        let c = TextController.highlighterCursor
        check(c !== NSCursor.iBeam && c !== NSCursor.arrow && c.image.size == NSSize(width: 24, height: 24)
              && c.hotSpot.x < 8 && c.hotSpot.y > 12, "the highlighter cursor: 24 pt, hot spot at the tip \(c.hotSpot)")
        t.updateCursor(at: CGPoint(x: r.minX - 40, y: r.minY - 40))
        check(!t.showsHighlighter, "off the page: not the highlighter")
        mc.tool(Int32(SAFEPDF_TOOL_SELECT.rawValue))
        check(mc.mode == SAFEPDF_MODE_SELECT.rawValue, "back to Select text")
        say("cursor: highlighter \(c.image.size) hot spot \(c.hotSpot)")
    }

    // MARK: sliding jumps

    private static func slidingJumps(_ doc: Document, _ pv: PageViewController) {
        check(PageViewController.slideAllowed(inWindow: true, reduceMotion: false)
              && !PageViewController.slideAllowed(inWindow: true, reduceMotion: true)
              && !PageViewController.slideAllowed(inWindow: false, reduceMotion: false),
              "jumps slide on screen unless Reduce motion is on")
        let n = doc.pageCount
        guard n > 1 else { say("sliding jumps: one page, skipped"); return }
        pv.setZoom(ZoomModel.auto)
        pv.setModes(ViewModes.start)
        let target = min(n - 1, 3)
        // The jump without a slide (Reduce motion, headless): at once.
        pv.slideOverride = false
        pv.show(page: 0, .top)
        let s0 = pv.slidesStarted
        let h0 = pv.history.back.count
        pv.jump(to: target)
        let dest = pv.scrollView.contentView.bounds.origin
        check(!pv.isSliding && pv.slidesStarted == s0 && pv.canvas.currentPage == target,
              "without a slide the jump is immediate")
        check(pv.history.back.count == h0 + 1, "the jump is recorded once")
        // The same jump sliding: intermediate positions, the destination exactly, recorded once.
        pv.show(page: 0, .top)
        let start = pv.scrollView.contentView.bounds.origin
        guard abs(start.y - dest.y) >= 4 else {
            pv.slideOverride = nil
            say("sliding jumps: the document fits the view (nothing to slide), skipped")
            return
        }
        pv.slideOverride = true
        let h1 = pv.history.back.count
        pv.jump(to: target)
        check(pv.isSliding && pv.slidesStarted == s0 + 1 && pv.canvas.currentPage == target,
              "the jump slides; the current page is the target at once")
        var seen: [CGFloat] = []
        let ms = pump(limit: 5) {
            seen.append(pv.scrollView.contentView.bounds.origin.y)
            if pv.canvas.currentPage != target { seen.append(-1e9) }
            return !pv.isSliding
        }
        let end = pv.scrollView.contentView.bounds.origin
        let lo = min(start.y, dest.y), hi = max(start.y, dest.y)
        let between = Set(seen.filter { $0 > lo + 0.5 && $0 < hi - 0.5 }).count
        check(!pv.isSliding && end == dest, "the slide ends exactly at the destination (\(end) vs \(dest))")
        check(between >= 2, "the slide passes through intermediate positions (\(between) seen)")
        check(!seen.contains(-1e9) && pv.canvas.currentPage == target, "the current page stays the target while sliding")
        check(pv.history.back.count == h1 + 1, "a sliding jump is recorded once")
        // Back slides too; a far jump starts close to the destination (at most slideMaxViews).
        pv.historyMove(back: true)
        pump(limit: 5) { !pv.isSliding }
        check(pv.canvas.currentPage == 0 && pv.scrollView.contentView.bounds.origin == start, "Back slides back to the start")
        if n > 8 {
            pv.jump(to: n - 1)
            let first = pv.scrollView.contentView.bounds.origin.y
            pump(limit: 5) { !pv.isSliding }
            let last = pv.scrollView.contentView.bounds.origin.y
            let h = pv.scrollView.contentView.bounds.height
            check(abs(last - first) <= PageViewController.slideMaxViews * h + 1,
                  "a far jump slides at most \(PageViewController.slideMaxViews) views (\(abs(last - first)) of \(h))")
        }
        pv.slideOverride = nil
        say(String(format: "sliding jump: page 1 -> %d in %.0f ms, %d frames, %d intermediate positions",
                   target + 1, ms, pv.slideFrames, between))
    }
}

extension Mark {
    /// A copy moved by `d` page units on both axes (the self-test's far-away mark).
    init(copying m: Mark, shiftedBy d: Double) {
        var c = safepdf_mark()
        c.id = m.id
        c.kind = m.kind
        c.page = m.page
        c.color = m.color
        c.size = m.size
        c.opacity = m.opacity
        if let p = m.point {
            c.has_point = 1
            c.point = safepdf_point(x: Double(p.x) + d, y: Double(p.y) + d)
        }
        if let r = m.rect {
            c.has_rect = 1
            c.rect = safepdf_box(llx: r.llx + d, lly: r.lly + d, urx: r.urx + d, ury: r.ury + d)
        }
        self.init(c)
    }
}
