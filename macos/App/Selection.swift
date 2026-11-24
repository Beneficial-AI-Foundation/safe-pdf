// Selection.swift — text selection on the page view, Copy and Select All, the pointer's cursor
// (task 11.3d1). Plan.md §6 Phase 11; docs/macos-design.md §1 (selection bands, accent colour)
// and §3 decision 1: every rule is a call into the exported logic the Tk viewer uses
// (safepdf_select.h: Select.dragRange, wordAt, lineAt, selBands, rangeText / copyStatus;
// safepdf_view.h: Toolbar.hitOf / cursorFor); Swift converts coordinates and draws.
//
// The Tk viewer's behaviour (Viewer.press / dragTo / selectWord / selectAll / copySel /
// hover): a press clears the selection; a drag selects on the page it started on, from the
// glyph nearest the press point to the glyph nearest the pointer (mapped onto that page even
// outside it); a click in place follows the link under it; a double click selects the word of
// the nearest glyph. Native additions on the same calls: a triple click selects the line
// (Select.lineAt), shift-click extends the selection from where it started. The selection is
// drawn as one translucent band per line (Select.selBands, task 10.18) in the system accent
// colour at 35 % — edges on device pixels so joined bands share an edge — above the page image.

import AppKit
import SafePdfC

/// The page-space ↔ view mapping of a laid-out page (the view's points), read from the exact
/// Geom.toScreen (safepdf_view_to_screen) at three page points: page → view is that affine map
/// (a quarter-turn rotation, a y-flip and the zoom), view → page its inverse (Geom.toPage is the
/// inverse of toScreen, theorem toPage_toScreen). Display doubles only.
struct PageTransform {
    // view.x = ox + ax * x + bx * y; view.y = oy + ay * x + by * y
    let ox, oy, ax, ay, bx, by: Double

    /// The view point of page point (x, y).
    func view(_ x: Double, _ y: Double) -> CGPoint {
        CGPoint(x: ox + ax * x + bx * y, y: oy + ay * x + by * y)
    }

    /// The page point at view point `v` (nil when the map is degenerate).
    func page(_ v: CGPoint) -> (x: Double, y: Double)? {
        let det = ax * by - bx * ay
        guard det != 0, det.isFinite else { return nil }
        let dx = Double(v.x) - ox, dy = Double(v.y) - oy
        return ((by * dx - bx * dy) / det, (ax * dy - ay * dx) / det)
    }

    /// The view rectangle of a page-space box (Viewer's Slot.rect: the two corners' images).
    func rect(_ b: safepdf_box) -> CGRect {
        let p = view(b.llx, b.lly), q = view(b.urx, b.ury)
        return CGRect(x: min(p.x, q.x), y: min(p.y, q.y), width: abs(q.x - p.x), height: abs(q.y - p.y))
    }
}

extension PageCanvasView {
    /// The page-space mapping of `page` in the current layout (nil when it is not laid out).
    func transform(ofPage page: Int) -> PageTransform? {
        guard let doc = document, page >= 0, page < doc.geometry.count, let pl = place(ofPage: page)
        else { return nil }
        let box = doc.geometry[page].box
        let zero = safepdf_rat(num: 0, den: 1), one = safepdf_rat(num: 1, den: 1)
        guard let o = ZoomModel.toScreen(z: pl.zoom, rot: pl.rotation, box: box, x: zero, y: zero),
              let ex = ZoomModel.toScreen(z: pl.zoom, rot: pl.rotation, box: box, x: one, y: zero),
              let ey = ZoomModel.toScreen(z: pl.zoom, rot: pl.rotation, box: box, x: zero, y: one)
        else { return nil }
        let b = Double(laidOutBacking)
        guard b > 0 else { return nil }
        return PageTransform(ox: (Double(pl.pixels.minX) + Double(o.x)) / b,
                             oy: (Double(pl.pixels.minY) + Double(o.y)) / b,
                             ax: Double(ex.x - o.x) / b, ay: Double(ex.y - o.y) / b,
                             bx: Double(ey.x - o.x) / b, by: Double(ey.y - o.y) / b)
    }

    /// The pages meeting the visible area (View.visiblePages).
    func visiblePages() -> [Int] {
        guard let holder = layout else { return [] }
        let b = laidOutBacking
        let v = visibleRect
        var band = safepdf_page_band()
        guard safepdf_view_pages_in_band(&holder.raw, UInt64(max(0, v.minY * b)), UInt64(max(0, v.maxY * b)),
                                         &band) == 0 else { return [] }
        var out: [Int] = []
        if let p = band.visible { for i in 0..<band.visible_count { out.append(p[i]) } }
        safepdf_free_page_band(&band)
        return out
    }

    /// `r` (view points) with its edges moved to the nearest device pixel.
    func pixelAligned(_ r: CGRect) -> CGRect {
        let b = laidOutBacking
        func f(_ v: CGFloat) -> CGFloat { (v * b).rounded() / b }
        let x0 = f(r.minX), y0 = f(r.minY), x1 = f(r.maxX), y1 = f(r.maxY)
        return CGRect(x: x0, y: y0, width: max(0, x1 - x0), height: max(0, y1 - y0))
    }

    /// `r` grown outwards to whole device pixels (search hits, as Tk's floor / ceil).
    func pixelOutward(_ r: CGRect) -> CGRect {
        let b = laidOutBacking
        let x0 = (r.minX * b).rounded(.down) / b, y0 = (r.minY * b).rounded(.down) / b
        let x1 = (r.maxX * b).rounded(.up) / b, y1 = (r.maxY * b).rounded(.up) / b
        return CGRect(x: x0, y: y0, width: x1 - x0, height: y1 - y0)
    }
}

/// A text selection: inclusive cell range on one page.
struct TextSelection: Equatable {
    let page: Int
    let first: Int
    let last: Int
}

/// Selection, copy, the pointer and the overlays of the page view; owns the find and link
/// controllers. One per page view.
@MainActor final class TextController: CanvasPointer {
    private weak var pages: PageViewController?
    let store = TextStore()
    private(set) lazy var find = FindController(self)
    private(set) lazy var links = LinkController(self)

    /// The selection (nil: none).
    private(set) var selection: TextSelection?
    /// The selection's bands in page space (Select.selBands), computed when it changes.
    private(set) var bands: [safepdf_box] = []
    /// Where the selection started (page point): shift-click extends from here.
    private var anchor: (page: Int, x: Double, y: Double)?
    /// A press that may become a drag: its page and page point, and its view point.
    private var press: (page: Int, x: Double, y: Double, view: CGPoint)?
    private var pressMoved = false
    /// The latest drag point (page space of the press page), applied when the index arrives.
    private var dragTo: (x: Double, y: Double)?
    private var dragWaiting = false
    /// Bumped on every press: work waiting for an index belongs to the press that started it.
    private var interaction = 0
    /// The row of the file attachment annotation icon at page point (x, y) of a page, if any
    /// (task 11.3f, Attach.iconAt; the sidebar's attachments panel answers).
    var attachmentAt: ((Int, Double, Double) -> Int?)?
    /// A click in place on a file attachment annotation's icon (Viewer.attSelect): its row.
    var onAttachmentIcon: ((Int) -> Void)?
    /// The active tool (Toolbar.Mode; Select text until the tools of task 11.3e).
    var mode = UInt32(SAFEPDF_MODE_SELECT.rawValue)
    /// The pasteboard Copy and Copy Address write (the self-test uses a private one).
    var pasteboard = NSPasteboard.general
    /// The cursor the pointer shows now (safepdf_cursor; the self-test reads it).
    private(set) var cursor = UInt32(SAFEPDF_CURSOR_ARROW.rawValue)
    /// The link under the pointer (page, index), for the status text on entering it.
    private var hoverLink: (page: Int, index: Int)?
    /// Called when the selection changes (the window's Copy state).
    var onSelectionChange: (() -> Void)?
    /// Called when a drag, double or triple click has finished selecting text (task 11.3e1:
    /// the Highlight tool highlights it on release, the bubble shows).
    var onSelectionFinished: (() -> Void)?
    /// Draws a page's marks under the search hits and the selection (task 11.3e1).
    var drawMarks: ((Int, PageTransform, PageCanvasView) -> Void)?
    /// Whether a mark lies under a page point (the cursor's hit test, task 11.3e1).
    var markAt: ((Int, Double, Double) -> Bool)?
    /// The window sheets attach to (nil: none; the self-test).
    var sheetWindow: (() -> NSWindow?)?
    /// Pixel distance a press may move and still be a click (in place).
    static let clickSlop: CGFloat = 3

    var canvas: PageCanvasView? { pages?.canvas }
    var pageView: PageViewController? { pages }
    var document: Document? { pages?.canvas.document }

    /// Connects to the page view (its canvas sends pointer events and asks for overlays).
    func attach(_ pv: PageViewController) {
        pages = pv
        pv.canvas.pointer = self
        pv.canvas.drawOverlay = { [weak self] page in self?.drawOverlay(page) }
        store.onIndex = { [weak self] page in self?.indexArrived(page) }
    }

    /// A new document (nil: none): no selection, no search, nothing cached.
    func reset(_ doc: Document?) {
        find.reset()
        links.reset()
        store.reset(doc)
        selection = nil
        bands = []
        anchor = nil
        press = nil
        dragTo = nil
        dragWaiting = false
        hoverLink = nil
        interaction += 1
        onSelectionChange?()
    }

    /// The layers state changed (task 11.3d2): the text indexes were built under the old state,
    /// so drop them with the selection and the search hit, as Tk's `applyLayers` does.
    func layersChanged() { reset(store.document) }

    /// The pill (status line).
    func status(_ text: String) { pages?.pill.show(text) }

    /// Redraws page `p`.
    func redraw(_ p: Int) {
        if let c = canvas, let r = c.rect(ofPage: p) { c.setNeedsDisplay(r.insetBy(dx: -2, dy: -2)) }
    }

    /// The page and page point under view point `v` (the page containing it, else the nearest:
    /// View.pageAt, as the Tk viewer's pagePointAt).
    func pagePoint(at v: CGPoint) -> (page: Int, x: Double, y: Double)? {
        guard let c = canvas, let p = c.page(at: v), let t = c.transform(ofPage: p), let q = t.page(v)
        else { return nil }
        return (p, q.x, q.y)
    }

    /// The key text of a command as the menu shows it (its accelerator: modifiers in Apple's
    /// order ⌃⌥⇧⌘, then the key's name; e.g. "⌘C").
    static func keyText(_ cmd: safepdf_cmd) -> String {
        let id = Commands.id(cmd)
        guard let cs = Chrome.commands(), id < cs.count, !cs[id].accel.shown.isEmpty else { return "" }
        let k = cs[id].accel
        var s = ""
        if k.mods & UInt32(SAFEPDF_MOD_CONTROL) != 0 { s += "⌃" }
        if k.mods & UInt32(SAFEPDF_MOD_OPTION) != 0 { s += "⌥" }
        if k.mods & UInt32(SAFEPDF_MOD_SHIFT) != 0 { s += "⇧" }
        if k.mods & UInt32(SAFEPDF_MOD_COMMAND) != 0 { s += "⌘" }
        return s + k.shown
    }

    // MARK: selection

    /// Sets the selection (nil: none), its bands, and redraws.
    func setSelection(_ s: TextSelection?) {
        let old = selection
        selection = s
        bands = []
        if let s, let sp = store.index(s.page), let l = safepdf_select_bands(sp.handle, s.first, s.last) {
            if let bs = l.pointee.boxes { for i in 0..<l.pointee.count { bands.append(bs[i]) } }
            safepdf_select_free_box_list(l)
        }
        if let o = old { redraw(o.page) }
        if let s { redraw(s.page) }
        if old != s { onSelectionChange?() }
    }

    /// The status after a selection change (Viewer.selStatus).
    private func selStatus() {
        guard let s = selection, let sp = store.index(s.page),
              let c = safepdf_select_copy(sp.handle, s.first, s.last) else { return }
        let n = c.pointee.chars
        safepdf_select_free_copy_result(c)
        let key = Self.keyText(SAFEPDF_CMD_COPY)
        status("page \(s.page + 1): selected \(n) characters (\(key.isEmpty ? "Copy" : key) copies)")
    }

    /// Runs `body` with page `page`'s index for the current press (at once, or when it arrives;
    /// dropped if another press came meanwhile). A page without text says so.
    private func withIndex(_ page: Int, _ body: @escaping (SelectPage) -> Void) {
        let token = interaction
        store.withIndex(page, priority: Int32(SAFEPDF_PRIO_CURRENT)) { [weak self] outcome in
            guard let self, self.interaction == token else { return }
            switch outcome {
            case .ready(let sp): body(sp)
            case .failed(let e): self.status("page \(page + 1): no text: \(e)")
            case .cancelled: break
            }
        }
    }

    /// Select All (⌘A): all the text of the current page (Viewer.selectAll).
    func selectAll() {
        guard let c = canvas, document != nil else { return }
        let p = c.currentPage
        interaction += 1
        withIndex(p) { [weak self] sp in
            guard let self else { return }
            if sp.cellCount == 0 {
                self.status("page \(p + 1): no text")
            } else {
                self.anchor = nil
                self.setSelection(TextSelection(page: p, first: 0, last: sp.cellCount - 1))
                self.selStatus()
            }
        }
    }

    /// Copy (⌘C): the selection's text on the pasteboard; the status counts the characters and
    /// the invisible ones among them (Viewer.copySel, Select.copyStatus, task 12.5). Returns
    /// the text copied (nil: nothing).
    @discardableResult
    func copy() -> String? {
        guard let s = selection, let sp = store.index(s.page) else {
            let key = Self.keyText(SAFEPDF_CMD_SELECT_ALL)
            status("nothing selected (drag over text, double-click a word, or \(key.isEmpty ? "Select All" : key))")
            return nil
        }
        guard let c = safepdf_select_copy(sp.handle, s.first, s.last) else { return nil }
        let text = Core.string(c.pointee.text)
        let st = Core.string(c.pointee.status)
        safepdf_select_free_copy_result(c)
        pasteboard.clearContents()
        pasteboard.setString(text, forType: .string)
        status(st)
        return text
    }

    /// The text under highlight quads of page `page` (task 11.6a: Cut puts a highlight's text on
    /// the pasteboard): the cells from the first quad's left end to the last quad's right end
    /// (Select.nearest, quads in reading order as Select.rangeBoxes makes them), copied as Copy
    /// copies cells; nil when the page's text index is not loaded or there is no text.
    func text(under quads: [safepdf_box], page: Int) -> String? {
        guard let f = quads.first, let l = quads.last, let sp = store.index(page), sp.cellCount > 0 else { return nil }
        var a = 0, b = 0
        let fx = min(f.llx + 0.5, (f.llx + f.urx) / 2), lx = max(l.urx - 0.5, (l.llx + l.urx) / 2)
        guard safepdf_select_nearest(sp.handle, fx, (f.lly + f.ury) / 2, &a) == 0,
              safepdf_select_nearest(sp.handle, lx, (l.lly + l.ury) / 2, &b) == 0,
              let c = safepdf_select_copy(sp.handle, min(a, b), max(a, b)) else { return nil }
        defer { safepdf_select_free_copy_result(c) }
        let s = Core.string(c.pointee.text)
        return s.isEmpty ? nil : s
    }

    // MARK: pointer (CanvasPointer)

    /// Whether a press (a click or a drag) is going on.
    var isPressing: Bool { press != nil }

    /// Forgets the press going on (task 11.3e1: the marks took the click).
    func cancelPress() {
        press = nil
        pressMoved = false
        dragTo = nil
        interaction += 1
    }

    /// The highlight boxes of the selection (Select.rangeBoxes: the quads a highlight gets and
    /// a note anchors to, as in the Tk viewer); empty without a selection or its index.
    func selectionBoxes() -> [safepdf_box] {
        guard let s = selection, let sp = store.index(s.page),
              let l = safepdf_select_range_boxes(sp.handle, s.first, s.last) else { return [] }
        defer { safepdf_select_free_box_list(l) }
        var out: [safepdf_box] = []
        if let bs = l.pointee.boxes { for i in 0..<l.pointee.count { out.append(bs[i]) } }
        return out
    }

    func pointerDown(at v: CGPoint, clicks: Int, shift: Bool) {
        guard document != nil,
              mode == SAFEPDF_MODE_SELECT.rawValue || mode == SAFEPDF_MODE_HIGHLIGHT.rawValue else { return }
        interaction += 1
        pressMoved = false
        dragTo = nil
        dragWaiting = false
        guard let (page, x, y) = pagePoint(at: v) else {
            press = nil
            setSelection(nil)
            return
        }
        if clicks >= 2 {
            // Double click: the word of the nearest glyph (Viewer.selectWord); triple: its line.
            press = nil
            withIndex(page) { [weak self] sp in
                guard let self else { return }
                var cell = 0
                guard safepdf_select_nearest(sp.handle, x, y, &cell) == 0 else { return }
                let r = clicks >= 3 ? safepdf_select_line_at(sp.handle, cell) : safepdf_select_word_at(sp.handle, cell)
                self.anchor = (page, x, y)
                self.setSelection(TextSelection(page: page, first: r.first, last: r.last))
                self.selStatus()
                self.onSelectionFinished?()
            }
            return
        }
        if shift, let a = anchor, a.page == page, selection?.page == page {
            // Shift-click: the selection from where it started to here (Select.dragRange);
            // dragging on extends it further.
            press = (page, a.x, a.y, v)
            pressMoved = true
            dragTo = (x, y)
            applyDrag(final: true)
            return
        }
        press = (page, x, y, v)
        anchor = (page, x, y)
        setSelection(nil)
        // Ask for the page's text now: the drag needs it.
        store.withIndex(page, priority: Int32(SAFEPDF_PRIO_CURRENT))
    }

    func pointerDragged(at v: CGPoint) {
        guard let p = press, let c = canvas, let t = c.transform(ofPage: p.page), let q = t.page(v) else { return }
        if !pressMoved && hypot(v.x - p.view.x, v.y - p.view.y) <= Self.clickSlop { return }
        pressMoved = true
        dragTo = (q.x, q.y)
        applyDrag(final: false)
    }

    func pointerUp(at v: CGPoint) {
        guard let p = press else { return }
        if !pressMoved {
            // A click in place: a file attachment annotation's icon selects its row in the
            // attachments panel (task 11.3f; never opened), else follow the link under it
            // (Viewer.dragTo).
            press = nil
            if let c = canvas, let t = c.transform(ofPage: p.page), let q = t.page(v) {
                if let i = attachmentAt?(p.page, q.x, q.y) {
                    onAttachmentIcon?(i)
                    return
                }
                links.click(page: p.page, x: q.x, y: q.y)
            }
            return
        }
        if let c = canvas, let t = c.transform(ofPage: p.page), let q = t.page(v) { dragTo = (q.x, q.y) }
        applyDrag(final: true)
    }

    /// Selects from the press point to the latest drag point on the press page
    /// (Select.dragRange); when the index has not arrived, once it does.
    private func applyDrag(final: Bool) {
        guard let p = press, let to = dragTo else { return }
        if final { press = nil }
        guard let sp = store.index(p.page) else {
            if let e = store.indexError(p.page) {
                if final { status("page \(p.page + 1): no text: \(e)") }
                return
            }
            guard !dragWaiting else {
                if final { pendingFinal = (p.page, p.x, p.y, to) }
                return
            }
            dragWaiting = true
            if final { pendingFinal = (p.page, p.x, p.y, to) }
            let token = interaction
            store.withIndex(p.page, priority: Int32(SAFEPDF_PRIO_CURRENT)) { [weak self] outcome in
                guard let self, self.interaction == token else { return }
                self.dragWaiting = false
                if case .failed(let e) = outcome { self.status("page \(p.page + 1): no text: \(e)") }
                guard case .ready = outcome else { return }
                if let f = self.pendingFinal {
                    self.pendingFinal = nil
                    self.select(f.page, from: (f.x, f.y), to: f.to, final: true)
                } else if let cur = self.press, let d = self.dragTo {
                    self.select(cur.page, from: (cur.x, cur.y), to: d, final: false)
                }
            }
            return
        }
        select(p.page, from: (p.x, p.y), to: to, final: final, page: sp)
    }

    /// A final drag that waits for its page's index.
    private var pendingFinal: (page: Int, x: Double, y: Double, to: (x: Double, y: Double))?

    private func select(_ page: Int, from a: (Double, Double), to b: (x: Double, y: Double), final: Bool,
                        page sp: SelectPage? = nil) {
        guard let sp = sp ?? store.index(page) else { return }
        var r = safepdf_select_range()
        if safepdf_select_drag(sp.handle, a.0, a.1, b.x, b.y, &r) == 0 {
            setSelection(TextSelection(page: page, first: r.first, last: r.last))
            if final {
                selStatus()
                onSelectionFinished?()
            }
        }
    }

    func pointerMoved(at v: CGPoint?) {
        guard press == nil else { return }
        updateCursor(at: v)
    }

    /// The cursor at view point `v` (Toolbar.hitOf / cursorFor, as Viewer.hover): over a link
    /// the pointing hand (and the status shows its target on entering it), over a glyph the
    /// I-beam, else the arrow. A page whose links or text have not arrived asks for them.
    func updateCursor(at v: CGPoint?) {
        var link: (page: Int, index: Int)? = nil
        var text = false
        var mark = false
        var overPage = false
        if let v, document != nil, let (page, x, y) = pagePoint(at: v) {
            overPage = canvas?.rect(ofPage: page)?.contains(v) ?? false
            mark = markAt?(page, x, y) ?? false
            if let ls = store.links(page) {
                if let i = ls.index(at: x, y) { link = (page, i) }
            } else if !store.linksKnown(page) {
                store.withLinks(page, priority: Int32(SAFEPDF_PRIO_VISIBLE))
            }
            let m = UInt32(mode)
            let wantsText = m == SAFEPDF_MODE_SELECT.rawValue || m == SAFEPDF_MODE_HIGHLIGHT.rawValue
            if link == nil && wantsText {
                if let sp = store.index(page) {
                    text = safepdf_select_over_text(sp.handle, x, y) != 0
                } else if !store.indexKnown(page) {
                    store.withIndex(page, priority: Int32(SAFEPDF_PRIO_VISIBLE))
                }
            }
        }
        let hit = safepdf_view_hit_of(mark, link != nil, text)
        cursor = safepdf_view_cursor_for(UInt32(mode), hit)
        // Task 11.6a: with the Highlight tool the page shows the highlighter where the exported
        // rule (Toolbar.cursorFor) gives the I-beam or the arrow — the rule is kept, only its
        // AppKit picture differs; links and marks keep the pointing hand.
        showsHighlighter = overPage && UInt32(mode) == SAFEPDF_MODE_HIGHLIGHT.rawValue
            && (cursor == SAFEPDF_CURSOR_IBEAM.rawValue || cursor == SAFEPDF_CURSOR_ARROW.rawValue)
        if canvas?.window != nil { (showsHighlighter ? Self.highlighterCursor : Self.nsCursor(cursor)).set() }
        if let l = link {
            if hoverLink.map({ $0.page != l.page || $0.index != l.index }) ?? true,
               let doc = document, let ls = store.links(l.page) {
                status(ls.describe(l.index, labels: doc.labels, pages: doc.pageCount))
            }
        }
        hoverLink = link
    }

    /// Whether the pointer shows the highlighter (the Highlight tool over a page; the self-test
    /// reads it).
    private(set) var showsHighlighter = false

    /// The highlighter cursor (task 11.6a): the SF Symbol `highlighter` drawn black with a white
    /// outline (legible on light and dark pages, as the system cursors), at 2x for Retina; the
    /// hot spot is the marker's tip at the lower left.
    static let highlighterCursor: NSCursor = {
        let side: CGFloat = 24
        let cfg = NSImage.SymbolConfiguration(pointSize: 17, weight: .medium)
        guard let sym = NSImage(systemSymbolName: "highlighter", accessibilityDescription: "Highlighter")?
            .withSymbolConfiguration(cfg) else { return .iBeam }
        let s = sym.size
        let origin = CGPoint(x: 2, y: 2)
        func tinted(_ c: NSColor) -> NSImage {
            NSImage(size: s, flipped: false) { r in
                sym.draw(in: r)
                c.set()
                r.fill(using: .sourceAtop)
                return true
            }
        }
        let black = tinted(.black), white = tinted(.white)
        let image = NSImage(size: NSSize(width: side, height: side), flipped: false) { _ in
            for dx in [-1.0, 0, 1] { for dy in [-1.0, 0, 1] where dx != 0 || dy != 0 {
                white.draw(at: CGPoint(x: origin.x + dx, y: origin.y + dy), from: .zero, operation: .sourceOver, fraction: 1)
            } }
            black.draw(at: origin, from: .zero, operation: .sourceOver, fraction: 1)
            return true
        }
        // NSCursor's hot spot is in flipped (top-left) coordinates. The marker's chisel tip sits
        // at about 13 % of the symbol's width and 77 % of its height from its top (measured on
        // the rendered symbol, above its baseline stroke).
        let top = side - origin.y - s.height
        return NSCursor(image: image, hotSpot: NSPoint(x: origin.x + 0.13 * s.width, y: top + 0.77 * s.height))
    }()

    /// The AppKit cursor of a safepdf_cursor.
    static func nsCursor(_ c: UInt32) -> NSCursor {
        switch c {
        case SAFEPDF_CURSOR_IBEAM.rawValue: return .iBeam
        case SAFEPDF_CURSOR_POINTING_HAND.rawValue: return .pointingHand
        case SAFEPDF_CURSOR_CROSSHAIR.rawValue: return .crosshair
        default: return .arrow
        }
    }

    // MARK: overlays

    /// An index arrived: the selection's bands (a drag that waited), the search's hits.
    private func indexArrived(_ page: Int) {
        if let s = selection, s.page == page, bands.isEmpty { setSelection(s) }
        find.indexArrived(page)
    }

    /// The visible area changed (scroll, layout): highlight-all asks for the visible pages'
    /// indexes.
    func visibleChanged() { find.visibleChanged() }

    /// Draws page `page`'s overlays above its image: the search hits, then the selection.
    private func drawOverlay(_ page: Int) {
        guard let c = canvas, let t = c.transform(ofPage: page) else { return }
        drawMarks?(page, t, c)
        find.draw(page, t, c)
        if let s = selection, s.page == page, !bands.isEmpty {
            let path = CGMutablePath()
            for b in bands { path.addRect(c.pixelAligned(t.rect(b))) }
            guard let cg = NSGraphicsContext.current?.cgContext else { return }
            cg.saveGState()
            cg.addPath(path)
            cg.setFillColor(Self.selectionColor.cgColor)
            cg.fillPath()
            cg.restoreGState()
        }
    }

    /// The selection's fill: the system accent colour at 35 % (light and dark; resolved for
    /// the appearance it is drawn in).
    static var selectionColor: NSColor { NSColor.controlAccentColor.withAlphaComponent(0.35) }
}
