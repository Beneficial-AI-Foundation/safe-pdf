// PageViewController.swift — the content item: an NSScrollView over the page canvas
// (tasks 11.3b, 11.3c1, 11.3c2). Plan.md §6 Phase 11; docs/macos-design.md §1 (zoom model: presets,
// quantised steps, zoom anchored at the pointer or the window centre — C2's View.reanchor;
// rotation) and §2 ("NSScrollView: native momentum, rubber-banding, responsive scrolling,
// overlay scrollers; live magnification during pinch (bitmap scales in the gesture, sharp
// re-render at gesture end)"; "the sharp image cross-fades over the scaled one").
//
// Every zoom or rotation change goes through `change(anchor:_:)`: it notes the page point under
// the anchor (the pointer, else the window centre), applies the change, lays the pages out again
// and scrolls so that View.reanchor's image of that point lies under the anchor again.
//
// Task 11.3c2 (the Tk viewer's navigation rules, Viewer.lean): the current page is the page the
// viewer went to as long as the view stays where the viewer put it (`ownTop`), else, in the
// vertical modes, the page under the window centre (Viewer.viewChanged) — so the last page is
// current after Last page even though it cannot scroll to the top. Page-at-a-time scrolling in
// the page scroll mode (View.wheelStep; keys past an edge turn the page), view modes and spreads,
// jumps recorded in the back/forward history (Links.History), the document's open settings on
// every open, and the status pill for notes and errors.

import AppKit
import QuartzCore
import SafePdfC

/// Centres the document view when it is narrower than the clip view.
final class CenteringClipView: NSClipView {
    override func constrainBoundsRect(_ proposedBounds: NSRect) -> NSRect {
        var r = super.constrainBoundsRect(proposedBounds)
        if let doc = documentView, r.width > doc.frame.width {
            r.origin.x = -((r.width - doc.frame.width) / 2).rounded(.down)
        }
        return r
    }
}

/// The page area's scroll view: records where a pinch happens, turns ⌘-scroll into zoom steps
/// at the pointer (the Tk viewer's Command-MouseWheel binding) and ignores smart magnify (a
/// two-finger double tap would leave an unquantised zoom).
final class PageScrollView: NSScrollView {
    /// The window location of the last magnify event (the pinch's anchor).
    private(set) var lastMagnifyLocation: NSPoint?
    /// Zoom in (true) or out at a window location.
    var onCommandScroll: ((Bool, NSPoint) -> Void)?
    /// Takes a wheel event without Command first (the page scroll mode's page-at-a-time rules);
    /// returns whether it handled it.
    var onWheel: ((NSEvent) -> Bool)?
    private var commandScrollAcc: CGFloat = 0

    override func magnify(with event: NSEvent) {
        lastMagnifyLocation = event.locationInWindow
        super.magnify(with: event)
    }

    override func smartMagnify(with event: NSEvent) {}

    override func scrollWheel(with event: NSEvent) {
        guard event.modifierFlags.contains(.command), let zoom = onCommandScroll else {
            if !event.modifierFlags.contains(.command), onWheel?(event) == true { return }
            super.scrollWheel(with: event)
            return
        }
        if event.phase == .began || event.phase == .mayBegin { commandScrollAcc = 0 }
        guard event.momentumPhase.isEmpty else { return } // no zoom steps from momentum
        let d = event.scrollingDeltaY
        if !event.hasPreciseScrollingDeltas {
            if d != 0 { zoom(d > 0, event.locationInWindow) } // one step per notch
            return
        }
        commandScrollAcc += d
        let threshold: CGFloat = 24
        if abs(commandScrollAcc) >= threshold {
            zoom(commandScrollAcc > 0, event.locationInWindow)
            commandScrollAcc = 0
        }
    }
}

/// Where `goTo` / `show(page:_:)` scroll (the Tk viewer's ScrollTo).
/// The view a reopen after Save keeps (task 11.3e2; 9.r8: the only open that carries the view
/// over): the view modes, the zoom choice, the user's rotation and the page.
struct KeptView {
    let modes: ViewModes
    let zoom: safepdf_zoom_choice
    let rotation: UInt32
    let page: Int
}

enum ScrollTarget {
    /// The page's top (View.topFor; the region's top in the page scroll mode).
    case top
    /// The page's bottom (View.bottomFor; the region's bottom in the page scroll mode).
    case bottom
    /// A destination's left and top in page units (Geom.toScreen; nil: the page's edge).
    case dest(left: safepdf_rat?, top: safepdf_rat?)
    /// Scroll fractions of the region (a history location).
    case frac(x: safepdf_rat, y: safepdf_rat)
    /// A fraction of the current page's height at the view's top (a new layout of the
    /// vertical modes keeps the view's place in the current page).
    case within(CGFloat)
    /// The current scroll position, as far as the new layout allows.
    case stay
}

/// Where a zoom or rotation change is anchored: a point of the document view (points) and its
/// position on screen relative to the clip view's bounds origin (points, unmagnified).
struct ViewAnchor {
    let doc: CGPoint
    let offset: CGPoint
}

final class PageViewController: NSViewController {
    let scrollView = PageScrollView()
    let canvas = PageCanvasView(frame: NSRect(x: 0, y: 0, width: 100, height: 100))
    private let emptyLabel = NSTextField(labelWithString: "Open a PDF with File > Open… (⌘O)")
    private var laidOutWidth: CGFloat = -1
    private var initialFrame: NSRect
    private var liveScrolling = false
    /// Called after the zoom, rotation or layout changed (the window updates its chrome).
    var onViewChange: (() -> Void)?
    /// Whether the last programmatic scroll was clamped to the document's edges (an anchored
    /// point then cannot stay exactly under its anchor; the self-test skips its check).
    private(set) var lastScrollClamped = false
    /// Cross-fades started (the self-test counts them).
    private(set) var crossFades = 0
    /// The view top (clip bounds origin y) where the viewer last put the view in the vertical
    /// modes (Viewer.ownTop): while the view stays there, the current page stays the page the
    /// viewer went to.
    private(set) var ownTop: CGFloat?
    /// The back/forward history (Links.History).
    let history = NavHistory()
    private var wheelX = WheelAxis()
    private var wheelY = WheelAxis()
    /// The transient status pill over the page area.
    let pill = StatusPill()
    /// Whether the current page's zoom was capped in the last layout (the pill says so once).
    private var wasCapped = false
    /// Non-zero while the viewer itself lays out and scrolls (a new layout moves the clip view
    /// on the way): the current-page rule waits until the view is where the viewer puts it.
    private var holdCurrent = 0
    /// The cross-fade's duration in seconds.
    static let crossFadeSeconds: CFTimeInterval = 0.18
    /// Selection, copy, find and links on the pages (task 11.3d1).
    let text = TextController()
    /// Marks: the tools, highlights and notes, free text and drawings, the bubble (task 11.3e1).
    let marks = MarksController()

    init(frame: NSRect = NSRect(x: 0, y: 0, width: 800, height: 900)) {
        initialFrame = frame
        super.init(nibName: nil, bundle: nil)
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    override func loadView() {
        let container = NSView(frame: initialFrame)
        scrollView.frame = container.bounds
        scrollView.autoresizingMask = [.width, .height]
        scrollView.contentView = CenteringClipView(frame: container.bounds)
        scrollView.hasVerticalScroller = true
        scrollView.hasHorizontalScroller = true
        scrollView.autohidesScrollers = true
        scrollView.scrollerStyle = .overlay
        // Semantic: light grey in light mode, dark in dark mode; the pages stay white.
        scrollView.backgroundColor = .underPageBackgroundColor
        scrollView.drawsBackground = true
        scrollView.documentView = canvas
        scrollView.contentView.postsBoundsChangedNotifications = true
        // Pinch: live magnification (the bitmap scales), committed to a quantised zoom at the
        // gesture's end. The range is set per layout so the result stays in the zoom range.
        scrollView.allowsMagnification = true
        // The cross-fade animates the clip view's layer (the visible area, not the whole
        // document view).
        scrollView.wantsLayer = true
        container.addSubview(scrollView)
        container.addSubview(pill)
        NSLayoutConstraint.activate([
            pill.centerXAnchor.constraint(equalTo: container.centerXAnchor),
            pill.bottomAnchor.constraint(equalTo: container.bottomAnchor, constant: -18),
            pill.widthAnchor.constraint(lessThanOrEqualTo: container.widthAnchor, constant: -48),
        ])

        emptyLabel.textColor = .secondaryLabelColor
        emptyLabel.font = .systemFont(ofSize: NSFont.systemFontSize + 2)
        emptyLabel.translatesAutoresizingMaskIntoConstraints = false
        container.addSubview(emptyLabel)
        NSLayoutConstraint.activate([
            emptyLabel.centerXAnchor.constraint(equalTo: container.centerXAnchor),
            emptyLabel.centerYAnchor.constraint(equalTo: container.centerYAnchor),
        ])
        view = container

        let nc = NotificationCenter.default
        nc.addObserver(self, selector: #selector(boundsChanged(_:)),
                       name: NSView.boundsDidChangeNotification, object: scrollView.contentView)
        nc.addObserver(self, selector: #selector(magnifyEnded(_:)),
                       name: NSScrollView.didEndLiveMagnifyNotification, object: scrollView)
        nc.addObserver(self, selector: #selector(liveScrollStarted(_:)),
                       name: NSScrollView.willStartLiveScrollNotification, object: scrollView)
        nc.addObserver(self, selector: #selector(liveScrollEnded(_:)),
                       name: NSScrollView.didEndLiveScrollNotification, object: scrollView)

        canvas.onSharpSwap = { [weak self] in self?.crossFade() }
        text.attach(self)
        marks.attach(self)
        canvas.onKeyScroll = { [weak self] dx, dy, pages in self?.keyScroll(dx: dx, dy: dy, pages: pages) }
        scrollView.onCommandScroll = { [weak self] zoomIn, loc in
            guard let self else { return }
            self.step(zoomIn: zoomIn, anchor: self.pointerAnchor(window: loc))
        }
        scrollView.onWheel = { [weak self] event in self?.pageModeWheel(event) ?? false }
        canvas.onRenderError = { [weak self] page, error in
            guard let self, let doc = self.canvas.document else { return }
            let text = PageText.of(labels: doc.labels, page: page, pages: doc.pageCount)
            self.pill.show("\(text): cannot render: \(error)")
        }
    }

    /// The page area's visible size in points (below the toolbar's inset), as the layout's
    /// canvas: the scroll view's frame less the insets and, with legacy (always shown) scrollers,
    /// the vertical scroller (a continuous layout scrolls vertically). It does not depend on
    /// whether scrollers are shown at the moment, so a fit zoom does not make the scroller it
    /// did not count appear (and the page overflow by its width).
    var canvasSize: CGSize {
        let frame = scrollView.frame.size
        let insets = scrollView.contentInsets
        var w = frame.width - insets.left - insets.right
        let h = frame.height - insets.top - insets.bottom
        if scrollView.scrollerStyle == .legacy, scrollView.hasVerticalScroller {
            w -= NSScroller.scrollerWidth(for: .regular, scrollerStyle: .legacy)
        }
        return CGSize(width: max(1, w), height: max(1, h))
    }

    /// Shows a document (nil: none). Every open starts afresh (task 9.r8, Viewer.openWith):
    /// continuous vertical scrolling, no spreads, left to right, Automatic Zoom, no rotation,
    /// page 1, an empty history — then the document's open settings apply (`/PageLayout`,
    /// `/Direction`, the open destination's page, zoom and position), and the pill lists what
    /// was not honoured.
    func show(_ doc: Document?, keep: KeptView? = nil) {
        holdCurrent += 1
        defer { holdCurrent -= 1 }
        _ = view
        emptyLabel.isHidden = doc != nil
        if scrollView.magnification != 1 { scrollView.magnification = 1 }
        history.clear()
        wheelX = WheelAxis()
        wheelY = WheelAxis()
        ownTop = nil
        wasCapped = false
        pill.fadeOut(animated: false)
        text.reset(doc)
        canvas.setDocument(doc, canvas: canvasSize)
        marks.reset(doc)
        var target = ScrollTarget.top
        var notes: [String] = []
        if let doc, let k = keep {
            // The reopen after Save (Viewer.afterWrite: openFile keepView, then goTo page): the
            // document's open settings are not applied again.
            canvas.modes = k.modes
            canvas.zoomChoice = k.zoom
            canvas.userRotation = k.rotation
            canvas.setCurrent(k.page)
            canvas.relayout(canvas: canvasSize)
            _ = doc
        } else if let doc {
            let s = doc.settings
            canvas.modes = s.modes
            canvas.zoomChoice = s.zoom
            if let p = s.destPage {
                canvas.setCurrent(p)
                target = .dest(left: s.left, top: s.top)
            }
            canvas.relayout(canvas: canvasSize)
            notes = s.notes + s.shellNotes
        }
        laidOutWidth = canvasSize.width
        updateMagnificationRange()
        apply(target)
        noteCap()
        onViewChange?()
        if !notes.isEmpty { pill.show(notes.joined(separator: "; ")) }
    }

    /// Re-lays the pages out for the current size (a window resize or a sidebar change): the
    /// vertical modes keep the view's place in the current page (Viewer.refresh), the page
    /// scroll mode keeps the scroll position as far as it can.
    func relayout() {
        holdCurrent += 1
        defer { holdCurrent -= 1 }
        commitMagnificationIfNeeded()
        var target = ScrollTarget.stay
        if canvas.modes.continuous, let r = canvas.rect(ofPage: canvas.currentPage), r.height > 0 {
            target = .within((visibleTop - r.minY) / r.height)
        }
        canvas.relayout(canvas: canvasSize)
        laidOutWidth = canvasSize.width
        updateMagnificationRange()
        apply(target)
        noteCap()
        onViewChange?()
    }

    /// What a reopen after Save keeps of the current view (nil: no document).
    var keptView: KeptView? {
        guard canvas.document != nil else { return nil }
        return KeptView(modes: canvas.modes, zoom: canvas.zoomChoice, rotation: canvas.userRotation,
                        page: canvas.currentPage)
    }

    /// The top of the visible area below the toolbar, in document-view points.
    var visibleTop: CGFloat { scrollView.contentView.bounds.origin.y + scrollView.contentInsets.top }

    /// The window moved to a screen with another backing scale (Retina ↔ non-Retina): lay out
    /// and render again for the new pixels, keeping the window centre's page point in place.
    func backingChanged() {
        guard canvas.document != nil, canvas.backing != canvas.laidOutBacking else { return }
        change(anchor: centreAnchor()) {}
    }

    /// Shows `page` from its top, also when it is the current page (Next page's path; the
    /// self-test).
    func scroll(toPage page: Int) { show(page: page, .top) }

    // MARK: navigation (task 11.3c2, Viewer.goTo / showAt / jumpTo / histMove)

    /// Moves to page `page` (clamped) scrolled as `target` — nothing when it is the current
    /// page (Viewer.goTo: Next, Previous, First, Last, the wheel's and keys' page turns).
    func goTo(_ page: Int, _ target: ScrollTarget = .top) {
        guard let doc = canvas.document, doc.pageCount > 0 else { return }
        let p = min(max(0, page), doc.pageCount - 1)
        guard p != canvas.currentPage else { return }
        show(page: p, target)
    }

    /// Shows page `page` (clamped) scrolled as `target`, also when it is the current page
    /// (Viewer.showAt). In the page scroll mode a page of another spread lays that spread out.
    func show(page: Int, _ target: ScrollTarget) {
        guard let doc = canvas.document, doc.pageCount > 0 else { return }
        holdCurrent += 1
        defer { holdCurrent -= 1 }
        commitMagnificationIfNeeded()
        let p = min(max(0, page), doc.pageCount - 1)
        wheelX = WheelAxis()
        wheelY = WheelAxis()
        canvas.setCurrent(p)
        if !canvas.isLaidOut(p) {
            canvas.relayout(canvas: canvasSize)
            laidOutWidth = canvasSize.width
            updateMagnificationRange()
            noteCap()
        }
        apply(target)
        onViewChange?()
    }

    /// Where the view is now (Links.Loc: page and the scroll fractions of the view's top-left).
    func currentLoc() -> NavLoc {
        let b = canvas.laidOutBacking
        let ins = scrollView.contentInsets
        let o = scrollView.contentView.bounds.origin
        let size = canvas.frame.size
        func frac(_ v: CGFloat, _ total: CGFloat) -> safepdf_rat {
            let den = max(1, (total * b).rounded())
            let num = min(max(0, (v * b).rounded()), den)
            guard den.isFinite, den < 9e15 else { return safepdf_rat(num: 0, den: 1) }
            return safepdf_rat(num: Int64(num), den: Int64(den))
        }
        return NavLoc(page: canvas.currentPage, x: frac(o.x + ins.left, size.width),
                      y: frac(o.y + ins.top, size.height))
    }

    /// A jump (a link, an outline item, the page field, Go to page): the current place goes on
    /// the history, then the page shows at the destination (Viewer.jumpTo). Returns false when
    /// the page is not in the document (the pill says so).
    @discardableResult
    func jump(to page: Int, left: safepdf_rat? = nil, top: safepdf_rat? = nil) -> Bool {
        guard let doc = canvas.document else { return false }
        guard page < doc.pageCount else {
            pill.show("destination page \(page + 1) is not in the document")
            return false
        }
        history.push(currentLoc())
        show(page: page, .dest(left: left, top: top))
        return true
    }

    /// Return in the page field (Viewer.pageEntry, Toolbar.pageEntry): a label or number jumps
    /// there (recorded in the history); an invalid entry leaves the view and the pill says why.
    func pageEntry(_ text: String) {
        guard let doc = canvas.document, doc.pageCount > 0 else { return }
        let cur = canvas.currentPage
        if let p = PageText.entry(labels: doc.labels, pages: doc.pageCount, current: cur, input: text) {
            if p != cur { jump(to: p) }
        } else {
            pill.show("no page \"\(text)\" (enter a page number or label)")
        }
    }

    /// Back or Forward in the history (Viewer.histMove); the pill says when there is nothing.
    func historyMove(back: Bool) {
        guard canvas.document != nil else { return }
        if let l = history.go(back: back, from: currentLoc()) {
            show(page: l.page, .frac(x: l.x, y: l.y))
        } else {
            pill.show(back ? "nothing to go back to" : "nothing to go forward to")
        }
    }

    /// Switches the view modes (View menu, the view-mode drop-down; Viewer.setViewMode): keeps
    /// the current page, shown from its top. Nothing when they do not change.
    func setModes(_ m: ViewModes) {
        holdCurrent += 1
        defer { holdCurrent -= 1 }
        guard canvas.document != nil, m != canvas.modes else { return }
        commitMagnificationIfNeeded()
        canvas.modes = m
        wheelX = WheelAxis()
        wheelY = WheelAxis()
        canvas.relayout(canvas: canvasSize)
        laidOutWidth = canvasSize.width
        updateMagnificationRange()
        apply(.top)
        noteCap()
        onViewChange?()
    }

    /// The spread information of the current page in the current spread mode.
    var spreadInfo: safepdf_spread_info? {
        guard let doc = canvas.document else { return nil }
        return Spreads.info(canvas.modes.spread, pages: doc.pageCount, page: canvas.currentPage)
    }

    /// Scrolls the current page as `target` says (Viewer.applyScroll); in the vertical modes
    /// the resulting view top is the viewer's own (`ownTop`).
    private func apply(_ target: ScrollTarget) {
        let clip = scrollView.contentView
        let ins = scrollView.contentInsets
        var origin = clip.bounds.origin
        let p = canvas.currentPage
        let vh = canvasSize.height
        let b = canvas.laidOutBacking
        let continuous = canvas.modes.continuous
        switch target {
        case .top:
            if continuous, let t = canvas.scrollTop(forPage: p, viewHeight: vh) { origin.y = t - ins.top }
            else { origin.y = -ins.top }
        case .bottom:
            if continuous, let t = canvas.scrollBottom(forPage: p, viewHeight: vh) { origin.y = t - ins.top }
            else { origin.y = canvas.frame.height }
        case .dest(let left, let top):
            if let doc = canvas.document, p < doc.geometry.count, let pl = canvas.place(ofPage: p) {
                let box = doc.geometry[p].box
                if let q = ZoomModel.toScreen(z: pl.zoom, rot: pl.rotation, box: box,
                                              x: left ?? box.llx, y: top ?? box.ury) {
                    origin.x = (pl.pixels.minX + q.x) / b - ins.left
                    origin.y = (pl.pixels.minY + q.y) / b - ins.top
                }
            }
        case .frac(let x, let y):
            origin.x = CGFloat(ZoomModel.double(x)) * canvas.frame.width - ins.left
            origin.y = CGFloat(ZoomModel.double(y)) * canvas.frame.height - ins.top
        case .within(let f):
            if let r = canvas.rect(ofPage: p) { origin.y = r.minY + f * r.height - ins.top }
        case .stay:
            break
        }
        scrollClip(to: origin, own: true)
    }

    /// Scrolls the clip view to `origin` (constrained to the document). `own`: the viewer put
    /// the view there (the current page stays), else the user did.
    private func scrollClip(to origin: CGPoint, own: Bool = false) {
        let clip = scrollView.contentView
        let r = clip.constrainBoundsRect(NSRect(origin: origin, size: clip.bounds.size))
        lastScrollClamped = abs(r.origin.x - origin.x) > 0.5 || abs(r.origin.y - origin.y) > 0.5
        if own && canvas.modes.continuous { ownTop = r.origin.y }
        clip.scroll(to: r.origin)
        scrollView.reflectScrolledClipView(clip)
        refresh()
    }

    /// The current-page rule (Viewer.viewChanged): in the vertical modes, once the view left
    /// the place the viewer put it, the current page is the page under the window centre.
    private func updateCurrentPage() {
        guard canvas.document != nil, canvas.modes.continuous, holdCurrent == 0 else { return }
        let y = scrollView.contentView.bounds.origin.y
        if let own = ownTop, abs(own - y) < 0.5 { return }
        ownTop = nil
        if let p = canvas.page(at: centreAnchor().doc), p != canvas.currentPage { canvas.setCurrent(p) }
    }

    /// Requests the renders the visible area needs (after the current-page rule).
    func refresh() {
        updateCurrentPage()
        canvas.updateRenders(visible: canvas.visibleRect)
        text.visibleChanged()
    }

    /// Scrolls so that `r` (document-view points) is visible: centred on an axis where it is not
    /// (Viewer.scrollToHit); the user's scroll (the current-page rule applies after it).
    func reveal(_ r: NSRect) {
        commitMagnificationIfNeeded()
        let ins = scrollView.contentInsets
        var origin = scrollView.contentView.bounds.origin
        let size = canvasSize
        let vx = origin.x + ins.left, vy = origin.y + ins.top
        if r.minX < vx || vx + size.width < r.maxX { origin.x = r.midX - size.width / 2 - ins.left }
        if r.minY < vy || vy + size.height < r.maxY { origin.y = r.midY - size.height / 2 - ins.top }
        scrollClip(to: origin)
    }

    /// The zoom percentage shown for the current page (Viewer.showStatus): the chosen
    /// percentage, or the zoom the page came out at (a fit mode, or a capped page).
    var shownPct: UInt32? {
        let p = canvas.currentPage
        if let pl = canvas.place(ofPage: p) {
            let c = canvas.zoomChoice
            if c.kind == SAFEPDF_ZOOM_PERCENT.rawValue && !pl.capped { return c.pct }
            return ZoomModel.zoomPct(pl.zoom, scaling: canvas.scaling)
        }
        return canvas.shownPct
    }

    /// The status note of a capped page (Viewer.showStatus), nil when the page is not capped.
    var capNote: String? {
        guard let pl = canvas.place(ofPage: canvas.currentPage), pl.capped, let k = ZoomModel.constants
        else { return nil }
        return "zoom limited to \(k.page_pixels / 1_048_576) Mpx per page"
    }

    /// Shows the cap note when the current page's zoom became capped.
    private func noteCap() {
        let note = capNote
        if let note, !wasCapped { pill.show(note) }
        wasCapped = note != nil
    }

    // MARK: page-at-a-time scrolling (task 11.3c2, Viewer.wheel)

    /// A wheel event in the page scroll mode: View.wheelStep per axis (the vertical one may
    /// turn the page after a push past the edge). Not handled in the vertical modes, where
    /// the native scroll view scrolls (momentum, rubber-banding).
    private func pageModeWheel(_ event: NSEvent) -> Bool {
        guard let doc = canvas.document, !canvas.modes.continuous, canvas.layout != nil else { return false }
        commitMagnificationIfNeeded()
        let b = canvas.laidOutBacking
        let now = UInt64(max(0, event.timestamp * 1000))
        let clip = scrollView.contentView
        let ins = scrollView.contentInsets
        let size = canvasSize
        for vertical in [false, true] {
            let raw = vertical ? event.scrollingDeltaY : event.scrollingDeltaX
            guard raw != 0, raw.isFinite else { continue }
            let kind: safepdf_wheel_kind
            let delta: Int64
            if event.hasPreciseScrollingDeltas {
                kind = SAFEPDF_WHEEL_PIXEL
                delta = Int64(max(-1e6, min(1e6, (raw * b).rounded())))
            } else {
                kind = SAFEPDF_WHEEL_LINE
                let r = max(-1e3, min(1e3, raw.rounded()))
                delta = r == 0 ? (raw > 0 ? 1 : -1) : Int64(r)
            }
            if delta == 0 { continue }
            let o = clip.bounds.origin
            let top = UInt64(max(0, ((vertical ? o.y + ins.top : o.x + ins.left) * b).rounded()))
            let view = UInt64(max(1, ((vertical ? size.height : size.width) * b).rounded()))
            let region = UInt64(max(1, ((vertical ? canvas.frame.height : canvas.frame.width) * b).rounded()))
            var axis = vertical ? wheelY : wheelX
            let (act, pos) = axis.step(kind: kind, delta: delta, cross: vertical, nowMs: now,
                                       top: top, view: view, region: max(region, view))
            switch act {
            case SAFEPDF_WHEEL_SCROLL:
                var origin = clip.bounds.origin
                if vertical { origin.y = CGFloat(pos) / b - ins.top } else { origin.x = CGFloat(pos) / b - ins.left }
                scrollClip(to: origin)
            case SAFEPDF_WHEEL_NEXT, SAFEPDF_WHEEL_PREV:
                let next = act == SAFEPDF_WHEEL_NEXT
                if let info = Spreads.info(canvas.modes.spread, pages: doc.pageCount, page: canvas.currentPage) {
                    let q = next ? info.next_page : info.prev_page
                    if q != canvas.currentPage {
                        goTo(q, next ? .top : .bottom)
                    } else {
                        axis.dropOwed()
                    }
                }
            default:
                break
            }
            // goTo resets the wheels; the state after the turn (the push owed) is kept.
            if vertical { wheelY = axis } else { wheelX = axis }
        }
        return true
    }

    // MARK: anchors (C2)

    /// The window centre: the middle of the visible area below the toolbar.
    func centreAnchor() -> ViewAnchor {
        let clip = scrollView.contentView
        let m = scrollView.magnification
        let ins = scrollView.contentInsets
        let size = canvasSize
        let offset = CGPoint(x: ins.left + size.width / 2, y: ins.top + size.height / 2)
        let doc = CGPoint(x: clip.bounds.origin.x + offset.x / m, y: clip.bounds.origin.y + offset.y / m)
        return ViewAnchor(doc: doc, offset: offset)
    }

    /// The pointer at window location `loc`.
    func pointerAnchor(window loc: NSPoint) -> ViewAnchor {
        let doc = canvas.convert(loc, from: nil)
        let clip = scrollView.contentView
        let m = scrollView.magnification
        return ViewAnchor(doc: doc, offset: CGPoint(x: (doc.x - clip.bounds.origin.x) * m,
                                                    y: (doc.y - clip.bounds.origin.y) * m))
    }

    /// Applies a zoom or rotation `change` anchored at `anchor`: the page point under it
    /// (View.pageAt, in the current view) is mapped into the new view by View.reanchor and
    /// scrolled back under the anchor. Ends any live magnification (back to 1).
    func change(anchor: ViewAnchor, _ change: () -> Void) {
        holdCurrent += 1
        defer { holdCurrent -= 1 }
        guard canvas.document != nil else { return }
        let before = canvas.anchor(at: anchor.doc)
        change()
        if scrollView.magnification != 1 { scrollView.magnification = 1 }
        canvas.relayout(canvas: canvasSize)
        laidOutWidth = canvasSize.width
        updateMagnificationRange()
        let target = before.flatMap { canvas.point(of: $0) } ?? anchor.doc
        scrollClip(to: CGPoint(x: target.x - anchor.offset.x, y: target.y - anchor.offset.y), own: true)
        noteCap()
        onViewChange?()
    }

    // MARK: zoom and rotation

    /// Sets the zoom choice (a preset, Actual Size, Page Fit, Page Width, Automatic Zoom),
    /// anchored at the window centre unless an anchor is given.
    func setZoom(_ c: safepdf_zoom_choice, anchor: ViewAnchor? = nil) {
        change(anchor: anchor ?? centreAnchor()) { canvas.zoomChoice = c }
    }

    /// Zoom In / Zoom Out (View.stepInZ / stepOutZ on the effective, quantised zoom); nothing at
    /// the end of the range. Returns whether the zoom changed.
    @discardableResult
    func step(zoomIn: Bool, anchor: ViewAnchor? = nil) -> Bool {
        guard canvas.document != nil, let base = canvas.baseZoom else { return false }
        let s = canvas.scaling
        let cur = ZoomModel.current(canvas.zoomChoice, base: base, scaling: s)
        guard let pct = ZoomModel.step(in: zoomIn, from: cur, scaling: s) else { return false }
        setZoom(ZoomModel.percent(pct), anchor: anchor)
        return true
    }

    /// Rotates the view a quarter turn (View.rotCw / rotCcw), keeping the window centre's page
    /// point at the centre.
    func rotate(clockwise: Bool) {
        change(anchor: centreAnchor()) {
            canvas.userRotation = ZoomModel.rotate(canvas.userRotation, clockwise: clockwise)
        }
    }

    /// The pinch's range: magnifications that keep the zoom within [minPct, maxPct].
    private func updateMagnificationRange() {
        guard let base = canvas.baseZoom, let k = ZoomModel.constants,
              let lo = ZoomModel.pctZoom(k.min_pct, scaling: canvas.scaling),
              let hi = ZoomModel.pctZoom(k.max_pct, scaling: canvas.scaling) else { return }
        let z = ZoomModel.double(base)
        guard z > 0 else { return }
        scrollView.minMagnification = min(1, ZoomModel.double(lo) / z)
        scrollView.maxMagnification = max(1, ZoomModel.double(hi) / z)
    }

    /// The end of a pinch: the magnified zoom becomes a quantised percentage (View.quant,
    /// View.zoomPct), the pages are laid out and rendered sharp at it, and the point under the
    /// pinch stays in place. Until the sharp renders come the canvas draws the old images scaled;
    /// each swap cross-fades.
    @objc private func magnifyEnded(_ note: Notification) {
        let loc = scrollView.lastMagnifyLocation
        commitMagnification(anchor: loc.map { pointerAnchor(window: $0) } ?? centreAnchor())
    }

    /// Turns the scroll view's magnification into the zoom choice (see `magnifyEnded`).
    func commitMagnification(anchor: ViewAnchor) {
        let m = scrollView.magnification
        guard canvas.document != nil, abs(m - 1) > 0.001, let base = canvas.baseZoom,
              let pct = ZoomModel.pinchPct(base: base, magnification: m, scaling: canvas.scaling) else {
            if scrollView.magnification != 1 { scrollView.magnification = 1 }
            return
        }
        setZoom(ZoomModel.percent(pct), anchor: anchor)
    }

    private func commitMagnificationIfNeeded() {
        if scrollView.magnification != 1 { commitMagnification(anchor: centreAnchor()) }
    }

    // MARK: cross-fade

    /// Fades the visible area from what it shows now (a scaled image) to what it shows after
    /// the coming redraw (the sharp render): a short CATransition on the clip view's layer.
    /// Skipped while the user scrolls (a fade would smear the motion) and while one runs.
    private func crossFade() {
        guard !liveScrolling, let layer = scrollView.contentView.layer else { return }
        let key = "org.safe-pdf.sharp"
        if layer.animation(forKey: key) != nil { return }
        let t = CATransition()
        t.type = .fade
        t.duration = Self.crossFadeSeconds
        t.timingFunction = CAMediaTimingFunction(name: .easeOut)
        layer.add(t, forKey: key)
        crossFades += 1
    }

    // MARK: key scrolling

    /// Scrolls by lines (arrows) or by a view less a little overlap (space, shift-space), as
    /// the Tk canvas's units and pages; past the end of the region the next page (spread) shows
    /// from its top, before its start the previous one from its bottom (Tk `::safepdf::step`).
    private func keyScroll(dx: Int, dy: Int, pages: Bool) {
        let clip = scrollView.contentView
        if let doc = canvas.document, let info = spreadInfo {
            let o = clip.bounds.origin
            let ins = scrollView.contentInsets
            let maxY = canvas.frame.height - clip.bounds.height
            let maxX = canvas.frame.width - clip.bounds.width + ins.left
            let atEnd = dy > 0 ? o.y >= maxY - 0.5 : (dx > 0 ? o.x >= maxX - 0.5 : false)
            let atStart = dy < 0 ? o.y <= -ins.top + 0.5 : (dx < 0 ? o.x <= -ins.left + 0.5 : false)
            if atEnd && doc.pageCount > 0 {
                goTo(info.next_page, .top)
                return
            }
            if atStart {
                goTo(info.prev_page, dy < 0 ? .bottom : .top)
                return
            }
        }
        let line: CGFloat = 40
        let size = canvasSize
        let stepX = pages ? max(line, size.width - line) : line
        let stepY = pages ? max(line, size.height - line) : line
        var origin = clip.bounds.origin
        origin.x += CGFloat(dx) * stepX
        origin.y += CGFloat(dy) * stepY
        scrollClip(to: origin)
    }

    // MARK: notifications

    @objc private func boundsChanged(_ note: Notification) {
        refresh()
    }

    @objc private func liveScrollStarted(_ note: Notification) { liveScrolling = true }

    @objc private func liveScrollEnded(_ note: Notification) { liveScrolling = false }

    override func viewDidLayout() {
        super.viewDidLayout()
        if !view.inLiveResize, abs(canvasSize.width - laidOutWidth) >= 1, canvas.document != nil {
            // Coalesced: a sidebar animation changes the width on every frame.
            NSObject.cancelPreviousPerformRequests(withTarget: self, selector: #selector(relayoutLater), object: nil)
            perform(#selector(relayoutLater), with: nil, afterDelay: 0.15)
        }
    }

    @objc private func relayoutLater() {
        if canvas.document != nil, abs(canvasSize.width - laidOutWidth) >= 1 { relayout() }
    }

    /// The end of a live window resize (the window controller calls this).
    func liveResizeEnded() {
        if canvas.document != nil { relayout() }
    }
}
