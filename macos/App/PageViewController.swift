// PageViewController.swift — the content item: an NSScrollView over the page canvas
// (tasks 11.3b, 11.3c1). Plan.md §6 Phase 11; docs/macos-design.md §1 (zoom model: presets,
// quantised steps, zoom anchored at the pointer or the window centre — C2's View.reanchor;
// rotation) and §2 ("NSScrollView: native momentum, rubber-banding, responsive scrolling,
// overlay scrollers; live magnification during pinch (bitmap scales in the gesture, sharp
// re-render at gesture end)"; "the sharp image cross-fades over the scaled one").
//
// Every zoom or rotation change goes through `change(anchor:_:)`: it notes the page point under
// the anchor (the pointer, else the window centre), applies the change, lays the pages out again
// and scrolls so that View.reanchor's image of that point lies under the anchor again.

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
    private var commandScrollAcc: CGFloat = 0

    override func magnify(with event: NSEvent) {
        lastMagnifyLocation = event.locationInWindow
        super.magnify(with: event)
    }

    override func smartMagnify(with event: NSEvent) {}

    override func scrollWheel(with event: NSEvent) {
        guard event.modifierFlags.contains(.command), let zoom = onCommandScroll else {
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
    /// The cross-fade's duration in seconds.
    static let crossFadeSeconds: CFTimeInterval = 0.18

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
        canvas.onKeyScroll = { [weak self] dx, dy, pages in self?.keyScroll(dx: dx, dy: dy, pages: pages) }
        scrollView.onCommandScroll = { [weak self] zoomIn, loc in
            guard let self else { return }
            self.step(zoomIn: zoomIn, anchor: self.pointerAnchor(window: loc))
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

    /// Shows a document (nil: none), from its first page, at Automatic Zoom.
    func show(_ doc: Document?) {
        _ = view
        emptyLabel.isHidden = doc != nil
        if scrollView.magnification != 1 { scrollView.magnification = 1 }
        canvas.setDocument(doc, canvas: canvasSize)
        laidOutWidth = canvasSize.width
        updateMagnificationRange()
        scroll(toPage: 0)
        refresh()
        onViewChange?()
    }

    /// Re-lays the pages out for the current size, keeping the current page at the top (a
    /// window resize or a sidebar change).
    func relayout() {
        commitMagnificationIfNeeded()
        let page = canvas.currentPage
        canvas.relayout(canvas: canvasSize)
        laidOutWidth = canvasSize.width
        updateMagnificationRange()
        scroll(toPage: page)
        refresh()
        onViewChange?()
    }

    /// The window moved to a screen with another backing scale (Retina ↔ non-Retina): lay out
    /// and render again for the new pixels, keeping the window centre's page point in place.
    func backingChanged() {
        guard canvas.document != nil, canvas.backing != canvas.laidOutBacking else { return }
        change(anchor: centreAnchor()) {}
    }

    /// Scrolls so that `page` shows from its top.
    func scroll(toPage page: Int) {
        let clip = scrollView.contentView
        guard let top = canvas.scrollTop(forPage: page, viewHeight: canvasSize.height) else { return }
        var origin = clip.bounds.origin
        origin.y = top - scrollView.contentInsets.top
        scrollClip(to: origin)
    }

    private func scrollClip(to origin: CGPoint) {
        let clip = scrollView.contentView
        let r = clip.constrainBoundsRect(NSRect(origin: origin, size: clip.bounds.size))
        lastScrollClamped = abs(r.origin.x - origin.x) > 0.5 || abs(r.origin.y - origin.y) > 0.5
        clip.scroll(to: r.origin)
        scrollView.reflectScrolledClipView(clip)
        refresh()
    }

    /// Requests the renders the visible area needs.
    func refresh() {
        canvas.updateRenders(visible: canvas.visibleRect)
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
        guard canvas.document != nil else { return }
        let before = canvas.anchor(at: anchor.doc)
        change()
        if scrollView.magnification != 1 { scrollView.magnification = 1 }
        canvas.relayout(canvas: canvasSize)
        laidOutWidth = canvasSize.width
        updateMagnificationRange()
        let target = before.flatMap { canvas.point(of: $0) } ?? anchor.doc
        scrollClip(to: CGPoint(x: target.x - anchor.offset.x, y: target.y - anchor.offset.y))
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
    /// the Tk canvas's units and pages.
    private func keyScroll(dx: Int, dy: Int, pages: Bool) {
        let clip = scrollView.contentView
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
