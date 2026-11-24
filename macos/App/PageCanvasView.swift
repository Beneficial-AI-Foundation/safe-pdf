// PageCanvasView.swift — the pages, laid out by safepdf_view_layout and drawn from renders
// (task 11.3b). Plan.md §6 Phase 11; docs/macos-design.md §2 (NSScrollView page area, dark
// canvas around paper-white pages) and §3 decision 4 (renders through the worker, callbacks on
// the main queue).
//
// Minimal on purpose: continuous vertical scrolling at Automatic Zoom. The zoom model, view
// modes, rotation, pinch and the cross-fade are task 11.3c.

import AppKit
import SafePdfC

/// A `safepdf_layout`, freed when the holder goes away.
final class LayoutHolder {
    var raw: safepdf_layout

    init(_ raw: safepdf_layout) { self.raw = raw }

    deinit { safepdf_free_layout(&raw) }
}

/// A laid-out page: rectangle in scroll-region pixels and the render zoom.
struct PagePlace {
    let page: Int
    let pixels: CGRect
    let key: ZoomKey?       // nil: the zoom does not fit the render call (not rendered)
    let capped: Bool
    let cropped: Bool
}

final class PageCanvasView: NSView {
    private(set) var document: Document?
    /// Backing pixels per point to use instead of the window's (the self-test, off screen).
    var scaleOverride: CGFloat?
    private(set) var layout: LayoutHolder?
    private(set) var places: [PagePlace] = []
    private var placeOf: [Int: Int] = [:]
    private var cache: [Int: (key: ZoomKey, image: CGImage)] = [:]
    private var inflight: [Int: (key: ZoomKey, id: safepdf_request_id)] = [:]
    /// The last render error per page (shown by 11.3c's status pill; logged for now).
    private(set) var errors: [Int: String] = [:]
    private(set) var currentPage = 0
    /// Called for every finished render (the self-test's timings).
    var onRender: ((RenderResult) -> Void)?
    /// Called when the page at the top of the view changes.
    var onCurrentPageChange: ((Int) -> Void)?
    /// Called when a layout cannot be computed (the window shows it as a sheet).
    var onError: ((String) -> Void)?

    override var isFlipped: Bool { true }
    override var isOpaque: Bool { false }

    /// Backing pixels per point.
    var backing: CGFloat {
        scaleOverride ?? window?.backingScaleFactor ?? NSScreen.main?.backingScaleFactor ?? 1
    }

    /// Requests in flight (the self-test waits for zero).
    var pendingCount: Int { inflight.count }

    /// Shows `doc` (nil: none); cancels the previous document's requests.
    func setDocument(_ doc: Document?, canvas: CGSize) {
        if let old = document {
            for (_, r) in inflight { safepdf_doc_cancel(old.handle, r.id) }
        }
        inflight.removeAll()
        cache.removeAll()
        errors.removeAll()
        document = doc
        currentPage = 0
        relayout(canvas: canvas)
    }

    /// Lays the pages out for a canvas of `canvas` points (the clip view's size).
    func relayout(canvas: CGSize) {
        guard let doc = document, doc.pageCount > 0 else {
            layout = nil
            places = []
            placeOf = [:]
            setFrameSize(canvas)
            needsDisplay = true
            return
        }
        let b = backing
        var geoms = doc.geometry()
        var params = safepdf_layout_params(
            scroll: SAFEPDF_SCROLL_VERTICAL.rawValue, spread: SAFEPDF_SPREAD_NONE.rawValue,
            user_rotation: 0, zoom: safepdf_zoom_choice(kind: SAFEPDF_ZOOM_AUTO.rawValue, pct: 0),
            scaling: Core.rat(Double(b)),
            canvas_w: UInt32(clamping: Int((canvas.width * b).rounded(.down))),
            canvas_h: UInt32(clamping: Int((canvas.height * b).rounded(.down))),
            page: currentPage, rtl: false)
        var out = safepdf_layout()
        guard safepdf_view_layout(&geoms, geoms.count, &params, &out) == 0 else {
            onError?("The pages could not be laid out (safepdf_view_layout failed).")
            return
        }
        let holder = LayoutHolder(out)
        var ps: [PagePlace] = []
        var index: [Int: Int] = [:]
        if let raw = holder.raw.places {
            for i in 0..<holder.raw.count {
                let p = raw[i]
                var key: ZoomKey? = nil
                if p.zoom.num > 0, p.zoom.den > 0, let n = UInt32(exactly: p.zoom.num),
                   let d = UInt32(exactly: p.zoom.den) {
                    key = ZoomKey(num: n, den: d, rotation: (p.rotation / 90) % 4)
                }
                index[p.page] = ps.count
                ps.append(PagePlace(page: p.page,
                                    pixels: CGRect(x: Double(p.x), y: Double(p.y), width: Double(p.w),
                                                   height: Double(p.h)),
                                    key: key, capped: p.capped, cropped: p.cropped))
            }
        }
        layout = holder
        places = ps
        placeOf = index
        setFrameSize(CGSize(width: max(canvas.width, CGFloat(holder.raw.region_w) / b),
                            height: max(canvas.height, CGFloat(holder.raw.region_h) / b)))
        needsDisplay = true
    }

    /// A page's rectangle in view points.
    func rect(ofPage page: Int) -> NSRect? {
        guard let i = placeOf[page] else { return nil }
        let b = backing
        let p = places[i].pixels
        return NSRect(x: p.minX / b, y: p.minY / b, width: p.width / b, height: p.height / b)
    }

    /// The scroll position (points, top of the clip view) that shows `page` from its top
    /// (View.topFor through safepdf_view_page_at).
    func scrollTop(forPage page: Int, viewHeight: CGFloat) -> CGFloat? {
        guard let holder = layout, let i = placeOf[page] else { return nil }
        let b = backing
        let p = places[i].pixels
        var hit = safepdf_page_hit()
        guard safepdf_view_page_at(&holder.raw, UInt64(p.midX), UInt64(p.minY),
                                   UInt64(max(0, viewHeight * b)), &hit) == 1 else { return nil }
        return CGFloat(hit.top) / b
    }

    /// Requests renders for the pages meeting `visible` (plus one each side, View.wantedPages),
    /// cancels requests for pages no longer wanted, drops far-away images, and updates the
    /// current page.
    func updateRenders(visible: NSRect) {
        guard let doc = document, let holder = layout else { return }
        let b = backing
        let top = UInt64(max(0, visible.minY * b))
        let bottom = UInt64(max(0, visible.maxY * b))
        var band = safepdf_page_band()
        guard safepdf_view_pages_in_band(&holder.raw, top, bottom, &band) == 0 else { return }
        var visiblePages: [Int] = []
        var wanted: [Int] = []
        if let v = band.visible { for i in 0..<band.visible_count { visiblePages.append(v[i]) } }
        if let w = band.wanted { for i in 0..<band.wanted_count { wanted.append(w[i]) } }
        safepdf_free_page_band(&band)

        var hit = safepdf_page_hit()
        let probe = top + (bottom - min(top, bottom)) / 3
        if safepdf_view_page_at(&holder.raw, UInt64(max(0, visible.midX * b)), probe,
                                bottom - min(top, bottom), &hit) == 1, hit.page != currentPage {
            currentPage = hit.page
            onCurrentPageChange?(hit.page)
        }

        let wantedSet = Set(wanted)
        for (page, r) in inflight where !wantedSet.contains(page) {
            safepdf_doc_cancel(doc.handle, r.id)
            inflight[page] = nil
        }
        for page in wanted {
            let prio = page == visiblePages.first ? Int32(SAFEPDF_PRIO_CURRENT) : Int32(SAFEPDF_PRIO_VISIBLE)
            request(page, doc: doc, priority: prio)
        }
        if let lo = wanted.min(), let hi = wanted.max() {
            for page in cache.keys where page < lo - 2 || page > hi + 2 { cache[page] = nil }
        }
    }

    private func request(_ page: Int, doc: Document, priority: Int32) {
        guard let i = placeOf[page], let key = places[i].key else { return }
        if cache[page]?.key == key { return }
        if let r = inflight[page] {
            if r.key == key { return }
            safepdf_doc_cancel(doc.handle, r.id)
            inflight[page] = nil
        }
        let id = Rendering.submit(doc, page: page, key: key, priority: priority) { [weak self] res in
            self?.renderDone(res)
        }
        if id != 0 { inflight[page] = (key, id) }
    }

    private func renderDone(_ res: RenderResult) {
        if inflight[res.page]?.id == res.id { inflight[res.page] = nil }
        if let image = res.image, let i = placeOf[res.page] {
            // Keep it when it is for the current zoom, or nothing better is there yet.
            if places[i].key == res.key || cache[res.page] == nil {
                cache[res.page] = (res.key, image)
                errors[res.page] = nil
                if let r = rect(ofPage: res.page) { setNeedsDisplay(r) }
            }
        } else if let e = res.error {
            errors[res.page] = e
            NSLog("SafePDF: page %d: %@", res.page + 1, e)
        }
        onRender?(res)
    }

    override func draw(_ dirtyRect: NSRect) {
        guard let cg = NSGraphicsContext.current?.cgContext else { return }
        cg.interpolationQuality = .high
        let b = backing
        for place in places {
            guard let r = rect(ofPage: place.page), r.intersects(dirtyRect) else { continue }
            // The paper stays white in dark mode (docs/macos-design.md §2).
            NSColor.white.setFill()
            r.fill()
            if let entry = cache[place.page] {
                var target = r
                if entry.key == place.key {
                    // At the current zoom the image is drawn pixel for pixel (a cropped page's
                    // image is smaller than its place).
                    target.size = CGSize(width: CGFloat(entry.image.width) / b,
                                         height: CGFloat(entry.image.height) / b)
                }
                cg.saveGState()
                cg.clip(to: r)
                cg.translateBy(x: target.minX, y: target.maxY)
                cg.scaleBy(x: 1, y: -1)
                cg.draw(entry.image, in: CGRect(origin: .zero, size: target.size))
                cg.restoreGState()
            }
            NSColor.separatorColor.setStroke()
            let frame = NSBezierPath(rect: r.insetBy(dx: -0.5, dy: -0.5))
            frame.lineWidth = 1
            frame.stroke()
        }
    }
}
