// PageCanvasView.swift — the pages, laid out by safepdf_view_layout and drawn from renders
// (tasks 11.3b, 11.3c1, 11.3c2). Plan.md §6 Phase 11; docs/macos-design.md §1 (zoom model, rotation,
// C2 anchoring), §2 (NSScrollView page area, dark canvas around paper-white pages, sharp image
// cross-fades over the scaled one) and §3 decision 4 (renders through the worker, callbacks on
// the main queue).
//
// Layout input: each page's exact CropBox and /Rotate (safepdf_doc_page_geom), the zoom choice
// (Toolbar.ZoomChoice), the user's rotation and the view modes (task 11.3c2: page or vertical
// scrolling, no / odd / even spreads, right to left; in the page scroll mode only the current
// page's spread is laid out). The current page is set by the page view controller (the Tk
// viewer's rule: the page it went to, else the page under the window centre). Keys the menu cannot carry (plain letters, Home/End, arrows,
// space) are handled here, through the exported key table, while the canvas is first responder.

import AppKit
import SafePdfC

/// A `safepdf_layout`, freed when the holder goes away.
final class LayoutHolder {
    var raw: safepdf_layout

    init(_ raw: safepdf_layout) { self.raw = raw }

    deinit { safepdf_free_layout(&raw) }
}

/// A laid-out page: rectangle in scroll-region pixels, the render key and the exact view
/// parameters (for re-anchoring).
struct PagePlace {
    let page: Int
    let pixels: CGRect
    let key: ZoomKey?       // nil: the zoom does not fit the render call (not rendered)
    let zoom: safepdf_rat   // pixels per page unit (the base zoom, capped per page)
    let rotation: UInt32    // degrees: page /Rotate + user rotation
    let capped: Bool
    let cropped: Bool
}

/// Who handles the pointer on the pages (task 11.3d1: selection, links, the cursor). Points
/// are the canvas's (view points, y down).
@MainActor protocol CanvasPointer: AnyObject {
    func pointerDown(at p: CGPoint, clicks: Int, shift: Bool)
    func pointerDragged(at p: CGPoint)
    func pointerUp(at p: CGPoint)
    /// The pointer moved (nil: it left the canvas).
    func pointerMoved(at p: CGPoint?)
}

/// A page point under a scroll-region position, in the view it was taken in (C2).
struct PageAnchor {
    let page: Int
    let q: CGPoint          // pixels from the page image's top-left
    let zoom: safepdf_rat
    let rotation: UInt32
    let backing: CGFloat
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
    /// The last render error per page (the status pill shows it, task 11.3c2).
    private(set) var errors: [Int: String] = [:]
    private(set) var currentPage = 0
    /// The view modes (every open starts with continuous vertical scrolling, no spreads).
    var modes = ViewModes.start
    /// The zoom drop-down's choice (Toolbar.ZoomChoice; every open starts at Automatic Zoom).
    var zoomChoice = ZoomModel.auto
    /// The user's rotation in degrees (0, 90, 180, 270), added to every page's /Rotate.
    var userRotation: UInt32 = 0
    /// The backing scale the current layout was made for.
    private(set) var laidOutBacking: CGFloat = 1
    /// The page whose size picked the current layout's zoom (the current page then).
    private(set) var laidOutPage = 0
    /// Called for every finished render (the self-test's timings).
    var onRender: ((RenderResult) -> Void)?
    /// Called when the page at the top of the view changes.
    var onCurrentPageChange: ((Int) -> Void)?
    /// Called with a page and its render error (the status pill shows it).
    var onRenderError: ((Int, String) -> Void)?
    /// Called when a layout cannot be computed (the window shows it as a sheet).
    var onError: ((String) -> Void)?
    /// Called just before a sharp render replaces a scaled (stale-zoom) image of a page in
    /// view: the page area cross-fades the swap.
    var onSharpSwap: (() -> Void)?
    /// Runs a command of the key table (Menu.Cmd id); returns whether it ran.
    var onKeyCommand: ((Int) -> Bool)?
    /// Scrolls by lines (arrows) or views (space) when no command takes a key: (dx, dy) in
    /// lines, or pages when `pages`.
    var onKeyScroll: ((_ dx: Int, _ dy: Int, _ pages: Bool) -> Void)?
    /// The pointer's handler (task 11.3d1).
    weak var pointer: CanvasPointer?
    /// Draws a page's overlays (search hits, the selection) above its image (task 11.3d1).
    var drawOverlay: ((Int) -> Void)?
    private var tracking: NSTrackingArea?

    override var isFlipped: Bool { true }
    override var isOpaque: Bool { false }
    override var acceptsFirstResponder: Bool { document != nil }

    /// Backing pixels per point.
    var backing: CGFloat {
        scaleOverride ?? window?.backingScaleFactor ?? NSScreen.main?.backingScaleFactor ?? 1
    }

    /// The layout's scaling (screen pixels per point) as an exact rational.
    var scaling: safepdf_rat { ZoomModel.scaling(laidOutBacking) }

    /// The zoom choice's zoom for the current page (the layout's base zoom).
    var baseZoom: safepdf_rat? { layout?.raw.base_zoom }

    /// The percentage shown for the current zoom (subtitle).
    var shownPct: UInt32? {
        guard let z = baseZoom else { return nil }
        return ZoomModel.zoomPct(z, scaling: scaling)
    }

    /// Requests in flight (the self-test waits for zero).
    var pendingCount: Int { inflight.count }

    /// Sharp renders that replaced a scaled image (the self-test counts them).
    private(set) var sharpSwaps = 0

    /// Shows `doc` (nil: none) at Automatic Zoom without rotation (every open starts afresh,
    /// 9.r8); cancels the previous document's requests.
    func setDocument(_ doc: Document?, canvas: CGSize) {
        if let old = document {
            for (_, r) in inflight { safepdf_doc_cancel(old.handle, r.id) }
        }
        inflight.removeAll()
        cache.removeAll()
        errors.removeAll()
        document = doc
        currentPage = 0
        zoomChoice = ZoomModel.auto
        userRotation = 0
        modes = .start
        relayout(canvas: canvas)
    }

    /// Lays the pages out for a canvas of `canvas` points (the clip view's size) with the
    /// current zoom choice, rotation and backing scale.
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
        var geoms = doc.geometry
        var params = safepdf_layout_params(
            scroll: modes.scroll, spread: modes.spread,
            user_rotation: userRotation, zoom: zoomChoice,
            scaling: ZoomModel.scaling(b),
            canvas_w: UInt32(clamping: Int((canvas.width * b).rounded(.down))),
            canvas_h: UInt32(clamping: Int((canvas.height * b).rounded(.down))),
            page: min(currentPage, doc.pageCount - 1), rtl: modes.rtl)
        var out = safepdf_layout()
        guard safepdf_view_layout(&geoms, geoms.count, &params, &out) == 0 else {
            onError?("The pages could not be laid out (safepdf_view_layout failed).")
            return
        }
        let holder = LayoutHolder(out)
        // Renders take the user's rotation; the worker adds each page's /Rotate.
        let extra = (userRotation / 90) % 4
        var ps: [PagePlace] = []
        var index: [Int: Int] = [:]
        if let raw = holder.raw.places {
            for i in 0..<holder.raw.count {
                let p = raw[i]
                var key: ZoomKey? = nil
                if p.zoom.num > 0, p.zoom.den > 0, let n = UInt32(exactly: p.zoom.num),
                   let d = UInt32(exactly: p.zoom.den) {
                    key = ZoomKey(num: n, den: d, rotation: extra)
                }
                index[p.page] = ps.count
                ps.append(PagePlace(page: p.page,
                                    pixels: CGRect(x: Double(p.x), y: Double(p.y), width: Double(p.w),
                                                   height: Double(p.h)),
                                    key: key, zoom: p.zoom, rotation: p.rotation,
                                    capped: p.capped, cropped: p.cropped))
            }
        }
        layout = holder
        places = ps
        placeOf = index
        laidOutBacking = b
        laidOutPage = Int(params.page)
        setFrameSize(CGSize(width: max(canvas.width, CGFloat(holder.raw.region_w) / b),
                            height: max(canvas.height, CGFloat(holder.raw.region_h) / b)))
        needsDisplay = true
    }

    /// Makes `page` the current page (the controller's rule) and reports a change. In the page
    /// scroll mode the caller lays the pages out again when the spread changed.
    func setCurrent(_ page: Int) {
        guard let doc = document, doc.pageCount > 0 else { return }
        let p = min(max(0, page), doc.pageCount - 1)
        guard p != currentPage else { return }
        currentPage = p
        onCurrentPageChange?(p)
    }

    /// Whether the current layout shows `page` (the page scroll mode lays out one spread).
    func isLaidOut(_ page: Int) -> Bool { placeOf[page] != nil }

    /// The page at a point of the view (points): the page containing it, else the nearest one
    /// (View.pageAt).
    func page(at point: CGPoint) -> Int? {
        guard let holder = layout else { return nil }
        let b = laidOutBacking
        var hit = safepdf_page_hit()
        guard safepdf_view_page_at(&holder.raw, UInt64(max(0, point.x * b)), UInt64(max(0, point.y * b)),
                                   0, &hit) == 1 else { return nil }
        return hit.page
    }

    /// The place of a page in the current layout.
    func place(ofPage page: Int) -> PagePlace? {
        guard let i = placeOf[page] else { return nil }
        return places[i]
    }

    /// A page's rectangle in view points.
    func rect(ofPage page: Int) -> NSRect? {
        guard let i = placeOf[page] else { return nil }
        let b = laidOutBacking
        let p = places[i].pixels
        return NSRect(x: p.minX / b, y: p.minY / b, width: p.width / b, height: p.height / b)
    }

    /// The page point under `point` (view points; the page containing it, else the nearest,
    /// View.pageAt), for re-anchoring after a zoom or rotation change.
    func anchor(at point: CGPoint) -> PageAnchor? {
        guard let holder = layout else { return nil }
        let b = laidOutBacking
        var hit = safepdf_page_hit()
        guard safepdf_view_page_at(&holder.raw, UInt64(max(0, point.x * b)), UInt64(max(0, point.y * b)),
                                   0, &hit) == 1, let pl = place(ofPage: hit.page) else { return nil }
        return PageAnchor(page: hit.page,
                          q: CGPoint(x: point.x * b - pl.pixels.minX, y: point.y * b - pl.pixels.minY),
                          zoom: pl.zoom, rotation: pl.rotation, backing: b)
    }

    /// Where the anchored page point lies in the current layout (view points), by View.reanchor
    /// from the view the anchor was taken in.
    func point(of a: PageAnchor) -> CGPoint? {
        guard let doc = document, a.page < doc.geometry.count, let pl = place(ofPage: a.page),
              let q2 = ZoomModel.reanchor(z: a.zoom, rot: a.rotation, z2: pl.zoom, rot2: pl.rotation,
                                          box: doc.geometry[a.page].box, q: a.q) else { return nil }
        let b = laidOutBacking
        return CGPoint(x: (pl.pixels.minX + q2.x) / b, y: (pl.pixels.minY + q2.y) / b)
    }

    /// The scroll position (points, top of the visible area) that shows `page` from its top
    /// (View.topFor through safepdf_view_page_at).
    func scrollTop(forPage page: Int, viewHeight: CGFloat) -> CGFloat? {
        hitOf(page, viewHeight: viewHeight).map { CGFloat($0.top) / laidOutBacking }
    }

    /// The scroll position that shows `page` down to its bottom (View.bottomFor).
    func scrollBottom(forPage page: Int, viewHeight: CGFloat) -> CGFloat? {
        hitOf(page, viewHeight: viewHeight).map { CGFloat($0.bottom) / laidOutBacking }
    }

    private func hitOf(_ page: Int, viewHeight: CGFloat) -> safepdf_page_hit? {
        guard let holder = layout, let i = placeOf[page] else { return nil }
        let b = laidOutBacking
        let p = places[i].pixels
        var hit = safepdf_page_hit()
        guard safepdf_view_page_at(&holder.raw, UInt64(p.midX), UInt64(p.minY),
                                   UInt64(max(0, viewHeight * b)), &hit) == 1 else { return nil }
        return hit
    }

    /// Requests renders for the pages meeting `visible` (plus one each side, View.wantedPages),
    /// cancels requests for pages no longer wanted and drops far-away images. The current page
    /// is rendered first.
    func updateRenders(visible: NSRect) {
        guard let doc = document, let holder = layout else { return }
        let b = laidOutBacking
        let top = UInt64(max(0, visible.minY * b))
        let bottom = UInt64(max(0, visible.maxY * b))
        var band = safepdf_page_band()
        guard safepdf_view_pages_in_band(&holder.raw, top, bottom, &band) == 0 else { return }
        var wanted: [Int] = []
        if let w = band.wanted { for i in 0..<band.wanted_count { wanted.append(w[i]) } }
        safepdf_free_page_band(&band)

        let wantedSet = Set(wanted)
        for (page, r) in inflight where !wantedSet.contains(page) {
            safepdf_doc_cancel(doc.handle, r.id)
            inflight[page] = nil
        }
        for page in wanted {
            let prio = page == currentPage ? Int32(SAFEPDF_PRIO_CURRENT) : Int32(SAFEPDF_PRIO_VISIBLE)
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
            let current = places[i].key == res.key
            if current || cache[res.page] == nil {
                let replacesScaled = current && cache[res.page].map { $0.key != res.key } == true
                if replacesScaled, let r = rect(ofPage: res.page), r.intersects(visibleRect) {
                    sharpSwaps += 1
                    onSharpSwap?()
                }
                cache[res.page] = (res.key, image)
                errors[res.page] = nil
                if let r = rect(ofPage: res.page) { setNeedsDisplay(r) }
            }
        } else if let e = res.error {
            errors[res.page] = e
            NSLog("SafePDF: page %d: %@", res.page + 1, e)
            onRenderError?(res.page, e)
        }
        onRender?(res)
    }

    /// The document's layers state changed (task 11.3d2, the layers panel; Viewer.applyLayers):
    /// running renders are stale and cancelled; the images shown stay, drawn as scaled stand-ins
    /// (their key no longer matches), until the renders under the new state replace them
    /// (cross-faded). Returns the number of renders requested again.
    @discardableResult
    func layersChanged() -> Int {
        guard let doc = document else { return 0 }
        for (_, r) in inflight { safepdf_doc_cancel(doc.handle, r.id) }
        inflight.removeAll()
        for (page, entry) in cache {
            cache[page] = (ZoomKey(num: 0, den: 1, rotation: entry.key.rotation), entry.image)
        }
        errors.removeAll()
        updateRenders(visible: visibleRect)
        return inflight.count
    }

    override func draw(_ dirtyRect: NSRect) {
        guard let cg = NSGraphicsContext.current?.cgContext else { return }
        cg.interpolationQuality = .high
        let b = laidOutBacking
        for place in places {
            guard let r = rect(ofPage: place.page), r.intersects(dirtyRect) else { continue }
            // The paper stays white in dark mode (docs/macos-design.md §2).
            NSColor.white.setFill()
            r.fill()
            // An image of another zoom is drawn scaled into the page until the sharp one comes
            // (then it cross-fades); one of another rotation would be drawn distorted: skipped.
            if let entry = cache[place.page], entry.key.rotation == place.key?.rotation {
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
            drawOverlay?(place.page)
            NSColor.separatorColor.setStroke()
            let frame = NSBezierPath(rect: r.insetBy(dx: -0.5, dy: -0.5))
            frame.lineWidth = 1
            frame.stroke()
        }
    }

    // MARK: keys (the key table's bindings that are not menu key equivalents)

    override func mouseDown(with event: NSEvent) {
        window?.makeFirstResponder(self)
        guard let p = pointer, document != nil else {
            super.mouseDown(with: event)
            return
        }
        p.pointerDown(at: convert(event.locationInWindow, from: nil), clicks: event.clickCount,
                      shift: event.modifierFlags.contains(.shift))
    }

    override func mouseDragged(with event: NSEvent) {
        guard let p = pointer, document != nil else { return super.mouseDragged(with: event) }
        p.pointerDragged(at: convert(event.locationInWindow, from: nil))
        autoscroll(with: event) // a drag past the visible area scrolls it
    }

    override func mouseUp(with event: NSEvent) {
        guard let p = pointer, document != nil else { return super.mouseUp(with: event) }
        p.pointerUp(at: convert(event.locationInWindow, from: nil))
    }

    override func mouseMoved(with event: NSEvent) {
        pointer?.pointerMoved(at: convert(event.locationInWindow, from: nil))
    }

    override func mouseExited(with event: NSEvent) {
        pointer?.pointerMoved(at: nil)
    }

    override func cursorUpdate(with event: NSEvent) {
        guard let p = pointer, document != nil else { return super.cursorUpdate(with: event) }
        p.pointerMoved(at: convert(event.locationInWindow, from: nil))
    }

    /// The pointer is tracked over the visible area (moves set the cursor, Toolbar.cursorFor).
    override func updateTrackingAreas() {
        super.updateTrackingAreas()
        if let t = tracking { removeTrackingArea(t) }
        let t = NSTrackingArea(rect: .zero, options: [.mouseMoved, .mouseEnteredAndExited, .cursorUpdate,
                                                      .activeInKeyWindow, .inVisibleRect],
                               owner: self, userInfo: nil)
        addTrackingArea(t)
        tracking = t
    }

    override func keyDown(with event: NSEvent) {
        if document != nil, let cmd = PageKeys.shared.command(for: event), onKeyCommand?(cmd) == true {
            return
        }
        if document != nil, let (dx, dy, pages) = PageKeys.scroll(for: event), let scroll = onKeyScroll {
            scroll(dx, dy, pages)
            return
        }
        super.keyDown(with: event)
    }
}

/// The page view's keys: the bindings of the exported key table (Menu.keyTable .aqua) that
/// KeyEquivalents keeps out of the menubar (no Command or Control: they would be taken from
/// text fields), plus the scrolling keys of the Tk viewer's canvas (arrows by lines, space and
/// shift-space by views).
@MainActor final class PageKeys {
    static let shared = PageKeys()

    private struct Binding {
        let character: String      // what KeyEquivalents matches (lower case for letters)
        let flags: NSEvent.ModifierFlags
        let letter: Bool
        let command: Int
    }

    private let bindings: [Binding]

    private init() {
        var bs: [Binding] = []
        for b in Chrome.keys() ?? [] where !b.isAction && !KeyEquivalents.usableInMenu(b.key) {
            guard let (eq, flags) = KeyEquivalents.translate(b.key) else { continue }
            let letter = eq.count == 1 && eq.unicodeScalars.allSatisfy { CharacterSet.letters.contains($0) }
            bs.append(Binding(character: eq, flags: flags, letter: letter, command: b.target))
        }
        bindings = bs
    }

    /// The keys handled here, as "mods:character" (the self-test lists them).
    var described: [String] { bindings.map { "\($0.flags.rawValue):\($0.character)->\($0.command)" } }

    private static let mask: NSEvent.ModifierFlags = [.command, .shift, .option, .control]

    /// The command a key event runs, if any. A letter matches with its Shift state; for other
    /// characters Shift is part of the character ("+" is Shift-= on many layouts) and ignored.
    func command(for event: NSEvent) -> Int? {
        guard event.type == .keyDown, let chars = event.charactersIgnoringModifiers, !chars.isEmpty
        else { return nil }
        let flags = event.modifierFlags.intersection(Self.mask)
        let lower = chars.lowercased()
        for b in bindings where b.character == lower || b.character == chars {
            if b.letter {
                if flags == b.flags { return b.command }
            } else if flags.subtracting(.shift) == b.flags.subtracting(.shift) {
                return b.command
            }
        }
        return nil
    }

    /// Arrow keys (one line), space and shift-space (one view) without other modifiers.
    static func scroll(for event: NSEvent) -> (Int, Int, Bool)? {
        guard event.type == .keyDown, let chars = event.charactersIgnoringModifiers,
              let u = chars.unicodeScalars.first else { return nil }
        let flags = event.modifierFlags.intersection(mask)
        switch Int(u.value) {
        case NSUpArrowFunctionKey where flags.isEmpty: return (0, -1, false)
        case NSDownArrowFunctionKey where flags.isEmpty: return (0, 1, false)
        case NSLeftArrowFunctionKey where flags.isEmpty: return (-1, 0, false)
        case NSRightArrowFunctionKey where flags.isEmpty: return (1, 0, false)
        case 0x20 where flags.isEmpty: return (0, 1, true)
        case 0x20 where flags == .shift: return (0, -1, true)
        default: return nil
        }
    }
}
