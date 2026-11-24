// SidebarThumbnails.swift — the thumbnails panel (task 11.3d2; the Tk viewer's 9.r9 panel).
// Plan.md §6 Phase 11; docs/macos-design.md §2 ("NSCollectionView thumbnails"); docs/viewer.md
// "Thumbnails panel". One image per page, Sidebar.thumbW wide (its height from the page's crop
// box with /Rotate and the user rotation, Sidebar.thumbSize), with the page label below, laid out
// by Sidebar.thumbLayout; the current page's thumbnail has a rounded background and follows the
// main view; a click goes to its page (recorded in the history, as a link); Up / Down move the
// keyboard selection, Return goes there.
//
// Rendering is lazy and off the critical path: only the visible thumbnails and thumbMargin more on
// each side (Sidebar.thumbsWanted) are rendered, through the document worker at the thumbnail
// priority (after every page render), at most `jobs` at once; requests for thumbnails no longer
// wanted are cancelled; at most thumbBudget images are kept (Sidebar.thumbEvict). Each image is
// rendered at the backing scale, at ½–⅛ of it when thumbBudget images would not fit the 32 MiB
// thumbnail reserve (task 12.3b's sizing rule, `SidebarRules.scale`). Nothing renders while the
// panel is hidden. Thumbnails show the layers state of the page view.
//
// Marks (task 11.3f): as in the Tk viewer (`Viewer.renderTask` / `workerFor` render thumbnails
// from `State.view`), while saved marks are changed or deleted the thumbnails are rendered from
// the same preview document as the pages (`setRenderSource`, fed by
// `PageCanvasView.onRenderSource`), so an edited or deleted saved mark shows there too. Marks
// not yet saved are drawn by the page view's overlay only, not on thumbnails (as in Tk).

import AppKit
import SafePdfC

/// One thumbnail's place: its page, the image's top in the panel (points), its size.
struct ThumbSlot {
    let page: Int
    let y: CGFloat
    let w: CGFloat
    let h: CGFloat
    let zoomNum: UInt64
    let zoomDen: UInt64
}

/// Places the thumbnails as Sidebar.thumbLayout does: one column, centred; each item is the
/// image with room for the highlight around it (6 pt above and on the sides) and the label below.
final class ThumbCollectionLayout: NSCollectionViewLayout {
    var slots: [ThumbSlot] = []
    var total: CGFloat = 0
    /// Room around the image for the current-page highlight (the Tk viewer's rounded rectangle:
    /// 6 px out, 2 px below the label).
    static let pad: CGFloat = 6

    func frame(of i: Int, width: CGFloat) -> NSRect {
        let s = slots[i]
        let k = SidebarRules.constants
        let w = s.w + 2 * Self.pad
        return NSRect(x: max(0, (width - w) / 2).rounded(.down), y: s.y - Self.pad, width: w,
                      height: s.h + CGFloat(k.label_h) + Self.pad + 2)
    }

    private var width: CGFloat { collectionView?.enclosingScrollView?.contentView.bounds.width ?? collectionView?.bounds.width ?? 200 }

    override var collectionViewContentSize: NSSize { NSSize(width: width, height: total) }

    override func layoutAttributesForElements(in rect: NSRect) -> [NSCollectionViewLayoutAttributes] {
        let w = width
        var out: [NSCollectionViewLayoutAttributes] = []
        for i in slots.indices {
            let f = frame(of: i, width: w)
            if f.maxY < rect.minY { continue }
            if f.minY > rect.maxY { break }
            let a = NSCollectionViewLayoutAttributes(forItemWith: IndexPath(item: i, section: 0))
            a.frame = f
            out.append(a)
        }
        return out
    }

    override func layoutAttributesForItem(at indexPath: IndexPath) -> NSCollectionViewLayoutAttributes? {
        guard slots.indices.contains(indexPath.item) else { return nil }
        let a = NSCollectionViewLayoutAttributes(forItemWith: indexPath)
        a.frame = frame(of: indexPath.item, width: width)
        return a
    }

    override func shouldInvalidateLayout(forBoundsChange newBounds: NSRect) -> Bool {
        abs(newBounds.width - width) >= 0.5
    }
}

/// The collection view: Return goes to the selected thumbnail.
final class ThumbCollectionView: NSCollectionView {
    var onReturn: (() -> Void)?

    override func keyDown(with event: NSEvent) {
        if let c = event.charactersIgnoringModifiers, c == "\r" || c == "\u{3}" {
            onReturn?()
            return
        }
        super.keyDown(with: event)
    }
}

/// A thumbnail's view: highlight, white frame with a 1 pt border, the image, the label.
final class ThumbItemView: NSView {
    var image: CGImage? { didSet { needsDisplay = true } }
    var label = "" { didSet { needsDisplay = true } }
    var current = false { didSet { needsDisplay = true } }
    var focused = false { didSet { needsDisplay = true } }
    var imageSize = CGSize(width: 98, height: 127)

    override var isFlipped: Bool { true }

    override func draw(_ dirtyRect: NSRect) {
        let pad = ThumbCollectionLayout.pad
        let img = NSRect(x: pad, y: pad, width: imageSize.width, height: imageSize.height)
        if current {
            NSColor.quaternaryLabelColor.setFill()
            NSBezierPath(roundedRect: bounds, xRadius: 5, yRadius: 5).fill()
        }
        if focused {
            NSColor.keyboardFocusIndicatorColor.setStroke()
            let p = NSBezierPath(roundedRect: bounds.insetBy(dx: 2, dy: 2), xRadius: 4, yRadius: 4)
            p.lineWidth = 2
            p.stroke()
        }
        NSColor.white.setFill()
        img.fill()
        if let cg = image, let ctx = NSGraphicsContext.current?.cgContext {
            ctx.saveGState()
            ctx.interpolationQuality = .high
            ctx.clip(to: img)
            ctx.translateBy(x: img.minX, y: img.maxY)
            ctx.scaleBy(x: 1, y: -1)
            ctx.draw(cg, in: CGRect(origin: .zero, size: img.size))
            ctx.restoreGState()
        }
        NSColor.separatorColor.setStroke()
        let frame = NSBezierPath(rect: img.insetBy(dx: -0.5, dy: -0.5))
        frame.lineWidth = 1
        frame.stroke()
        let attrs: [NSAttributedString.Key: Any] = [
            .font: NSFont.systemFont(ofSize: NSFont.smallSystemFontSize),
            .foregroundColor: NSColor.secondaryLabelColor,
        ]
        let text = NSAttributedString(string: label, attributes: attrs)
        let size = text.size()
        let labelTop = img.maxY + 3
        text.draw(in: NSRect(x: max(0, (bounds.width - size.width) / 2), y: labelTop,
                             width: min(size.width, bounds.width), height: size.height))
    }
}

final class ThumbItem: NSCollectionViewItem {
    static let id = NSUserInterfaceItemIdentifier("org.safe-pdf.thumb")

    override func loadView() { view = ThumbItemView(frame: NSRect(x: 0, y: 0, width: 110, height: 155)) }

    var thumbView: ThumbItemView? { view as? ThumbItemView }

    override var isSelected: Bool { didSet { thumbView?.focused = isSelected } }
}

final class ThumbnailsPanel: NSView, NSCollectionViewDataSource, NSCollectionViewDelegate {
    let scroll = NSScrollView()
    let collection = ThumbCollectionView()
    private let layout = ThumbCollectionLayout()
    private(set) weak var document: Document?
    /// Page labels (Toolbar.entryText through PageText.field).
    private var labels: [String] = []
    private(set) var slots: [ThumbSlot] = []
    /// The user rotation (quarter turns) the slots were laid out for.
    private(set) var quarters: UInt32 = 0
    /// Rendered images by page (at most thumbBudget).
    private(set) var images: [Int: CGImage] = [:]
    /// Thumbnail renders in flight: page -> request id.
    private(set) var inflight: [Int: safepdf_request_id] = [:]
    /// The current page (highlighted).
    private(set) var current = 0
    /// The preview of edited saved marks the thumbnails are rendered from (task 11.3f, the Tk
    /// viewer's `State.view`); nil: the document itself.
    private(set) var renderSource: PreviewSource?
    /// The handle thumbnail renders go to now (and are cancelled on).
    private var renderHandle: OpaquePointer? { renderSource?.handle ?? document?.handle }
    /// Rendering happens only while the panel is shown.
    var active = false { didSet { if active && !oldValue { updateRenders() } } }
    /// Backing scale to use instead of the window's (the self-test, off screen).
    var scaleOverride: CGFloat?
    /// Goes to a page (recorded in the history: the window's jump).
    var onJump: ((Int) -> Void)?
    /// Counts for the self-test: thumbnails rendered, requests cancelled, images evicted.
    private(set) var renderedCount = 0
    private(set) var cancelledCount = 0
    private(set) var evictedCount = 0
    /// Renders of thumbnails in flight at most (the Tk viewer's thumbJobs).
    static let jobs = 2
    /// A generation: results of an older one (another document, rotation or layers state) are
    /// dropped.
    private var generation = 0

    override init(frame: NSRect) {
        super.init(frame: frame)
        collection.collectionViewLayout = layout
        collection.dataSource = self
        collection.delegate = self
        collection.isSelectable = true
        collection.allowsMultipleSelection = false
        collection.backgroundColors = [.clear]
        collection.register(ThumbItem.self, forItemWithIdentifier: ThumbItem.id)
        collection.onReturn = { [weak self] in self?.returnPressed() }
        collection.setAccessibilityLabel("Thumbnails")
        scroll.documentView = collection
        scroll.hasVerticalScroller = true
        scroll.autohidesScrollers = true
        scroll.drawsBackground = false
        scroll.frame = bounds
        scroll.autoresizingMask = [.width, .height]
        addSubview(scroll)
        scroll.contentView.postsBoundsChangedNotifications = true
        NotificationCenter.default.addObserver(self, selector: #selector(scrolled(_:)),
                                               name: NSView.boundsDidChangeNotification, object: scroll.contentView)
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    private var backing: CGFloat {
        scaleOverride ?? window?.backingScaleFactor ?? NSScreen.main?.backingScaleFactor ?? 2
    }

    /// Shows `doc` (nil: none): lays the thumbnails out for the user rotation, nothing rendered
    /// until the panel is shown.
    func setDocument(_ doc: Document?, quarters q: UInt32, current page: Int) {
        cancelAll()
        images.removeAll()
        renderSource = nil
        document = doc
        labels = doc?.labels ?? []
        current = page
        relayout(quarters: q)
    }

    /// Lays the thumbnails out again (a new document or rotation, Viewer.buildThumbs).
    func relayout(quarters q: UInt32) {
        cancelAll()
        images.removeAll()
        generation += 1
        quarters = q % 4
        var s: [ThumbSlot] = []
        if let doc = document {
            var sizes: [(UInt32, UInt32, UInt64, UInt64)] = []
            for p in 0..<doc.pageCount {
                if let t = SidebarRules.thumb(doc, page: p, quarters: quarters) {
                    sizes.append((t.width, t.height, t.zoom_num, t.zoom_den))
                } else {
                    sizes.append((SidebarRules.constants.width, SidebarRules.constants.width, 1, 1))
                }
            }
            if let (ys, total) = SidebarRules.layout(heights: sizes.map(\.1)) {
                for (p, sz) in sizes.enumerated() where p < ys.count {
                    s.append(ThumbSlot(page: p, y: CGFloat(ys[p]), w: CGFloat(sz.0), h: CGFloat(sz.1),
                                       zoomNum: sz.2, zoomDen: sz.3))
                }
                layout.total = CGFloat(total)
            }
        }
        if s.isEmpty { layout.total = 0 }
        slots = s
        layout.slots = s
        collection.reloadData()
        layout.invalidateLayout()
        collection.setFrameSize(NSSize(width: scroll.contentView.bounds.width, height: layout.total))
        scroll.contentView.scroll(to: .zero)
        scroll.reflectScrolledClipView(scroll.contentView)
        markCurrent(scroll: true)
        updateRenders()
    }

    /// The page labels arrived: the labels under the thumbnails follow.
    func setLabels(_ ls: [String]) {
        labels = ls
        for case let item as ThumbItem in collection.visibleItems() {
            if let ip = collection.indexPath(for: item) { item.thumbView?.label = labelText(ip.item) }
        }
    }

    private func labelText(_ p: Int) -> String {
        guard let doc = document else { return "\(p + 1)" }
        return PageText.field(labels: labels, page: p, pages: doc.pageCount).entry
    }

    /// The main view's current page changed: the highlight follows and is scrolled into view
    /// (Viewer.markThumb, PDF.js's scrollThumbnailIntoView).
    func setCurrent(_ page: Int) {
        guard page != current else { return }
        let old = current
        current = page
        for p in [old, page] {
            if let item = collection.item(at: IndexPath(item: p, section: 0)) as? ThumbItem {
                item.thumbView?.current = p == current
            }
        }
        markCurrent(scroll: true)
    }

    private func markCurrent(scroll doScroll: Bool) {
        guard slots.indices.contains(current) else { return }
        if doScroll {
            let f = layout.frame(of: current, width: scroll.contentView.bounds.width)
            collection.scrollToVisible(f.insetBy(dx: 0, dy: -8))
        }
    }

    /// The rectangle (panel points) of a page's thumbnail item.
    func itemFrame(_ page: Int) -> NSRect? {
        slots.indices.contains(page) ? layout.frame(of: page, width: scroll.contentView.bounds.width) : nil
    }

    // MARK: rendering (Viewer.thumbView, thumbPoll)

    @objc private func scrolled(_ note: Notification) { updateRenders() }

    /// The visible band of the panel in its coordinates.
    var band: (top: CGFloat, bottom: CGFloat) {
        let r = scroll.contentView.bounds
        return (max(0, r.minY), max(0, r.maxY))
    }

    /// Requests the wanted thumbnails (visible plus thumbMargin each side, nearest the middle
    /// first), cancels the others in flight, drops images beyond thumbBudget.
    func updateRenders() {
        guard active, let doc = document, !slots.isEmpty else { return }
        let (top, bottom) = band
        guard bottom > top else { return }
        let want = SidebarRules.wanted(heights: slots.map { UInt32($0.h) }, top: UInt64(top.rounded(.down)),
                                       bottom: UInt64(bottom.rounded(.up)))
        let wantSet = Set(want)
        let handle = renderHandle ?? doc.handle
        for (p, id) in inflight where !wantSet.contains(p) {
            safepdf_doc_cancel(handle, id)
            inflight[p] = nil
            cancelledCount += 1
        }
        for p in SidebarRules.evict(held: Array(images.keys), wanted: want, center: want.first ?? current) {
            images[p] = nil
            evictedCount += 1
            if let item = collection.item(at: IndexPath(item: p, section: 0)) as? ThumbItem { item.thumbView?.image = nil }
        }
        for p in want where images[p] == nil && inflight[p] == nil {
            if inflight.count >= Self.jobs { break }
            submit(p, doc: doc)
        }
    }

    /// The render zoom of a thumbnail: thumbW / page width at the backing scale, divided by 2^k
    /// for the 12.3b scale k; nil when it does not fit the render call.
    func renderKey(_ s: ThumbSlot) -> ZoomKey? {
        let b = max(1, backing)
        let b64 = UInt64((b * 64).rounded())
        let k = SidebarRules.scale(w: Int((s.w * b).rounded()), h: Int((s.h * b).rounded()))
        var num = s.zoomNum.multipliedReportingOverflow(by: b64)
        var den = s.zoomDen.multipliedReportingOverflow(by: 64 << UInt64(min(max(k, 0), 3)))
        guard !num.overflow, !den.overflow, num.partialValue > 0, den.partialValue > 0 else { return nil }
        var g = num.partialValue, r = den.partialValue
        while r != 0 { (g, r) = (r, g % r) }
        num.partialValue /= g
        den.partialValue /= g
        if let n = UInt32(exactly: num.partialValue), let d = UInt32(exactly: den.partialValue) {
            return ZoomKey(num: n, den: d, rotation: quarters)
        }
        let z = Double(num.partialValue) / Double(den.partialValue)
        guard z.isFinite, z > 0, z * 65536 < Double(UInt32.max) else { return nil }
        return ZoomKey(num: UInt32(max(1, (z * 65536).rounded())), den: 65536, rotation: quarters)
    }

    private func submit(_ p: Int, doc: Document) {
        guard slots.indices.contains(p), let key = renderKey(slots[p]) else { return }
        let gen = generation
        let id = Rendering.submit(handle: renderHandle ?? doc.handle, layers: doc.layers, page: p, key: key,
                                  priority: Int32(SAFEPDF_PRIO_THUMBNAIL)) { [weak self] res in
            self?.done(res, generation: gen)
        }
        if id != 0 { inflight[p] = id }
    }

    private func done(_ res: RenderResult, generation gen: Int) {
        if inflight[res.page] == res.id { inflight[res.page] = nil }
        guard gen == generation else { return }
        if let img = res.image {
            images[res.page] = img
            renderedCount += 1
            if let item = collection.item(at: IndexPath(item: res.page, section: 0)) as? ThumbItem {
                item.thumbView?.image = img
            }
        }
        updateRenders()
    }

    private func cancelAll() {
        if let h = renderHandle {
            for (_, id) in inflight { safepdf_doc_cancel(h, id) }
        }
        inflight.removeAll()
    }

    /// The thumbnails are rendered from `source` from now on (task 11.3f; the page canvas's
    /// `onRenderSource`: a new preview of edited saved marks, or nil for the document itself, as
    /// Viewer.updatePreview's new generation lays the Tk thumbnails out again). Running requests
    /// are cancelled and every thumbnail is rendered again. Returns whether the source changed.
    @discardableResult
    func setRenderSource(_ source: PreviewSource?) -> Bool {
        guard document != nil, source !== renderSource else { return false }
        cancelAll()
        renderSource = source
        sourceChanges += 1
        rerenderAll()
        return true
    }

    /// Changes of the rendering source so far (the self-test counts them).
    private(set) var sourceChanges = 0

    /// The layers state changed (Viewer.applyLayers): every thumbnail is rendered again.
    func layersChanged() {
        rerenderAll()
    }

    /// Drops every image and renders the wanted thumbnails again.
    private func rerenderAll() {
        cancelAll()
        images.removeAll()
        generation += 1
        for case let item as ThumbItem in collection.visibleItems() { item.thumbView?.image = nil }
        updateRenders()
    }

    // MARK: data source and delegate

    func collectionView(_ collectionView: NSCollectionView, numberOfItemsInSection section: Int) -> Int {
        slots.count
    }

    func collectionView(_ collectionView: NSCollectionView,
                        itemForRepresentedObjectAt indexPath: IndexPath) -> NSCollectionViewItem {
        let item = collectionView.makeItem(withIdentifier: ThumbItem.id, for: indexPath)
        if let t = item as? ThumbItem, let v = t.thumbView, slots.indices.contains(indexPath.item) {
            let s = slots[indexPath.item]
            v.imageSize = CGSize(width: s.w, height: s.h)
            v.label = labelText(indexPath.item)
            v.current = indexPath.item == current
            v.image = images[indexPath.item]
            v.focused = t.isSelected
            v.setAccessibilityElement(true)
            v.setAccessibilityRole(.button)
            v.setAccessibilityLabel("Page \(v.label)")
        }
        return item
    }

    func collectionView(_ collectionView: NSCollectionView, didSelectItemsAt indexPaths: Set<IndexPath>) {
        guard let p = indexPaths.first?.item else { return }
        // A click goes there at once (Viewer.thumbClick); the arrow keys only move the keyboard
        // selection, Return goes (Viewer.thumbKey).
        let type = NSApp.currentEvent?.type
        if type == .leftMouseDown || type == .leftMouseUp {
            collectionView.deselectAll(nil)
            activate(p)
        }
    }

    private func returnPressed() {
        guard let p = collection.selectionIndexPaths.first?.item else { return }
        collection.deselectAll(nil)
        activate(p)
    }

    /// Goes to page `p` (nothing when it is the current page, Viewer.thumbClick).
    func activate(_ p: Int) {
        guard slots.indices.contains(p), p != current else { return }
        onJump?(p)
    }
}
