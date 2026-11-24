// PageViewController.swift — the content item: an NSScrollView over the page canvas
// (task 11.3b). Plan.md §6 Phase 11; docs/macos-design.md §2 ("NSScrollView: native momentum,
// rubber-banding, responsive scrolling, overlay scrollers"; content edge-to-edge under the
// toolbar). Live magnification, zoom and the scroll-edge tuning are task 11.3c.

import AppKit

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

final class PageViewController: NSViewController {
    let scrollView = NSScrollView()
    let canvas = PageCanvasView(frame: NSRect(x: 0, y: 0, width: 100, height: 100))
    private let emptyLabel = NSTextField(labelWithString: "Open a PDF with File > Open… (⌘O)")
    private var laidOutWidth: CGFloat = -1
    private var initialFrame: NSRect

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

        NotificationCenter.default.addObserver(
            self, selector: #selector(boundsChanged(_:)),
            name: NSView.boundsDidChangeNotification, object: scrollView.contentView)
    }

    /// The clip view's visible size in points (below the toolbar's inset).
    var canvasSize: CGSize {
        let clip = scrollView.contentView.bounds.size
        let insets = scrollView.contentInsets
        return CGSize(width: max(1, clip.width - insets.left - insets.right),
                      height: max(1, clip.height - insets.top - insets.bottom))
    }

    /// Shows a document (nil: none), from its first page.
    func show(_ doc: Document?) {
        _ = view
        emptyLabel.isHidden = doc != nil
        canvas.setDocument(doc, canvas: canvasSize)
        laidOutWidth = canvasSize.width
        scroll(toPage: 0)
        refresh()
    }

    /// Re-lays the pages out for the current size and backing scale, keeping the current page
    /// at the top (zoom anchoring, C2, is task 11.3c).
    func relayout() {
        let page = canvas.currentPage
        canvas.relayout(canvas: canvasSize)
        laidOutWidth = canvasSize.width
        scroll(toPage: page)
        refresh()
    }

    /// Scrolls so that `page` shows from its top.
    func scroll(toPage page: Int) {
        let clip = scrollView.contentView
        guard let top = canvas.scrollTop(forPage: page, viewHeight: canvasSize.height) else { return }
        var origin = clip.bounds.origin
        origin.y = top - scrollView.contentInsets.top
        let r = clip.constrainBoundsRect(NSRect(origin: origin, size: clip.bounds.size))
        clip.scroll(to: r.origin)
        scrollView.reflectScrolledClipView(clip)
        refresh()
    }

    /// Requests the renders the visible area needs.
    func refresh() {
        canvas.updateRenders(visible: canvas.visibleRect)
    }

    @objc private func boundsChanged(_ note: Notification) {
        refresh()
    }

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
