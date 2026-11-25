// SidebarViewController.swift — the sidebar item with its four panels (tasks 11.3b, 11.3d2).
// Plan.md §6 Phase 11; docs/macos-design.md §2 ("NSSplitViewController with a sidebar item —
// glass/vibrancy material automatic; a segmented control (SF Symbols) switches thumbnails /
// outline / attachments / layers"); docs/viewer.md "Sidebar" (task 9.r9).
//
// The switcher shows a button only for the panels the document has (Sidebar.buttons: thumbnails
// always, the outline, attachments and layers when there are some). Once the document's outline,
// attachments and layers are known, the sidebar opens as its /PageMode says (Sidebar.onLoad:
// UseThumbs, UseOutlines, UseAttachments, UseOC, each when the document has that content; without
// a page mode the outline when there is one; UseNone and FullScreen keep it closed); the toggle
// reopens the last panel chosen while the document has it (Sidebar.pick). Each panel lives in its
// own file (SidebarThumbnails, SidebarOutline, SidebarAttachments, SidebarLayers); this
// controller wires them to the page view: a thumbnail or outline click jumps (recorded in the
// history), a layers toggle re-renders the pages and the thumbnails.

import AppKit
import SafePdfC

final class SidebarViewController: NSViewController {
    let thumbnails = ThumbnailsPanel(frame: NSRect(x: 0, y: 0, width: 220, height: 560))
    let outline = OutlinePanel(frame: NSRect(x: 0, y: 0, width: 220, height: 560))
    let attachments = AttachmentsPanel(frame: NSRect(x: 0, y: 0, width: 220, height: 560))
    let layers = LayersPanel(frame: NSRect(x: 0, y: 0, width: 220, height: 560))

    private let switcher = NSSegmentedControl()
    private let heading = NSTextField(labelWithString: "")
    private let container = NSView()
    /// The panels each switcher segment shows now (Sidebar.buttons).
    private(set) var buttons: [safepdf_panel] = [SAFEPDF_PANEL_THUMBNAILS]
    /// What the document has (Sidebar.Content).
    private(set) var content = SidebarRules.content(outline: false, attachments: false, layers: false)
    /// The panel shown in the sidebar.
    private(set) var panel = SAFEPDF_PANEL_THUMBNAILS
    /// The reopen after Save (task 11.3e2): keep the sidebar as it was; the panel it showed (nil:
    /// it was closed).
    private var keeping = false
    private var keepOnLoad: safepdf_panel?
    /// The last panel the user chose (Sidebar.pick's `last`; the outline at first).
    private(set) var lastChosen = SAFEPDF_PANEL_OUTLINE
    private(set) weak var document: Document?
    private weak var pages: PageViewController?
    /// Requests for the panels' content still outstanding (outline, attachments, layers).
    private(set) var pending = 0
    /// The panel the document's page mode opened (nil: closed), once known.
    private(set) var loadPanel: safepdf_panel?
    /// Whether the sidebar is shown (the window sets it; thumbnails render only then).
    var isShown = false { didSet { updateActive() } }
    /// The panels' content arrived: the window opens the sidebar on the panel (nil: closed).
    var onLoaded: ((safepdf_panel?) -> Void)?
    /// A status message for the pill.
    var onStatus: ((String) -> Void)?
    /// An external link (an outline URI item): the window asks before copying it.
    var onExternalLink: ((String) -> Void)?
    /// Something changed that the window's chrome shows (content flags, the current page).
    var onChange: (() -> Void)?
    /// Asks the window to open the sidebar on the panel chosen (task 11.3f: an attachment icon
    /// was clicked); without a window (the self-test) `isShown` is set instead.
    var onReveal: (() -> Void)?

    override func loadView() {
        let v = NSView(frame: NSRect(x: 0, y: 0, width: 220, height: 600))
        switcher.trackingMode = .selectOne
        switcher.target = self
        switcher.action = #selector(panelChanged(_:))
        switcher.translatesAutoresizingMaskIntoConstraints = false
        heading.font = .systemFont(ofSize: NSFont.smallSystemFontSize, weight: .semibold)
        heading.textColor = .secondaryLabelColor
        heading.translatesAutoresizingMaskIntoConstraints = false
        container.translatesAutoresizingMaskIntoConstraints = false
        v.addSubview(switcher)
        v.addSubview(heading)
        v.addSubview(container)
        NSLayoutConstraint.activate([
            switcher.topAnchor.constraint(equalTo: v.safeAreaLayoutGuide.topAnchor, constant: 8),
            switcher.centerXAnchor.constraint(equalTo: v.centerXAnchor),
            heading.topAnchor.constraint(equalTo: switcher.bottomAnchor, constant: 8),
            heading.leadingAnchor.constraint(equalTo: v.leadingAnchor, constant: 12),
            heading.trailingAnchor.constraint(lessThanOrEqualTo: v.trailingAnchor, constant: -12),
            container.topAnchor.constraint(equalTo: heading.bottomAnchor, constant: 4),
            container.leadingAnchor.constraint(equalTo: v.leadingAnchor),
            container.trailingAnchor.constraint(equalTo: v.trailingAnchor),
            container.bottomAnchor.constraint(equalTo: v.bottomAnchor),
        ])
        for p in [thumbnails, outline, attachments, layers] as [NSView] {
            p.frame = container.bounds
            p.autoresizingMask = [.width, .height]
            p.isHidden = true
            container.addSubview(p)
        }
        view = v
        rebuildSwitcher()
        showPanel(SAFEPDF_PANEL_THUMBNAILS)
    }

    /// The view of a panel.
    func view(of p: safepdf_panel) -> NSView {
        switch p {
        case SAFEPDF_PANEL_OUTLINE: return outline
        case SAFEPDF_PANEL_ATTACHMENTS: return attachments
        case SAFEPDF_PANEL_LAYERS: return layers
        default: return thumbnails
        }
    }

    // MARK: document

    /// Shows `doc` (nil: none) next to the page view `pv`: the thumbnails are laid out, the
    /// outline, attachments and layers are requested; once all three are known `onLoaded` gets
    /// the panel the page mode opens (Sidebar.onLoad). Every open starts afresh (9.r8): the
    /// default layers state, no panel carried over.
    func show(_ doc: Document?, pages pv: PageViewController, keep: Bool = false) {
        _ = view
        keepOnLoad = keep ? (isShown ? panel : nil) : nil
        keeping = keep
        document = doc
        pages = pv
        loadPanel = nil
        content = SidebarRules.content(outline: false, attachments: false, layers: false)
        thumbnails.scaleOverride = pv.canvas.scaleOverride
        thumbnails.setDocument(doc, quarters: pv.canvas.userRotation / 90, current: pv.canvas.currentPage)
        wire(pv)
        rebuildSwitcher()
        guard let doc else {
            pending = 0
            outline.load(nil) { _ in }
            attachments.load(nil) { _ in }
            layers.load(nil) { _ in }
            return
        }
        pending = 3
        outline.load(doc) { [weak self, weak doc] has in
            guard let self, let doc, self.document === doc else { return }
            self.content.has_outline = has
            self.arrived()
        }
        attachments.load(doc) { [weak self, weak doc] has in
            guard let self, let doc, self.document === doc else { return }
            self.content.has_attachments = has
            self.arrived()
        }
        layers.load(doc) { [weak self, weak doc] has in
            guard let self, let doc, self.document === doc else { return }
            self.content.has_layers = has
            self.arrived()
        }
    }

    private func arrived() {
        pending = max(0, pending - 1)
        rebuildSwitcher()
        onChange?()
        guard pending == 0, let doc = document else { return }
        if keeping {
            // The reopen after Save keeps the sidebar (Viewer.openWith keepView: open on the last
            // panel when it was shown, Sidebar.pick).
            loadPanel = keepOnLoad.map { SidebarRules.pick(last: $0, content) }
        } else {
            loadPanel = SidebarRules.onLoad(pageMode: doc.settings.pageMode, content)
        }
        if let p = loadPanel { choose(p) } // the panel shown is the toggle's `last` (Sidebar.pick)
        onLoaded?(loadPanel)
    }

    /// Connects the panels to the page view.
    private func wire(_ pv: PageViewController) {
        thumbnails.onJump = { [weak pv, weak self] p in
            pv?.jump(to: p)
            self?.onChange?()
        }
        outline.onActivate = { [weak self] a in self?.activate(a) }
        attachments.onStatus = { [weak self] s in self?.status(s) }
        layers.onStatus = { [weak self] s in self?.status(s) }
        // Task 11.3f: the thumbnails are rendered from the pages' preview of edited saved marks
        // (the Tk viewer's State.view); a click on a file attachment annotation's icon selects
        // its row (Viewer.attSelect).
        pv.canvas.onRenderSource = { [weak self] s in self?.thumbnails.setRenderSource(s) }
        pv.text.attachmentAt = { [weak self] page, x, y in self?.attachments.iconAt(page: page, x: x, y: y) }
        pv.text.onAttachmentIcon = { [weak self] i in self?.revealAttachment(i) }
        layers.onChanged = { [weak self, weak pv] in
            pv?.canvas.layersChanged()
            pv?.text.layersChanged()
            self?.thumbnails.layersChanged()
            self?.onChange?()
        }
    }

    /// Selects attachment `i` (a click on its annotation's icon on the page, Viewer.attSelect):
    /// the attachments panel is chosen, the window opens the sidebar (`onReveal`), the row is
    /// selected and shown, and the pill describes it. The attachment is never opened.
    func revealAttachment(_ i: Int) {
        guard attachments.rows.indices.contains(i) else { return }
        if SidebarRules.available(SAFEPDF_PANEL_ATTACHMENTS, content) { choose(SAFEPDF_PANEL_ATTACHMENTS) }
        if let onReveal { onReveal() } else { isShown = true }
        attachments.select(i)
        status(attachments.selectedText(i))
    }

    private func status(_ s: String) {
        if let onStatus { onStatus(s) } else { pages?.pill.show(s) }
    }

    /// Activates an outline item (Viewer.activate): a destination in the document is a jump
    /// (recorded in the history); an external address is the window's to confirm; anything else
    /// is described in the pill and never followed.
    func activate(_ a: NavAction) {
        guard let pv = pages, let doc = document else { return }
        switch a.kind {
        case SAFEPDF_ACTION_GOTO:
            pv.jump(to: a.page, left: a.left.map(Core.rat), top: a.top.map(Core.rat))
            onChange?()
        case SAFEPDF_ACTION_URI where onExternalLink != nil:
            onExternalLink?(a.text)
        default:
            status(SidebarRules.describe(a, labels: doc.labels, pages: doc.pageCount))
        }
    }

    // MARK: following the page view

    /// The page view changed: the thumbnails' highlight follows the current page, a new user
    /// rotation lays them out again, page labels that arrived are shown.
    func sync() {
        guard let pv = pages, document != nil else { return }
        let q = (pv.canvas.userRotation / 90) % 4
        if q != thumbnails.quarters {
            thumbnails.relayout(quarters: q)
        }
        thumbnails.setCurrent(pv.canvas.currentPage)
    }

    /// The page labels arrived.
    func labelsArrived() {
        thumbnails.setLabels(document?.labels ?? [])
    }

    // MARK: panels

    /// The panel the toggle opens (Sidebar.pick).
    var togglePanel: safepdf_panel { SidebarRules.pick(last: lastChosen, content) }

    /// Rebuilds the switcher: one segment per panel the document has (Sidebar.buttons).
    private func rebuildSwitcher() {
        let bs = SidebarRules.panels.filter { SidebarRules.available($0.panel, content) }
        buttons = bs.map(\.panel)
        switcher.segmentCount = bs.count
        for (i, p) in bs.enumerated() {
            switcher.setImage(NSImage(systemSymbolName: p.symbol, accessibilityDescription: p.title), forSegment: i)
            switcher.setToolTip(p.tip, forSegment: i)
            switcher.setWidth(36, forSegment: i)
        }
        if !buttons.contains(panel) { showPanel(SAFEPDF_PANEL_THUMBNAILS) }
        switcher.selectedSegment = buttons.firstIndex(of: panel) ?? 0
    }

    @objc private func panelChanged(_ sender: NSSegmentedControl) {
        let i = sender.selectedSegment
        guard buttons.indices.contains(i) else { return }
        choose(buttons[i])
    }

    /// The user chose a panel (the switcher, the toggle): it is shown and remembered.
    func choose(_ p: safepdf_panel) {
        lastChosen = p
        showPanel(p)
    }

    /// Shows panel `p` (thumbnails when the document does not have it).
    func showPanel(_ p: safepdf_panel) {
        let q = SidebarRules.available(p, content) ? p : SAFEPDF_PANEL_THUMBNAILS
        panel = q
        for v in [thumbnails, outline, attachments, layers] as [NSView] { v.isHidden = v !== view(of: q) }
        heading.stringValue = SidebarRules.panels.first { $0.panel == q }?.title ?? ""
        switcher.selectedSegment = buttons.firstIndex(of: q) ?? 0
        updateActive()
    }

    private func updateActive() {
        thumbnails.active = isShown && panel == SAFEPDF_PANEL_THUMBNAILS && document != nil
    }
}
