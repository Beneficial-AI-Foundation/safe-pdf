// DocumentWindowController.swift — the document window: unified toolbar, split view with the
// sidebar and the page area, command routing and enabled states (task 11.3b); the zoom and
// rotation commands, the zoom drop-down and the page view's keys (task 11.3c1).
// Plan.md §6 Phase 11; docs/macos-design.md §2 (window with full-size content view, unified
// toolbar, title = document name with proxy icon; NSSplitViewController sidebar) and §3
// decision 1 (enabled rules from the exported Menu.Ctx table).

import AppKit
import SafePdfC

final class DocumentWindowController: NSWindowController, NSWindowDelegate, NSMenuItemValidation,
    NSToolbarItemValidation, SafePdfCommandTarget, ZoomPresetTarget
{
    let pages = PageViewController()
    let sidebar = SidebarViewController()
    private let split = NSSplitViewController()
    private var sidebarItem: NSSplitViewItem?
    private var chromeToolbar: DocumentToolbar?
    /// The open PDF (not NSWindowController.document, which is for NSDocument).
    private(set) var pdf: Document?
    private var states: ChromeStates?

    init() {
        let window = NSWindow(
            contentRect: NSRect(x: 0, y: 0, width: 980, height: 1000),
            styleMask: [.titled, .closable, .miniaturizable, .resizable, .fullSizeContentView],
            backing: .buffered, defer: true)
        window.title = Chrome.appName()
        window.toolbarStyle = .unified
        window.titlebarSeparatorStyle = .automatic
        window.minSize = NSSize(width: 480, height: 360)
        window.tabbingMode = .disallowed // window tabs are a later issue (#13)
        super.init(window: window)
        window.delegate = self

        let side = NSSplitViewItem(sidebarWithViewController: sidebar)
        side.canCollapse = true
        side.isCollapsed = true
        side.minimumThickness = 180
        side.maximumThickness = 360
        let content = NSSplitViewItem(viewController: pages)
        #if compiler(>=6.2) // the macOS 26 SDK (Xcode 26) ships with Swift 6.2
        if #available(macOS 26, *) {
            // Liquid Glass: the sidebar floats over the page area, which extends under it.
            content.automaticallyAdjustsSafeAreaInsets = true
        }
        #endif
        split.addSplitViewItem(side)
        split.addSplitViewItem(content)
        sidebarItem = side
        window.contentViewController = split
        window.setContentSize(NSSize(width: 980, height: 1000))

        if let tb = DocumentToolbar(identifier: "org.safe-pdf.document") {
            chromeToolbar = tb
            window.toolbar = tb.toolbar
        }
        pages.canvas.onCurrentPageChange = { [weak self] _ in self?.updateChrome() }
        pages.onViewChange = { [weak self] in self?.updateChrome() }
        pages.canvas.onKeyCommand = { [weak self] cmd in self?.run(cmd) ?? false }
        pages.canvas.onError = { [weak self] message in
            guard let self else { return }
            Sheets.error("Cannot show the document", detail: message, on: self.window)
        }
        window.center()
        window.setFrameAutosaveName("SafePDFDocumentWindow")
        updateChrome()
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    /// Opens `url` in this window; errors from the C API appear as a sheet.
    func open(_ url: URL) {
        let t0 = Core.nowMs()
        let doc: Document
        do {
            doc = try Document(url: url)
        } catch {
            Sheets.error("“\(url.lastPathComponent)” could not be opened.", detail: error.message, on: window)
            return
        }
        NSLog("SafePDF: opened %@ (%d pages) in %.1f ms", url.lastPathComponent, doc.pageCount,
              Core.nowMs() - t0)
        pdf = doc
        window?.representedURL = url
        window?.title = url.lastPathComponent
        pages.show(doc)
        window?.makeFirstResponder(pages.canvas)
        NSDocumentController.shared.noteNewRecentDocumentURL(url)
        updateChrome()
    }

    // MARK: chrome states

    private func context() -> safepdf_ctx {
        var c = safepdf_ctx()
        if let doc = pdf {
            let page = pages.canvas.currentPage
            c.has_doc = true
            c.page = page
            c.pages = doc.pageCount
            c.on_first = page == 0
            c.on_last = page + 1 >= doc.pageCount
            // TODO(11.3c2/d/e): outline, selection, marks, history, undo and dirty flags.
        }
        return c
    }

    /// Recomputes enabled states (safepdf_view_states), the page field and the subtitle.
    func updateChrome() {
        states = Chrome.states(context())
        if let st = states { chromeToolbar?.apply(st) }
        if let doc = pdf {
            var entry: UnsafeMutablePointer<CChar>? = nil
            var of: UnsafeMutablePointer<CChar>? = nil
            let page = pages.canvas.currentPage
            if safepdf_view_page_field(nil, 0, page, doc.pageCount, &entry, &of) == 0 {
                chromeToolbar?.setPage(entry: Core.take(entry) ?? "", of: Core.take(of) ?? "")
            } else {
                _ = Core.take(entry)
                _ = Core.take(of)
            }
            let zoom = pages.canvas.shownPct.map { " · \($0)%" } ?? ""
            window?.subtitle = "page \(page + 1)/\(doc.pageCount)\(zoom)"
        } else {
            chromeToolbar?.setPage(entry: "", of: "")
            window?.subtitle = ""
        }
        chromeToolbar?.setZoom(pages.canvas.zoomChoice)
    }

    /// Whether a command can run now: the exported rule and this shell implements it.
    func isEnabled(_ cmd: Int) -> Bool {
        guard Commands.implemented.contains(cmd), let st = states, cmd >= 0,
              cmd < st.commandEnabled.count else { return false }
        return st.commandEnabled[cmd]
    }

    // MARK: commands

    @objc func performSafePdfCommand(_ sender: Any?) {
        let cmd = (sender as? NSMenuItem)?.tag ?? (sender as? NSToolbarItem)?.tag ?? -1
        _ = run(cmd)
    }

    /// Runs command `cmd` when it is enabled (menu, toolbar, or a page-view key); returns
    /// whether it ran. Zoom and rotation from the menu and keys anchor at the window centre.
    @discardableResult
    func run(_ cmd: Int) -> Bool {
        guard isEnabled(cmd) else { return false }
        guard let doc = pdf else {
            AppDelegate.shared?.perform(cmd)
            return true
        }
        let page = pages.canvas.currentPage
        switch cmd {
        case Commands.id(SAFEPDF_CMD_CLOSE):
            window?.performClose(nil)
        case Commands.id(SAFEPDF_CMD_OUTLINE):
            split.toggleSidebar(nil)
        case Commands.id(SAFEPDF_CMD_NEXT_PAGE), Commands.id(SAFEPDF_CMD_PREV_PAGE):
            var info = safepdf_spread_info()
            guard safepdf_view_spread(SAFEPDF_SPREAD_NONE.rawValue, doc.pageCount, page, &info) == 0 else { return false }
            pages.scroll(toPage: cmd == Commands.id(SAFEPDF_CMD_NEXT_PAGE) ? info.next_page : info.prev_page)
        case Commands.id(SAFEPDF_CMD_FIRST_PAGE):
            pages.scroll(toPage: 0)
        case Commands.id(SAFEPDF_CMD_LAST_PAGE):
            pages.scroll(toPage: max(0, doc.pageCount - 1))
        case Commands.id(SAFEPDF_CMD_ZOOM_IN), Commands.id(SAFEPDF_CMD_ZOOM_OUT):
            pages.step(zoomIn: cmd == Commands.id(SAFEPDF_CMD_ZOOM_IN))
        case Commands.id(SAFEPDF_CMD_ACTUAL_SIZE):
            pages.setZoom(safepdf_zoom_choice(kind: SAFEPDF_ZOOM_ACTUAL.rawValue, pct: 0))
        case Commands.id(SAFEPDF_CMD_FIT_PAGE):
            pages.setZoom(safepdf_zoom_choice(kind: SAFEPDF_ZOOM_PAGE_FIT.rawValue, pct: 0))
        case Commands.id(SAFEPDF_CMD_FIT_WIDTH):
            pages.setZoom(safepdf_zoom_choice(kind: SAFEPDF_ZOOM_PAGE_WIDTH.rawValue, pct: 0))
        case Commands.id(SAFEPDF_CMD_ROTATE_CW), Commands.id(SAFEPDF_CMD_ROTATE_CCW):
            pages.rotate(clockwise: cmd == Commands.id(SAFEPDF_CMD_ROTATE_CW))
        default:
            AppDelegate.shared?.perform(cmd)
        }
        updateChrome()
        return true
    }

    /// An entry of the zoom drop-down (tag = index into Toolbar.ZoomChoice.presets).
    @objc func chooseZoomPreset(_ sender: Any?) {
        guard pdf != nil, let tag = (sender as? NSMenuItem)?.tag, let tb = chromeToolbar,
              tag >= 0, tag < tb.zoomPresets.count else { return }
        pages.setZoom(ZoomModel.choice(tb.zoomPresets[tag]))
        updateChrome()
    }

    @objc func performSafePdfAction(_ sender: Any?) {
        // TODO(11.3d): Find next / Find previous.
    }

    func validateMenuItem(_ item: NSMenuItem) -> Bool {
        if item.action == MainMenu.commandSelector { return isEnabled(item.tag) }
        if item.action == MainMenu.actionSelector { return false } // TODO(11.3d)
        if item.action == DocumentToolbar.zoomSelector { return pdf != nil }
        return true
    }

    func validateToolbarItem(_ item: NSToolbarItem) -> Bool {
        if item.action == MainMenu.commandSelector { return isEnabled(item.tag) }
        return item.isEnabled
    }

    // MARK: window delegate

    func windowDidChangeBackingProperties(_ notification: Notification) {
        // Retina ↔ non-Retina: layout and renders for the new pixels, centre kept in place.
        if pdf != nil { pages.backingChanged() }
    }

    func windowDidEndLiveResize(_ notification: Notification) {
        pages.liveResizeEnded()
    }

    func windowWillClose(_ notification: Notification) {
        pages.show(nil)
        pdf = nil
    }
}
