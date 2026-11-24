// DocumentWindowController.swift — the document window: unified toolbar, split view with the
// sidebar and the page area, command routing and enabled states (task 11.3b); the zoom and
// rotation commands, the zoom drop-down and the page view's keys (task 11.3c1); view modes and
// spreads, the page field, back/forward, open settings, the subtitle `page k/n · zoom`, the
// titlebar flags for repaired and encrypted files (task 11.3c2).
// Plan.md §6 Phase 11; docs/macos-design.md §2 (window with full-size content view, unified
// toolbar, title = document name with proxy icon; NSSplitViewController sidebar) and §3
// decision 1 (enabled rules from the exported Menu.Ctx table).

import AppKit
import SafePdfC

final class DocumentWindowController: NSWindowController, NSWindowDelegate, NSMenuItemValidation,
    NSToolbarItemValidation, SafePdfCommandTarget, ZoomPresetTarget, ViewChoiceTarget
{
    let pages = PageViewController()
    let sidebar = SidebarViewController()
    private let split = NSSplitViewController()
    private var sidebarItem: NSSplitViewItem?
    private var chromeToolbar: DocumentToolbar?
    /// The open PDF (not NSWindowController.document, which is for NSDocument).
    private(set) var pdf: Document?
    private var states: ChromeStates?
    private var flagsAccessory: NSTitlebarAccessoryViewController?

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
        chromeToolbar?.onPageEntry = { [weak self] text in self?.pageEntry(text) }
        chromeToolbar?.onPageCancel = { [weak self] in self?.pageFieldDone() }
        chromeToolbar?.onPageLeave = { [weak self] in self?.revertPageField() }
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
        // `/DisplayDocTitle`: the document's `/Title` instead of the file name (task 9.r8).
        window?.title = doc.settings.title ?? url.lastPathComponent
        setFlags(repaired: doc.repaired, encrypted: doc.encrypted)
        pages.show(doc)
        if doc.settings.centerWindow { window?.center() }
        window?.makeFirstResponder(pages.canvas)
        NSDocumentController.shared.noteNewRecentDocumentURL(url)
        doc.loadLabels { [weak self, weak doc] in
            guard let self, let doc, self.pdf === doc else { return }
            self.updateChrome()
        }
        updateChrome()
    }

    // MARK: titlebar flags

    /// The persistent flags (docs/macos-design.md §2): a small titlebar accessory saying the file
    /// was repaired and / or is encrypted; none for a plain file.
    private func setFlags(repaired: Bool, encrypted: Bool) {
        if let old = flagsAccessory, let i = window?.titlebarAccessoryViewControllers.firstIndex(of: old) {
            window?.removeTitlebarAccessoryViewController(at: i)
        }
        flagsAccessory = nil
        guard let window, let view = Self.flagsView(repaired: repaired, encrypted: encrypted) else { return }
        let acc = NSTitlebarAccessoryViewController()
        acc.view = view
        acc.layoutAttribute = .trailing
        #if compiler(>=6.2) // the macOS 26 SDK: the scroll-edge effect under the accessory
        if #available(macOS 26.1, *) { acc.preferredScrollEdgeEffectStyle = .soft }
        #endif
        window.addTitlebarAccessoryViewController(acc)
        flagsAccessory = acc
    }

    /// The flags' view (nil: nothing to flag). Each flag is an SF Symbol and a word, with a
    /// tooltip that says what it means.
    static func flagsView(repaired: Bool, encrypted: Bool) -> NSView? {
        var views: [NSView] = []
        func flag(_ symbol: String, _ text: String, _ tip: String) {
            let image = NSImageView(image: NSImage(systemSymbolName: symbol, accessibilityDescription: text) ?? NSImage())
            image.contentTintColor = .secondaryLabelColor
            let label = NSTextField(labelWithString: text)
            label.font = .systemFont(ofSize: NSFont.smallSystemFontSize)
            label.textColor = .secondaryLabelColor
            let stack = NSStackView(views: [image, label])
            stack.spacing = 3
            stack.toolTip = tip
            stack.setAccessibilityElement(true)
            stack.setAccessibilityLabel("\(text): \(tip)")
            views.append(stack)
        }
        if repaired {
            flag("wrench.adjustable", "Repaired",
                 "The file is damaged; it was opened by the repair path and may not show as its author intended.")
        }
        if encrypted {
            flag("lock", "Encrypted", "The file is encrypted (opened with the empty user password).")
        }
        guard !views.isEmpty else { return nil }
        let stack = NSStackView(views: views)
        stack.spacing = 10
        stack.edgeInsets = NSEdgeInsets(top: 0, left: 8, bottom: 0, right: 10)
        stack.frame = NSRect(origin: .zero, size: stack.fittingSize)
        return stack
    }

    // MARK: chrome states

    /// What the enabled rules look at (Viewer.menuCtx): first and last spread, history.
    private func context() -> safepdf_ctx {
        Self.context(pdf: pdf, pages: pages)
    }

    /// Menu.Ctx of a page view (the self-test checks it without a window).
    static func context(pdf: Document?, pages: PageViewController) -> safepdf_ctx {
        var c = safepdf_ctx()
        if let doc = pdf, doc.pageCount > 0 {
            let page = pages.canvas.currentPage
            c.has_doc = true
            c.page = page
            c.pages = doc.pageCount
            if let info = pages.spreadInfo {
                c.on_first = info.spread == 0
                c.on_last = info.spread + 1 >= info.spread_count
            }
            c.can_back = pages.history.canBack
            c.can_forward = pages.history.canForward
            // TODO(11.3d/e): outline, selection, marks, undo and dirty flags.
        }
        return c
    }

    /// The window subtitle: the page as the Tk title shows it (Links.pageText, with labels) and
    /// the zoom, `page iii (3/120) · 150%`.
    static func subtitle(pdf: Document?, pages: PageViewController) -> String {
        guard let doc = pdf, doc.pageCount > 0 else { return "" }
        let text = PageText.of(labels: doc.labels, page: pages.canvas.currentPage, pages: doc.pageCount)
        return text + (pages.shownPct.map { " · \($0)%" } ?? "")
    }

    /// Recomputes enabled states (safepdf_view_states), the page field, the view-mode and zoom
    /// drop-downs and the subtitle.
    func updateChrome() {
        states = Chrome.states(context())
        if let st = states { chromeToolbar?.apply(st) }
        if let doc = pdf, doc.pageCount > 0 {
            let f = PageText.field(labels: doc.labels, page: pages.canvas.currentPage, pages: doc.pageCount)
            chromeToolbar?.setPage(entry: f.entry, of: f.of)
        } else {
            chromeToolbar?.setPage(entry: "", of: "", force: true)
        }
        window?.subtitle = Self.subtitle(pdf: pdf, pages: pages)
        chromeToolbar?.setZoom(pages.canvas.zoomChoice)
        chromeToolbar?.setViewChoice(pages.canvas.modes.choice)
    }

    // MARK: page field (Toolbar.pageEntry)

    /// Return in the page field (Viewer.pageEntry): a label or number jumps there (recorded in
    /// the history); an invalid entry reverts the field and the pill says why.
    private func pageEntry(_ text: String) {
        pages.pageEntry(text)
        pageFieldDone()
    }

    /// Leaves the page field: its text shows the current page again, the page view has the
    /// focus.
    private func pageFieldDone() {
        window?.makeFirstResponder(pages.canvas)
        revertPageField()
    }

    /// The page field shows the current page again.
    private func revertPageField() {
        if let doc = pdf, doc.pageCount > 0 {
            let f = PageText.field(labels: doc.labels, page: pages.canvas.currentPage, pages: doc.pageCount)
            chromeToolbar?.setPage(entry: f.entry, of: f.of, force: true)
        }
        updateChrome()
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
        guard pdf != nil else {
            AppDelegate.shared?.perform(cmd)
            return true
        }
        guard Self.perform(cmd, pages: pages) else {
            switch cmd {
            case Commands.id(SAFEPDF_CMD_CLOSE):
                window?.performClose(nil)
            case Commands.id(SAFEPDF_CMD_OUTLINE):
                split.toggleSidebar(nil)
            case Commands.id(SAFEPDF_CMD_GOTO_PAGE):
                chromeToolbar?.focusPageField(in: window)
            default:
                AppDelegate.shared?.perform(cmd)
            }
            updateChrome()
            return true
        }
        updateChrome()
        return true
    }

    /// The page view's commands (navigation, view modes, zoom, rotation), shared with the
    /// self-test: returns false for a command that is not one of them.
    static func perform(_ cmd: Int, pages: PageViewController) -> Bool {
        guard let doc = pages.canvas.document else { return false }
        var modes = pages.canvas.modes
        switch cmd {
        case Commands.id(SAFEPDF_CMD_NEXT_PAGE), Commands.id(SAFEPDF_CMD_PREV_PAGE):
            guard let info = pages.spreadInfo else { return true }
            pages.goTo(cmd == Commands.id(SAFEPDF_CMD_NEXT_PAGE) ? info.next_page : info.prev_page)
        case Commands.id(SAFEPDF_CMD_FIRST_PAGE):
            pages.goTo(0)
        case Commands.id(SAFEPDF_CMD_LAST_PAGE):
            pages.goTo(max(0, doc.pageCount - 1))
        case Commands.id(SAFEPDF_CMD_BACK), Commands.id(SAFEPDF_CMD_FORWARD):
            pages.historyMove(back: cmd == Commands.id(SAFEPDF_CMD_BACK))
        case Commands.id(SAFEPDF_CMD_SCROLL_PAGE), Commands.id(SAFEPDF_CMD_SCROLL_VERTICAL):
            modes.scroll = cmd == Commands.id(SAFEPDF_CMD_SCROLL_PAGE)
                ? SAFEPDF_SCROLL_PAGE.rawValue : SAFEPDF_SCROLL_VERTICAL.rawValue
            pages.setModes(modes)
        case Commands.id(SAFEPDF_CMD_SPREAD_NONE):
            modes.spread = SAFEPDF_SPREAD_NONE.rawValue
            pages.setModes(modes)
        case Commands.id(SAFEPDF_CMD_SPREAD_ODD):
            modes.spread = SAFEPDF_SPREAD_ODD.rawValue
            pages.setModes(modes)
        case Commands.id(SAFEPDF_CMD_SPREAD_EVEN):
            modes.spread = SAFEPDF_SPREAD_EVEN.rawValue
            pages.setModes(modes)
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
            return false
        }
        return true
    }

    /// Whether a view-mode command's radio entry is on (Menu.Cmd.radio: the mode it sets is
    /// the current one); nil for other commands.
    static func radioOn(_ cmd: Int, modes m: ViewModes) -> Bool? {
        switch cmd {
        case Commands.id(SAFEPDF_CMD_SCROLL_PAGE): return m.scroll == SAFEPDF_SCROLL_PAGE.rawValue
        case Commands.id(SAFEPDF_CMD_SCROLL_VERTICAL): return m.scroll == SAFEPDF_SCROLL_VERTICAL.rawValue
        case Commands.id(SAFEPDF_CMD_SPREAD_NONE): return m.spread == SAFEPDF_SPREAD_NONE.rawValue
        case Commands.id(SAFEPDF_CMD_SPREAD_ODD): return m.spread == SAFEPDF_SPREAD_ODD.rawValue
        case Commands.id(SAFEPDF_CMD_SPREAD_EVEN): return m.spread == SAFEPDF_SPREAD_EVEN.rawValue
        default: return nil
        }
    }

    /// An entry of the view-mode drop-down (tag = Toolbar.ViewChoice index; ViewChoice.modes).
    @objc func chooseViewChoice(_ sender: Any?) {
        guard pdf != nil, let tag = (sender as? NSMenuItem)?.tag, tag >= 0,
              let m = pages.canvas.modes.choosing(UInt32(tag)) else { return }
        pages.setModes(m)
        updateChrome()
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
        // While the page field has the focus, keys without Command or Control (Page Up/Down,
        // function keys) belong to it, not to the menu.
        if chromeToolbar?.isEditingPage == true, !item.keyEquivalent.isEmpty,
           item.keyEquivalentModifierMask.intersection([.command, .control]).isEmpty {
            return false
        }
        if item.action == MainMenu.commandSelector {
            if let on = Self.radioOn(item.tag, modes: pages.canvas.modes) {
                item.state = pdf != nil && on ? .on : .off
            }
            return isEnabled(item.tag)
        }
        if item.action == MainMenu.actionSelector { return false } // TODO(11.3d)
        if item.action == DocumentToolbar.zoomSelector || item.action == DocumentToolbar.viewSelector {
            return pdf != nil
        }
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
        setFlags(repaired: false, encrypted: false)
    }
}
