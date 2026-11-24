// DocumentWindowController.swift — the document window: unified toolbar, split view with the
// sidebar and the page area, command routing and enabled states (task 11.3b); the zoom and
// rotation commands, the zoom drop-down and the page view's keys (task 11.3c1); view modes and
// spreads, the page field, back/forward, open settings, the subtitle `page k/n · zoom`, the
// titlebar flags for repaired and encrypted files (task 11.3c2); Copy, Select All, Find and Find
// next / previous, the search field and the external-link sheet's window (task 11.3d1); the
// sidebar's panels, the page mode's panel, native full screen with the identity line (task
// 11.3d2, SidebarViewController, FullScreen.swift); Save, Save As…, XFDF import / export, the
// unsaved-marks question on close and on opening another file, the reopen after Save keeping
// the view (task 11.3e2, SaveController).
// Plan.md §6 Phase 11; docs/macos-design.md §2 (window with full-size content view, unified
// toolbar, title = document name with proxy icon; NSSplitViewController sidebar) and §3
// decision 1 (enabled rules from the exported Menu.Ctx table).

import AppKit
import SafePdfC

final class DocumentWindowController: NSWindowController, NSWindowDelegate, NSMenuItemValidation,
    NSToolbarItemValidation, SafePdfCommandTarget, ZoomPresetTarget, ViewChoiceTarget, MarksCommandTarget,
    SaveHost
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
    /// The 12.5 identity line in full screen (task 11.3d2).
    private var identity: IdentityLine?
    /// The document's `/PageMode /FullScreen` put the window in full screen: leaving applies
    /// `/NonFullScreenPageMode` to the sidebar (Viewer.setFullScreen).
    private var documentFullScreen = false
    /// Save, Save As…, XFDF and the unsaved-marks question (task 11.3e2), with sheets on this
    /// window.
    private(set) var saver = SaveController(dialogs: SheetDialogs(window: { nil }))
    /// The unsaved-marks question was answered for this close (the next close goes through).
    private var closeConfirmed = false

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
        wireText()
        pages.canvas.onKeyCommand = { [weak self] cmd in self?.run(cmd) ?? false }
        pages.canvas.onError = { [weak self] message in
            guard let self else { return }
            Sheets.error("Cannot show the document", detail: message, on: self.window)
        }
        window.collectionBehavior.insert(.fullScreenPrimary)
        identity = IdentityLine(pages: pages)
        wireSidebar()
        saver = SaveController(dialogs: SheetDialogs(window: { [weak self] in self?.window }))
        saver.host = self
        window.center()
        window.setFrameAutosaveName("SafePDFDocumentWindow")
        updateChrome()
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    /// Opens `url` in this window after the unsaved-marks question (Viewer.openDialog:
    /// confirmDiscard "opening another file"); errors from the C API appear as a sheet.
    func open(_ url: URL) {
        saver.confirmDiscard("opening another file") { [weak self] go in
            if go { self?.load(url) }
        }
    }

    /// Opens `url` once the unsaved-marks question was answered already (File → Open…).
    func openConfirmed(_ url: URL) { load(url) }

    /// The reopen after Save (task 11.3e2; Viewer.afterWrite): the written file, keeping the
    /// view mode, zoom, rotation, page, sidebar and layers (9.r8).
    func reopenAfterSave(_ url: URL, keep: KeptView?) -> Bool {
        load(url, keep: keep)
        return pdf?.url.standardizedFileURL == url.standardizedFileURL
    }

    /// Loads `url` into this window (no question); `keep`: the reopen after Save.
    private func load(_ url: URL, keep: KeptView? = nil) {
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
        // The reopen after a save keeps the layers' state (Tk 9.r11b).
        if keep != nil { doc.layers = pdf?.layers }
        pdf = doc
        window?.representedURL = url
        // `/DisplayDocTitle`: the document's `/Title` instead of the file name (task 9.r8).
        window?.title = doc.settings.title ?? url.lastPathComponent
        setFlags(repaired: doc.repaired, encrypted: doc.encrypted)
        pages.show(doc, keep: keep)
        sidebar.show(doc, pages: pages, keep: keep != nil)
        if keep == nil, doc.settings.centerWindow { window?.center() }
        window?.makeFirstResponder(pages.canvas)
        NSDocumentController.shared.noteNewRecentDocumentURL(url)
        doc.loadLabels { [weak self, weak doc] in
            guard let self, let doc, self.pdf === doc else { return }
            self.sidebar.labelsArrived()
            self.updateChrome()
        }
        updateChrome()
        if keep == nil { applyFullScreenSetting(doc) }
    }

    /// Task 11.3d1: the search field runs Find; the selection's changes update Copy's state;
    /// the external-link sheet attaches to this window.
    private func wireText() {
        chromeToolbar?.onSearch = { [weak self] text, forward in
            guard let self, self.pdf != nil else { return }
            self.pages.text.find.step(raw: text, forward: forward)
        }
        chromeToolbar?.onSearchCancel = { [weak self] in
            guard let self else { return }
            self.pages.text.find.close()
            self.window?.makeFirstResponder(self.pages.canvas)
        }
        chromeToolbar?.onSearchClear = { [weak self] in self?.pages.text.find.close() }
        let marksSel = pages.text.onSelectionChange
        pages.text.onSelectionChange = { [weak self] in
            marksSel?()
            self?.updateChrome()
        }
        pages.text.sheetWindow = { [weak self] in self?.window }
        // Task 11.3e1: marks change the edited dot, the Edit menu and the pressed tool; the
        // tools' pop-overs anchor to their buttons; Escape goes through the marks first.
        pages.marks.onChange = { [weak self] in self?.updateChrome() }
        pages.marks.toolbarItem = { [weak self] t in self?.chromeToolbar?.item(forTool: t) }
        pages.canvas.onEscape = { [weak self] in
            self?.escapeKey()
            return true
        }
    }

    /// Copy, Select All, Undo and Redo while text is being edited (the search or page field,
    /// the note editor, a free-text box) act on that text, not on the page's (task 11.3e1: the
    /// menu's commands reach this controller from the note popover's window too).
    private var fieldEditor: NSTextView? {
        let r = NSApp.keyWindow?.firstResponder ?? window?.firstResponder
        guard let t = r as? NSTextView, t.isEditable else { return nil }
        return t
    }

    /// Escape on the page view (Viewer.escape): the marks close their topmost transient and
    /// dismiss the bubble; when nothing was open, Escape leaves full screen.
    private func escapeKey() {
        if !pages.marks.escape(), let w = window, w.styleMask.contains(.fullScreen) {
            w.toggleFullScreen(nil)
        }
    }

    // MARK: marks (task 11.3e1)

    /// An entry of the highlight-colour submenu: `highlight COLOR` (Viewer.highlight).
    @objc func chooseHighlightColor(_ sender: Any?) {
        guard pdf != nil, let tag = (sender as? NSMenuItem)?.tag, (0..<5).contains(tag) else { return }
        pages.marks.highlight(Int32(tag))
        updateChrome()
    }

    /// A tool button of the toolbar (Viewer.tool).
    @objc func performSafePdfTool(_ sender: Any?) {
        guard pdf != nil, let tag = (sender as? NSToolbarItem)?.tag ?? (sender as? NSMenuItem)?.tag, tag >= 0
        else { return }
        pages.marks.tool(Int32(tag))
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
        var c = Self.context(pdf: pdf, pages: pages)
        if c.has_doc { c.has_outline = sidebar.content.has_outline }
        return c
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
            c.has_sel = pages.text.selection != nil
            // Task 11.3e1: the selected mark, undo / redo and unsaved changes (the store).
            c.has_mark = pages.marks.markSel != nil
            if let st = pages.marks.model?.state {
                c.dirty = st.dirty != 0
                c.can_undo = st.can_undo != 0
                c.can_redo = st.can_redo != 0
            }
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
        sidebar.isShown = !(sidebarItem?.isCollapsed ?? true)
        sidebar.sync()
        // Task 11.3e1: the edited dot (unsaved marks) and the pressed tool.
        window?.isDocumentEdited = pdf != nil && pages.marks.dirty
        chromeToolbar?.setPressedTool(Int32(pages.marks.pressedTool))
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
        if let ed = fieldEditor {
            if cmd == Commands.id(SAFEPDF_CMD_COPY) { ed.copy(nil); return true }
            if cmd == Commands.id(SAFEPDF_CMD_SELECT_ALL) { ed.selectAll(nil); return true }
            if cmd == Commands.id(SAFEPDF_CMD_UNDO) { ed.undoManager?.undo(); return true }
            if cmd == Commands.id(SAFEPDF_CMD_REDO) { ed.undoManager?.redo(); return true }
        }
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
                toggleSidebarPanel()
            case Commands.id(SAFEPDF_CMD_GOTO_PAGE):
                chromeToolbar?.focusPageField(in: window)
            case Commands.id(SAFEPDF_CMD_FIND):
                chromeToolbar?.focusSearch(in: window)
            case Commands.id(SAFEPDF_CMD_SAVE):
                saver.save()
            case Commands.id(SAFEPDF_CMD_SAVE_AS):
                saver.saveAs()
            case Commands.id(SAFEPDF_CMD_EXPORT_XFDF):
                saver.exportXfdf()
            case Commands.id(SAFEPDF_CMD_IMPORT_XFDF):
                saver.importXfdf()
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
        case Commands.id(SAFEPDF_CMD_COPY):
            pages.text.copy()
        case Commands.id(SAFEPDF_CMD_SELECT_ALL):
            pages.text.selectAll()
        case Commands.id(SAFEPDF_CMD_UNDO), Commands.id(SAFEPDF_CMD_REDO):
            pages.marks.undoRedo(undo: cmd == Commands.id(SAFEPDF_CMD_UNDO))
        case Commands.id(SAFEPDF_CMD_HIGHLIGHT):
            pages.marks.highlight(nil)
        case Commands.id(SAFEPDF_CMD_ADD_NOTE):
            pages.marks.addNote(at: nil)
        case Commands.id(SAFEPDF_CMD_DELETE_MARK):
            pages.marks.deleteSelected()
        case Commands.id(SAFEPDF_CMD_HL_TOOL):
            pages.marks.toggleHighlightTool()
        case Commands.id(SAFEPDF_CMD_SHOW_ALL):
            pages.marks.toggleShowAll()
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

    /// Find next / Find previous (⌘G / ⇧⌘G, Menu.Action): the search field's text, as the Tk
    /// key bindings use the find bar's.
    @objc func performSafePdfAction(_ sender: Any?) {
        guard pdf != nil, let tag = (sender as? NSMenuItem)?.tag else { return }
        let forward = tag == Int(SAFEPDF_ACTION_FIND_NEXT.rawValue)
        guard forward || tag == Int(SAFEPDF_ACTION_FIND_PREV.rawValue) else { return }
        pages.text.find.step(raw: chromeToolbar?.searchText ?? "", forward: forward)
    }

    func validateMenuItem(_ item: NSMenuItem) -> Bool {
        // While the page field has the focus, keys without Command or Control (Page Up/Down,
        // function keys) belong to it, not to the menu.
        if chromeToolbar?.isEditingPage == true || chromeToolbar?.isEditingSearch == true, !item.keyEquivalent.isEmpty,
           item.keyEquivalentModifierMask.intersection([.command, .control]).isEmpty {
            return false
        }
        if item.action == MainMenu.commandSelector {
            if let ed = fieldEditor {
                if item.tag == Commands.id(SAFEPDF_CMD_COPY) { return ed.selectedRange().length > 0 }
                if item.tag == Commands.id(SAFEPDF_CMD_SELECT_ALL) { return true }
                if item.tag == Commands.id(SAFEPDF_CMD_UNDO) { return ed.undoManager?.canUndo ?? false }
                if item.tag == Commands.id(SAFEPDF_CMD_REDO) { return ed.undoManager?.canRedo ?? false }
            }
            // The Edit menu's check entries (Menu.hlToolVar, showAllVar).
            if item.tag == Commands.id(SAFEPDF_CMD_HL_TOOL) {
                item.state = pdf != nil && pages.marks.ui.tool != 0 ? .on : .off
            }
            if item.tag == Commands.id(SAFEPDF_CMD_SHOW_ALL) {
                item.state = pdf != nil && pages.marks.ui.show_all != 0 ? .on : .off
            }
            if let on = Self.radioOn(item.tag, modes: pages.canvas.modes) {
                item.state = pdf != nil && on ? .on : .off
            }
            if item.tag == Commands.id(SAFEPDF_CMD_OUTLINE) { // a check entry (Menu.outlineVar)
                item.state = pdf != nil && !(sidebarItem?.isCollapsed ?? true) ? .on : .off
            }
            return isEnabled(item.tag)
        }
        if item.action == MainMenu.actionSelector { return pdf != nil }
        if item.action == MainMenu.colorSelector {
            item.state = pdf != nil && Int32(item.tag) == pages.marks.hlColor ? .on : .off
            return pdf != nil && pages.marks.model != nil
        }
        if item.action == DocumentToolbar.zoomSelector || item.action == DocumentToolbar.viewSelector {
            return pdf != nil
        }
        return true
    }

    func validateToolbarItem(_ item: NSToolbarItem) -> Bool {
        if item.action == MainMenu.commandSelector { return isEnabled(item.tag) }
        if item.action == MainMenu.toolSelector { return item.isEnabled && pages.marks.model != nil }
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

    /// ⌘W, the close button, File → Close: with unsaved marks the close waits for Save / Don't
    /// Save / Cancel (Viewer: confirmDiscard "closing").
    func windowShouldClose(_ sender: NSWindow) -> Bool {
        if closeConfirmed || pdf == nil || !pages.marks.dirty { return true }
        saver.confirmDiscard("closing") { [weak self] go in
            guard let self, go else { return }
            self.closeConfirmed = true
            self.window?.close()
        }
        return false
    }

    /// Quitting (Viewer: confirmDiscard "quitting"): `done` gets whether to go on.
    func confirmQuit(_ done: @escaping @MainActor (Bool) -> Void) {
        saver.confirmDiscard("quitting", done: done)
    }

    func windowWillClose(_ notification: Notification) {
        closeConfirmed = false
        identity?.sync(show: false, url: nil)
        pages.show(nil)
        sidebar.show(nil, pages: pages)
        pdf = nil
        setFlags(repaired: false, encrypted: false)
    }

    // MARK: sidebar (task 11.3d2)

    /// Connects the sidebar to the window: the page mode's panel on load, status notes in the
    /// pill, external outline links confirmed before their address is copied.
    private func wireSidebar() {
        sidebar.onLoaded = { [weak self] panel in
            guard let self else { return }
            // Full screen keeps the sidebar closed (Sidebar.onLoad gives none for FullScreen).
            self.setSidebar(shown: panel != nil)
        }
        sidebar.onStatus = { [weak self] s in self?.pages.pill.show(s) }
        sidebar.onChange = { [weak self] in self?.updateChrome() }
        sidebar.onExternalLink = { [weak self] uri in self?.confirmUri(uri) }
    }

    /// Opens (with its panel already chosen) or closes the sidebar.
    func setSidebar(shown: Bool) {
        guard let item = sidebarItem else { return }
        if item.isCollapsed == shown {
            if window?.isVisible == true { item.animator().isCollapsed = !shown } else { item.isCollapsed = !shown }
        }
        sidebar.isShown = shown
        updateChrome()
    }

    /// The sidebar toggle (F9, ⌃⌘S, View → Sidebar, the toolbar button; Sidebar.afterToggle):
    /// closes it, or opens it on the last panel chosen while the document has it.
    func toggleSidebarPanel() {
        let shown = !(sidebarItem?.isCollapsed ?? true)
        if !shown { sidebar.choose(sidebar.togglePanel) }
        setSidebar(shown: !shown)
    }

    /// An external address of an outline item (Viewer.confirmUri): copied to the clipboard only
    /// when the user confirms; never opened.
    private func confirmUri(_ uri: String) {
        guard let window else { return }
        Sheets.ask("Copy the link address?", detail: "The outline item points to an external address:\n\(uri)\n\nSafePDF never opens it.",
                   buttons: ["Copy Address", "Cancel"], on: window) { [weak self] i in
            if i == 0 {
                NSPasteboard.general.clearContents()
                NSPasteboard.general.setString(uri, forType: .string)
                self?.pages.pill.show("copied the link address to the clipboard (not opened): \(uri)")
            } else {
                self?.pages.pill.show("external link not followed: \(uri)")
            }
        }
    }

    // MARK: full screen (task 11.3d2; Viewer.setFullScreen, 12.5 syncIdentity)

    /// `/PageMode /FullScreen` (Viewer.applyOpenSettings): the window enters native full screen
    /// once it is on screen, with the sidebar closed. The identity line shows before it enters.
    private func applyFullScreenSetting(_ doc: Document) {
        guard doc.settings.pageMode == SAFEPDF_PAGE_MODE_FULL_SCREEN.rawValue, let window,
              !window.styleMask.contains(.fullScreen) else { return }
        DispatchQueue.main.async { [weak self, weak doc] in
            guard let self, let doc, self.pdf === doc, let w = self.window, w.isVisible,
                  !w.styleMask.contains(.fullScreen) else { return }
            self.documentFullScreen = true
            w.toggleFullScreen(nil)
        }
    }

    func windowWillEnterFullScreen(_ notification: Notification) {
        identity?.sync(show: pdf != nil, url: pdf?.url)
    }

    func windowDidFailToEnterFullScreen(_ window: NSWindow) {
        documentFullScreen = false
        identity?.sync(show: false, url: nil)
    }

    func windowDidExitFullScreen(_ notification: Notification) {
        identity?.sync(show: false, url: nil)
        // Leaving the document's full screen applies /NonFullScreenPageMode to the sidebar.
        if documentFullScreen, let doc = pdf {
            let p = SidebarRules.onLoad(pageMode: doc.settings.nonFullScreenMode, sidebar.content)
            if let p { sidebar.showPanel(p) }
            setSidebar(shown: p != nil)
        }
        documentFullScreen = false
    }

    /// Escape: the marks' transients first, then leaving full screen (the Tk viewer's escape and
    /// escapeWindow).
    override func cancelOperation(_ sender: Any?) {
        escapeKey()
    }
}
