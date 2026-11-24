// DocumentToolbar.swift — the unified toolbar built from the exported toolbar table
// (task 11.3b). Plan.md §6 Phase 11; docs/macos-design.md §2 ("NSToolbar with standard items;
// SF Symbols icons; ... same item order as the Tk bar; no user customisation"). Items and order
// come from safepdf_view_toolbar (Toolbar.layout), enabled and visible states from
// safepdf_view_states. The zoom drop-down chooses Toolbar.ZoomChoice presets (task 11.3c1); the
// page field is editable (Toolbar.pageEntry: Return jumps, Escape restores; page labels) and the
// view-mode drop-down chooses Toolbar.ViewChoice entries (task 11.3c2); the search field
// (NSSearchToolbarItem, after the table's items) runs Find (task 11.3d1: Return / ⇧Return find
// next / previous, Escape returns to the page); the tools are task 11.3e.

import AppKit
import SafePdfC

/// The zoom drop-down's entries send this up the responder chain (tag = preset index).
@MainActor @objc protocol ZoomPresetTarget {
    func chooseZoomPreset(_ sender: Any?)
}

/// The view-mode drop-down's entries send this up the responder chain (tag = the
/// Toolbar.ViewChoice index, safepdf_view_choice).
@MainActor @objc protocol ViewChoiceTarget {
    func chooseViewChoice(_ sender: Any?)
}

@MainActor final class DocumentToolbar: NSObject, NSToolbarDelegate, NSTextFieldDelegate, NSSearchFieldDelegate {
    static let zoomSelector = #selector(ZoomPresetTarget.chooseZoomPreset(_:))
    static let viewSelector = #selector(ViewChoiceTarget.chooseViewChoice(_:))
    /// Return in the page field, with its text.
    var onPageEntry: ((String) -> Void)?
    /// Escape in the page field (the window restores it and gives the page view the focus).
    var onPageCancel: (() -> Void)?
    /// The page field lost the focus (leaving it reverts it, as in the Tk viewer).
    var onPageLeave: (() -> Void)?
    /// Return (forward) or ⇧Return (backward) in the search field, with its text.
    var onSearch: ((String, Bool) -> Void)?
    /// Escape in the search field (the window closes the search and focuses the page view).
    var onSearchCancel: (() -> Void)?
    /// The search field's clear button (the search closes).
    var onSearchClear: (() -> Void)?
    /// The search field's identifier (not in the exported table: the Tk viewer's find bar).
    static let searchID = NSToolbarItem.Identifier("org.safe-pdf.toolbar.search")
    private var searchItem: NSSearchToolbarItem?
    private var viewMenuItem: NSMenuToolbarItem?
    private let viewChoices: [ViewChoiceSpec] = Chrome.viewChoices() ?? []
    /// The zoom drop-down's presets (Toolbar.ZoomChoice.presets), in menu order.
    let zoomPresets: [ZoomPresetSpec] = Chrome.zoomPresets() ?? []
    private var zoomMenuItem: NSMenuToolbarItem?
    let toolbar: NSToolbar
    private let specs: [ToolbarItemSpec]
    /// Item identifier per table index (nil for separators: NSToolbar has none).
    private var identifierOf: [Int: NSToolbarItem.Identifier] = [:]
    private var specOf: [NSToolbarItem.Identifier: Int] = [:]
    private var order: [NSToolbarItem.Identifier] = []
    private var items: [NSToolbarItem.Identifier: NSToolbarItem] = [:]
    private let pageField = NSTextField(string: "")
    private let ofLabel = NSTextField(labelWithString: "")
    /// The page field's width (fitPageField; "888" wide until a document is open).
    private lazy var pageWidth = pageField.widthAnchor.constraint(equalToConstant: Self.fieldWidth(for: ["888"], in: pageField))
    private var pageStack: NSStackView?
    private var fitKey = ""
    /// The gap between the page field and "of N".
    static let pageGap: CGFloat = 4
    /// The widest the page field gets (a longer label scrolls inside it).
    static let pageFieldMax: CGFloat = 96
    /// macOS 26 (Liquid Glass toolbar): the page field draws no bezel of its own.
    static var borderlessPageField: Bool {
        if #available(macOS 26, *) { return true }
        return false
    }
    private var lastStates: ChromeStates?

    /// The SF Symbol for a Tk icon name.
    static func symbol(for icon: String) -> String {
        switch icon {
        case "sidebar": return "sidebar.left"
        case "up": return "chevron.up"
        case "down": return "chevron.down"
        case "minus": return "minus.magnifyingglass"
        case "plus": return "plus.magnifyingglass"
        case "select": return "character.cursor.ibeam"
        case "highlight": return "highlighter"
        case "comment": return "text.bubble"
        case "text": return "textformat"
        case "draw": return "pencil.tip"
        case "image": return "photo"
        case "print": return "printer"
        case "save": return "square.and.arrow.down"
        case "more": return "ellipsis.circle"
        default: return "questionmark.square.dashed"
        }
    }

    /// nil when the toolbar table cannot be read.
    init?(identifier: String) {
        guard let specs = Chrome.toolbar() else { return nil }
        self.specs = specs
        toolbar = NSToolbar(identifier: identifier)
        super.init()
        var lastGroup: UInt32? = nil
        for (i, s) in specs.enumerated() {
            if let g = lastGroup, g != s.group { order.append(.flexibleSpace) }
            lastGroup = s.group
            guard s.kind != SAFEPDF_ITEM_SEPARATOR.rawValue else { continue }
            let id = NSToolbarItem.Identifier("org.safe-pdf.toolbar.\(s.id)")
            identifierOf[i] = id
            specOf[id] = i
            order.append(id)
            if s.action == SAFEPDF_ACT_COMMAND.rawValue && s.cmd == Int32(Commands.id(SAFEPDF_CMD_OUTLINE)) {
                order.append(.sidebarTrackingSeparator)
            }
        }
        toolbar.delegate = self
        toolbar.allowsUserCustomization = false
        toolbar.displayMode = .iconOnly
    }

    /// Item identifiers in table order (the self-test checks every one builds).
    var identifiers: [NSToolbarItem.Identifier] { order }

    func toolbarDefaultItemIdentifiers(_ toolbar: NSToolbar) -> [NSToolbarItem.Identifier] {
        order + [Self.searchID]
    }

    func toolbarAllowedItemIdentifiers(_ toolbar: NSToolbar) -> [NSToolbarItem.Identifier] {
        order + [Self.searchID]
    }

    func toolbar(_ toolbar: NSToolbar, itemForItemIdentifier itemIdentifier: NSToolbarItem.Identifier,
                 willBeInsertedIntoToolbar flag: Bool) -> NSToolbarItem? {
        makeItem(itemIdentifier)
    }

    /// Builds (once) the item for an identifier.
    func makeItem(_ id: NSToolbarItem.Identifier) -> NSToolbarItem? {
        if let it = items[id] { return it }
        if id == Self.searchID {
            let item = searchToolbarItem()
            items[id] = item
            return item
        }
        guard let i = specOf[id] else { return nil }
        let s = specs[i]
        let item: NSToolbarItem
        switch s.kind {
        case SAFEPDF_ITEM_PAGE_FIELD.rawValue:
            item = pageFieldItem(id)
        case SAFEPDF_ITEM_ZOOM_BOX.rawValue:
            item = zoomItem(id)
        case SAFEPDF_ITEM_VIEW_BOX.rawValue:
            item = viewItem(id)
        default:
            item = buttonItem(id, s)
        }
        item.autovalidates = false
        if let st = lastStates { apply(st, to: item, index: i) }
        items[id] = item
        return item
    }

    private func label(_ tooltip: String) -> String {
        // "Save (⌘S)" → "Save"
        if let r = tooltip.range(of: " (") { return String(tooltip[..<r.lowerBound]) }
        return tooltip
    }

    private func buttonItem(_ id: NSToolbarItem.Identifier, _ s: ToolbarItemSpec) -> NSToolbarItem {
        let image = NSImage(systemSymbolName: Self.symbol(for: s.icon), accessibilityDescription: label(s.tooltip))
        if s.action == SAFEPDF_ACT_MORE.rawValue {
            let item = NSMenuToolbarItem(itemIdentifier: id)
            item.image = image
            item.label = label(s.tooltip)
            item.toolTip = s.tooltip
            item.showsIndicator = false
            item.menu = overflowMenu()
            return item
        }
        let item = NSToolbarItem(itemIdentifier: id)
        item.image = image
        item.label = label(s.tooltip)
        item.toolTip = s.tooltip
        item.isBordered = true
        if s.action == SAFEPDF_ACT_COMMAND.rawValue {
            item.action = MainMenu.commandSelector
            item.tag = Int(s.cmd)
        } else if s.action == SAFEPDF_ACT_TOOL.rawValue {
            // Task 11.3e1: the tools (Toolbar.Tool; the active mode's button shows pressed).
            item.action = MainMenu.toolSelector
            item.tag = Int(s.tool)
            toolItems[s.tool] = item
            toolSymbols[s.tool] = Self.symbol(for: s.icon)
        } else {
            item.action = nil
            item.tag = -1
        }
        return item
    }

    /// The tool buttons by tool (safepdf_tool), once built.
    private var toolItems: [Int32: NSToolbarItem] = [:]
    private var toolSymbols: [Int32: String] = [:]
    private var pressed: Int32 = -1

    /// The toolbar item of a tool (a pop-over's anchor).
    func item(forTool t: Int32) -> NSToolbarItem? {
        if toolItems[t] == nil, let i = specs.firstIndex(where: { $0.action == SAFEPDF_ACT_TOOL.rawValue && $0.tool == t }),
           let id = identifierOf[i] {
            _ = makeItem(id)
        }
        return toolItems[t]
    }

    /// Shows tool `t`'s button pressed (Toolbar.pressed: exactly the active mode's), in the
    /// accent colour.
    func setPressedTool(_ t: Int32) {
        pressed = t
        for (tool, item) in toolItems {
            guard let name = toolSymbols[tool],
                  let base = NSImage(systemSymbolName: name, accessibilityDescription: item.label) else { continue }
            if tool == t {
                let cfg = NSImage.SymbolConfiguration(hierarchicalColor: .controlAccentColor)
                item.image = base.withSymbolConfiguration(cfg) ?? base
            } else {
                item.image = base
            }
        }
    }

    /// The tool shown pressed (the self-test reads it).
    var pressedTool: Int32 { pressed }

    /// The overflow menu (Toolbar.overflow) from its exported table.
    private func overflowMenu() -> NSMenu {
        let menu = NSMenu(title: "Tools")
        guard let t = Chrome.overflowMenu() else { return menu }
        for e in t.entries {
            if e.kind == SAFEPDF_ENTRY_SEPARATOR.rawValue {
                if let last = menu.items.last, !last.isSeparatorItem { menu.addItem(.separator()) }
            } else if e.cmd >= 0 {
                let item = NSMenuItem(title: e.label, action: MainMenu.commandSelector, keyEquivalent: "")
                item.tag = e.cmd
                menu.addItem(item)
            } else {
                let item = NSMenuItem(title: e.label, action: nil, keyEquivalent: "")
                item.isEnabled = false
                menu.addItem(item)
            }
        }
        return menu
    }

    private func pageFieldItem(_ id: NSToolbarItem.Identifier) -> NSToolbarItem {
        pageField.isEditable = true
        pageField.isSelectable = true
        pageField.alignment = .right
        pageField.bezelStyle = .roundedBezel
        pageField.delegate = self
        pageField.usesSingleLineMode = true
        pageField.cell?.isScrollable = true
        pageField.toolTip = "Page (Return goes there, Escape restores)"
        pageField.setAccessibilityLabel("Page")
        // Task 11.6a: the field is as wide as the document's widest entry (fitPageField), not a
        // fixed wide box, and "of N" follows it closely; the stack hugs its content so the
        // toolbar (and the macOS 26 glass capsule) does not stretch it.
        pageField.alignment = .center
        // On macOS 26 the toolbar's glass capsule is the field's visual frame: the rounded bezel is
        // not drawn there but its padding was still reserved, which left a visible gap between the
        // previous/next chevrons and the number (the human's check, 2026-11-24). There the field is
        // borderless, sized to its text, and the number sits right next to "of N".
        if Self.borderlessPageField {
            pageField.isBordered = false
            pageField.drawsBackground = false
            pageField.focusRingType = .default
            pageField.alignment = .right
            pageWidth.constant = Self.fieldWidth(for: ["888"], in: pageField)
        }
        pageWidth.isActive = true
        pageField.setContentHuggingPriority(.required, for: .horizontal)
        ofLabel.textColor = .secondaryLabelColor
        ofLabel.setContentHuggingPriority(.required, for: .horizontal)
        ofLabel.setContentCompressionResistancePriority(.required, for: .horizontal)
        let stack = NSStackView(views: [pageField, ofLabel])
        stack.orientation = .horizontal
        stack.alignment = .centerY
        stack.spacing = Self.pageGap
        stack.setHuggingPriority(.required, for: .horizontal)
        pageStack = stack
        let item = NSToolbarItem(itemIdentifier: id)
        item.view = stack
        item.label = "Page"
        item.toolTip = "Page"
        return item
    }

    private func zoomItem(_ id: NSToolbarItem.Identifier) -> NSToolbarItem {
        let item = NSMenuToolbarItem(itemIdentifier: id)
        let menu = NSMenu(title: "Zoom")
        for (i, p) in zoomPresets.enumerated() {
            let mi = NSMenuItem(title: p.label, action: Self.zoomSelector, keyEquivalent: "")
            mi.tag = i
            mi.state = p.kind == SAFEPDF_ZOOM_AUTO.rawValue ? .on : .off
            menu.addItem(mi)
            // The named choices, a separator, the percentages.
            let pctKind = SAFEPDF_ZOOM_PERCENT.rawValue
            if p.kind != pctKind, i + 1 < zoomPresets.count, zoomPresets[i + 1].kind == pctKind {
                menu.addItem(.separator())
            }
        }
        item.menu = menu
        item.title = menu.items.first(where: { $0.state == .on })?.title ?? "Zoom"
        item.label = "Zoom"
        item.toolTip = "Zoom"
        zoomMenuItem = item
        return item
    }

    private func viewItem(_ id: NSToolbarItem.Identifier) -> NSToolbarItem {
        let item = NSMenuToolbarItem(itemIdentifier: id)
        let menu = NSMenu(title: "View mode")
        for c in viewChoices {
            let mi = NSMenuItem(title: c.label, action: Self.viewSelector, keyEquivalent: "")
            mi.tag = Int(c.choice)
            mi.image = NSImage(systemSymbolName: Self.viewSymbol(c.choice), accessibilityDescription: c.label)
            menu.addItem(mi)
        }
        item.menu = menu
        item.label = "View mode"
        viewMenuItem = item
        setViewChoice(ViewModes.start.choice)
        return item
    }

    /// The SF Symbol of a view-mode choice.
    static func viewSymbol(_ choice: UInt32) -> String {
        switch choice {
        case SAFEPDF_VIEW_SINGLE.rawValue: return "doc"
        case SAFEPDF_VIEW_TWO.rawValue: return "book"
        case SAFEPDF_VIEW_TWO_SCROLL.rawValue: return "rectangle.split.2x2"
        default: return "rectangle.split.1x2"
        }
    }

    /// Shows the view-mode choice (Toolbar.ViewChoice.ofModes): its entry checked, its icon and
    /// "View mode: LABEL" as the tooltip (the Tk drop-down's).
    func setViewChoice(_ choice: UInt32) {
        guard let item = viewMenuItem else { return }
        var label = ""
        for mi in item.menu.items where mi.action == Self.viewSelector {
            mi.state = UInt32(mi.tag) == choice ? .on : .off
            if UInt32(mi.tag) == choice { label = mi.title }
        }
        item.image = NSImage(systemSymbolName: Self.viewSymbol(choice), accessibilityDescription: "View mode")
        item.toolTip = "View mode: \(label)"
    }

    /// The view-mode drop-down's checked entry (the self-test checks it).
    var viewChoiceShown: UInt32? {
        viewMenuItem?.menu.items.first(where: { $0.state == .on }).map { UInt32($0.tag) }
    }

    /// Applies enabled / visible states (and whether this shell implements the command).
    func apply(_ states: ChromeStates) {
        lastStates = states
        for (i, id) in identifierOf {
            if let item = items[id] { apply(states, to: item, index: i) }
        }
    }

    private func apply(_ st: ChromeStates, to item: NSToolbarItem, index i: Int) {
        let s = specs[i]
        guard s.kind == SAFEPDF_ITEM_BUTTON.rawValue else { return }
        var enabled = i < st.itemEnabled.count ? st.itemEnabled[i] : false
        if s.action == SAFEPDF_ACT_COMMAND.rawValue {
            enabled = enabled && Commands.implemented.contains(Int(s.cmd))
        }
        item.isEnabled = enabled
        item.isHidden = i < st.itemVisible.count ? !st.itemVisible[i] : false
    }

    /// Shows the zoom choice: its entry checked, its label (ZoomChoice.label, e.g. "137%" after a
    /// pinch) as the drop-down's title.
    func setZoom(_ c: safepdf_zoom_choice) {
        guard let item = zoomMenuItem else { return }
        for mi in item.menu.items where mi.action == Self.zoomSelector && mi.tag < zoomPresets.count {
            mi.state = ZoomModel.same(ZoomModel.choice(zoomPresets[mi.tag]), c) ? .on : .off
        }
        item.title = ZoomModel.label(c)
    }

    /// The zoom drop-down's title (the self-test checks it).
    var zoomTitle: String? { zoomMenuItem?.title }

    /// Shows the page field's texts (safepdf_view_page_field); empty without a document. The
    /// field is left alone while it is being edited (unless `force`).
    func setPage(entry: String, of: String, force: Bool = false) {
        if force || !isEditingPage { pageField.stringValue = entry }
        ofLabel.stringValue = of
        pageField.isEnabled = !of.isEmpty
    }

    /// The width the page field needs for the widest of `entries` (its font, its bezel and
    /// text insets), between two digits' width and `pageFieldMax`.
    static func fieldWidth(for entries: [String], in field: NSTextField) -> CGFloat {
        let font = field.font ?? .systemFont(ofSize: NSFont.systemFontSize)
        let attrs: [NSAttributedString.Key: Any] = [.font: font]
        func w(_ s: String) -> CGFloat { (s as NSString).size(withAttributes: attrs).width }
        var text = w("88")
        for e in entries { text = max(text, w(e)) }
        if borderlessPageField {
            // No bezel: only the text cell's own inset (2 pt a side) and room for the caret.
            return min(Self.pageFieldMax, ceil(text + 6))
        }
        let probe = NSTextField(string: "8")
        probe.font = font
        probe.bezelStyle = .roundedBezel
        let pad = max(8, (probe.cell?.cellSize.width ?? 0) - w("8"))
        return min(Self.pageFieldMax, ceil(text + pad + 2))
    }

    /// Sizes the page field for the document: its widest page label or number (Toolbar.entryText
    /// shows one of them). Measured once per document and once more when its labels arrive.
    func fitPageField(labels: [String], pages: Int) {
        let key = "\(pages):\(labels.count):\(labels.lazy.map(\.utf16.count).max() ?? 0)"
        guard key != fitKey else { return }
        fitKey = key
        var entries = [String(max(pages, 1))]
        entries += labels.prefix(100_000)
        pageWidth.constant = Self.fieldWidth(for: entries, in: pageField)
        pageStack?.layoutSubtreeIfNeeded()
    }

    /// The page field's width and the gap from its right edge to "of N" (the self-test).
    var pageFieldMetrics: (width: CGFloat, gap: CGFloat) {
        pageStack?.layoutSubtreeIfNeeded()
        return (pageWidth.constant, ofLabel.frame.minX - pageField.frame.maxX)
    }

    /// Whether the page field has the keyboard focus (its keys stay out of the page view and
    /// the menu's plain key equivalents).
    var isEditingPage: Bool { pageField.currentEditor() != nil }

    /// The page field's texts (the self-test reads them).
    var pageTexts: (entry: String, of: String) { (pageField.stringValue, ofLabel.stringValue) }

    /// Go to page…: the page field takes the focus with its text selected (PDF.js).
    func focusPageField(in window: NSWindow?) {
        guard let window, pageField.window === window else { return }
        window.makeFirstResponder(pageField)
        pageField.selectText(nil)
    }

    // MARK: search field (task 11.3d1)

    private func searchToolbarItem() -> NSSearchToolbarItem {
        let item = NSSearchToolbarItem(itemIdentifier: Self.searchID)
        let f = item.searchField
        f.placeholderString = "Find"
        f.sendsWholeSearchString = true
        f.sendsSearchStringImmediately = false
        f.delegate = self
        f.target = self
        f.action = #selector(searchFieldAction(_:))
        f.toolTip = "Find in the document (Return: next, ⇧Return: previous, Escape: back to the page)"
        f.setAccessibilityLabel("Find")
        item.label = "Find"
        item.toolTip = f.toolTip
        searchItem = item
        return item
    }

    /// The search field's text ("" without the item).
    var searchText: String { searchItem?.searchField.stringValue ?? "" }

    /// Whether the search field has the keyboard focus.
    var isEditingSearch: Bool { searchItem?.searchField.currentEditor() != nil }

    /// Find… (⌘F): the search field takes the focus with its text selected.
    func focusSearch(in window: NSWindow?) {
        guard let window, let item = searchItem, item.searchField.window === window else { return }
        item.beginSearchInteraction()
        window.makeFirstResponder(item.searchField)
        item.searchField.selectText(nil)
    }

    /// The field's action: only its clear button gets here (Return is taken below).
    @objc private func searchFieldAction(_ sender: NSSearchField) {
        if sender.stringValue.isEmpty { onSearchClear?() }
    }

    /// Return and Escape in the page field and the search field (other keys edit the text).
    func control(_ control: NSControl, textView: NSTextView, doCommandBy commandSelector: Selector) -> Bool {
        if let f = searchItem?.searchField, control === f {
            if commandSelector == #selector(NSResponder.insertNewline(_:)) {
                let back = NSApp.currentEvent?.modifierFlags.contains(.shift) ?? false
                onSearch?(f.stringValue, !back)
                return true
            }
            if commandSelector == #selector(NSResponder.cancelOperation(_:)) {
                onSearchCancel?()
                return true
            }
            return false
        }
        guard control === pageField else { return false }
        if commandSelector == #selector(NSResponder.insertNewline(_:)) {
            onPageEntry?(pageField.stringValue)
            return true
        }
        if commandSelector == #selector(NSResponder.cancelOperation(_:)) {
            onPageCancel?()
            return true
        }
        return false
    }

    /// Leaving the page field (a click elsewhere, Tab): it reverts to the current page.
    func controlTextDidEndEditing(_ obj: Notification) {
        guard (obj.object as? NSTextField) === pageField else { return }
        onPageLeave?()
    }

    /// Typing into the page field (the self-test's path for Return / Escape without a window).
    func typePage(_ text: String, commit: Bool) {
        pageField.stringValue = text
        if commit { onPageEntry?(text) } else { onPageCancel?() }
    }
}
