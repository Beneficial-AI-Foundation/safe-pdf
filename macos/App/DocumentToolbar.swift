// DocumentToolbar.swift — the unified toolbar built from the exported toolbar table
// (task 11.3b). Plan.md §6 Phase 11; docs/macos-design.md §2 ("NSToolbar with standard items;
// SF Symbols icons; ... same item order as the Tk bar; no user customisation"). Items and order
// come from safepdf_view_toolbar (Toolbar.layout), enabled and visible states from
// safepdf_view_states. The zoom drop-down chooses Toolbar.ZoomChoice presets (task 11.3c1); the
// page field is editable (Toolbar.pageEntry: Return jumps, Escape restores; page labels) and the
// view-mode drop-down chooses Toolbar.ViewChoice entries (task 11.3c2); the tools are task 11.3e.

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

@MainActor final class DocumentToolbar: NSObject, NSToolbarDelegate, NSTextFieldDelegate {
    static let zoomSelector = #selector(ZoomPresetTarget.chooseZoomPreset(_:))
    static let viewSelector = #selector(ViewChoiceTarget.chooseViewChoice(_:))
    /// Return in the page field, with its text.
    var onPageEntry: ((String) -> Void)?
    /// Escape in the page field (the window restores it and gives the page view the focus).
    var onPageCancel: (() -> Void)?
    /// The page field lost the focus (leaving it reverts it, as in the Tk viewer).
    var onPageLeave: (() -> Void)?
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

    func toolbarDefaultItemIdentifiers(_ toolbar: NSToolbar) -> [NSToolbarItem.Identifier] { order }

    func toolbarAllowedItemIdentifiers(_ toolbar: NSToolbar) -> [NSToolbarItem.Identifier] { order }

    func toolbar(_ toolbar: NSToolbar, itemForItemIdentifier itemIdentifier: NSToolbarItem.Identifier,
                 willBeInsertedIntoToolbar flag: Bool) -> NSToolbarItem? {
        makeItem(itemIdentifier)
    }

    /// Builds (once) the item for an identifier.
    func makeItem(_ id: NSToolbarItem.Identifier) -> NSToolbarItem? {
        if let it = items[id] { return it }
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
        } else {
            // TODO(11.3e): the tools (Toolbar.Mode, exactly one pressed). Disabled until then.
            item.action = nil
            item.tag = -1
        }
        return item
    }

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
        pageField.widthAnchor.constraint(equalToConstant: 56).isActive = true
        ofLabel.textColor = .secondaryLabelColor
        let stack = NSStackView(views: [pageField, ofLabel])
        stack.orientation = .horizontal
        stack.spacing = 4
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
        } else if s.action == SAFEPDF_ACT_TOOL.rawValue {
            enabled = false // TODO(11.3e)
        }
        item.isEnabled = enabled
        if #available(macOS 15, *) {
            item.isHidden = i < st.itemVisible.count ? !st.itemVisible[i] : false
        }
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

    /// Return and Escape in the page field (other keys edit the text).
    func control(_ control: NSControl, textView: NSTextView, doCommandBy commandSelector: Selector) -> Bool {
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
