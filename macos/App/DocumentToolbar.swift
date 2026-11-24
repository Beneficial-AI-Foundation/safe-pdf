// DocumentToolbar.swift — the unified toolbar built from the exported toolbar table
// (task 11.3b). Plan.md §6 Phase 11; docs/macos-design.md §2 ("NSToolbar with standard items;
// SF Symbols icons; ... same item order as the Tk bar; no user customisation"). Items and order
// come from safepdf_view_toolbar (Toolbar.layout), enabled and visible states from
// safepdf_view_states. The page field, the zoom and view-mode drop-downs only display for now
// (task 11.3c); the tools are task 11.3e.

import AppKit
import SafePdfC

@MainActor final class DocumentToolbar: NSObject, NSToolbarDelegate {
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
        // TODO(11.3c): editable with Toolbar.pageEntry (Enter / Escape / revert) and page labels.
        pageField.isEditable = false
        pageField.isSelectable = false
        pageField.alignment = .right
        pageField.bezelStyle = .roundedBezel
        pageField.widthAnchor.constraint(equalToConstant: 48).isActive = true
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
        // TODO(11.3c): the zoom model (ZoomChoice presets, stepping, anchoring). Shown, inert.
        for p in Chrome.zoomPresets() ?? [] {
            let mi = NSMenuItem(title: p.label, action: nil, keyEquivalent: "")
            mi.state = p.kind == SAFEPDF_ZOOM_AUTO.rawValue ? .on : .off
            menu.addItem(mi)
        }
        item.menu = menu
        item.title = menu.items.first(where: { $0.state == .on })?.title ?? "Zoom"
        item.label = "Zoom"
        item.toolTip = "Zoom"
        return item
    }

    private func viewItem(_ id: NSToolbarItem.Identifier) -> NSToolbarItem {
        let item = NSMenuToolbarItem(itemIdentifier: id)
        let menu = NSMenu(title: "View mode")
        let current = safepdf_view_choice_of_modes(SAFEPDF_SCROLL_VERTICAL.rawValue, SAFEPDF_SPREAD_NONE.rawValue)
        // TODO(11.3c): the view modes (ViewChoice.modes). Shown, inert.
        for c in Chrome.viewChoices() ?? [] {
            let mi = NSMenuItem(title: c.label, action: nil, keyEquivalent: "")
            mi.state = c.choice == current ? .on : .off
            menu.addItem(mi)
        }
        item.menu = menu
        item.image = NSImage(systemSymbolName: "rectangle.split.1x2", accessibilityDescription: "View mode")
        item.label = "View mode"
        item.toolTip = "View mode"
        return item
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

    /// Shows the page field's texts (safepdf_view_page_field); empty without a document.
    func setPage(entry: String, of: String) {
        pageField.stringValue = entry
        ofLabel.stringValue = of
    }
}
