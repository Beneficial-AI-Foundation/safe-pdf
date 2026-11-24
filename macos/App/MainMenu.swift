// MainMenu.swift — the menubar built from the exported menu table (task 11.3b).
// Plan.md §6 Phase 11; docs/macos-design.md §2 ("real NSMenu menubar built from the same
// exported table ... a proper application menu (About SafePDF, Hide, Quit); File/Edit/View/Go
// plus the standard Window and Help menus").
//
// Every item sends `performSafePdfCommand:` (tag = Menu.Cmd) or `performSafePdfAction:`
// (tag = Menu.Action) up the responder chain with a nil target; the window controller and the
// application delegate validate them (Menu.Cmd.enabled via safepdf_view_states, and only for
// commands this shell implements).

import AppKit
import SafePdfC

/// Selectors of the menubar's items.
@MainActor @objc protocol SafePdfCommandTarget {
    func performSafePdfCommand(_ sender: Any?)
    func performSafePdfAction(_ sender: Any?)
}

/// What building the menubar produced (printed by the self-test).
struct MenuStats {
    var menus = 0
    var items = 0
    var keyEquivalents = 0
    var hiddenAlternates = 0
    var commandsPresent = Set<Int>()
    var skippedKeys: [String] = []
}

@MainActor enum MainMenu {
    static let commandSelector = #selector(SafePdfCommandTarget.performSafePdfCommand(_:))
    static let actionSelector = #selector(SafePdfCommandTarget.performSafePdfAction(_:))

    /// Builds the menubar. nil when a table cannot be read from the C API.
    static func build() -> (NSMenu, MenuStats)? {
        guard let commands = Chrome.commands(), let actions = Chrome.actions(),
              let table = Chrome.menubar(), let keys = Chrome.keys() else { return nil }
        var stats = MenuStats()
        var used = Set<String>()
        let appName = Chrome.appName()
        let quit = Commands.id(SAFEPDF_CMD_QUIT)
        let about = Commands.id(SAFEPDF_CMD_ABOUT)

        func keyId(_ eq: String, _ flags: NSEvent.ModifierFlags) -> String { "\(flags.rawValue):\(eq)" }

        func apply(_ key: KeySpec, to item: NSMenuItem) {
            guard KeyEquivalents.usableInMenu(key), let (eq, flags) = KeyEquivalents.translate(key)
            else {
                if !key.key.isEmpty { stats.skippedKeys.append("\(key.shown)") }
                return
            }
            let k = keyId(eq, flags)
            if used.contains(k) { stats.skippedKeys.append("\(key.shown) (taken)"); return }
            used.insert(k)
            item.keyEquivalent = eq
            item.keyEquivalentModifierMask = flags
            stats.keyEquivalents += 1
        }

        func commandItem(_ cmd: Int, label: String, accel: KeySpec) -> NSMenuItem {
            let item = NSMenuItem(title: label, action: commandSelector, keyEquivalent: "")
            item.tag = cmd
            apply(accel, to: item)
            stats.items += 1
            stats.commandsPresent.insert(cmd)
            return item
        }

        let bar = NSMenu(title: "Main Menu")

        // Application menu: About, Services, Hide, Quit (the table's About and Quit move here).
        let appMenu = NSMenu(title: appName)
        if about < commands.count {
            appMenu.addItem(commandItem(about, label: commands[about].label, accel: commands[about].accel))
        }
        appMenu.addItem(.separator())
        let services = NSMenuItem(title: "Services", action: nil, keyEquivalent: "")
        let servicesMenu = NSMenu(title: "Services")
        services.submenu = servicesMenu
        NSApp.servicesMenu = servicesMenu
        appMenu.addItem(services)
        appMenu.addItem(.separator())
        let hide = NSMenuItem(title: "Hide \(appName)", action: #selector(NSApplication.hide(_:)), keyEquivalent: "h")
        appMenu.addItem(hide)
        let hideOthers = NSMenuItem(title: "Hide Others",
                                    action: #selector(NSApplication.hideOtherApplications(_:)),
                                    keyEquivalent: "h")
        hideOthers.keyEquivalentModifierMask = [.command, .option]
        appMenu.addItem(hideOthers)
        appMenu.addItem(NSMenuItem(title: "Show All", action: #selector(NSApplication.unhideAllApplications(_:)),
                                   keyEquivalent: ""))
        used.insert(keyId("h", [.command]))
        used.insert(keyId("h", [.command, .option]))
        appMenu.addItem(.separator())
        if quit < commands.count {
            appMenu.addItem(commandItem(quit, label: "Quit \(appName)", accel: commands[quit].accel))
        }
        let appItem = NSMenuItem(title: appName, action: nil, keyEquivalent: "")
        appItem.submenu = appMenu
        bar.addItem(appItem)

        // File, Edit, View, Go, Help from the table.
        var menus: [NSMenu] = []
        for title in table.menus {
            let m = NSMenu(title: title)
            m.autoenablesItems = true
            menus.append(m)
        }
        for e in table.entries where e.menu < menus.count {
            let m = menus[e.menu]
            switch e.kind {
            case SAFEPDF_ENTRY_SEPARATOR.rawValue:
                if let last = m.items.last, !last.isSeparatorItem { m.addItem(.separator()) }
            case SAFEPDF_ENTRY_COLORS.rawValue:
                // The highlight-colour submenu (TODO 11.3e: the five colours from the marks API).
                let item = NSMenuItem(title: e.label, action: nil, keyEquivalent: "")
                item.submenu = NSMenu(title: e.label)
                item.isEnabled = false
                m.addItem(item)
                stats.items += 1
            default:
                guard e.cmd >= 0 else { continue }
                if e.cmd == quit || e.cmd == about { continue }
                m.addItem(commandItem(e.cmd, label: e.label, accel: e.accel))
            }
        }
        // Hidden alternates: the key table's other bindings (⌘=, the X11 Ctrl keys, F9 ...)
        // and the key actions (Find next / previous), each next to its command.
        let commandMenu: [Int: NSMenu] = {
            var d: [Int: NSMenu] = [:]
            for e in table.entries where e.menu < menus.count && e.cmd >= 0 { d[e.cmd] = menus[e.menu] }
            return d
        }()
        let fallback = menus.count > 1 ? menus[1] : (menus.first ?? appMenu)
        for b in keys {
            if b.isAction {
                guard b.target < actions.count else { continue }
                let item = NSMenuItem(title: actions[b.target].label, action: actionSelector, keyEquivalent: "")
                item.tag = b.target
                apply(b.key, to: item)
                guard !item.keyEquivalent.isEmpty else { continue }
                item.isHidden = true
                item.allowsKeyEquivalentWhenHidden = true
                fallback.addItem(item)
                stats.hiddenAlternates += 1
            } else {
                guard b.target < commands.count, b.key != commands[b.target].accel else { continue }
                let item = NSMenuItem(title: commands[b.target].label, action: commandSelector, keyEquivalent: "")
                item.tag = b.target
                apply(b.key, to: item)
                guard !item.keyEquivalent.isEmpty else { continue }
                item.isHidden = true
                item.allowsKeyEquivalentWhenHidden = true
                (commandMenu[b.target] ?? fallback).addItem(item)
                stats.hiddenAlternates += 1
            }
        }
        // Cut and Paste for the text fields (the search and page fields; task 11.3d1): hidden,
        // sent to the first responder (the field editor validates them; the page view has none).
        if let edit = menus.first(where: { $0.title == "Edit" }) ?? menus.dropFirst().first {
            for (title, sel, key) in [("Cut", #selector(NSText.cut(_:)), "x"), ("Paste", #selector(NSText.paste(_:)), "v")]
            where !used.contains(keyId(key, [.command])) {
                let item = NSMenuItem(title: title, action: sel, keyEquivalent: key)
                item.isHidden = true
                item.allowsKeyEquivalentWhenHidden = true
                edit.addItem(item)
                used.insert(keyId(key, [.command]))
            }
        }
        for m in menus {
            while let last = m.items.last, last.isSeparatorItem { m.removeItem(last) }
        }

        // Window menu (standard) before Help.
        let windowMenu = NSMenu(title: "Window")
        windowMenu.addItem(NSMenuItem(title: "Minimize", action: #selector(NSWindow.performMiniaturize(_:)),
                                      keyEquivalent: "m"))
        windowMenu.addItem(NSMenuItem(title: "Zoom", action: #selector(NSWindow.performZoom(_:)),
                                      keyEquivalent: ""))
        windowMenu.addItem(.separator())
        windowMenu.addItem(NSMenuItem(title: "Bring All to Front",
                                      action: #selector(NSApplication.arrangeInFront(_:)), keyEquivalent: ""))
        NSApp.windowsMenu = windowMenu

        for (i, m) in menus.enumerated() {
            if table.menus[i] == "Help" {
                let wi = NSMenuItem(title: "Window", action: nil, keyEquivalent: "")
                wi.submenu = windowMenu
                bar.addItem(wi)
                NSApp.helpMenu = m
            }
            let item = NSMenuItem(title: m.title, action: nil, keyEquivalent: "")
            item.submenu = m
            bar.addItem(item)
        }
        if NSApp.helpMenu == nil {
            let wi = NSMenuItem(title: "Window", action: nil, keyEquivalent: "")
            wi.submenu = windowMenu
            bar.addItem(wi)
        }
        stats.menus = bar.items.count
        return (bar, stats)
    }
}
