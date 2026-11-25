// ChromeTables.swift — Swift copies of the exported chrome tables (task 11.3b).
// Plan.md §6 Phase 11; docs/macos-design.md §2 (menubar and toolbar "built from the same
// exported table") and §3 decision 2 (flat C structs, one safepdf_free_* each). The tables are
// SafePdf/Shell/App/Menu.lean and Toolbar.lean, reached through safepdf_view.h; every C struct
// is copied into Swift values and freed at once.

import Foundation
import SafePdfC

/// A neutral key: modifier mask (SAFEPDF_MOD_*), X11/Tk keysym, the name shown in labels.
struct KeySpec: Equatable {
    let mods: UInt32
    let key: String
    let shown: String

    init(_ k: safepdf_key) {
        mods = k.mods
        key = Core.string(k.key)
        shown = Core.string(k.shown)
    }
}

/// A command (Menu.Cmd) or a key action (Menu.Action).
struct CommandSpec {
    let id: Int
    let name: String
    let label: String
    let accel: KeySpec
}

/// One entry of a menu table.
struct MenuEntrySpec {
    let menu: Int
    let kind: UInt32
    let cmd: Int          // -1: none
    let accel: KeySpec
    let radioGroup: UInt32
    let radioValue: String
    let label: String
}

/// Menus and their entries, top to bottom.
struct MenuTableSpec {
    let menus: [String]
    let entries: [MenuEntrySpec]
}

/// A toolbar item (Toolbar.layout), left to right.
struct ToolbarItemSpec {
    let group: UInt32
    let kind: UInt32
    let action: Int32
    let cmd: Int32
    let tool: Int32
    let id: String
    let icon: String
    let tooltip: String
}

/// A key binding of the main window (Menu.keyTable .aqua).
struct KeyBindingSpec {
    let isAction: Bool
    let target: Int
    let key: KeySpec
    let x11: Bool
}

/// An entry of the zoom drop-down.
struct ZoomPresetSpec {
    let kind: UInt32
    let pct: UInt32
    let label: String
    let key: String
}

/// An entry of the view-mode drop-down.
struct ViewChoiceSpec {
    let choice: UInt32
    let label: String
    let key: String
}

/// Enabled and visible states (Menu.Cmd.enabled, Button.enabled / visible).
struct ChromeStates {
    let commandEnabled: [Bool]
    let itemEnabled: [Bool]
    let itemVisible: [Bool]
}

/// Readers of the exported tables. Each returns nil when the C call fails.
enum Chrome {
    static let commandCount = Int(SAFEPDF_CMD_COUNT.rawValue)

    static func commands() -> [CommandSpec]? {
        var c = safepdf_commands()
        guard safepdf_view_commands(&c) == 0 else { return nil }
        defer { safepdf_free_commands(&c) }
        return copy(c)
    }

    static func actions() -> [CommandSpec]? {
        var c = safepdf_commands()
        guard safepdf_view_actions(&c) == 0 else { return nil }
        defer { safepdf_free_commands(&c) }
        return copy(c)
    }

    private static func copy(_ c: safepdf_commands) -> [CommandSpec] {
        guard let items = c.items else { return [] }
        return (0..<c.count).map { i in
            let it = items[i]
            return CommandSpec(id: Int(it.id), name: Core.string(it.name),
                               label: Core.string(it.label), accel: KeySpec(it.accel))
        }
    }

    /// The menubar (Menu.menubar).
    static func menubar() -> MenuTableSpec? {
        var t = safepdf_menu_table()
        guard safepdf_view_menubar(&t) == 0 else { return nil }
        defer { safepdf_free_menu_table(&t) }
        return copy(t)
    }

    /// The toolbar's overflow menu (Toolbar.overflow).
    static func overflowMenu() -> MenuTableSpec? {
        var t = safepdf_menu_table()
        guard safepdf_view_overflow_menu(&t) == 0 else { return nil }
        defer { safepdf_free_menu_table(&t) }
        return copy(t)
    }

    private static func copy(_ t: safepdf_menu_table) -> MenuTableSpec {
        var menus: [String] = []
        if let labels = t.menu_labels {
            for i in 0..<t.menu_count { menus.append(Core.string(labels[i])) }
        }
        var entries: [MenuEntrySpec] = []
        if let es = t.entries {
            for i in 0..<t.entry_count {
                let e = es[i]
                entries.append(MenuEntrySpec(menu: Int(e.menu), kind: e.kind, cmd: Int(e.cmd),
                                             accel: KeySpec(e.accel), radioGroup: e.radio_group,
                                             radioValue: Core.string(e.radio_value),
                                             label: Core.string(e.label)))
            }
        }
        return MenuTableSpec(menus: menus, entries: entries)
    }

    static func toolbar() -> [ToolbarItemSpec]? {
        var t = safepdf_toolbar()
        guard safepdf_view_toolbar(&t) == 0 else { return nil }
        defer { safepdf_free_toolbar(&t) }
        guard let items = t.items else { return [] }
        return (0..<t.count).map { i in
            let it = items[i]
            return ToolbarItemSpec(group: it.group, kind: it.kind, action: it.action, cmd: it.cmd,
                                   tool: it.tool, id: Core.string(it.id), icon: Core.string(it.icon),
                                   tooltip: Core.string(it.tooltip))
        }
    }

    static func keys() -> [KeyBindingSpec]? {
        var t = safepdf_key_table()
        guard safepdf_view_keys(&t) == 0 else { return nil }
        defer { safepdf_free_key_table(&t) }
        guard let items = t.items else { return [] }
        return (0..<t.count).map { i in
            let it = items[i]
            return KeyBindingSpec(isAction: it.target_kind == 1, target: Int(it.target),
                                  key: KeySpec(it.key), x11: it.x11)
        }
    }

    static func zoomPresets() -> [ZoomPresetSpec]? {
        var p = safepdf_zoom_presets()
        guard safepdf_view_zoom_presets(&p) == 0 else { return nil }
        defer { safepdf_free_zoom_presets(&p) }
        guard let items = p.items else { return [] }
        return (0..<p.count).map { i in
            let it = items[i]
            return ZoomPresetSpec(kind: it.choice.kind, pct: it.choice.pct,
                                  label: Core.string(it.label), key: Core.string(it.key))
        }
    }

    static func viewChoices() -> [ViewChoiceSpec]? {
        var c = safepdf_view_choices()
        guard safepdf_view_view_choices(&c) == 0 else { return nil }
        defer { safepdf_free_view_choices(&c) }
        guard let items = c.items else { return [] }
        return (0..<c.count).map { i in
            let it = items[i]
            return ViewChoiceSpec(choice: it.choice, label: Core.string(it.label),
                                  key: Core.string(it.key))
        }
    }

    static func states(_ ctx: safepdf_ctx) -> ChromeStates? {
        var ctx = ctx
        var s = safepdf_chrome_states()
        guard safepdf_view_states(&ctx, &s) == 0 else { return nil }
        defer { safepdf_free_chrome_states(&s) }
        let cmds = withUnsafeBytes(of: s.command_enabled) { raw in
            raw.bindMemory(to: Bool.self).prefix(commandCount).map { $0 }
        }
        var enabled: [Bool] = []
        var visible: [Bool] = []
        if let e = s.item_enabled, let v = s.item_visible {
            for i in 0..<s.item_count {
                enabled.append(e[i])
                visible.append(v[i])
            }
        }
        return ChromeStates(commandEnabled: cmds, itemEnabled: enabled, itemVisible: visible)
    }

    static func appName() -> String { Core.take(safepdf_view_app_name()) ?? "SafePDF" }

    static func aboutDetail() -> String { Core.take(safepdf_view_about_detail()) ?? "" }
}
