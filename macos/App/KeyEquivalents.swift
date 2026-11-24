// KeyEquivalents.swift — neutral keys (Menu.lean's key table) to AppKit key equivalents
// (task 11.3b). Plan.md §6 Phase 11; docs/macos-design.md §1 "Keys" (the macOS column of the
// key table) — safepdf_view.h says translating keysyms is the shell's job.

import AppKit
import SafePdfC

enum KeyEquivalents {
    /// AppKit key equivalent and modifier mask for a neutral key, or nil when the key has no
    /// AppKit equivalent (or is empty).
    static func translate(_ k: KeySpec) -> (String, NSEvent.ModifierFlags)? {
        guard let equivalent = character(for: k.key) else { return nil }
        var flags: NSEvent.ModifierFlags = []
        if k.mods & UInt32(SAFEPDF_MOD_COMMAND) != 0 { flags.insert(.command) }
        if k.mods & UInt32(SAFEPDF_MOD_SHIFT) != 0 { flags.insert(.shift) }
        if k.mods & UInt32(SAFEPDF_MOD_OPTION) != 0 { flags.insert(.option) }
        if k.mods & UInt32(SAFEPDF_MOD_CONTROL) != 0 { flags.insert(.control) }
        return (equivalent, flags)
    }

    /// Whether a binding is safe as a menu key equivalent. A key with neither Command nor
    /// Control (a plain letter, an arrow, Delete) would be taken from the page field and other
    /// text fields, so only function and paging keys may go without them; the rest is left for
    /// the page view's own key handling (task 11.3c).
    static func usableInMenu(_ k: KeySpec) -> Bool {
        let strong = UInt32(SAFEPDF_MOD_COMMAND | SAFEPDF_MOD_CONTROL)
        if k.mods & strong != 0 { return true }
        return ["Prior", "Next", "PageUp", "PageDown", "F1", "F2", "F3", "F4", "F5", "F6", "F7",
                "F8", "F9", "F10", "F11", "F12"].contains(k.key)
    }

    private static func function(_ code: Int) -> String {
        guard let scalar = Unicode.Scalar(code) else { return "" }
        return String(Character(scalar))
    }

    /// The character AppKit matches for a keysym.
    static func character(for keysym: String) -> String? {
        switch keysym {
        case "": return nil
        case "plus", "KP_Add": return "+"
        case "minus", "KP_Subtract": return "-"
        case "equal": return "="
        case "bracketleft": return "["
        case "bracketright": return "]"
        case "period": return "."
        case "comma": return ","
        case "slash": return "/"
        case "question": return "?"
        case "space": return " "
        case "Escape": return "\u{1b}"
        case "Return": return "\r"
        case "Tab": return "\t"
        case "BackSpace": return "\u{8}"
        case "Delete": return function(NSDeleteFunctionKey)
        case "Up": return function(NSUpArrowFunctionKey)
        case "Down": return function(NSDownArrowFunctionKey)
        case "Left": return function(NSLeftArrowFunctionKey)
        case "Right": return function(NSRightArrowFunctionKey)
        case "Prior", "PageUp": return function(NSPageUpFunctionKey)
        case "Next", "PageDown": return function(NSPageDownFunctionKey)
        case "Home": return function(NSHomeFunctionKey)
        case "End": return function(NSEndFunctionKey)
        default:
            if keysym.hasPrefix("F"), let n = Int(keysym.dropFirst()), (1...35).contains(n) {
                return function(NSF1FunctionKey + n - 1)
            }
            // Letters and digits: AppKit wants the unshifted character; Shift is in the mask.
            if keysym.count == 1 { return keysym.lowercased() }
            return nil
        }
    }
}
