// Sheets.swift — open and save panels and alerts as document-modal sheets (task 11.3b).
// Plan.md §6 Phase 11; docs/macos-design.md §2 ("NSOpenPanel/NSSavePanel (UTType pdf), NSAlert
// as document-modal sheets"). Save itself, and the Save / Don't Save / Cancel and first-overwrite
// prompts that use these helpers, are task 11.3e.

import AppKit
import UniformTypeIdentifiers

@MainActor enum Sheets {
    /// Asks for a PDF to open: a sheet on `window`, or an app-modal panel without one.
    static func openPDF(on window: NSWindow?, completion: @escaping @MainActor (URL) -> Void) {
        let panel = NSOpenPanel()
        panel.allowedContentTypes = [.pdf]
        panel.allowsMultipleSelection = false
        panel.canChooseDirectories = false
        if let window {
            panel.beginSheetModal(for: window) { response in
                if response == .OK, let url = panel.url { completion(url) }
            }
        } else if panel.runModal() == .OK, let url = panel.url {
            completion(url)
        }
    }

    /// Asks where to save a PDF (used by Save As, task 11.3e).
    static func savePDF(on window: NSWindow, suggestedName: String,
                        completion: @escaping @MainActor (URL) -> Void) {
        let panel = NSSavePanel()
        panel.allowedContentTypes = [.pdf]
        panel.nameFieldStringValue = suggestedName
        panel.canCreateDirectories = true
        panel.beginSheetModal(for: window) { response in
            if response == .OK, let url = panel.url { completion(url) }
        }
    }

    /// Shows an error (a message from the C API) as a sheet, or app-modal without a window.
    static func error(_ title: String, detail: String, on window: NSWindow?) {
        let alert = NSAlert()
        alert.alertStyle = .warning
        alert.messageText = title
        alert.informativeText = detail
        alert.addButton(withTitle: "OK")
        if let window {
            alert.beginSheetModal(for: window, completionHandler: nil)
        } else {
            alert.runModal()
        }
    }

    /// Asks a question with buttons (first is the default) as a sheet; the completion receives
    /// the index of the button pressed (used by the 11.3e prompts and the link confirmation).
    static func ask(_ title: String, detail: String, buttons: [String], on window: NSWindow,
                    completion: @escaping @MainActor (Int) -> Void) {
        let alert = NSAlert()
        alert.messageText = title
        alert.informativeText = detail
        for b in buttons { alert.addButton(withTitle: b) }
        alert.beginSheetModal(for: window) { response in
            completion(response.rawValue - NSApplication.ModalResponse.alertFirstButtonReturn.rawValue)
        }
    }
}
