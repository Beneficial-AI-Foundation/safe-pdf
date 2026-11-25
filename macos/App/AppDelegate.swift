// AppDelegate.swift — application life cycle: menubar, the document window, files from Finder
// and `open -a`, About and Quit (task 11.3b); the unsaved-marks question before quitting and
// before opening another file (task 11.3e2). Plan.md §6 Phase 11; docs/macos-design.md §2
// (application menu, NSOpenPanel, the bundle's open-with).

import AppKit
import SafePdfC

@MainActor final class AppDelegate: NSObject, NSApplicationDelegate, NSMenuItemValidation,
    SafePdfCommandTarget
{
    /// The running delegate (window controllers forward app-level commands to it).
    static weak var shared: AppDelegate?

    private var controller: DocumentWindowController?
    private var launched = false
    private var pending: [URL] = []
    private let initialPath: String?

    init(initialPath: String?) {
        self.initialPath = initialPath
        super.init()
        AppDelegate.shared = self
    }

    func applicationDidFinishLaunching(_ notification: Notification) {
        guard let (menu, _) = MainMenu.build() else {
            Sheets.error("SafePDF cannot start", detail: "The menu tables could not be read from the core.", on: nil)
            NSApp.terminate(nil)
            return
        }
        NSApp.mainMenu = menu
        if let problem = Core.configureWorker() {
            Sheets.error("SafePDF cannot render documents", detail: problem, on: nil)
        }
        let wc = ensureWindow()
        wc.showWindow(nil)
        NSApp.activate()
        launched = true
        if let url = pending.first {
            wc.open(url)
        } else if let path = initialPath {
            wc.open(URL(fileURLWithPath: path))
        } else {
            Sheets.openPDF(on: wc.window) { url in wc.open(url) }
        }
        pending = []
    }

    /// Files from Finder, the Dock or `open -a SafePDF FILE` (one window: the first file).
    func application(_ application: NSApplication, open urls: [URL]) {
        guard let url = urls.first else { return }
        if !launched {
            pending = urls
            return
        }
        let wc = ensureWindow()
        if wc.pdf?.url.standardizedFileURL != url.standardizedFileURL { wc.open(url) }
        wc.showWindow(nil)
    }

    func applicationShouldTerminateAfterLastWindowClosed(_ sender: NSApplication) -> Bool { true }

    /// ⌘Q with unsaved marks: each document window asks Save / Don't Save / Cancel in turn
    /// (Viewer: confirmDiscard "quitting"); Cancel, or a failed save, keeps the app running.
    func applicationShouldTerminate(_ sender: NSApplication) -> NSApplication.TerminateReply {
        let windows = [controller].compactMap { $0 }.filter { $0.window != nil && $0.pages.marks.dirty }
        guard !windows.isEmpty else { return .terminateNow }
        Self.askInTurn(windows[...]) { go in NSApp.reply(toApplicationShouldTerminate: go) }
        return .terminateLater
    }

    /// Asks each window in turn; stops at the first that does not go on.
    private static func askInTurn(_ ws: ArraySlice<DocumentWindowController>, done: @escaping @MainActor (Bool) -> Void) {
        guard let first = ws.first else { done(true); return }
        first.showWindow(nil)
        first.confirmQuit { go in
            if go { askInTurn(ws.dropFirst(), done: done) } else { done(false) }
        }
    }

    private func ensureWindow() -> DocumentWindowController {
        if let c = controller, c.window != nil { return c }
        let c = DocumentWindowController()
        controller = c
        return c
    }

    /// Application-level commands (Open, Quit, About), also when no window is open.
    func perform(_ cmd: Int) {
        switch cmd {
        case Commands.id(SAFEPDF_CMD_OPEN_FILE):
            let wc = ensureWindow()
            wc.showWindow(nil)
            // The unsaved-marks question comes before the panel (Viewer.openDialog).
            wc.saver.confirmDiscard("opening another file") { [weak wc] go in
                guard go, let wc else { return }
                Sheets.openPDF(on: wc.window) { [weak wc] url in wc?.openConfirmed(url) }
            }
        case Commands.id(SAFEPDF_CMD_QUIT):
            NSApp.terminate(nil)
        case Commands.id(SAFEPDF_CMD_ABOUT):
            NSApp.orderFrontStandardAboutPanel(options: [
                .applicationName: Chrome.appName(),
                .credits: NSAttributedString(string: Chrome.aboutDetail(), attributes: [
                    .font: NSFont.systemFont(ofSize: NSFont.smallSystemFontSize),
                    .foregroundColor: NSColor.labelColor,
                ]),
            ])
        default:
            break // not an application-level command
        }
    }

    @objc func performSafePdfCommand(_ sender: Any?) {
        let cmd = (sender as? NSMenuItem)?.tag ?? -1
        if isEnabled(cmd) { perform(cmd) }
    }

    @objc func performSafePdfAction(_ sender: Any?) {}

    /// Without a document window: the exported rule for "no document" (Open, Quit, About).
    private func isEnabled(_ cmd: Int) -> Bool {
        guard Commands.implemented.contains(cmd), let st = Chrome.states(safepdf_ctx()),
              cmd >= 0, cmd < st.commandEnabled.count else { return false }
        return st.commandEnabled[cmd]
    }

    func validateMenuItem(_ item: NSMenuItem) -> Bool {
        if item.action == MainMenu.commandSelector { return isEnabled(item.tag) }
        if item.action == MainMenu.actionSelector { return false }
        return true
    }
}
