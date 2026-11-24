// SmokeSession.swift — the scripted, headless session of the native app (task 11.5): the macOS
// counterpart of the Tk smoke (scripts/viewer-smoke.sh) and of the viewer corpus session
// (scripts/viewer-corpus.sh, docs/viewer-corpus.md M8/M9), run by scripts/macos-smoke.sh and
// scripts/macos-corpus.sh. Plan.md §6 Phases 8–11 (M8, M9, M11); docs/macos-smoke.md.
//
//   SAFEPDF_MACOS_SESSION=SCRIPT SAFEPDF_MACOS_SESSION_OUT=DIR safepdf-mac
//
// Background discipline (10.16, 10.19): the activation policy is Prohibited before anything else
// (main.swift); the session never calls `run`, `activate`, `showWindow` or `makeKeyAndOrderFront`.
// It drives the app's own DocumentWindowController — the menu commands (`run`, the menubar items
// found by their key equivalents, the colour and tool items, the zoom and view drop-downs), the
// page view, the sidebar panels, the marks and the SaveController — but hosts the window's
// content off the window (the split view is detached from it), so no popover, note editor or
// sheet can ever be ordered in: the controllers take their headless path (canvas.window == nil),
// exactly as the self-test does. The save flow's questions and panels are answered by script
// (ScriptedDialogs); Copy and Copy Address go to a private pasteboard, never the user's; external
// addresses are never opened (there is no NSWorkspace call in the app). After every step the
// session checks that no window of the process is visible.
//
// The script: one command per line, `#` comments, `$OUT` (the output directory) and `$IN` (the
// SAFEPDF_SESSION_IN directory, inputs) expanded. Every command is listed in docs/macos-smoke.md;
// `expect KEY OP VALUE` checks a state value (`=`, `!=`, `~` contains, `^` prefix, `<`, `>`,
// `<=`, `>=` numeric). Output: every step and check on stderr and in DIR/session.txt, the corpus
// pass's numbers in DIR/corpus.json; the last line `session: N steps, F failures, …`. Exit 0
// when no check failed.

import AppKit
import Darwin
import SafePdfC
import UniformTypeIdentifiers

@MainActor final class SmokeSession: NSObject {
    private let out: String
    private let input: String
    private var log = ""
    private var failures = 0
    private var steps = 0
    private var lineNo = 0
    private let wc: DocumentWindowController
    private let root: NSView
    private let dialogs = ScriptedDialogs()
    private let pb: NSPasteboard
    private var menu: NSMenu?
    private var commandIds: [String: Int] = [:]
    /// The longest a command call or one run-loop pass kept the main thread busy (ms).
    private var maxBlockMs = 0.0
    private var maxBlockWhat = ""
    /// Per page of the open document: the first render delivered at the page's current key
    /// (request to delivery on the main thread, ms), and render errors.
    private var firstImage: [Int: Double] = [:]
    private var renderErrors: [Int: String] = [:]
    private var openStarted = 0.0
    private var openToFirst: Double?
    /// An external outline address waiting for Copy Address / Cancel.
    private var pendingOutlineURI: String?
    /// The last find query typed (Find next / previous use it, as the search field's text).
    private var lastQuery = ""
    /// Values a measuring command stored (`expect` reads them as keys).
    private var vars: [String: String] = [:]
    /// The largest physical footprint (lifetime maximum) of this process and of its child
    /// processes (the document workers), sampled while the run loop runs.
    private var peakSelf: UInt64 = 0
    private var peakChild: UInt64 = 0
    private var lastSample = 0.0
    private var skips: [String] = []
    /// `async on`: commands return without waiting for their renders (the non-blocking checks).
    private var noWait = false

    private var pages: PageViewController { wc.pages }
    private var canvas: PageCanvasView { wc.pages.canvas }

    init(out: String, input: String) {
        self.out = out
        self.input = input
        pb = NSPasteboard(name: NSPasteboard.Name("org.safe-pdf.smoke.\(getpid())"))
        let controller = DocumentWindowController()
        let window = controller.window
        // No frame is saved into the defaults, and the window is never ordered in.
        window?.setFrameAutosaveName("")
        window?.isReleasedWhenClosed = false
        // The content lives off the window: popovers, the note editor and the text box editor
        // take their headless path (no window), as in the self-test.
        let content = window?.contentViewController
        window?.contentViewController = nil
        let host = content?.view ?? NSView()
        host.frame = NSRect(x: 0, y: 0, width: 980, height: 1000)
        host.layoutSubtreeIfNeeded()
        wc = controller
        root = host
        super.init()
        canvas.scaleOverride = 2
        wc.saver.dialogs = dialogs
        pages.text.pasteboard = pb
        // Outline items with an external address: the session answers Copy Address / Cancel
        // (the window's own sheet is never shown headless).
        wc.sidebar.onExternalLink = { [weak self] uri in
            self?.pendingOutlineURI = uri
            self?.say("  outline: external address asked: \(uri)")
        }
        canvas.onRender = { [weak self] res in self?.rendered(res) }
        NotificationCenter.default.addObserver(self, selector: #selector(willClose(_:)),
                                               name: NSWindow.willCloseNotification, object: wc.window)
        if let (m, _) = MainMenu.build() { menu = m }
        for c in Chrome.commands() ?? [] {
            commandIds[Self.norm(c.name)] = c.id
            commandIds[Self.norm(c.label)] = c.id
        }
    }

    /// NSWindow.willCloseNotification of the document window (counted: `close` checks AppKit
    /// posted it).
    private var willCloses = 0
    @objc private func willClose(_ n: Notification) { willCloses += 1 }

    static func norm(_ s: String) -> String {
        String(s.lowercased().unicodeScalars.filter { CharacterSet.alphanumerics.contains($0) })
    }

    // MARK: output

    private func say(_ s: String) {
        log += s + "\n"
        FileHandle.standardError.write(Data((s + "\n").utf8))
    }

    private func check(_ ok: Bool, _ what: @autoclosure () -> String) {
        if ok { return }
        failures += 1
        say("FAIL (line \(lineNo)): " + what())
    }

    // MARK: run loop

    /// Runs the main run loop until `done()` or `limit` seconds; each pass's time counts as
    /// blocking (a callback that keeps the main thread busy). Returns the time waited (ms).
    @discardableResult
    private func pump(_ limit: Double, until done: () -> Bool) -> Double {
        let t0 = Core.nowMs()
        while !done() && Core.nowMs() - t0 < limit * 1000 {
            let a = Core.nowMs()
            RunLoop.main.run(mode: .default, before: Date(timeIntervalSinceNow: 0.005))
            let d = Core.nowMs() - a
            if d > maxBlockMs + 10 && d > 15 {
                maxBlockMs = d
                maxBlockWhat = "a run-loop pass (line \(lineNo))"
            }
            sampleMemory()
        }
        return Core.nowMs() - t0
    }

    /// Everything the last step started has finished: renders, the sidebar's panels, text
    /// indexes, a search, the marks preview.
    private var idle: Bool {
        canvas.pendingCount == 0 && wc.sidebar.pending == 0 && !pages.text.find.searching
            && pages.text.store.pendingCount == 0
            && (pages.marks.model.map { pages.marks.preview.isCurrent($0) && !pages.marks.preview.busy } ?? true)
    }

    private func waitIdle(_ limit: Double = 60) {
        if noWait { return }
        pump(limit) { idle }
        if !idle { say("  (still busy after \(Int(limit)) s)") }
    }

    /// Runs `body` as a user action and records its time on the main thread.
    private func timed(_ what: String, _ body: () -> Void) {
        let t0 = Core.nowMs()
        body()
        let d = Core.nowMs() - t0
        vars["last_ms"] = String(format: "%.1f", d)
        if d > maxBlockMs {
            maxBlockMs = d
            maxBlockWhat = "\(what) (line \(lineNo))"
        }
    }

    private func sampleMemory() {
        let now = Core.nowMs()
        guard now - lastSample > 200 else { return }
        lastSample = now
        peakSelf = max(peakSelf, Self.footprint(getpid()))
        var buf = [pid_t](repeating: 0, count: 64)
        let n = Int(proc_listchildpids(getpid(), &buf, Int32(buf.count * MemoryLayout<pid_t>.size)))
        for i in 0..<min(max(0, n), buf.count) where buf[i] > 0 {
            peakChild = max(peakChild, Self.footprint(buf[i]))
        }
    }

    /// A process's lifetime maximum physical footprint (bytes; 0 when unknown).
    static func footprint(_ pid: pid_t) -> UInt64 {
        var info = rusage_info_v4()
        let rc = withUnsafeMutablePointer(to: &info) { p in
            p.withMemoryRebound(to: rusage_info_t?.self, capacity: 1) { proc_pid_rusage(pid, RUSAGE_INFO_V4, $0) }
        }
        return rc == 0 ? info.ri_lifetime_max_phys_footprint : 0
    }

    private func rendered(_ res: RenderResult) {
        guard let place = canvas.place(ofPage: res.page), place.key == res.key else { return }
        if res.image != nil {
            if firstImage[res.page] == nil {
                firstImage[res.page] = res.ms
                if res.page == canvas.currentPage, openToFirst == nil, openStarted > 0 {
                    openToFirst = Core.nowMs() - openStarted
                }
            }
        } else if let e = res.error {
            renderErrors[res.page] = e
        }
    }

    // MARK: entry

    static func run(script: String, out: String, input: String) -> Int32 {
        try? FileManager.default.createDirectory(atPath: out, withIntermediateDirectories: true)
        guard let text = try? String(contentsOfFile: script, encoding: .utf8) else {
            FileHandle.standardError.write(Data("session: cannot read \(script)\n".utf8))
            return 2
        }
        let s = SmokeSession(out: out, input: input)
        return s.run(text)
    }

    private func run(_ text: String) -> Int32 {
        let t0 = Core.nowMs()
        say("session: activation policy \(NSApp.activationPolicy() == .prohibited ? "prohibited" : "NOT prohibited")")
        check(NSApp.activationPolicy() == .prohibited, "the activation policy is not Prohibited")
        if let problem = Core.configureWorker() {
            check(false, problem)
        } else {
            say("session: worker \(Core.workerPath() ?? "?")")
        }
        for raw in text.components(separatedBy: "\n") {
            lineNo += 1
            let line = raw.trimmingCharacters(in: .whitespaces)
            if line.isEmpty || line.hasPrefix("#") { continue }
            let expanded = line.replacingOccurrences(of: "$OUT", with: out).replacingOccurrences(of: "$IN", with: input)
            steps += 1
            if !expanded.hasPrefix("expect ") { say("> \(expanded)") }
            step(expanded)
            let shown = NSApp.windows.filter { $0.isVisible }
            check(shown.isEmpty, "a window became visible: \(shown.map { $0.title.isEmpty ? String(describing: type(of: $0)) : $0.title })")
            check(NSApp.activationPolicy() == .prohibited && !NSApp.isActive, "the app became active")
            if line == "stop" { break }
        }
        pb.releaseGlobally()
        sampleMemory()
        let summary = String(format: "session: %d steps, %d failures, %d skipped steps, longest block %.0f ms (%@), %.1f s",
                             steps, failures, skips.count, maxBlockMs, maxBlockWhat.isEmpty ? "-" : maxBlockWhat,
                             (Core.nowMs() - t0) / 1000)
        say(summary)
        for s in skips { say("session:   skipped: \(s)") }
        try? log.write(toFile: "\(out)/session.txt", atomically: true, encoding: .utf8)
        return failures == 0 ? 0 : 1
    }

    // MARK: commands

    private func words(_ s: String) -> [String] { s.split(separator: " ", omittingEmptySubsequences: true).map(String.init) }

    /// The text after the first `k` words (spaces inside kept).
    private func rest(_ s: String, after k: Int) -> String {
        var t = Substring(s)
        for _ in 0..<k {
            t = t.drop { $0 == " " }
            t = t.drop { $0 != " " }
        }
        return String(t.drop { $0 == " " })
    }

    private func step(_ line: String) {
        let w = words(line)
        guard let op = w.first else { return }
        let a = Array(w.dropFirst())
        switch op {
        case "say": say("  " + rest(line, after: 1))
        case "stop": break
        case "fixture": fixture(a, line)
        case "open": open(rest(line, after: 1))
        case "open-error": openError(rest(line, after: 1))
        case "cmd": command(rest(line, after: 1), mustRun: true)
        case "try": command(rest(line, after: 1), mustRun: false)
        case "key": key(a.first ?? "")
        case "wait": waitIdle()
        case "sleep": pump((Double(a.first ?? "0") ?? 0) / 1000) { false }
        case "zoom": zoomPreset(rest(line, after: 1))
        case "zoompct": timed("zoom \(a.first ?? "")") { pages.setZoom(ZoomModel.percent(UInt32(a.first ?? "100") ?? 100)) }
            waitIdle()
        case "view": viewChoice(rest(line, after: 1))
        case "goto": timed("page field") { pages.pageEntry(rest(line, after: 1)); wc.updateChrome() }
            waitIdle()
        case "size": resize(a)
        case "scale": scale(a)
        case "dark": dark(a.first == "on")
        case "measure-paper": measurePaper()
        case "measure-mark": measureMark()
        case "measure-selection": measureSelection()
        case "snapshot": snapshot(a.first ?? "snap")
        case "wheel": wheel(a)
        case "wheel-turn":
            let from = canvas.currentPage
            var k = 0
            while canvas.currentPage == from && k < 100 { wheel([a.first ?? "-30", "1"]); k += 1 }
            vars["turn_events"] = String(k)
            say("  page \(from + 1) -> \(canvas.currentPage + 1) after \(k) wheel events")
        case "dblclick": glyphClick(a, clicks: 2)
        case "click-glyph": glyphClick(a, clicks: 1)
        case "drag": drag(a)
        case "dblclick-hit": hitClick()
        case "find": lastQuery = rest(line, after: 1); find(forward: true, typed: true)
        case "find-next": find(forward: true, typed: false)
        case "find-prev": find(forward: false, typed: false)
        case "find-close": pages.text.find.close()
        case "link": link(a)
        case "link-answer": linkAnswer(a.first == "copy")
        case "outline": outline(a.first ?? "0")
        case "outline-answer": outlineAnswer(a.first == "copy")
        case "panel": panel(a.first ?? "")
        case "thumb": timed("thumbnail") { wc.sidebar.thumbnails.activate((Int(a.first ?? "1") ?? 1) - 1); wc.updateChrome() }
            waitIdle()
        case "attach-save": attachSave(a)
        case "layer": layer(a)
        case "color": colorItem(a.first ?? "yellow")
        case "tool": tool(a.first ?? "select")
        case "note": note(rest(line, after: 1))
        case "note-close": noteClose(rest(line, after: 1))
        case "note-at": noteAt(a)
        case "note-left": noteLeft()
        case "note-save":
            check(pages.marks.noteOpen != nil, "no note editor open")
            timed("note save") { pages.marks.noteSave(rest(line, after: 1)) }
            wc.updateChrome()
            waitIdle()
        case "select-mark": selectMark(a.first ?? "last")
        case "open-mark": selectMark(a.first ?? "last", open: true)
        case "freetext": freeText(a, rest(line, after: 3))
        case "ink": ink(a)
        case "escape": _ = pages.marks.escape()
        case "answer": dialogs.answers += a
        case "saveurl": dialogs.saveURLs.append(URL(fileURLWithPath: rest(line, after: 1)))
        case "openurl": dialogs.openURLs.append(URL(fileURLWithPath: rest(line, after: 1)))
        case "seedless": wc.saver.randomBytes = { _ in nil }
        case "seeded": wc.saver.randomBytes = SaveController.secureRandom
        case "close": close()
        case "quit": quit()
        case "copy-file": copyFile(a)
        case "append-file": appendFile(a.first ?? "", rest(line, after: 2))
        case "chmod": if a.count == 2, let m = Int(a[0], radix: 8) { chmod(a[1], mode_t(m)) }
        case "prefix": prefix(a)
        case "corpus-pass": corpusPass()
        case "measure": measureState()
        case "list-keys": listKeys()
        case "measure-ink": measureInk()
        case "expect": expect(line)
        case "remember": if a.count == 2 { vars[a[0]] = value(a[1]); say("  \(a[0]) = \(vars[a[0]] ?? "")") }
        case "async": noWait = a.first == "on"
        case "open-nowait": noWait = true; open(rest(line, after: 1)); noWait = false
        case "skip": skips.append(rest(line, after: 1)); say("  SKIP: \(rest(line, after: 1))")
        default: check(false, "unknown command \(op)")
        }
    }

    // MARK: fixtures (the self-test's generators)

    private func fixture(_ a: [String], _ line: String) {
        guard a.count >= 2 else { check(false, "fixture KIND PATH"); return }
        let data: Data
        switch a[0] {
        case "text3": data = SelfTest.textPDF()
        case "attachments": data = SelfTest.attachmentsPDF()
        case "layers": data = SelfTest.layersPDF()
        case "settings": data = SelfTest.settingsPDF(rest(line, after: 3), title: "Open Settings Test")
        default: check(false, "unknown fixture \(a[0])"); return
        }
        check((try? data.write(to: URL(fileURLWithPath: a[1]))) != nil, "write fixture \(a[1])")
    }

    // MARK: open, close, quit

    private func open(_ path: String) {
        firstImage = [:]
        renderErrors = [:]
        openToFirst = nil
        openStarted = Core.nowMs()
        let before = wc.pdf
        timed("open") { wc.open(URL(fileURLWithPath: path)) }
        waitIdle()
        // The page labels arrive after the open (Document.loadLabels).
        pump(0.2) { false }
        waitIdle()
        let opened = wc.pdf != nil && wc.pdf !== before
        vars["opened"] = opened ? "1" : "0"
        vars["open_ms"] = String(format: "%.1f", openToFirst ?? -1)
        if let d = wc.pdf, opened {
            say(String(format: "  opened %@: %d pages, first page shown after %.1f ms%@%@", d.url.lastPathComponent,
                       d.pageCount, openToFirst ?? -1, d.repaired ? " (repaired)" : "", d.encrypted ? " (encrypted)" : ""))
        } else {
            say("  not opened (pdf \(wc.pdf?.url.lastPathComponent ?? "none"))")
        }
    }

    private func openError(_ path: String) {
        // The open path of DocumentWindowController.load: Document(url:) and its error text (the
        // window shows it as a sheet; never shown headless).
        do {
            _ = try Document(url: URL(fileURLWithPath: path))
            vars["error"] = ""
            check(false, "\(path) opened, an error was expected")
        } catch {
            vars["error"] = error.message
            say("  open error: \(error.message)")
        }
    }

    /// The close button (windowShouldClose, then close()).
    private func close() {
        guard let w = wc.window else { return }
        let mark = closeMark()
        var should = false
        timed("close") {
            should = wc.windowShouldClose(w)
            if should { w.close() }
        }
        settleClose(mark, should: should)
    }

    private func closeMark() -> (closes: Int, pills: Int, asked: Int) {
        (willCloses, pages.pill.history.count, dialogs.asked.count)
    }

    /// After a close: AppKit ignores close() of a window that was closed before and never
    /// ordered in again (the app orders it in with showWindow on the next open; a session never
    /// does). When the close went on — windowShouldClose said yes, or the unsaved-marks question
    /// was answered without "cancelled" — and no willClose was posted, the session posts it, so
    /// the controller's windowWillClose runs as in the app. Sets `closed`.
    private func settleClose(_ mark: (closes: Int, pills: Int, asked: Int), should: Bool?) {
        pump(0.05) { false }
        var emulated = false
        if wc.pdf != nil, willCloses == mark.closes, let w = wc.window {
            let asked = dialogs.asked.count > mark.asked
            let cancelled = pages.pill.history.dropFirst(mark.pills).contains { $0.contains("cancelled") }
            let goes = should == true || (asked && !cancelled) || (should == nil && !asked)
            if goes {
                NotificationCenter.default.post(name: NSWindow.willCloseNotification, object: w)
                emulated = true
            }
        }
        let closed = wc.pdf == nil
        vars["closed"] = closed ? "1" : "0"
        say("  closed: \(closed)\(emulated ? " (willClose posted by the session: the window was closed before)" : "")")
    }

    private func quit() {
        var go: Bool? = nil
        timed("quit") { wc.confirmQuit { go = $0 } }
        pump(5) { go != nil }
        vars["quit"] = go == true ? "1" : "0"
        say("  quit goes on: \(go.map(String.init) ?? "no answer")")
    }

    // MARK: commands, keys, drop-downs

    private func command(_ name: String, mustRun: Bool) {
        guard let id = commandIds[Self.norm(name)] else { check(false, "no command \(name)"); return }
        var ran = false
        let mark = closeMark()
        timed("command \(name)") { ran = wc.run(id) }
        if id == Commands.id(SAFEPDF_CMD_CLOSE), ran { settleClose(mark, should: nil) }
        vars["ran"] = ran ? "1" : "0"
        if mustRun { check(ran, "command \(name) did not run (disabled)") } else { say("  ran: \(ran)") }
        waitIdle()
    }

    /// `cmd+shift+s`, `pagedown`, `f9`, `r` … to a key event's characters and modifiers.
    private func keySpec(_ spec: String) -> (String, NSEvent.ModifierFlags)? {
        var flags: NSEvent.ModifierFlags = []
        var parts = spec.lowercased().split(separator: "+").map(String.init)
        if spec.hasSuffix("++") { parts = parts.filter { !$0.isEmpty } + ["plus"] }
        guard let last = parts.popLast() else { return nil }
        for m in parts {
            switch m {
            case "cmd": flags.insert(.command)
            case "shift": flags.insert(.shift)
            case "opt", "alt": flags.insert(.option)
            case "ctrl": flags.insert(.control)
            default: return nil
            }
        }
        func fn(_ c: Int) -> String { SelfTest.function(c) }
        let named: [String: String] = [
            "plus": "+", "minus": "-", "equal": "=", "space": " ", "escape": "\u{1b}", "return": "\r",
            "tab": "\t", "delete": fn(NSDeleteFunctionKey), "backspace": "\u{8}",
            "up": fn(NSUpArrowFunctionKey), "down": fn(NSDownArrowFunctionKey),
            "left": fn(NSLeftArrowFunctionKey), "right": fn(NSRightArrowFunctionKey),
            "pageup": fn(NSPageUpFunctionKey), "pagedown": fn(NSPageDownFunctionKey),
            "home": fn(NSHomeFunctionKey), "end": fn(NSEndFunctionKey), "comma": ",", "period": ".",
            "bracketleft": "[", "bracketright": "]", "slash": "/", "question": "?",
        ]
        if let c = named[last] { return (c, flags) }
        if last.hasPrefix("f"), let n = Int(last.dropFirst()), (1...35).contains(n) { return (fn(NSF1FunctionKey + n - 1), flags) }
        if last.count == 1 { return (last, flags) }
        return nil
    }

    private func menuItem(_ eq: String, _ flags: NSEvent.ModifierFlags) -> NSMenuItem? {
        func walk(_ m: NSMenu) -> NSMenuItem? {
            for it in m.items {
                if let sub = it.submenu, let f = walk(sub) { return f }
                if !it.keyEquivalent.isEmpty, it.keyEquivalent == eq,
                   it.keyEquivalentModifierMask.intersection([.command, .shift, .option, .control]) == flags {
                    return it
                }
            }
            return nil
        }
        return menu.flatMap(walk)
    }

    /// A key: through the menubar's key equivalents first (as AppKit's performKeyEquivalent
    /// does: the item, its validation and its action), else the page view's keys (keyDown).
    private func key(_ spec: String) {
        guard let (chars, flags) = keySpec(spec) else { check(false, "bad key \(spec)"); return }
        if let item = menuItem(chars, flags) {
            let enabled = wc.validateMenuItem(item)
            vars["via"] = "menu:\(item.title)"
            say("  \(spec): menu item “\(item.title)”\(item.isHidden ? " (hidden alternate)" : "")\(enabled ? "" : " — disabled")")
            guard enabled else { vars["ran"] = "0"; waitIdle(); return }
            let mark = closeMark()
            defer { if item.tag == Commands.id(SAFEPDF_CMD_CLOSE), item.action == MainMenu.commandSelector { settleClose(mark, should: nil) } }
            timed("key \(spec)") {
                switch item.action {
                case MainMenu.commandSelector: wc.performSafePdfCommand(item)
                case MainMenu.actionSelector: wc.performSafePdfAction(item)
                case MainMenu.colorSelector: wc.chooseHighlightColor(item)
                default:
                    skips.append("key \(spec): the standard AppKit item “\(item.title)” is not sent headless")
                }
            }
            vars["ran"] = "1"
        } else {
            var f = flags
            if (chars.unicodeScalars.first?.value ?? 0) >= 0xF700 { f.insert(.function) }
            guard let ev = NSEvent.keyEvent(with: .keyDown, location: .zero, modifierFlags: f, timestamp: 0,
                                            windowNumber: 0, context: nil, characters: chars,
                                            charactersIgnoringModifiers: chars, isARepeat: false, keyCode: 0)
            else { check(false, "key event \(spec)"); return }
            vars["via"] = "page view"
            say("  \(spec): page view key")
            timed("key \(spec)") { canvas.keyDown(with: ev) }
            vars["ran"] = "1"
        }
        wc.updateChrome()
        waitIdle()
    }

    private func zoomPreset(_ label: String) {
        guard let ps = Chrome.zoomPresets(), let i = ps.firstIndex(where: { Self.norm($0.label) == Self.norm(label) })
        else { check(false, "no zoom preset \(label) (have \(Chrome.zoomPresets()?.map(\.label) ?? []))"); return }
        let item = NSMenuItem(title: ps[i].label, action: DocumentToolbar.zoomSelector, keyEquivalent: "")
        item.tag = i
        timed("zoom \(label)") { wc.chooseZoomPreset(item) }
        waitIdle()
    }

    private func viewChoice(_ label: String) {
        guard let vs = Chrome.viewChoices(), let v = vs.first(where: { Self.norm($0.label) == Self.norm(label) })
        else { check(false, "no view choice \(label) (have \(Chrome.viewChoices()?.map(\.label) ?? []))"); return }
        let item = NSMenuItem(title: v.label, action: DocumentToolbar.viewSelector, keyEquivalent: "")
        item.tag = Int(v.choice)
        timed("view \(label)") { wc.chooseViewChoice(item) }
        waitIdle()
    }

    private func colorItem(_ name: String) {
        let names = ["yellow", "green", "blue", "pink", "red"]
        guard let i = names.firstIndex(of: name.lowercased()) else { check(false, "colour \(name)"); return }
        let item = NSMenuItem(title: name, action: MainMenu.colorSelector, keyEquivalent: "")
        item.tag = i
        check(wc.validateMenuItem(item), "the colour item \(name) is disabled")
        timed("colour \(name)") { wc.chooseHighlightColor(item) }
        waitIdle()
    }

    private func tool(_ name: String) {
        let tools = ["select": SAFEPDF_TOOL_SELECT, "highlight": SAFEPDF_TOOL_HIGHLIGHT, "comment": SAFEPDF_TOOL_COMMENT,
                     "text": SAFEPDF_TOOL_TEXT, "draw": SAFEPDF_TOOL_DRAW]
        guard let t = tools[name] else { check(false, "tool \(name)"); return }
        let item = NSMenuItem(title: name, action: MainMenu.toolSelector, keyEquivalent: "")
        item.tag = Int(t.rawValue)
        timed("tool \(name)") { wc.performSafePdfTool(item) }
        waitIdle()
    }

    // MARK: window size, backing scale, appearance

    private func resize(_ a: [String]) {
        guard a.count == 2, let w = Double(a[0]), let h = Double(a[1]) else { check(false, "size W H"); return }
        timed("resize") {
            root.setFrameSize(NSSize(width: w, height: h))
            root.layoutSubtreeIfNeeded()
            pages.liveResizeEnded()
        }
        waitIdle()
        say("  page area \(pages.canvasSize)")
    }

    private func scale(_ a: [String]) {
        guard let s = Double(a.first ?? "") else { check(false, "scale S"); return }
        timed("backing change") {
            canvas.scaleOverride = CGFloat(s)
            if wc.pdf != nil { pages.backingChanged() }
        }
        waitIdle()
    }

    private func dark(_ on: Bool) {
        let ap = on ? NSAppearance(named: .darkAqua) : NSAppearance(named: .aqua)
        root.appearance = ap
        pages.scrollView.appearance = ap
        pages.scrollView.needsDisplay = true
        canvas.needsDisplay = true
    }

    private func shot() -> NSBitmapImageRep? {
        canvas.needsDisplay = true
        return SelfTest.snapshot(pages.scrollView, scale: canvas.backing)
    }

    private func snapshot(_ name: String) {
        guard let rep = shot() else { check(false, "snapshot"); return }
        check(SelfTest.writePNG(rep, "\(out)/\(name).png"), "write \(name).png")
    }

    private func mean(_ rep: NSBitmapImageRep, _ r: CGRect) -> (r: CGFloat, g: CGFloat, b: CGFloat)? {
        let o = pages.scrollView.contentView.bounds.origin
        let s = rep.size.width > 0 ? CGFloat(rep.pixelsWide) / rep.size.width : 1
        let x0 = Int(((r.minX - o.x) * s).rounded(.up)), x1 = Int(((r.maxX - o.x) * s).rounded(.down))
        let y0 = Int(((r.minY - o.y) * s).rounded(.up)), y1 = Int(((r.maxY - o.y) * s).rounded(.down))
        var sr: CGFloat = 0, sg: CGFloat = 0, sb: CGFloat = 0, n: CGFloat = 0
        for y in stride(from: max(0, y0), to: min(rep.pixelsHigh, y1), by: max(1, (y1 - y0) / 40)) {
            for x in stride(from: max(0, x0), to: min(rep.pixelsWide, x1), by: max(1, (x1 - x0) / 40)) {
                guard let c = rep.colorAt(x: x, y: y)?.usingColorSpace(.sRGB) else { continue }
                sr += c.redComponent
                sg += c.greenComponent
                sb += c.blueComponent
                n += 1
            }
        }
        return n > 0 ? (sr / n, sg / n, sb / n) : nil
    }

    private func store(_ prefix: String, _ c: (r: CGFloat, g: CGFloat, b: CGFloat)?) {
        guard let c else { check(false, "\(prefix): nothing measured"); return }
        vars["\(prefix).r"] = String(format: "%.3f", c.r)
        vars["\(prefix).g"] = String(format: "%.3f", c.g)
        vars["\(prefix).b"] = String(format: "%.3f", c.b)
        vars["\(prefix).lum"] = String(format: "%.3f", (c.r + c.g + c.b) / 3)
        say(String(format: "  %@: r %.3f g %.3f b %.3f", prefix, c.r, c.g, c.b))
    }

    /// The paper (a blank corner inside the current page) and the canvas around the pages (the
    /// visible area's left edge strip).
    private func measurePaper() {
        guard let rep = shot(), let pr = canvas.rect(ofPage: canvas.currentPage) else { check(false, "measure-paper"); return }
        let vis = pages.scrollView.contentView.bounds
        let paper = CGRect(x: pr.minX + 2, y: max(pr.minY, vis.minY) + 2, width: 6, height: 6)
        store("paper", mean(rep, paper))
        let bg = CGRect(x: vis.minX, y: vis.minY + 2, width: max(1, min(6, pr.minX - vis.minX - 1)), height: 6)
        store("background", mean(rep, bg))
    }

    /// The colour under the last mark (its rectangle, the middle half).
    private func measureMark() {
        if let mk = pages.marks.model?.listAll().last, !canvas.visiblePages().contains(mk.page) {
            pages.goTo(mk.page)
            wc.updateChrome()
            waitIdle()
        }
        guard let m = pages.marks.model, let mk = m.listAll().last(where: { $0.isHighlight }) ?? m.listAll().last,
              let r = mk.rect,
              let t = canvas.transform(ofPage: mk.page), let rep = shot() else { check(false, "measure-mark"); return }
        let v = t.rect(r)
        store("mark", mean(rep, v.insetBy(dx: v.width / 4, dy: v.height / 4)))
    }

    private func measureSelection() {
        guard let band = pages.text.bands.first, let s = pages.text.selection,
              let t = canvas.transform(ofPage: s.page), let rep = shot() else { check(false, "measure-selection"); return }
        store("selection", mean(rep, canvas.pixelAligned(t.rect(band))))
    }

    // MARK: pointer

    private func wheel(_ a: [String]) {
        guard a.count >= 2, let dy = Int32(a[0]), let n = Int(a[1]) else { check(false, "wheel DY N"); return }
        var sent = 0
        var seen = [canvas.currentPage + 1]
        defer {
            vars["wheel_pages"] = seen.map(String.init).joined(separator: ",")
            let up = zip(seen, seen.dropFirst()).allSatisfy { $0 < $1 }
            let down = zip(seen, seen.dropFirst()).allSatisfy { $0 > $1 }
            vars["wheel_monotonic"] = up || down ? "1" : "0"
            say("  wheel: pages \(vars["wheel_pages"] ?? "")")
        }
        var emulated = 0
        do {
            for _ in 0..<n {
                guard let cg = CGEvent(scrollWheelEvent2Source: nil, units: .pixel, wheelCount: 1, wheel1: dy,
                                       wheel2: 0, wheel3: 0), let e = NSEvent(cgEvent: cg) else { break }
                let clip = pages.scrollView.contentView
                let o = clip.bounds.origin
                let page = canvas.currentPage
                timed("wheel event") { pages.scrollView.scrollWheel(with: e) }
                if clip.bounds.origin == o && canvas.currentPage == page && canvas.modes.continuous {
                    // NSScrollView scrolls only in a window: the session moves the clip view by the
                    // event's precise delta as AppKit's own scrolling does (no momentum, no
                    // elasticity); the page view follows through its bounds-changed observer.
                    let maxY = max(0, canvas.frame.height - clip.bounds.height)
                    let y = min(max(0, o.y - e.scrollingDeltaY), maxY)
                    timed("wheel event") {
                        clip.scroll(to: NSPoint(x: o.x, y: y))
                        pages.scrollView.reflectScrolledClipView(clip)
                    }
                    emulated += 1
                }
                sent += 1
                RunLoop.main.run(mode: .default, before: Date(timeIntervalSinceNow: 0.001))
                let p = canvas.currentPage + 1
                if seen.last != p { seen.append(p) }
            }
        }
        if sent == 0 { skips.append("wheel: no CGEvent scroll events in this session") }
        if emulated > 0 { say("  wheel: \(emulated) of \(sent) events scrolled by the session (continuous mode, AppKit's scrolling)") }
        vars["wheel_events"] = String(sent)
        wc.updateChrome()
        waitIdle()
    }

    private func index(_ p: Int) -> SelectPage? {
        var done: TextOutcome<SelectPage>? = nil
        pages.text.store.withIndex(p, priority: Int32(SAFEPDF_PRIO_CURRENT)) { done = $0 }
        pump(60) { done != nil }
        if case .ready(let sp)? = done { return sp }
        return nil
    }

    private func glyphPoint(_ page: Int, _ g: Int) -> CGPoint? {
        guard let sp = index(page), g >= 0, g < sp.cellCount, let t = canvas.transform(ofPage: page) else { return nil }
        let b = sp.boxes[g]
        return t.view((b.llx + b.urx) / 2, (b.lly + b.ury) / 2)
    }

    private func glyphClick(_ a: [String], clicks: Int) {
        guard a.count == 2, let p = Int(a[0]), let g = Int(a[1]), let v = glyphPoint(p - 1, g) else {
            check(false, "glyph PAGE INDEX: no such glyph")
            return
        }
        timed("click") {
            pages.marks.pointerDown(at: v, clicks: clicks, shift: false)
            pages.marks.pointerUp(at: v)
        }
        wc.updateChrome()
        waitIdle()
    }

    private func drag(_ a: [String]) {
        guard a.count == 3, let p = Int(a[0]), let g0 = Int(a[1]), let g1 = Int(a[2]),
              let v0 = glyphPoint(p - 1, g0), let v1 = glyphPoint(p - 1, g1) else { check(false, "drag PAGE A B"); return }
        timed("drag") {
            pages.marks.pointerDown(at: v0, clicks: 1, shift: false)
            pages.marks.pointerDragged(at: CGPoint(x: (v0.x + v1.x) / 2, y: (v0.y + v1.y) / 2))
            pages.marks.pointerDragged(at: v1)
            pages.marks.pointerUp(at: v1)
        }
        wc.updateChrome()
        waitIdle()
    }

    /// Double click on the current search hit (its first box).
    private func hitClick() {
        guard let h = pages.text.find.hit, let hs = pages.text.find.hits(h.page), h.index < hs.count,
              let b = hs[h.index].first, let t = canvas.transform(ofPage: h.page) else { check(false, "no current hit"); return }
        let v = t.view((b.llx + b.urx) / 2, (b.lly + b.ury) / 2)
        timed("double click") {
            pages.marks.pointerDown(at: v, clicks: 2, shift: false)
            pages.marks.pointerUp(at: v)
        }
        wc.updateChrome()
        waitIdle()
    }

    // MARK: find, links, outline

    private func find(forward: Bool, typed: Bool) {
        let t0 = Core.nowMs()
        timed("find") { pages.text.find.step(raw: lastQuery, forward: forward) }
        pump(60) { !pages.text.find.searching }
        vars["find_ms"] = String(format: "%.0f", Core.nowMs() - t0)
        wc.updateChrome()
        waitIdle()
        say("  find: \(pages.text.find.lastMessage) (\(vars["find_ms"] ?? "?") ms)")
    }

    private func link(_ a: [String]) {
        guard a.count == 2, let p = Int(a[0]), let i = Int(a[1]) else { check(false, "link PAGE N"); return }
        var got: TextOutcome<PageLinks>? = nil
        pages.text.store.withLinks(p - 1, priority: Int32(SAFEPDF_PRIO_CURRENT)) { got = $0 }
        pump(60) { got != nil }
        guard case .ready(let ls)? = got, i - 1 < ls.links.count, i >= 1 else { check(false, "page \(p) has no link \(i)"); return }
        // The click itself, through the canvas's pointer (Links.linkAt at the link's centre).
        let l = ls.links[i - 1]
        say("  link \(i): \(ls.describe(i - 1, labels: wc.pdf?.labels ?? [], pages: wc.pdf?.pageCount ?? 0))")
        let r = l.box
        var hitPoint: (Double, Double)? = nil
        for fy in stride(from: 0.1, through: 0.9, by: 0.1) where hitPoint == nil {
            for fx in stride(from: 0.1, through: 0.9, by: 0.1) {
                let x = r.llx + (r.urx - r.llx) * fx, y = r.lly + (r.ury - r.lly) * fy
                if ls.index(at: x, y) == i - 1 { hitPoint = (x, y); break }
            }
        }
        if let t = canvas.transform(ofPage: p - 1), let hp = hitPoint {
            let v = t.view(hp.0, hp.1)
            timed("link click") {
                pages.marks.pointerMoved(at: v)
                pages.marks.pointerDown(at: v, clicks: 1, shift: false)
                pages.marks.pointerUp(at: v)
            }
            vars["hover_cursor"] = pages.text.cursor == SAFEPDF_CURSOR_POINTING_HAND.rawValue ? "hand" : "other"
        } else {
            timed("link") { pages.text.links.activate(ls, i - 1) }
        }
        pump(5) { pages.text.links.pendingURI != nil || idle }
        vars["uri"] = pages.text.links.pendingURI ?? ""
        wc.updateChrome()
        waitIdle()
    }

    private func linkAnswer(_ copy: Bool) {
        guard let uri = pages.text.links.pendingURI else { check(false, "no external link is waiting"); return }
        if let a = pages.text.links.pendingAlert {
            check(a.buttons.map(\.title) == ["Copy Address", "Cancel"] && LinkController.shownAddress(a) == uri,
                  "the external-link sheet: \(a.buttons.map(\.title)) \(LinkController.shownAddress(a) ?? "-")")
        }
        pages.text.links.answer(copy: copy, uri: uri)
    }

    private func outline(_ which: String) {
        let rows = wc.sidebar.outline.rows
        guard !rows.isEmpty else { check(false, "no outline"); return }
        var i = Int(which) ?? 0
        if which == "third" { i = rows.count / 3 }
        if which == "last" { i = rows.count - 1 }
        guard rows.indices.contains(i) else { check(false, "outline row \(which) of \(rows.count)"); return }
        let before = canvas.currentPage
        let t0 = Core.nowMs()
        timed("outline") { wc.sidebar.outline.activate(i) }
        wc.updateChrome()
        waitIdle()
        vars["outline_title"] = rows[i].title
        vars["outline_ms"] = String(format: "%.0f", Core.nowMs() - t0)
        say("  outline row \(i) “\(rows[i].title)”: page \(before + 1) -> \(canvas.currentPage + 1) (\(vars["outline_ms"] ?? "?") ms)")
    }

    private func outlineAnswer(_ copy: Bool) {
        guard let uri = pendingOutlineURI else { check(false, "no outline address is waiting"); return }
        pendingOutlineURI = nil
        // The window's confirmUri, with the private pasteboard.
        if copy {
            pb.clearContents()
            pb.setString(uri, forType: .string)
            pages.pill.show("copied the link address to the clipboard (not opened): \(uri)")
        } else {
            pages.pill.show("external link not followed: \(uri)")
        }
    }

    private func panel(_ name: String) {
        let ps = ["thumbnails": SAFEPDF_PANEL_THUMBNAILS, "outline": SAFEPDF_PANEL_OUTLINE,
                  "attachments": SAFEPDF_PANEL_ATTACHMENTS, "layers": SAFEPDF_PANEL_LAYERS]
        guard let p = ps[name] else { check(false, "panel \(name)"); return }
        timed("panel") {
            wc.sidebar.choose(p)
            wc.setSidebar(shown: true)
        }
        waitIdle()
    }

    private func attachSave(_ a: [String]) {
        guard a.count == 2, let i = Int(a[0]) else { check(false, "attach-save I PATH"); return }
        var msg: String? = nil
        wc.sidebar.attachments.save(i - 1, to: URL(fileURLWithPath: a[1])) { msg = $0 }
        pump(30) { msg != nil }
        vars["attach"] = msg ?? ""
        say("  \(msg ?? "no answer")")
    }

    private func layer(_ a: [String]) {
        guard let i = Int(a.first ?? "") else { check(false, "layer I"); return }
        var changed = false
        timed("layer") { changed = wc.sidebar.layers.toggle(i - 1) }
        vars["layer_changed"] = changed ? "1" : "0"
        waitIdle()
    }

    // MARK: marks

    private func note(_ text: String) {
        command("add note", mustRun: true)
        check(pages.marks.noteOpen != nil, "no note editor open after Add note")
        timed("note save") { pages.marks.noteSave(text) }
        wc.updateChrome()
        waitIdle()
    }

    private func noteClose(_ shown: String) {
        check(pages.marks.noteOpen != nil, "no note editor open")
        timed("note close") { pages.marks.noteCloseWithoutSave(shown) }
        wc.updateChrome()
        waitIdle()
    }

    /// A note at page point (x, y) of PAGE (the context menu's Add note…), its editor left open.
    private func noteAt(_ a: [String]) {
        guard a.count == 3, let p = Int(a[0]), let x = Double(a[1]), let y = Double(a[2]),
              let t = canvas.transform(ofPage: p - 1) else { check(false, "note-at PAGE X Y"); return }
        timed("note at") { pages.marks.addNote(at: t.view(x, y)) }
        wc.updateChrome()
        waitIdle()
    }

    /// A note left of the last mark (the Tk session's right click left of the highlight, then
    /// Add note… in the context menu): its editor stays open.
    private func noteLeft() {
        guard let m = pages.marks.model, let mk = m.listAll().last, let r = mk.rect,
              let t = canvas.transform(ofPage: mk.page) else { check(false, "note-left: no mark"); return }
        let x = max(r.llx - 18, 4), y = (r.lly + r.ury) / 2
        timed("note at") { pages.marks.addNote(at: t.view(x, y)) }
        wc.updateChrome()
        waitIdle()
    }

    private func selectMark(_ which: String, open: Bool = false) {
        guard let m = pages.marks.model, let mk = (which == "first" ? m.listAll().first : m.listAll().last),
              let t = canvas.transform(ofPage: mk.page) else { check(false, "no mark to select"); return }
        let pt: CGPoint
        if let p = mk.point, mk.isNote {
            pt = CGPoint(x: p.x + 2, y: p.y - 2)
        } else if let r = mk.rect {
            pt = CGPoint(x: (r.llx + r.urx) / 2, y: (r.lly + r.ury) / 2)
        } else {
            check(false, "the mark has no place")
            return
        }
        // A click on it (the canvas's pointer: the marks first).
        let v = t.view(Double(pt.x), Double(pt.y))
        timed("select mark") {
            pages.marks.pointerDown(at: v, clicks: 1, shift: false)
            pages.marks.pointerUp(at: v)
        }
        if pages.marks.markSel != mk.id || open { _ = pages.marks.selectMark(page: mk.page, at: pt, openIt: open) }
        check(pages.marks.markSel == mk.id, "the \(mk.name) is not selected")
        wc.updateChrome()
        waitIdle()
    }

    private func freeText(_ a: [String], _ text: String) {
        guard a.count >= 3, let p = Int(a[0]), let x = Double(a[1]), let y = Double(a[2]),
              let t = canvas.transform(ofPage: p - 1) else { check(false, "freetext PAGE X Y TEXT"); return }
        tool("text")
        let v = t.view(x, y)
        timed("text box") {
            pages.marks.pointerDown(at: v, clicks: 1, shift: false)
            pages.marks.pointerUp(at: v)
            pages.marks.freeTextString = text
            pages.marks.commitFreeText()
        }
        tool("text")
        wc.updateChrome()
        waitIdle()
    }

    private func ink(_ a: [String]) {
        guard a.count == 3, let p = Int(a[0]), let x = Double(a[1]), let y = Double(a[2]),
              let t = canvas.transform(ofPage: p - 1) else { check(false, "ink PAGE X Y"); return }
        tool("draw")
        let v = t.view(x, y)
        timed("stroke") {
            pages.marks.pointerDown(at: v, clicks: 1, shift: false)
            for i in 1...6 { pages.marks.pointerDragged(at: CGPoint(x: v.x + CGFloat(i) * 10, y: v.y + CGFloat(i % 2) * 4)) }
            pages.marks.pointerUp(at: CGPoint(x: v.x + 60, y: v.y))
        }
        tool("select")
        wc.updateChrome()
        waitIdle()
    }

    // MARK: files

    private func copyFile(_ a: [String]) {
        guard a.count == 2 else { check(false, "copy-file SRC DST"); return }
        try? FileManager.default.removeItem(atPath: a[1])
        check((try? FileManager.default.copyItem(atPath: a[0], toPath: a[1])) != nil, "copy \(a[0]) -> \(a[1])")
    }

    private func appendFile(_ path: String, _ text: String) {
        guard let fh = FileHandle(forWritingAtPath: path) else { check(false, "append to \(path)"); return }
        fh.seekToEndOfFile()
        fh.write(Data((text + "\n").utf8))
        try? fh.close()
    }

    /// `prefix A B`: A's bytes are a prefix of B, and B is longer (C7: Save appends).
    private func prefix(_ a: [String]) {
        guard a.count == 2, let x = FileManager.default.contents(atPath: a[0]),
              let y = FileManager.default.contents(atPath: a[1]) else { check(false, "prefix A B: unreadable"); return }
        check(y.count > x.count && y.prefix(x.count) == x, "\(a[0]) (\(x.count) bytes) is not a prefix of \(a[1]) (\(y.count) bytes)")
        say("  prefix: \(x.count) -> \(y.count) bytes (\(y.count - x.count) appended)")
    }

    // MARK: state

    /// Every command's accelerator from the exported table and the menubar item AppKit would
    /// match for it (`keys` stores how many accelerators reach their own command).
    private func listKeys() {
        var good = 0, total = 0
        for c in Chrome.commands() ?? [] where !c.accel.key.isEmpty {
            total += 1
            var via = "page view (no menu key equivalent)"
            if KeyEquivalents.usableInMenu(c.accel), let (eq, flags) = KeyEquivalents.translate(c.accel) {
                if let it = menuItem(eq, flags) {
                    via = "menu “\(it.title)” tag \(it.tag) key \(Self.shown(eq, flags))"
                    if it.tag == c.id && it.action == MainMenu.commandSelector { good += 1 }
                } else {
                    via = "NOT IN THE MENUBAR"
                }
            } else if let (eq, flags) = KeyEquivalents.translate(c.accel),
                      let ev = NSEvent.keyEvent(with: .keyDown, location: .zero, modifierFlags: flags, timestamp: 0,
                                                windowNumber: 0, context: nil, characters: eq,
                                                charactersIgnoringModifiers: eq, isARepeat: false, keyCode: 0),
                      PageKeys.shared.command(for: ev) == c.id {
                via = "page view key"
                good += 1
            }
            say("  \(c.name) “\(c.label)” \(c.accel.shown): \(via)")
        }
        vars["keys"] = "\(good)/\(total)"
    }

    /// A key equivalent as the menu shows it (⌃⌥⇧⌘ and the key).
    static func shown(_ eq: String, _ f: NSEvent.ModifierFlags) -> String {
        var s = ""
        if f.contains(.control) { s += "⌃" }
        if f.contains(.option) { s += "⌥" }
        if f.contains(.shift) { s += "⇧" }
        if f.contains(.command) { s += "⌘" }
        let names: [Int: String] = [NSPageUpFunctionKey: "PageUp", NSPageDownFunctionKey: "PageDown",
                                    NSUpArrowFunctionKey: "↑", NSDownArrowFunctionKey: "↓",
                                    NSHomeFunctionKey: "Home", NSEndFunctionKey: "End", NSDeleteFunctionKey: "⌦"]
        if let u = eq.unicodeScalars.first, let n = names[Int(u.value)] { return s + n }
        if let u = eq.unicodeScalars.first, u.value >= UInt32(NSF1FunctionKey), u.value <= UInt32(NSF1FunctionKey + 34) {
            return s + "F\(Int(u.value) - NSF1FunctionKey + 1)"
        }
        return s + eq.uppercased()
    }

    /// The share of ink (pixels darker than 0.9) on the current page (`ink`), and its size in
    /// pixels.
    private func measureInk() {
        guard let rep = shot(), let pr = canvas.rect(ofPage: canvas.currentPage) else { check(false, "measure-ink"); return }
        let vis = pages.scrollView.contentView.bounds
        let r = pr.intersection(vis)
        let s = CGFloat(rep.pixelsWide) / max(1, rep.size.width)
        let x0 = Int(((r.minX - vis.minX) * s).rounded(.up)), x1 = Int(((r.maxX - vis.minX) * s).rounded(.down))
        let y0 = Int(((r.minY - vis.minY) * s).rounded(.up)), y1 = Int(((r.maxY - vis.minY) * s).rounded(.down))
        var dark = 0, n = 0
        let step = max(1, (x1 - x0) / 200)
        for y in stride(from: max(0, y0), to: min(rep.pixelsHigh, y1), by: step) {
            for x in stride(from: max(0, x0), to: min(rep.pixelsWide, x1), by: step) {
                guard let c = rep.colorAt(x: x, y: y)?.usingColorSpace(.sRGB) else { continue }
                n += 1
                if (c.redComponent + c.greenComponent + c.blueComponent) / 3 < 0.9 { dark += 1 }
            }
        }
        vars["ink"] = String(format: "%.4f", n > 0 ? Double(dark) / Double(n) : 0)
        vars["page-px"] = "\(x1 - x0)x\(y1 - y0)"
        say("  ink \(vars["ink"] ?? "?") of \(vars["page-px"] ?? "?") px")
    }

    private func measureState() {
        for k in ["page", "pages", "zoom", "choice", "scroll", "spread", "rotation", "title", "subtitle", "pill",
                  "dirty", "marks", "saved", "selection", "sidebar", "panel", "key", "errors"] {
            say("  \(k) = \(value(k))")
        }
    }

    private func enabled(_ name: String) -> Bool {
        guard let id = commandIds[Self.norm(name)] else { return false }
        wc.updateChrome()
        return wc.isEnabled(id)
    }

    private func value(_ key: String) -> String {
        if let v = vars[key] { return v }
        let doc = wc.pdf
        if key.hasPrefix("enabled:") { return enabled(String(key.dropFirst(8))) ? "1" : "0" }
        if key.hasPrefix("radio:") {
            guard let id = commandIds[Self.norm(String(key.dropFirst(6)))] else { return "?" }
            let item = NSMenuItem(title: "", action: MainMenu.commandSelector, keyEquivalent: "")
            item.tag = id
            _ = wc.validateMenuItem(item)
            return item.state == .on ? "1" : "0"
        }
        if key.hasPrefix("layer:") {
            return wc.sidebar.layers.checked((Int(key.dropFirst(6)) ?? 0) - 1).map { $0 ? "1" : "0" } ?? "-"
        }
        if key.hasPrefix("file:") {
            let p = String(key.dropFirst(5))
            return FileManager.default.contents(atPath: p).map { String(decoding: $0, as: UTF8.self) } ?? "<missing>"
        }
        if key.hasPrefix("size:") {
            return FileManager.default.contents(atPath: String(key.dropFirst(5))).map { String($0.count) } ?? "-1"
        }
        let m = pages.marks.model
        switch key {
        case "page": return String(canvas.currentPage + 1)
        case "pages": return String(doc?.pageCount ?? 0)
        case "doc": return doc?.url.lastPathComponent ?? ""
        case "zoom": return pages.shownPct.map(String.init) ?? "-"
        case "choice": return ZoomModel.label(canvas.zoomChoice)
        case "scroll": return canvas.modes.scroll == SAFEPDF_SCROLL_PAGE.rawValue ? "page" : "vertical"
        case "spread":
            switch canvas.modes.spread {
            case SAFEPDF_SPREAD_ODD.rawValue: return "odd"
            case SAFEPDF_SPREAD_EVEN.rawValue: return "even"
            default: return "none"
            }
        case "rtl": return canvas.modes.rtl ? "1" : "0"
        case "rotation": return String(canvas.userRotation)
        case "title": return wc.window?.title ?? ""
        case "subtitle": return wc.window?.subtitle ?? ""
        case "pill": return pages.pill.history.last ?? ""
        case "pills": return pages.pill.history.joined(separator: " | ")
        case "edited": return wc.window?.isDocumentEdited == true ? "1" : "0"
        case "dirty": return pages.marks.dirty ? "1" : "0"
        case "marks": return String(m?.state.mark_count ?? 0)
        case "saved": return String(m?.listAll().filter(\.isSaved).count ?? 0)
        case "undo-depth": return String(m?.state.undo_depth ?? 0)
        case "last-mark":
            guard let mk = m?.listAll().last else { return "none" }
            return "\(mk.name) p\(mk.page + 1) \(MarksPalette.name(mk.color)) \(mk.text)"
        case "kinds":
            return (m?.listAll() ?? []).map { $0.isHighlight ? "H" : $0.isNote ? "N" : $0.isFreeText ? "T" : $0.isInk ? "I" : "?" }
                .joined()
        case "mark-selected": return pages.marks.markSel == nil ? "0" : "1"
        case "note-open": return pages.marks.noteOpen == nil ? "0" : "1"
        case "tool": return String(pages.marks.pressedTool)
        case "selection":
            guard let s = pages.text.selection else { return "none" }
            return "p\(s.page + 1):\(s.first)-\(s.last)"
        case "clipboard": return pb.string(forType: .string) ?? ""
        case "sidebar": return wc.sidebar.isShown ? "shown" : "hidden"
        case "panel":
            switch wc.sidebar.panel {
            case SAFEPDF_PANEL_OUTLINE: return "outline"
            case SAFEPDF_PANEL_ATTACHMENTS: return "attachments"
            case SAFEPDF_PANEL_LAYERS: return "layers"
            default: return "thumbnails"
            }
        case "buttons": return String(wc.sidebar.buttons.count)
        case "outline-rows": return String(wc.sidebar.outline.rows.count)
        case "attachments": return String(wc.sidebar.attachments.rows.count)
        case "attachment-names": return wc.sidebar.attachments.rows.map(\.name).joined(separator: ",")
        case "layer-rows": return String(wc.sidebar.layers.rows.count)
        case "find": return pages.text.find.lastMessage
        case "hit": return pages.text.find.hit.map { "\($0.page + 1):\($0.index)" } ?? "none"
        case "uri-pending": return pages.text.links.pendingURI ?? pendingOutlineURI ?? ""
        case "history-back": return pages.history.canBack ? "1" : "0"
        case "errors": return String(canvas.errors.count)
        case "key":
            guard let k = canvas.place(ofPage: canvas.currentPage)?.key else { return "-" }
            return "\(k.num)/\(k.den)"
        case "backing": return String(format: "%g", canvas.backing)
        case "encrypted": return doc?.encrypted == true ? "1" : "0"
        case "repaired": return doc?.repaired == true ? "1" : "0"
        case "orient":
            guard let r = canvas.rect(ofPage: canvas.currentPage) else { return "-" }
            return r.width > r.height ? "landscape" : "portrait"
        case "top": return String(format: "%.1f", pages.visibleTop)
        case "centre-x", "centre-y", "centre-page":
            guard let a = canvas.anchor(at: pages.centreAnchor().doc) else { return "-" }
            let z = ZoomModel.double(a.zoom)
            if key == "centre-page" { return String(a.page + 1) }
            return String(format: "%.2f", Double(key == "centre-x" ? a.q.x : a.q.y) / max(z, 1e-9))
        case "viewchoice":
            let c = canvas.modes.choice
            return Chrome.viewChoices()?.first { $0.choice == c }?.label ?? "-"
        case "page-w": return canvas.rect(ofPage: canvas.currentPage).map { String(format: "%.1f", $0.width) } ?? "-"
        case "page-h": return canvas.rect(ofPage: canvas.currentPage).map { String(format: "%.1f", $0.height) } ?? "-"
        case "page2-x":
            return canvas.rect(ofPage: 1).map { String(format: "%.1f", $0.minX) } ?? "-"
        case "page1-x":
            return canvas.rect(ofPage: 0).map { String(format: "%.1f", $0.minX) } ?? "-"
        case "laid-out": return String(canvas.places.count)
        case "visible-pages": return canvas.visiblePages().map { String($0 + 1) }.joined(separator: ",")
        case "asked": return dialogs.asked.last.map { "\($0.title) [\($0.keys.joined(separator: " "))] \($0.message)" } ?? ""
        case "asked-count": return String(dialogs.asked.count)
        case "maxblock": return String(format: "%.0f", maxBlockMs)
        case "policy": return NSApp.activationPolicy() == .prohibited ? "prohibited" : "other"
        case "visible-windows": return String(NSApp.windows.filter(\.isVisible).count)
        case "cursor": return String(pages.text.cursor)
        case "doc-title": return doc?.settings.title ?? "-"
        default: return "<unknown key \(key)>"
        }
    }

    private func expect(_ line: String) {
        let w = words(line)
        guard w.count >= 3 else { check(false, "expect KEY OP VALUE"); return }
        let key = w[1], op = w[2]
        var want = rest(line, after: 3)
        if want.hasPrefix("@"), let v = vars[String(want.dropFirst())] { want = v }
        let got = value(key)
        let ok: Bool
        switch op {
        case "=": ok = got == want
        case "!=": ok = got != want
        case "~": ok = got.contains(want)
        case "!~": ok = !got.contains(want)
        case "^": ok = got.hasPrefix(want)
        case "<", ">", "<=", ">=":
            if let g = Double(got), let x = Double(want) {
                ok = op == "<" ? g < x : op == ">" ? g > x : op == "<=" ? g <= x : g >= x
            } else {
                ok = false
            }
        case "near":
            // `expect KEY near VALUE TOL`
            let parts = words(want)
            if parts.count == 2, let g = Double(got), let x = Double(parts[0].hasPrefix("@") ? (vars[String(parts[0].dropFirst())] ?? "") : parts[0]),
               let tol = Double(parts[1]) {
                ok = abs(g - x) <= tol
            } else {
                ok = false
            }
        default: ok = false
        }
        say("  expect \(key) \(op) \(want): \(ok ? "ok" : "FAILED") (\(got.prefix(300)))")
        check(ok, "expect \(key) \(op) \(want): got \(got.prefix(300))")
    }

    // MARK: corpus pass (M8)

    /// Next page from the first page to the last, waiting after each step until the new current
    /// page has its image and no render is pending (the Tk driver's wait); per page the time to
    /// display (the render's request to its delivery on the main thread), the wait after Next
    /// page, render errors, the longest block of the main thread, the peak footprints. Writes
    /// DIR/corpus.json.
    private func corpusPass() {
        guard let doc = wc.pdf else {
            writeCorpus(["opened": false, "file": vars["file"] ?? ""])
            check(false, "corpus-pass: no document")
            return
        }
        let n = doc.pageCount
        var waits: [Double] = []
        var missing: [Int] = []
        if canvas.currentPage != 0 { pages.goTo(0); waitIdle() }
        var guardSteps = 0
        while canvas.currentPage < n - 1 && guardSteps < n + 5 {
            guardSteps += 1
            let from = canvas.currentPage
            let t0 = Core.nowMs()
            timed("next page") { _ = wc.run(Commands.id(SAFEPDF_CMD_NEXT_PAGE)) }
            let cur = canvas.currentPage
            pump(30) { (firstImage[cur] != nil || renderErrors[cur] != nil) && canvas.pendingCount == 0 }
            waits.append(Core.nowMs() - t0)
            if cur == from { break }
        }
        waitIdle()
        for p in 0..<n where firstImage[p] == nil && renderErrors[p] == nil { missing.append(p + 1) }
        sampleMemory()
        let ttd = (0..<n).map { firstImage[$0] ?? -1 }
        let res: [String: Any] = [
            "file": doc.url.lastPathComponent, "opened": true, "pages": n,
            "open_ms": openToFirst ?? -1, "ttd_ms": ttd, "wait_ms": waits,
            "errors": Dictionary(uniqueKeysWithValues: renderErrors.map { (String($0.key + 1), $0.value) }),
            "missing": missing, "last_page": canvas.currentPage + 1,
            "max_block_ms": maxBlockMs, "max_block_what": maxBlockWhat,
            "peak_app_bytes": peakSelf, "peak_worker_bytes": peakChild,
            "encrypted": doc.encrypted, "repaired": doc.repaired,
        ]
        writeCorpus(res)
        say(String(format: "  corpus: %d pages, %d displayed, %d errors, %d missing; last page %d; longest block %.0f ms",
                   n, n - missing.count - renderErrors.count, renderErrors.count, missing.count,
                   canvas.currentPage + 1, res["max_block_ms"] as? Double ?? -1))
        check(missing.isEmpty, "pages never displayed: \(missing.prefix(20))")
    }

    private func writeCorpus(_ obj: [String: Any]) {
        guard let d = try? JSONSerialization.data(withJSONObject: obj, options: [.sortedKeys]) else { return }
        try? d.write(to: URL(fileURLWithPath: "\(out)/corpus.json"))
    }
}
