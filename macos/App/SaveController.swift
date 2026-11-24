// SaveController.swift — Save, Save As…, the unsaved-marks question and XFDF import / export
// (task 11.3e2). Plan.md §4 S8/C7, §6 Phases 9–12; docs/macos-design.md §1–§3 ("Save stays in
// the GUI process"); docs/viewer.md 9.5c, 9.r2, 9.r6, 9.r8, 9.11; docs/crypto-review.md (12.4).
//
// The flow is the Tk viewer's (SafePdf/Shell/App/Viewer.lean: save, overwriteInto, saveAsOnce,
// saveAs, saveTo, afterWrite, checkTarget, dialogDirOf, confirmDiscard, importXfdf, exportXfdf),
// step for step; every rule and text comes from the exported Lean code (safepdf_marks.h:
// save_route, disk_state, write_problem, target_problem, the questions and their buttons,
// unsaved_answer, close_goes_on, default_target, with_ext, dialog_dir, saved_status,
// import_status, tmp_name, save_build with its checks and notes, xfdf_export / _import). This
// file does the file I/O (the capped read-back, the atomic write: a temporary file in the
// target's folder, read back, the replaced file's permissions, rename) and the dialogs.
//
// IVs (task 12.4): every save of an encrypted document passes 64 fresh bytes from
// SecRandomCopyBytes; without them nothing is saved (the store also refuses, ERR_NEED_SEED).
// The bytes are never logged and are zeroed after the call.
// Output budget (task 12.3b): the Tk viewer reserves a save's output in its 192 MiB work pool
// (Viewer.withOutput); here the pool's ceiling (safepdf_marks_output_ceiling) is the
// `max_output` of a save, and half of it that of an XFDF export (Tk reserves twice the
// export's estimate: the text and its UTF-8 bytes).

import AppKit
import Security
import SafePdfC
import UniformTypeIdentifiers

/// A dialog button: its key (Save.*Buttons: "save", "dontsave", "overwrite", "saveas",
/// "cancel") and label.
struct DialogButton: Equatable {
    let key: String
    let label: String
}

/// The questions and file panels of the save flow: document-modal sheets in the app; the
/// self-test answers them by script (no panel or alert is ever shown headless).
@MainActor protocol SaveDialogs: AnyObject {
    /// Asks `message` with `buttons` (display order, left to right); `dflt` the default key.
    /// `done` gets the key chosen ("cancel" for Escape).
    func choose(_ title: String, _ message: String, buttons: [DialogButton], dflt: String,
                done: @escaping @MainActor (String) -> Void)
    /// A Yes / No question; `done` gets whether Yes was chosen.
    func yesNo(_ title: String, _ message: String, done: @escaping @MainActor (Bool) -> Void)
    /// Asks for a file to write (it confirms replacing an existing file); nil: cancelled.
    func saveURL(_ title: String, directory: URL, name: String, type: UTType,
                 done: @escaping @MainActor (URL?) -> Void)
    /// Asks for a file to read; nil: cancelled.
    func openURL(_ title: String, directory: URL, type: UTType, done: @escaping @MainActor (URL?) -> Void)
}

/// What the save flow works on: the open document and its page view, and the reopen after a
/// save (the window controller; a small host in the self-test).
@MainActor protocol SaveHost: AnyObject {
    var pages: PageViewController { get }
    var pdf: Document? { get }
    /// Opens `url` again after a save, keeping `keep` (9.r8: the only open that carries the view
    /// over). Returns whether it opened.
    func reopenAfterSave(_ url: URL, keep: KeptView?) -> Bool
}

/// A built save (safepdf_save_result, freed with this object).
final class BuiltSave {
    private var r: safepdf_save_result

    init(_ r: safepdf_save_result) { self.r = r }
    deinit { safepdf_free_save_result(&r) }

    var data: Data {
        guard let b = r.bytes else { return Data() }
        return Data(bytes: b, count: r.size)
    }
    var marksWritten: Int { r.marks_written }
    var marksTotal: Int { r.marks_total }
    var appended: Int { r.appended }
    var flags: UInt32 { r.flags }
    var deletedSaved: Int { r.deleted_saved }
    var notes: [String] {
        guard let ns = r.notes else { return [] }
        return (0..<r.note_count).map { Core.string(ns[$0]) }
    }

    /// The status after it was written to `path` (Save.savedStatus).
    func status(path: String) -> String {
        Core.take(safepdf_marks_saved_status(path, &r)) ?? "saved to \(path)"
    }
}

/// Why a file could not be written.
struct WriteError: Error { let message: String }

@MainActor final class SaveController {
    weak var host: SaveHost?
    var dialogs: SaveDialogs
    /// The files this session wrote (Viewer.ownFiles, resolved paths): a further Save into one
    /// asks nothing.
    private(set) var ownFiles: [String] = []
    /// The source of the IV seeds (SecRandomCopyBytes; the self-test may make it fail).
    var randomBytes: (Int) -> [UInt8]? = SaveController.secureRandom
    /// The largest XFDF file read for an import (Xfdf.Limits.maxBytes + 1: the reader refuses
    /// anything larger itself).
    static let importReadCap = 8 * 1024 * 1024 + 1

    init(dialogs: SaveDialogs) { self.dialogs = dialogs }

    private var pages: PageViewController? { host?.pages }
    private var model: MarksModel? { host?.pages.marks.model }

    /// Shows a status message in the pill (the Tk viewer's status line).
    private func status(_ s: String) { pages?.pill.show(s) }

    /// The last status message ("" when none).
    var lastStatus: String { pages?.pill.history.last ?? "" }

    // MARK: helpers (paths, files)

    /// `n` fresh random bytes from the operating system (Security.framework), nil on failure.
    nonisolated static func secureRandom(_ n: Int) -> [UInt8]? {
        var b = [UInt8](repeating: 0, count: n)
        let rc = b.withUnsafeMutableBytes { raw -> Int32 in
            guard let p = raw.baseAddress else { return -1 }
            return SecRandomCopyBytes(kSecRandomDefault, n, p)
        }
        return rc == errSecSuccess ? b : nil
    }

    static func base(_ path: String) -> String { (path as NSString).lastPathComponent }

    /// The folder of `path` ("." when it has none; Viewer.dirOf).
    static func dirOf(_ path: String) -> String {
        let d = (path as NSString).deletingLastPathComponent
        return d.isEmpty ? "." : d
    }

    /// `path` with symbolic links resolved (itself when it does not exist).
    static func resolved(_ path: String) -> String {
        URL(fileURLWithPath: path).resolvingSymlinksInPath().standardizedFileURL.path
    }

    /// Whether two paths name the same file (Viewer.samePath).
    static func samePath(_ a: String, _ b: String) -> Bool { resolved(a) == resolved(b) }

    /// Whether this session wrote `path` (Viewer.isOwn).
    func isOwn(_ path: String) -> Bool { ownFiles.contains { Self.samePath($0, path) } }

    private static func writable(_ path: String) -> Bool { FileManager.default.isWritableFile(atPath: path) }

    private static func isDir(_ path: String) -> Bool {
        var d: ObjCBool = false
        return FileManager.default.fileExists(atPath: path, isDirectory: &d) && d.boolValue
    }

    private static func exists(_ path: String) -> Bool { FileManager.default.fileExists(atPath: path) }

    /// The folder a file dialog for the document `path` starts in (Viewer.dialogDirOf,
    /// Save.dialogDir): its folder when that exists (and, with `write`, is writable), else home.
    static func dialogDir(of path: String, write: Bool = true) -> URL {
        let dir = dirOf(path)
        let usable = isDir(dir) && (writable(dir) || !write)
        let home = ProcessInfo.processInfo.environment["HOME"] ?? ""
        let d = Core.take(safepdf_marks_dialog_dir(dir, usable ? 1 : 0, home)) ?? dir
        return URL(fileURLWithPath: d, isDirectory: true)
    }

    /// A message on one line (Save.oneLine).
    static func oneLine(_ s: String) -> String { Core.take(safepdf_marks_one_line(s)) ?? s }

    /// The buttons of a dialog (SAFEPDF_DIALOG_*) in the macOS order.
    static func buttons(_ dialog: Int32) -> [DialogButton] {
        var b = safepdf_dialog_buttons()
        guard safepdf_marks_dialog_buttons(dialog, 1, &b) == 0 else { return [] }
        let keys = withUnsafeBytes(of: b.key) { Array($0) }
        let labels = withUnsafeBytes(of: b.label) { Array($0) }
        func str(_ bytes: [UInt8], _ i: Int, _ w: Int) -> String {
            let slice = bytes[(i * w)..<((i + 1) * w)]
            return String(decoding: slice.prefix { $0 != 0 }, as: UTF8.self)
        }
        return (0..<min(b.count, 3)).map {
            DialogButton(key: str(keys, $0, 16), label: str(labels, $0, 32))
        }
    }

    /// The file `path` read back for the changed-on-disk check: at most `cap` bytes; nil when it
    /// cannot be opened (missing); empty bytes when a read fails (changed).
    static func readCapped(_ path: String, cap: Int) -> Data? {
        guard let fh = FileHandle(forReadingAtPath: path) else { return nil }
        defer { try? fh.close() }
        do { return try fh.read(upToCount: cap) ?? Data() } catch { return Data() }
    }

    /// The opened file on disk against the bytes the store was opened from (Save.diskStateAt):
    /// SAFEPDF_DISK_*.
    static func diskState(_ m: MarksModel, path: String) -> Int32 {
        guard let d = readCapped(path, cap: m.originalSize + 1) else {
            return safepdf_marks_disk_state(m.handle, nil, 0)
        }
        return d.withUnsafeBytes { raw in
            let p = raw.bindMemory(to: UInt8.self).baseAddress
            // An empty read is still "read": a non-NULL pointer with length 0.
            var zero: UInt8 = 0
            return p.map { safepdf_marks_disk_state(m.handle, $0, raw.count) }
                ?? safepdf_marks_disk_state(m.handle, &zero, 0)
        }
    }

    /// **The atomic write** (Save.writeAtomic): a new temporary file next to `target`
    /// (Save.tmpName), written, closed, read back and compared, given the permissions of the
    /// file it replaces, then renamed over `target`; removed on failure.
    static func writeAtomic(_ target: String, _ data: Data) throws(WriteError) {
        let dir = dirOf(target)
        let stamp = DispatchTime.now().uptimeNanoseconds
        guard let name = Core.take(safepdf_marks_tmp_name(base(target), stamp)) else {
            throw WriteError(message: "no temporary file name")
        }
        let tmp = (dir as NSString).appendingPathComponent(name)
        func fail(_ what: String) -> WriteError {
            let e = WriteError(message: "\(what): \(String(cString: strerror(errno)))")
            unlink(tmp)
            return e
        }
        let fd = open(tmp, O_WRONLY | O_CREAT | O_EXCL, 0o666)
        if fd < 0 { throw fail("cannot create \(tmp)") }
        var off = 0
        let ok: Bool = data.withUnsafeBytes { raw in
            guard let p = raw.baseAddress else { return true }
            while off < raw.count {
                let n = write(fd, p + off, raw.count - off)
                if n <= 0 { return false }
                off += n
            }
            return true
        }
        if !ok {
            close(fd)
            throw fail("cannot write \(tmp)")
        }
        if fsync(fd) != 0 || close(fd) != 0 { throw fail("cannot write \(tmp)") }
        // Capped read-back (task 12.1): more than `data.count` bytes is already a mismatch.
        guard let back = readCapped(tmp, cap: data.count + 1), back == data else {
            unlink(tmp)
            throw WriteError(message: "the temporary file \(tmp) does not read back as written")
        }
        // An overwritten file keeps its mode (Viewer.keepPermissions, task 9.r2).
        if let attrs = try? FileManager.default.attributesOfItem(atPath: target),
           let mode = attrs[.posixPermissions] as? NSNumber {
            if chmod(tmp, mode_t(mode.uint16Value)) != 0 { throw fail("cannot copy the permissions of \(target)") }
        }
        if rename(tmp, target) != 0 { throw fail("cannot rename \(tmp) to \(target)") }
    }

    // MARK: building

    /// Builds the bytes Save writes (safepdf_marks_save_build: C7, strict reopen, read-back of
    /// every mark; fresh IVs for an encrypted document; the output ceiling). On failure the pill
    /// says why (`prefix` names the target), a certified document's refusal is a sheet that
    /// offers the XFDF export instead; nil.
    func build(_ m: MarksModel, prefix: String) -> BuiltSave? {
        var seed: [UInt8] = []
        if m.state.encrypted != 0 {
            guard let s = randomBytes(64), s.count >= 64 else {
                status("\(prefix): no fresh random bytes for the encryption's IVs (the system's random source failed); nothing was written")
                return nil
            }
            seed = s
        }
        defer {
            // The seed is never kept or logged.
            for i in seed.indices { seed[i] = 0 }
        }
        var r = safepdf_save_result()
        var err: UnsafeMutablePointer<CChar>? = nil
        let ceiling = safepdf_marks_output_ceiling()
        let rc: Int32 = seed.withUnsafeBufferPointer { b in
            safepdf_marks_save_build(m.handle, b.count > 0 ? b.baseAddress : nil, b.count, nil, ceiling, &r, &err)
        }
        if rc == Int32(SAFEPDF_SAVE_OK) {
            if let err { free(err) }
            return BuiltSave(r)
        }
        let msg = Core.take(err) ?? "the save failed (\(rc))"
        status("\(prefix): \(msg)")
        if rc == Int32(SAFEPDF_SAVE_ERR_CERTIFIED) {
            // /DocMDP P1/P2: refused; the marks can still leave as XFDF (Save.certifiedRefusal).
            dialogs.choose("This document cannot be saved with marks", msg,
                           buttons: [DialogButton(key: "cancel", label: "OK"),
                                     DialogButton(key: "export", label: "Export Annotations…")],
                           dflt: "export") { [weak self] key in
                if key == "export" { self?.exportXfdf() }
            }
        }
        return nil
    }

    // MARK: Save (Viewer.save, overwriteInto, afterWrite)

    /// **Save** (⌘S; Save.route): nothing to do without unsaved marks; else into the opened file,
    /// asking Overwrite / Save As… / Cancel before the first overwrite of this session
    /// (`confirmed`: the unsaved-marks question said so already). `done` gets whether the marks
    /// are saved afterwards.
    func save(confirmed: Bool = false, done: @escaping @MainActor (Bool) -> Void = { _ in }) {
        guard let doc = host?.pdf, let m = model else { done(false); return }
        let path = doc.url.path
        let st = m.state
        let route = safepdf_marks_save_route(st.dirty, 0, 0, (confirmed || isOwn(path)) ? 1 : 0)
        switch route {
        case Int32(SAFEPDF_ROUTE_NOTHING):
            status("no unsaved marks: nothing to save")
            done(true)
        case Int32(SAFEPDF_ROUTE_SAVE_AS):
            saveAs(done: done)
        case Int32(SAFEPDF_ROUTE_OVERWRITE), Int32(SAFEPDF_ROUTE_OVERWRITE_ASK):
            overwriteInto(path, ask: route == Int32(SAFEPDF_ROUTE_OVERWRITE_ASK)) { [weak self] r in
                if let r { done(r) } else { self?.saveAs(done: done) ?? done(false) }
            }
        default:
            done(false)
        }
    }

    /// **Save into the opened file** `path` (Viewer.overwriteInto): builds first (an encrypted
    /// file without fresh randomness, a certified one, a failed check: refused before any
    /// question); refuses a read-only file or folder; refuses when the file on disk no longer
    /// holds the bytes it was opened from (checked before the question and again just before
    /// writing) and then offers Save As…; with `ask` asks Overwrite / Save As… / Cancel; writes
    /// atomically to the resolved path (a symbolic link stays one) and reopens in place.
    /// `done(nil)`: the user chose Save As….
    func overwriteInto(_ path: String, ask: Bool, done: @escaping @MainActor (Bool?) -> Void) {
        guard let m = model, let pv = pages else { done(false); return }
        let name = Self.base(path)
        guard let built = build(m, prefix: "cannot save to \(name)") else { done(false); return }
        let real = Self.resolved(path)
        let dir = Self.dirOf(real)
        if Self.exists(real),
           let p = Core.take(safepdf_marks_write_problem(name, Self.writable(real) ? 1 : 0, Self.writable(dir) ? 1 : 0)) {
            status("cannot save: \(p)")
            done(false)
            return
        }
        let changed: (Int32) -> Void = { [weak self] ds in
            guard let self else { done(false); return }
            let q = Core.take(safepdf_marks_changed_question(name, ds)) ?? ""
            self.dialogs.choose("File changed on disk", q, buttons: Self.buttons(Int32(SAFEPDF_DIALOG_CHANGED)),
                                dflt: "saveas") { [weak self] key in
                if key == "saveas" { done(nil); return }
                self?.status("not saved: \(name) changed on disk since it was opened; nothing was written (Save As… writes a new file)")
                done(false)
            }
        }
        let d0 = Self.diskState(m, path: real)
        if d0 != Int32(SAFEPDF_DISK_SAME) { changed(d0); return }
        let keep = pv.keptView
        let write: () -> Void = { [weak self] in
            guard let self else { done(false); return }
            let d1 = Self.diskState(m, path: real)
            if d1 != Int32(SAFEPDF_DISK_SAME) { changed(d1); return }
            self.status("saving to \(path)...")
            do {
                try Self.writeAtomic(real, built.data)
            } catch {
                self.status("cannot save to \(name): \(Self.oneLine((error as? WriteError)?.message ?? "\(error)"))")
                done(false)
                return
            }
            self.afterWrite(path, built, keep: pv.keptView ?? keep)
            done(true)
        }
        guard ask else { write(); return }
        let q = Core.take(safepdf_marks_overwrite_question(m.handle, name)) ?? ""
        dialogs.choose("Save", q, buttons: Self.buttons(Int32(SAFEPDF_DIALOG_OVERWRITE)), dflt: "overwrite") { [weak self] key in
            if key == "saveas" { done(nil); return }
            if key != "overwrite" {
                self?.status("save cancelled")
                done(false)
                return
            }
            write()
        }
    }

    /// After a save wrote `path` (Viewer.afterWrite): remembered as written by this session,
    /// reopened keeping the view (9.r8) on the same page, and reported — with the protection
    /// notes and the revision-retention note when saved marks were deleted (12.5).
    private func afterWrite(_ path: String, _ built: BuiltSave, keep: KeptView?) {
        let real = Self.resolved(path)
        ownFiles.removeAll { $0 == real }
        ownFiles.insert(real, at: 0)
        _ = host?.reopenAfterSave(URL(fileURLWithPath: path), keep: keep)
        status(built.status(path: path))
    }

    // MARK: Save As… (Viewer.saveAs, saveAsOnce, saveTo, checkTarget)

    /// **Save As…** (⇧⌘S): one round of `saveAsOnce`, asked again (at most three times) while
    /// the chosen file is the opened one and it changed on disk.
    func saveAs(done: @escaping @MainActor (Bool) -> Void = { _ in }) {
        saveAsRound(0, done: done)
    }

    private func saveAsRound(_ round: Int, done: @escaping @MainActor (Bool) -> Void) {
        guard round < 3 else { done(false); return }
        saveAsOnce { [weak self] r in
            if let r { done(r) } else { self?.saveAsRound(round + 1, done: done) ?? done(false) }
        }
    }

    /// One round: asks for a file proposing STEM-annotated.pdf (Save.defaultTarget) in the
    /// document's folder, checks it (checkTarget) and writes the marks there; the opened file
    /// itself needs an explicit yes (unless this session wrote it) and goes through
    /// `overwriteInto`. `done(nil)`: ask for another file.
    func saveAsOnce(done: @escaping @MainActor (Bool?) -> Void) {
        guard let doc = host?.pdf, model != nil else { done(false); return }
        let path = doc.url.path
        let proposal = Core.take(safepdf_marks_default_target(path)) ?? path
        dialogs.saveURL("Save As", directory: Self.dialogDir(of: path), name: Self.base(proposal), type: .pdf) { [weak self] chosen in
            guard let self else { done(false); return }
            guard let chosen else {
                self.status("save cancelled")
                done(false)
                return
            }
            self.checkTarget(chosen.path, ext: "pdf", export: false) { [weak self] target in
                guard let self, let target else { done(false); return }
                if Self.samePath(target, path) {
                    if self.isOwn(path) {
                        self.overwriteInto(path, ask: false, done: done)
                        return
                    }
                    let q = Core.take(safepdf_marks_opened_overwrite_question(Self.base(path))) ?? ""
                    self.dialogs.yesNo("Save As", q) { [weak self] yes in
                        guard let self else { done(false); return }
                        if !yes {
                            self.status("save cancelled")
                            done(false)
                            return
                        }
                        self.overwriteInto(path, ask: false, done: done)
                    }
                    return
                }
                done(self.saveTo(target))
            }
        }
    }

    /// Writes the document with its unsaved marks to another file `target` (Viewer.saveTo;
    /// Save.write: built and checked, then the atomic write keeping the permissions of a file it
    /// replaces) and opens it on the same page. Returns whether it was written.
    func saveTo(_ target: String) -> Bool {
        guard let m = model, let pv = pages else { return false }
        let name = Self.base(target)
        guard let built = build(m, prefix: "cannot save to \(name)") else { return false }
        status("saving to \(target)...")
        do {
            try Self.writeAtomic(target, built.data)
        } catch {
            status("cannot save to \(name): cannot write \(target): \(Self.oneLine(error.message))")
            return false
        }
        afterWrite(target, built, keep: pv.keptView)
        return true
    }

    /// The file a Save As… or Export panel returned, made ready to write (Viewer.checkTarget,
    /// task 9.r6): the extension added when missing (Save.withExt; when that names an existing
    /// file the panel did not confirm, the user is asked first), then refused when it is a
    /// folder, a read-only file, in a folder that is not writable or — for an export — the
    /// opened document itself (Save.targetProblem). `done(nil)`: nothing is written.
    func checkTarget(_ chosen: String, ext: String, export: Bool, done: @escaping @MainActor (String?) -> Void) {
        let what = export ? "export" : "save"
        let target = Core.take(safepdf_marks_with_ext(chosen, ext)) ?? chosen
        let name = Self.base(target)
        let rest: () -> Void = { [weak self] in
            guard let self else { done(nil); return }
            let isDir = Self.isDir(target)
            let ex = Self.exists(target)
            let fw = ex && Self.writable(target)
            let dw = Self.writable(Self.dirOf(target))
            var opened = false
            if export, let pdf = self.host?.pdf { opened = Self.samePath(target, pdf.url.path) }
            if let p = Core.take(safepdf_marks_target_problem(name, isDir ? 1 : 0, ex ? 1 : 0, fw ? 1 : 0,
                                                              dw ? 1 : 0, opened ? 1 : 0)) {
                self.status("cannot \(what): \(p)")
                done(nil)
                return
            }
            done(target)
        }
        if target != chosen && Self.exists(target) {
            let q = Core.take(safepdf_marks_replace_question(name)) ?? ""
            dialogs.yesNo(export ? "Export Annotations" : "Save As", q) { [weak self] yes in
                if !yes {
                    self?.status("\(what) cancelled")
                    done(nil)
                    return
                }
                rest()
            }
            return
        }
        rest()
    }

    // MARK: the unsaved-marks question (Viewer.confirmDiscard)

    /// **Before `what`** (closing, quitting, opening another file): with unsaved marks asks Save
    /// / Don't Save / Cancel (Save.unsavedQuestion); Save saves into the opened file without a
    /// second question; a failed or cancelled save and Cancel abort `what` (Save.closeGoesOn).
    /// `done` gets whether to go on. Nothing is ever saved without this answer.
    func confirmDiscard(_ what: String, done: @escaping @MainActor (Bool) -> Void) {
        guard let doc = host?.pdf, let m = model, m.state.dirty != 0 else { done(true); return }
        let path = doc.url.path
        let name = Self.base(path)
        let q = Core.take(safepdf_marks_unsaved_question(m.handle, name, what, 0, 0, isOwn(path) ? 0 : 1)) ?? ""
        dialogs.choose("Unsaved marks", q, buttons: Self.buttons(Int32(SAFEPDF_DIALOG_UNSAVED)), dflt: "save") { [weak self] key in
            guard let self else { done(false); return }
            let ans = safepdf_marks_unsaved_answer(key)
            let finish: @MainActor (Bool) -> Void = { [weak self] saved in
                let go = safepdf_marks_close_goes_on(1, ans, saved ? 1 : 0) != 0
                if !go, let self {
                    if ans == Int32(SAFEPDF_ANSWER_CANCEL) {
                        self.status("\(what) cancelled: there are unsaved marks")
                    } else {
                        self.status("\(self.lastStatus); \(what) cancelled")
                    }
                }
                done(go)
            }
            if ans == Int32(SAFEPDF_ANSWER_SAVE) { self.save(confirmed: true, done: finish) } else { finish(false) }
        }
    }

    // MARK: XFDF (Viewer.importXfdf, exportXfdf)

    /// The XFDF file type.
    static var xfdfType: UTType { UTType(filenameExtension: "xfdf") ?? .xml }

    /// **Export annotations…**: every mark (saved or not; Xfdf.toXfdf, dated now, `<f href>` the
    /// PDF's file name) to `url` (else a panel proposing STEM.xfdf), after checkTarget (never
    /// onto the opened PDF), written atomically.
    func exportXfdf(to url: URL? = nil) {
        guard let doc = host?.pdf, model != nil else { return }
        let pdf = doc.url.path
        let go: @MainActor (URL?) -> Void = { [weak self] chosen in
            guard let self else { return }
            guard let chosen else {
                self.status("export cancelled")
                return
            }
            self.checkTarget(chosen.path, ext: "xfdf", export: true) { [weak self] target in
                guard let self, let target, let m = self.model else { return }
                let name = Self.base(target)
                var out = safepdf_marks_bytes()
                var err: UnsafeMutablePointer<CChar>? = nil
                // Tk reserves twice the estimate (the text and its UTF-8 bytes) in its pool.
                let ceiling = safepdf_marks_output_ceiling() / 2
                guard safepdf_marks_xfdf_export(m.handle, Self.base(pdf), nil, ceiling, &out, &err) == 0 else {
                    self.status("cannot export to \(name): \(Core.take(err) ?? "the export failed")")
                    return
                }
                if let err { free(err) }
                defer { safepdf_free_marks_bytes(&out) }
                let data = out.data.map { Data(bytes: $0, count: out.size) } ?? Data()
                do {
                    try Self.writeAtomic(target, data)
                    self.status("exported \(m.state.mark_count) mark(s) to \(name)")
                } catch {
                    self.status("cannot export to \(name): \(Self.oneLine((error as? WriteError)?.message ?? "\(error)"))")
                }
            }
        }
        if let url { go(url); return }
        let proposal = Core.take(safepdf_marks_xfdf_target(pdf)) ?? "annotations.xfdf"
        dialogs.saveURL("Export Annotations", directory: Self.dialogDir(of: pdf), name: Self.base(proposal),
                        type: Self.xfdfType, done: go)
    }

    /// **Import annotations…**: reads the XFDF file `url` (else a panel), adds its marks as
    /// unsaved marks (one undo step; marks already present are not added again) and reports
    /// added / already present / skipped with the first skip's reason; a refused file changes
    /// nothing and the pill says why.
    func importXfdf(from url: URL? = nil) {
        guard let doc = host?.pdf, model != nil else { return }
        let go: @MainActor (URL?) -> Void = { [weak self] chosen in
            guard let self else { return }
            guard let chosen else {
                self.status("import cancelled")
                return
            }
            guard let m = self.model else { return }
            let name = chosen.lastPathComponent
            guard let bytes = Self.readCapped(chosen.path, cap: Self.importReadCap) else {
                self.status("cannot import \(name): cannot read \(chosen.path)")
                return
            }
            switch m.importXfdf(bytes, name: name) {
            case .success(let r): self.status(r.status)
            case .failure(let e): self.status("cannot import \(name): \(e.message)")
            }
        }
        if let url { go(url); return }
        dialogs.openURL("Import Annotations", directory: Self.dialogDir(of: doc.url.path, write: false),
                        type: Self.xfdfType, done: go)
    }
}

/// The dialogs as document-modal sheets on a window (NSAlert, NSSavePanel, NSOpenPanel).
@MainActor final class SheetDialogs: SaveDialogs {
    private let window: () -> NSWindow?

    init(window: @escaping () -> NSWindow?) { self.window = window }

    func choose(_ title: String, _ message: String, buttons: [DialogButton], dflt: String,
                done: @escaping @MainActor (String) -> Void) {
        // NSAlert puts its first button rightmost (the default, Return), the next ones to its
        // left: added right to left, the dialog shows `buttons` in their display order.
        // The default goes first (rightmost), whatever its place in `buttons`.
        let ordered = buttons.filter { $0.key == dflt } + buttons.reversed().filter { $0.key != dflt }
        let alert = NSAlert()
        alert.messageText = title
        alert.informativeText = message
        for b in ordered {
            let button = alert.addButton(withTitle: b.label)
            if b.key == "cancel" || b.key == "no" { button.keyEquivalent = "\u{1b}" }
        }
        let respond: (NSApplication.ModalResponse) -> Void = { r in
            let i = r.rawValue - NSApplication.ModalResponse.alertFirstButtonReturn.rawValue
            done(ordered.indices.contains(i) ? ordered[i].key : "cancel")
        }
        if let w = window() { alert.beginSheetModal(for: w, completionHandler: respond) } else { respond(alert.runModal()) }
    }

    func yesNo(_ title: String, _ message: String, done: @escaping @MainActor (Bool) -> Void) {
        choose(title, message, buttons: [DialogButton(key: "no", label: "No"), DialogButton(key: "yes", label: "Yes")],
               dflt: "yes") { done($0 == "yes") }
    }

    func saveURL(_ title: String, directory: URL, name: String, type: UTType,
                 done: @escaping @MainActor (URL?) -> Void) {
        let panel = NSSavePanel()
        panel.title = title
        panel.allowedContentTypes = [type]
        panel.directoryURL = directory
        panel.nameFieldStringValue = name
        panel.canCreateDirectories = true
        if let w = window() {
            panel.beginSheetModal(for: w) { r in done(r == .OK ? panel.url : nil) }
        } else {
            done(panel.runModal() == .OK ? panel.url : nil)
        }
    }

    func openURL(_ title: String, directory: URL, type: UTType, done: @escaping @MainActor (URL?) -> Void) {
        let panel = NSOpenPanel()
        panel.title = title
        panel.allowedContentTypes = [type]
        panel.directoryURL = directory
        panel.allowsMultipleSelection = false
        panel.canChooseDirectories = false
        if let w = window() {
            panel.beginSheetModal(for: w) { r in done(r == .OK ? panel.url : nil) }
        } else {
            done(panel.runModal() == .OK ? panel.url : nil)
        }
    }
}
