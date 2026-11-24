// SelfTestSave.swift — the self-test's checks of task 11.3e2 (Save + XFDF parity): on a copy of
// the input in the self-test's directory (never next to the goldens), Save through the real
// SaveController with scripted dialogs (no alert or panel is ever shown headless): the
// first-overwrite question, the written file (the original bytes a prefix, C7), the reopen
// listing the marks as saved and keeping view mode, zoom, rotation and page (9.r8); a second
// save appending without a question; deleting a saved highlight: the preview (Save.preview)
// no longer shows it (pixels) and the save carries the revision-retention note; an encrypted
// file saved with a fresh seed (and refused without one), the RC4 note; the changed-on-disk
// check (Cancel, and Save As… to another file); the unsaved-marks question's Cancel / Don't
// Save / Save paths and a failed save aborting the close; XFDF export, import (one undo step,
// already present on a second import), a malformed file refused with the store unchanged, and
// the export refused onto a folder. Task 11.3f: the thumbnails follow the preview (rendered from
// it while a saved mark is deleted, from the file again after the undo).
// Plan.md §4 S8/C7, §6 Phases 9–12; docs/macos-design.md §3 ("Save stays in the GUI process").

import AppKit
import SafePdfC
import UniformTypeIdentifiers

/// The self-test's answers to the save flow's questions and panels, in order.
@MainActor final class ScriptedDialogs: SaveDialogs {
    /// Keys for `choose` and "yes"/"no" for `yesNo` (none left: Cancel / No).
    var answers: [String] = []
    var saveURLs: [URL?] = []
    var openURLs: [URL?] = []
    /// What was asked: title, message and button keys.
    private(set) var asked: [(title: String, message: String, keys: [String])] = []

    func choose(_ title: String, _ message: String, buttons: [DialogButton], dflt: String,
                done: @escaping @MainActor (String) -> Void) {
        asked.append((title, message, buttons.map(\.key)))
        done(answers.isEmpty ? "cancel" : answers.removeFirst())
    }

    func yesNo(_ title: String, _ message: String, done: @escaping @MainActor (Bool) -> Void) {
        asked.append((title, message, ["no", "yes"]))
        done((answers.isEmpty ? "no" : answers.removeFirst()) == "yes")
    }

    func saveURL(_ title: String, directory: URL, name: String, type: UTType,
                 done: @escaping @MainActor (URL?) -> Void) {
        asked.append((title, name, []))
        done(saveURLs.isEmpty ? nil : saveURLs.removeFirst())
    }

    func openURL(_ title: String, directory: URL, type: UTType, done: @escaping @MainActor (URL?) -> Void) {
        asked.append((title, "", []))
        done(openURLs.isEmpty ? nil : openURLs.removeFirst())
    }
}

/// The self-test's window stand-in: the page view and its document; the reopen after a save as
/// the window controller does it (keeping the view and the layers).
@MainActor final class SelfTestSaveHost: SaveHost {
    let pages: PageViewController
    var pdf: Document?
    private(set) var reopens = 0

    init(pages: PageViewController) { self.pages = pages }

    func open(_ url: URL) -> Bool {
        guard let d = try? Document(url: url) else { return false }
        pdf = d
        pages.show(d)
        return true
    }

    func reopenAfterSave(_ url: URL, keep: KeptView?) -> Bool {
        guard let d = try? Document(url: url) else { return false }
        if keep != nil { d.layers = pdf?.layers }
        pdf = d
        pages.show(d, keep: keep)
        reopens += 1
        return true
    }
}

extension SelfTest {
    /// The mean colour of a canvas rectangle in a 2x snapshot of the scroll view.
    private static func meanColor(_ pv: PageViewController, _ r: CGRect) -> (r: CGFloat, g: CGFloat, b: CGFloat)? {
        guard r.minX.isFinite, r.minY.isFinite, r.maxX.isFinite, r.maxY.isFinite, abs(r.minX) < 1e6, abs(r.maxX) < 1e6,
              abs(r.minY) < 1e6, abs(r.maxY) < 1e6, let rep = snapshot(pv.scrollView, scale: 2) else { return nil }
        let o = pv.scrollView.contentView.bounds.origin
        let x0 = Int(((r.minX - o.x) * 2).rounded(.up)), x1 = Int(((r.maxX - o.x) * 2).rounded(.down))
        let y0 = Int(((r.minY - o.y) * 2).rounded(.up)), y1 = Int(((r.maxY - o.y) * 2).rounded(.down))
        var sr: CGFloat = 0, sg: CGFloat = 0, sb: CGFloat = 0, n: CGFloat = 0
        for y in stride(from: max(0, y0), to: min(rep.pixelsHigh, y1), by: 1) {
            for x in stride(from: max(0, x0), to: min(rep.pixelsWide, x1), by: 1) {
                guard let c = rep.colorAt(x: x, y: y)?.usingColorSpace(.sRGB) else { continue }
                sr += c.redComponent
                sg += c.greenComponent
                sb += c.blueComponent
                n += 1
            }
        }
        return n > 0 ? (sr / n, sg / n, sb / n) : nil
    }

    /// The pixels of a thumbnail (to compare two renders).
    private static func thumbBytes(_ img: CGImage?) -> Data? {
        guard let img, let d = img.dataProvider?.data else { return nil }
        return d as Data
    }

    private static func fileBytes(_ path: String) -> Data { FileManager.default.contents(atPath: path) ?? Data() }

    /// Waits for the preview of the store's current state and for the renders it asked for.
    private static func waitPreview(_ pv: PageViewController) {
        guard let m = pv.marks.model else { return }
        pump(limit: 60) { pv.marks.preview.isCurrent(m) && !pv.marks.preview.busy }
        waitRenders(pv)
    }

    /// Task 11.3e2 (see the file's comment). `path` the input; everything is written into `dir`.
    static func saveParity(_ pv: PageViewController, dir: String, path: String) {
        let sdir = "\(dir)/save"
        try? FileManager.default.removeItem(atPath: sdir)
        try? FileManager.default.createDirectory(atPath: sdir, withIntermediateDirectories: true)
        let copy = "\(sdir)/copy.pdf"
        guard (try? FileManager.default.copyItem(atPath: path, toPath: copy)) != nil else {
            check(false, "save: copy the input to \(copy)")
            return
        }
        let original = fileBytes(copy)
        let host = SelfTestSaveHost(pages: pv)
        let dialogs = ScriptedDialogs()
        let saver = SaveController(dialogs: dialogs)
        saver.host = host
        pv.canvas.scaleOverride = 2
        guard host.open(URL(fileURLWithPath: copy)), let doc0 = host.pdf, let m0 = pv.marks.model else {
            check(false, "save: open the copy")
            return
        }
        waitRenders(pv)
        check(Commands.implemented.isSuperset(of: [SAFEPDF_CMD_SAVE, SAFEPDF_CMD_SAVE_AS, SAFEPDF_CMD_IMPORT_XFDF,
                                                   SAFEPDF_CMD_EXPORT_XFDF].map(Commands.id)),
              "Save, Save As, Import and Export XFDF are implemented")
        let n = doc0.pageCount
        let saved0 = m0.state.mark_count
        say("save: \(URL(fileURLWithPath: path).lastPathComponent), \(n) pages, \(saved0) saved marks, encrypted \(doc0.encrypted)")

        // A view to keep: 150 %, page-at-a-time scrolling when there are pages enough,
        // turned once, on the last page but at most the second.
        pv.setZoom(ZoomModel.percent(150))
        if n > 2 {
            pv.setModes(ViewModes(scroll: SAFEPDF_SCROLL_PAGE.rawValue, spread: SAFEPDF_SPREAD_NONE.rawValue))
        }
        pv.rotate(clockwise: true)
        let page = min(1, n - 1)
        pv.goTo(page)
        waitRenders(pv)
        guard let keep = pv.keptView, let t = pv.canvas.transform(ofPage: page),
              let pr = pv.canvas.rect(ofPage: page) else {
            check(false, "save: page \(page + 1) not laid out")
            return
        }
        // A band of the page in view (page space), for a red highlight; a point for a note.
        let vis = pr.intersection(pv.canvas.visibleRect)
        say("save: page \(page + 1) at \(pr), visible part \(vis)")
        guard !vis.isNull, vis.width > 40, vis.height > 80 else {
            check(false, "save: page \(page + 1) is not in view (\(vis))")
            return
        }
        let a = CGPoint(x: vis.minX + vis.width * 0.25, y: vis.minY + vis.height * 0.2)
        let b = CGPoint(x: vis.minX + vis.width * 0.75, y: vis.minY + vis.height * 0.2 + 30)
        guard let pa = t.page(a), let pb = t.page(b) else { check(false, "save: page points"); return }
        let band = safepdf_box(llx: min(pa.x, pb.x), lly: min(pa.y, pb.y), urx: max(pa.x, pb.x), ury: max(pa.y, pb.y))
        let notePt = t.page(CGPoint(x: vis.midX, y: vis.minY + vis.height * 0.6)).map { CGPoint(x: $0.x, y: $0.y) }
        func bandRect() -> CGRect? { pv.canvas.transform(ofPage: page).map { $0.rect(band) } }
        let m0Before = bandRect().flatMap { meanColor(pv, $0) }

        // 1. The first Save asks Overwrite / Save As… / Cancel; Cancel writes nothing.
        guard case .success(let hl) = m0.addHighlight(page: page, color: Int32(SAFEPDF_COLOR_RED), quads: [band]),
              case .success = m0.addNote(page: page, color: Int32(SAFEPDF_COLOR_YELLOW), text: "self-test note",
                                         anchor: Int32(SAFEPDF_ANCHOR_POINT), point: notePt, quads: []) else {
            check(false, "save: add a highlight and a note")
            return
        }
        var result: Bool? = nil
        dialogs.answers = ["cancel"]
        saver.save { result = $0 }
        check(result == false && fileBytes(copy) == original && pv.marks.dirty,
              "Cancel at the first overwrite writes nothing")
        check(dialogs.asked.last?.title == "Save" && dialogs.asked.last?.keys == ["saveas", "cancel", "overwrite"],
              "the first overwrite asks Overwrite / Save As… / Cancel: \(dialogs.asked.last.map { "\($0.title) \($0.keys)" } ?? "nothing")")
        check(dialogs.asked.last?.message.contains("Save 2 new or changed mark(s) into copy.pdf?") == true,
              "the overwrite question's text")

        // 2. Overwrite: the file grows by an incremental update, reopened with the marks saved.
        dialogs.answers = ["overwrite"]
        result = nil
        saver.save { result = $0 }
        let first = fileBytes(copy)
        check(result == true, "Save into the opened file")
        check(first.count > original.count && first.prefix(original.count) == original,
              "the original bytes are a prefix of the saved file (C7): \(original.count) -> \(first.count)")
        check(host.reopens == 1 && host.pdf !== doc0, "the saved file was reopened")
        guard let m1 = pv.marks.model else { check(false, "save: no store after the reopen"); return }
        let all1 = m1.listAll()
        check(all1.count == Int(saved0) + 2 && all1.allSatisfy(\.isSaved) && m1.state.dirty == 0,
              "after Save the marks are listed as saved (\(all1.count))")
        if let k = pv.keptView {
            check(k.modes == keep.modes && k.zoom.kind == keep.zoom.kind && k.zoom.pct == keep.zoom.pct && k.rotation == keep.rotation && k.page == keep.page,
                  "the reopen keeps mode, zoom, rotation and page (\(k.page + 1), \(k.rotation)°)")
        }
        let st1 = saver.lastStatus
        say("save: \(st1)")
        check(st1.hasPrefix("saved 2 new, changed or deleted mark(s) as an incremental update") &&
              st1.contains("the original bytes unchanged at its start"), "the saved status")
        if doc0.encrypted {
            let rc4 = path.contains("rc4")
            check(st1.contains("legacy RC4") == rc4, "the RC4 note \(rc4 ? "shown" : "absent")")
        }
        waitRenders(pv)
        let m1Saved = bandRect().flatMap { meanColor(pv, $0) }

        // 3. A second save appends again, without a question (this session wrote the file).
        let asked = dialogs.asked.count
        _ = m1.addNote(page: page, color: Int32(SAFEPDF_COLOR_BLUE), text: "second",
                       anchor: Int32(SAFEPDF_ANCHOR_POINT), point: notePt.map { CGPoint(x: $0.x + 20, y: $0.y) }, quads: [])
        result = nil
        saver.save { result = $0 }
        let second = fileBytes(copy)
        check(result == true && dialogs.asked.count == asked, "the second Save asks nothing")
        check(second.count > first.count && second.prefix(first.count) == first, "the second save appends")

        // 4. Delete the saved highlight: the preview no longer shows it; Save notes the retention.
        guard let m2 = pv.marks.model else { return }
        // Task 11.3f: a sidebar next to the page view, its thumbnails shown.
        let side = SidebarViewController()
        side.view.frame = NSRect(x: 0, y: 0, width: 220, height: 600)
        side.show(host.pdf, pages: pv)
        // The page mode's panel is chosen once the panels' content is there: wait for it first.
        pump(limit: 30) { side.pending == 0 }
        let th = side.thumbnails
        th.scaleOverride = 2
        side.isShown = true
        side.showPanel(SAFEPDF_PANEL_THUMBNAILS)
        th.frame = NSRect(x: 0, y: 0, width: 220, height: 560)
        th.scroll.frame = th.bounds
        th.collection.layoutSubtreeIfNeeded()
        let clip = th.scroll.contentView
        if let f = th.itemFrame(page) {
            clip.scroll(to: NSPoint(x: 0, y: max(0, f.minY - 8)))
            th.scroll.reflectScrolledClipView(clip)
        }
        th.updateRenders()
        pump(limit: 60) { th.inflight.isEmpty && th.images[page] != nil }
        let thumbWith = thumbBytes(th.images[page])
        let changesBefore = th.sourceChanges
        let builtBefore = pv.marks.preview.built
        check(m2.delete(hl) == nil, "delete the saved highlight")
        waitPreview(pv)
        check(pv.marks.preview.built > builtBefore && pv.canvas.renderSource != nil,
              "the pages are rendered from the preview after deleting a saved mark")
        check(th.renderSource != nil && th.renderSource === pv.canvas.renderSource && th.sourceChanges > changesBefore,
              "the thumbnails are rendered from the same preview (task 11.3f)")
        pump(limit: 60) { th.inflight.isEmpty && th.images[page] != nil }
        let thumbWithout = thumbBytes(th.images[page])
        check(thumbWith != nil && thumbWithout != nil && thumbWith != thumbWithout,
              "page \(page + 1)'s thumbnail changes when its saved highlight is deleted")
        let m2Deleted = bandRect().flatMap { meanColor(pv, $0) }
        if let before = m0Before, let withHl = m1Saved, let after = m2Deleted {
            say(String(format: "save: band green %.3f (file) -> %.3f (saved highlight) -> %.3f (preview after delete)",
                       before.g, withHl.g, after.g))
            check(before.g - withHl.g > 0.08, "the saved red highlight is rendered")
            check(abs(after.g - before.g) < 0.03, "the preview shows the page without the deleted highlight")
        } else {
            check(false, "save: band snapshots")
        }
        if let rep = snapshot(pv.scrollView, scale: 2) { check(writePNG(rep, "\(sdir)/preview-deleted-2x.png"), "write png") }
        pv.marks.undoRedo(undo: true)
        waitPreview(pv)
        check(pv.canvas.renderSource == nil, "undoing the delete renders from the file again")
        check(th.renderSource == nil, "undoing the delete renders the thumbnails from the file again")
        pump(limit: 60) { th.inflight.isEmpty && th.images[page] != nil }
        check(thumbBytes(th.images[page]) == thumbWith, "page \(page + 1)'s thumbnail shows the saved highlight again")
        say("save: thumbnails follow the preview (\(th.sourceChanges - changesBefore) source changes)")
        // Detached before the save reopens the file.
        side.show(nil, pages: pv)
        pv.canvas.onRenderSource = nil
        pv.text.attachmentAt = nil
        pv.text.onAttachmentIcon = nil
        pv.marks.undoRedo(undo: false)
        waitPreview(pv)
        result = nil
        saver.save { result = $0 }
        let st4 = saver.lastStatus
        check(result == true && st4.contains("; note: the 1 deleted mark(s) are still in the file's earlier revision"),
              "Save after deleting a saved mark notes the retention: \(st4)")
        check(pv.marks.model?.find(hl) == nil && pv.canvas.renderSource == nil, "the deleted mark is gone after the reopen")

        // 5. Encrypted: no fresh randomness, no save.
        if doc0.encrypted, let m = pv.marks.model {
            _ = m.addNote(page: page, color: Int32(SAFEPDF_COLOR_GREEN), text: "seedless",
                          anchor: Int32(SAFEPDF_ANCHOR_POINT), point: notePt, quads: [])
            let before = fileBytes(copy)
            saver.randomBytes = { _ in nil }
            result = nil
            saver.save { result = $0 }
            saver.randomBytes = SaveController.secureRandom
            check(result == false && fileBytes(copy) == before && saver.lastStatus.contains("no fresh random bytes"),
                  "an encrypted file is not saved without fresh random bytes")
            result = nil
            saver.save { result = $0 }
            check(result == true, "and is saved with them")
        }

        // 6. Changed on disk: Cancel writes nothing; Save As… writes another file.
        if let m = pv.marks.model {
            _ = m.addNote(page: page, color: Int32(SAFEPDF_COLOR_PINK), text: "disk",
                          anchor: Int32(SAFEPDF_ANCHOR_POINT), point: notePt, quads: [])
            let opened = fileBytes(copy)
            if let fh = FileHandle(forWritingAtPath: copy) {
                fh.seekToEndOfFile()
                fh.write(Data("%changed\n".utf8))
                try? fh.close()
            }
            let modified = fileBytes(copy)
            dialogs.answers = ["cancel"]
            result = nil
            saver.save { result = $0 }
            check(result == false && fileBytes(copy) == modified && dialogs.asked.last?.title == "File changed on disk"
                  && dialogs.asked.last?.keys == ["cancel", "saveas"],
                  "a file changed on disk is not overwritten (Cancel)")
            check(saver.lastStatus.hasPrefix("not saved: copy.pdf changed on disk"), "the changed-on-disk status")
            let other = "\(sdir)/other.pdf"
            dialogs.answers = ["saveas"]
            dialogs.saveURLs = [URL(fileURLWithPath: other)]
            result = nil
            saver.save { result = $0 }
            let o = fileBytes(other)
            check(result == true && o.count > opened.count && o.prefix(opened.count) == opened,
                  "Save As… after the change writes the document as opened, with the marks, to another file")
            check(host.pdf?.url.lastPathComponent == "other.pdf" && pv.marks.dirty == false, "Save As… opens the written file")
            check(dialogs.asked.last?.title == "Save As" && dialogs.asked.last?.message == "copy-annotated.pdf",
                  "Save As… proposes STEM-annotated.pdf")
        }

        // 7. The unsaved-marks question: Cancel, Don't Save, Save; a failed save aborts.
        if let m = pv.marks.model, let cur = host.pdf?.url.path {
            _ = m.addNote(page: page, color: Int32(SAFEPDF_COLOR_YELLOW), text: "unsaved",
                          anchor: Int32(SAFEPDF_ANCHOR_POINT), point: notePt, quads: [])
            let disk = fileBytes(cur)
            var go: Bool? = nil
            dialogs.answers = ["cancel"]
            saver.confirmDiscard("closing") { go = $0 }
            check(go == false && pv.marks.dirty && saver.lastStatus == "closing cancelled: there are unsaved marks",
                  "Cancel keeps the window open")
            check(dialogs.asked.last?.title == "Unsaved marks" && dialogs.asked.last?.keys == ["dontsave", "cancel", "save"]
                  && dialogs.asked.last?.message.contains("Save them before closing?") == true,
                  "the unsaved-marks question: \(dialogs.asked.last?.message ?? "")")
            go = nil
            dialogs.answers = ["dontsave"]
            saver.confirmDiscard("quitting") { go = $0 }
            check(go == true && fileBytes(cur) == disk, "Don't Save goes on and writes nothing")
            chmod(cur, 0o444)
            go = nil
            dialogs.answers = ["save"]
            saver.confirmDiscard("closing") { go = $0 }
            check(go == false && fileBytes(cur) == disk && saver.lastStatus.hasSuffix("; closing cancelled"),
                  "a failed Save aborts the close: \(saver.lastStatus)")
            chmod(cur, 0o644)
            go = nil
            let asked7 = dialogs.asked.count
            dialogs.answers = ["save"]
            saver.confirmDiscard("closing") { go = $0 }
            check(go == true && !pv.marks.dirty && dialogs.asked.count == asked7 + 1,
                  "Save in the question saves without a second question and goes on")
        }

        // 8. XFDF: export, import into a fresh copy (one undo step), again (already present),
        // a malformed file refused, the export refused onto the opened PDF.
        let xfdf = "\(sdir)/marks.xfdf"
        let exported = pv.marks.model?.state.mark_count ?? 0
        saver.exportXfdf(to: URL(fileURLWithPath: xfdf))
        let x = String(decoding: fileBytes(xfdf), as: UTF8.self)
        check(x.contains("<xfdf") && saver.lastStatus == "exported \(exported) mark(s) to marks.xfdf",
              "XFDF export: \(saver.lastStatus)")
        let folder = "\(sdir)/folder.xfdf"
        try? FileManager.default.createDirectory(atPath: folder, withIntermediateDirectories: true)
        saver.exportXfdf(to: URL(fileURLWithPath: folder))
        check(saver.lastStatus == "cannot export: folder.xfdf is a folder; choose a file name",
              "the export is refused onto a folder: \(saver.lastStatus)")
        let fresh = "\(sdir)/fresh.pdf"
        try? FileManager.default.copyItem(atPath: path, toPath: fresh)
        guard host.open(URL(fileURLWithPath: fresh)), let mf = pv.marks.model else {
            check(false, "save: open the fresh copy")
            return
        }
        let s0 = mf.state
        dialogs.openURLs = [URL(fileURLWithPath: xfdf)]
        saver.importXfdf()
        let s1 = mf.state
        let added = Int(s1.mark_count) - Int(s0.mark_count)
        check(added > 0 && s1.dirty != 0 && s1.undo_depth == s0.undo_depth + 1,
              "XFDF import adds the marks as one undo step (\(added) added)")
        check(saver.lastStatus.hasPrefix("marks.xfdf: \(added) imported, "), "the import status: \(saver.lastStatus)")
        saver.importXfdf(from: URL(fileURLWithPath: xfdf))
        check(mf.state.mark_count == s1.mark_count && saver.lastStatus.contains("0 imported, \(added) already present"),
              "a second import adds nothing: \(saver.lastStatus)")
        let bad = "\(sdir)/bad.xfdf"
        try? Data("<notxfdf/>".utf8).write(to: URL(fileURLWithPath: bad))
        let sb = mf.state
        saver.importXfdf(from: URL(fileURLWithPath: bad))
        let sa = mf.state
        check(saver.lastStatus.hasPrefix("cannot import bad.xfdf:") && sa.mark_count == sb.mark_count
              && sa.undo_depth == sb.undo_depth && sa.pending == sb.pending,
              "a malformed XFDF file is refused and the store is unchanged: \(saver.lastStatus)")
        pv.marks.undoRedo(undo: true)
        check(mf.state.mark_count == s0.mark_count, "one undo removes the imported marks")
        dialogs.openURLs = []
        saver.importXfdf()
        check(saver.lastStatus == "import cancelled", "a cancelled import panel")
        say("save: \(dialogs.asked.count) questions and panels answered by script")
        pv.show(nil)
    }
}
