// SelfTestSidebar.swift — the self-test's checks of task 11.3d2 (the sidebar and the honest UI):
// thumbnails (count, sizes, lazy rendering at the thumbnail priority, the current-page highlight
// following the view, a click's jump in the history), the outline (rows, the jump target), the
// attachments (listed without decoding, bytes saved to a file, refused targets), the layers
// (a toggle changes the layers state and re-renders the pages and thumbnails; radio groups and
// locked groups), the page mode's panel, and the identity line of a full-screen state (the strip,
// without entering real full screen). Plan.md §6 Phase 11; docs/macos-design.md §1–§3. Headless
// like SelfTest.swift; the attachment and optional-content fixtures are generated into the
// output directory as the Tk smoke cases 1v and 1w generate theirs (no golden has either).

import AppKit
import SafePdfC

extension SelfTest {
    /// A PDF from its objects (object number -> body), with an xref table and `/Root 1 0 R`.
    static func pdfData(_ objs: [Int: String]) -> Data {
        let n = (objs.keys.max() ?? 0) + 1
        var body = Data("%PDF-1.7\n".utf8)
        var offs: [Int: Int] = [:]
        for k in objs.keys.sorted() {
            offs[k] = body.count
            body.append(Data("\(k) 0 obj\n".utf8))
            body.append(objs[k].map { Data($0.utf8) } ?? Data())
            body.append(Data("\nendobj\n".utf8))
        }
        let x = body.count
        var tail = "xref\n0 \(n)\n0000000000 65535 f \n"
        for k in 1..<n {
            tail += offs[k].map { String(format: "%010d 00000 n \n", $0) } ?? "0000000000 65535 f \n"
        }
        tail += "trailer\n<< /Size \(n) /Root 1 0 R >>\nstartxref\n\(x)\n%%EOF\n"
        body.append(Data(tail.utf8))
        return body
    }

    static let hello = "Hello from an attachment.\n"
    static let dataBin = String(repeating: "0123456789abcdef", count: 64)

    /// att.pdf (the Tk smoke case 1v's shape, without compression): `/PageMode /UseAttachments`,
    /// an outline, a name tree with hello.txt (/Desc, /Params /Size, text/plain), data.bin and an
    /// external file specification, two pages.
    static func attachmentsPDF() -> Data {
        func stream(_ d: String, _ s: String) -> String { "<< \(d) /Length \(s.utf8.count) >>\nstream\n\(s)\nendstream" }
        let c = "0.6 g 72 600 300 100 re f"
        return pdfData([
            1: "<< /Type /Catalog /Pages 2 0 R /PageMode /UseAttachments /Outlines 20 0 R /Names << /EmbeddedFiles 10 0 R >> >>",
            2: "<< /Type /Pages /Kids [3 0 R 4 0 R] /Count 2 /MediaBox [0 0 612 792] >>",
            3: "<< /Type /Page /Parent 2 0 R /Contents 9 0 R >>",
            4: "<< /Type /Page /Parent 2 0 R /Contents 9 0 R >>",
            9: stream("", c),
            10: "<< /Names [(data.bin) 14 0 R (hello.txt) 13 0 R (z) 15 0 R] >>",
            13: "<< /Type /Filespec /F (hello.txt) /UF (hello.txt) /Desc (A greeting) /EF << /F 16 0 R >> >>",
            14: "<< /Type /Filespec /F (data.bin) /EF << /F 17 0 R >> >>",
            15: "<< /Type /Filespec /F (external.pdf) >>",
            16: stream("/Type /EmbeddedFile /Subtype /text#2Fplain /Params << /Size \(hello.utf8.count) /CreationDate (D:20251123101500Z) >>", hello),
            17: stream("/Type /EmbeddedFile", dataBin),
            20: "<< /Type /Outlines /First 21 0 R /Last 21 0 R /Count 1 >>",
            21: "<< /Title (Start) /Parent 20 0 R /Dest [3 0 R /Fit] >>",
        ])
    }

    /// oc.pdf (the Tk smoke case 1w's): `/PageMode /UseOC`; groups Base ON, Extra OFF, Notes,
    /// the radio pair English ON / French OFF under the heading "Languages", Locked (nested under
    /// Notes, locked), Orphan (not in /Order: under "Additional Layers").
    static func layersPDF() -> Data {
        func sq(_ tag: String, _ rgb: String, _ x: Int, _ y: Int) -> String {
            "/OC /\(tag) BDC \(rgb) rg \(x) \(y) 100 100 re f EMC\n"
        }
        let c = sq("oa", "1 0 0", 50, 600) + sq("ob", "0 0 1", 200, 600) + sq("oe", "1 0.5 0", 50, 400) +
            sq("of", "0.5 0 0.5", 200, 400) + sq("ol", "0.3 0.3 0.3", 350, 400) + sq("on", "0 0.5 0.5", 50, 200)
        var objs: [Int: String] = [
            1: "<< /Type /Catalog /Pages 2 0 R /PageMode /UseOC /OCProperties 21 0 R >>",
            2: "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",
            3: "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Resources << /Properties << /oa 10 0 R /ob 11 0 R /oe 13 0 R /of 14 0 R /ol 15 0 R /on 16 0 R >> >> >>",
            4: "<< /Length \(c.utf8.count) >>\nstream\n\(c)endstream",
        ]
        for (k, nm) in [(10, "Base"), (11, "Extra"), (12, "Notes"), (13, "English"), (14, "French"),
                        (15, "Locked"), (16, "Orphan")] {
            objs[k] = "<< /Type /OCG /Name (\(nm)) >>"
        }
        objs[21] = "<< /OCGs [10 0 R 11 0 R 12 0 R 13 0 R 14 0 R 15 0 R 16 0 R] /D << /Name (Default) /OFF [11 0 R 14 0 R] /RBGroups [[13 0 R 14 0 R]] /Locked [15 0 R] /Order [10 0 R 11 0 R [(Languages) 13 0 R 14 0 R] 12 0 R [15 0 R]] >> >>"
        return pdfData(objs)
    }

    /// The bytes of a CGImage (to compare two renders).
    private static func bytes(_ img: CGImage?) -> Data? {
        guard let img, let d = img.dataProvider?.data else { return nil }
        return d as Data
    }

    /// Opens `path` in the sidebar next to `pv` and waits until the panels' content is known.
    private static func openInSidebar(_ path: String, _ pv: PageViewController,
                                      _ sb: SidebarViewController) -> (Document, safepdf_panel?)? {
        let doc: Document
        do { doc = try Document(url: URL(fileURLWithPath: path)) } catch {
            check(false, "open \(path): \(error.message)")
            return nil
        }
        var loaded = false
        var panel: safepdf_panel? = nil
        sb.onLoaded = { p in
            loaded = true
            panel = p
        }
        pv.show(doc)
        sb.show(doc, pages: pv)
        pump(limit: 30) { loaded }
        check(loaded, "\((path as NSString).lastPathComponent): the sidebar's content did not arrive")
        sb.onLoaded = nil
        return (doc, panel)
    }

    static func sidebarChecks(_ doc: Document, _ pv: PageViewController, dir: String) {
        let sdir = "\(dir)/sidebar"
        try? FileManager.default.createDirectory(atPath: sdir, withIntermediateDirectories: true)
        let sb = SidebarViewController()
        sb.view.frame = NSRect(x: 0, y: 0, width: 220, height: 600)
        sb.view.layoutSubtreeIfNeeded()
        let n = doc.pageCount
        pv.canvas.scaleOverride = 2
        sb.thumbnails.scaleOverride = 2

        // 1. Thumbnails of the document under test.
        guard let (d0, p0) = openInSidebar(doc.url.path, pv, sb) else { return }
        _ = p0
        sb.isShown = true
        sb.showPanel(SAFEPDF_PANEL_THUMBNAILS)
        let th = sb.thumbnails
        th.frame = NSRect(x: 0, y: 0, width: 220, height: 560)
        th.scroll.frame = th.bounds
        th.collection.layoutSubtreeIfNeeded()
        th.updateRenders()
        check(th.slots.count == n, "thumbnails: \(th.slots.count) of \(n) laid out")
        let k = SidebarRules.constants
        if let s = th.slots.first, let t = SidebarRules.thumb(d0, page: 0, quarters: 0) {
            check(s.w == CGFloat(k.width) && s.y == CGFloat(k.top) && UInt32(s.h) == t.height,
                  "thumbnail 1: \(s.w) x \(s.h) at y \(s.y)")
        }
        let wantFirst = SidebarRules.wanted(heights: th.slots.map { UInt32($0.h) }, top: 0, bottom: 560)
        let t0 = Core.nowMs()
        pump(limit: 60) { th.inflight.isEmpty && wantFirst.allSatisfy { th.images[$0] != nil } }
        check(wantFirst.allSatisfy { th.images[$0] != nil }, "thumbnails rendered: \(th.images.keys.sorted()) of \(wantFirst)")
        if let img = th.images[0], let s = th.slots.first {
            let k2 = SidebarRules.scale(w: Int(s.w * 2), h: Int(s.h * 2))
            let ew = Double(s.w) * 2 / Double(1 << k2)
            check(abs(Double(img.width) - ew) <= 2, "thumbnail 1 image \(img.width) px wide, expected about \(ew) (scale \(k2))")
            say(String(format: "thumbnails: %d laid out, %d rendered (%@) in %.0f ms; page 1 %.0f x %.0f pt, image %d x %d px",
                       th.slots.count, th.renderedCount, wantFirst.map { String($0 + 1) }.joined(separator: ","),
                       Core.nowMs() - t0, Double(s.w), Double(s.h), img.width, img.height))
        }
        // The current-page highlight follows the view; a click jumps (recorded in the history).
        if n > 1 {
            pv.goTo(n - 1)
            sb.sync()
            check(th.current == n - 1, "thumbnail highlight on page \(th.current + 1), expected \(n)")
            if let f = th.itemFrame(n - 1) {
                let b = th.band
                check(f.minY >= b.top - 9 && f.maxY <= b.bottom + 9 || f.height > b.bottom - b.top,
                      "the current thumbnail scrolled into view: \(f) in \(b)")
            }
            // Scrolled to the end, thumbnails at the start are not wanted: none stays in flight.
            th.updateRenders()
            let wantEnd = Set(SidebarRules.wanted(heights: th.slots.map { UInt32($0.h) },
                                                  top: UInt64(th.band.top), bottom: UInt64(th.band.bottom)))
            check(th.inflight.keys.allSatisfy { wantEnd.contains($0) }, "thumbnail requests off screen: \(th.inflight.keys.sorted())")
            pump(limit: 60) { th.inflight.isEmpty }
            pv.history.clear()
            th.activate(0)
            check(pv.canvas.currentPage == 0 && pv.history.canBack, "thumbnail click: page \(pv.canvas.currentPage + 1), history \(pv.history.canBack)")
            sb.sync()
            check(th.current == 0, "highlight back on page 1")
            say("thumbnails: highlight follows the view (page \(n) -> 1), \(th.cancelledCount) off-screen requests cancelled, \(th.evictedCount) evicted")
        }

        // 1b. Many pages: requests scrolled off screen are cancelled; at most thumbBudget images.
        var many: [Int: String] = [
            1: "<< /Type /Catalog /Pages 2 0 R >>",
            2: "<< /Type /Pages /Kids [\((0..<60).map { "\(10 + $0) 0 R" }.joined(separator: " "))] /Count 60 /MediaBox [0 0 612 792] >>",
            3: "<< /Length 25 >>\nstream\n0.5 g 72 72 300 300 re f\nendstream",
        ]
        for i in 0..<60 { many[10 + i] = "<< /Type /Page /Parent 2 0 R /Contents 3 0 R >>" }
        let manyPath = "\(sdir)/many.pdf"
        check((try? pdfData(many).write(to: URL(fileURLWithPath: manyPath))) != nil, "write many.pdf")
        if openInSidebar(manyPath, pv, sb) != nil {
            sb.isShown = true
            sb.showPanel(SAFEPDF_PANEL_THUMBNAILS)
            th.updateRenders()
            let firstAsked = th.inflight.keys.sorted()
            let clip = th.scroll.contentView
            clip.scroll(to: NSPoint(x: 0, y: max(0, th.collection.frame.height - clip.bounds.height)))
            th.scroll.reflectScrolledClipView(clip)
            check(!firstAsked.isEmpty && th.cancelledCount > 0 && firstAsked.allSatisfy { th.inflight[$0] == nil },
                  "scrolled away: requests for \(firstAsked) cancelled (\(th.cancelledCount))")
            var y: CGFloat = clip.bounds.minY
            while y > 0 {
                pump(limit: 30) { th.inflight.isEmpty }
                y = max(0, y - clip.bounds.height)
                clip.scroll(to: NSPoint(x: 0, y: y))
                th.scroll.reflectScrolledClipView(clip)
            }
            pump(limit: 30) { th.inflight.isEmpty }
            check(th.images.count <= Int(k.budget) && th.evictedCount > 0,
                  "thumbnail budget: \(th.images.count) kept, \(th.evictedCount) evicted (budget \(k.budget))")
            say("thumbnails, 60 pages: \(th.cancelledCount) requests cancelled off screen, \(th.renderedCount) rendered, \(th.images.count) kept, \(th.evictedCount) evicted")
        }

        // 2. The outline (outline.pdf, or the document's own).
        let golden = (doc.url.path as NSString).deletingLastPathComponent
        let outlinePath = ((golden as NSString).deletingLastPathComponent as NSString)
            .appendingPathComponent("pages/outline.pdf")
        if FileManager.default.fileExists(atPath: outlinePath),
           let (od, panel) = openInSidebar(outlinePath, pv, sb) {
            let ol = sb.outline
            check(sb.content.has_outline && !ol.rows.isEmpty, "outline.pdf: outline rows \(ol.rows.count)")
            check(panel == SAFEPDF_PANEL_OUTLINE, "outline.pdf: the sidebar opens on the outline (no page mode)")
            check(sb.buttons.contains(SAFEPDF_PANEL_OUTLINE) && !sb.buttons.contains(SAFEPDF_PANEL_ATTACHMENTS),
                  "outline.pdf: switcher \(sb.buttons.map(\.rawValue))")
            if let i = ol.rows.indices.last(where: { ol.rows[$0].action.kind == SAFEPDF_ACTION_GOTO && ol.rows[$0].action.page > 0 })
                ?? ol.rows.indices.first(where: { ol.rows[$0].action.kind == SAFEPDF_ACTION_GOTO }) {
                pv.history.clear()
                let target = ol.rows[i].action.page
                ol.activate(i)
                check(pv.canvas.currentPage == min(target, od.pageCount - 1) && pv.history.canBack,
                      "outline item \(i) \"\(ol.rows[i].title)\": page \(pv.canvas.currentPage + 1), expected \(target + 1)")
                say("outline.pdf: \(ol.rows.count) rows (\(ol.visibleIndices.count) shown), item \"\(ol.rows[i].title)\" -> page \(target + 1)")
            } else {
                check(false, "outline.pdf: no item goes to a page")
            }
        }

        // 3. Attachments.
        let attPath = "\(sdir)/att.pdf"
        check((try? attachmentsPDF().write(to: URL(fileURLWithPath: attPath))) != nil, "write att.pdf")
        if let (_, panel) = openInSidebar(attPath, pv, sb) {
            let at = sb.attachments
            check(panel == SAFEPDF_PANEL_ATTACHMENTS, "att.pdf: /UseAttachments opens the attachments panel")
            check(sb.buttons == [SAFEPDF_PANEL_THUMBNAILS, SAFEPDF_PANEL_OUTLINE, SAFEPDF_PANEL_ATTACHMENTS],
                  "att.pdf: switcher \(sb.buttons.map(\.rawValue))")
            let names = at.rows.map(\.name)
            check(names == ["data.bin", "hello.txt", "external.pdf"], "attachments listed: \(names)")
            if let h = at.rows.firstIndex(where: { $0.name == "hello.txt" }) {
                check(at.rows[h].sizeText == "26 B" && at.rows[h].tooltip.contains("A greeting") &&
                      at.rows[h].tooltip.contains("Type: text/plain"), "hello.txt row: \(at.rows[h].sizeText) [\(at.rows[h].tooltip)]")
                let out = "\(sdir)/saved-hello.txt"
                try? FileManager.default.removeItem(atPath: out)
                var msg = ""
                at.save(h, to: URL(fileURLWithPath: out)) { msg = $0 }
                pump(limit: 30) { !msg.isEmpty }
                let saved = FileManager.default.contents(atPath: out)
                check(saved == Data(hello.utf8), "saved hello.txt: \(msg)")
                // The opened PDF is refused (and unchanged).
                let before = FileManager.default.contents(atPath: attPath)
                msg = ""
                at.save(h, to: URL(fileURLWithPath: attPath)) { msg = $0 }
                pump(limit: 30) { !msg.isEmpty }
                check(msg.contains("is the opened document") && FileManager.default.contents(atPath: attPath) == before,
                      "saving over the opened PDF refused: \(msg)")
                say("attachments: \(at.rows.map { "\($0.name) \($0.sizeText)" }.joined(separator: ", ")); \(msg)")
            }
            if let d = at.rows.firstIndex(where: { $0.name == "data.bin" }) {
                let out = "\(sdir)/saved-data.bin"
                try? FileManager.default.removeItem(atPath: out)
                var msg = ""
                at.save(d, to: URL(fileURLWithPath: out)) { msg = $0 }
                pump(limit: 30) { !msg.isEmpty }
                check(FileManager.default.contents(atPath: out) == Data(dataBin.utf8), "saved data.bin: \(msg)")
            }
            if let e = at.rows.firstIndex(where: { $0.name == "external.pdf" }) {
                var msg = ""
                at.save(e, to: URL(fileURLWithPath: "\(sdir)/external.pdf")) { msg = $0 }
                pump(limit: 30) { !msg.isEmpty }
                check(msg.hasPrefix("cannot save attachment external.pdf:") && !FileManager.default.fileExists(atPath: "\(sdir)/external.pdf"),
                      "external file refused: \(msg)")
            }
        }

        // 4. Layers: a toggle changes the state and re-renders the pages and the thumbnails.
        let ocPath = "\(sdir)/oc.pdf"
        check((try? layersPDF().write(to: URL(fileURLWithPath: ocPath))) != nil, "write oc.pdf")
        if let (od, panel) = openInSidebar(ocPath, pv, sb) {
            let ly = sb.layers
            check(panel == SAFEPDF_PANEL_LAYERS, "oc.pdf: /UseOC opens the layers panel")
            check(sb.buttons.contains(SAFEPDF_PANEL_LAYERS), "oc.pdf: Show Layers button")
            let labels = ly.rows.map(\.label)
            say("layers: \(labels.joined(separator: " | "))")
            check(labels == ["Base", "Extra", "Languages", "English", "French", "Notes", "Locked", "Additional Layers", "Orphan"],
                  "layer rows \(labels)")
            pump(limit: 60) { pv.canvas.pendingCount == 0 }
            sb.isShown = true
            sb.showPanel(SAFEPDF_PANEL_THUMBNAILS)
            th.updateRenders()
            pump(limit: 60) { th.inflight.isEmpty && th.images[0] != nil }
            let before = renderBytes(od)
            let thumbsBefore = th.renderedCount
            check(od.layers == nil && ly.checked(1) == false, "Extra starts OFF in the default state")
            let changed = ly.toggle(1)
            check(changed && ly.checked(1) == true && od.layers?.isOn(safepdf_oc_key(num: 11, gen: 0)) == true,
                  "toggling Extra turns it ON in the document's layers state")
            check(pv.canvas.pendingCount > 0, "the toggle re-renders the visible pages")
            pump(limit: 60) { pv.canvas.pendingCount == 0 && th.inflight.isEmpty && th.images[0] != nil }
            check(th.renderedCount > thumbsBefore, "the toggle re-renders the thumbnails")
            let after = renderBytes(od)
            check(before != nil && after != nil && before != after, "the page renders differently with Extra ON")
            // Radio pair: French ON turns English OFF; the locked group never changes.
            ly.toggle(4)
            check(ly.checked(4) == true && ly.checked(3) == false, "radio: French on, English off")
            check(!ly.toggle(6) && ly.checked(6) == true, "the locked layer does not change")
            check(pv.canvas.errors.isEmpty, "render errors under the layers state: \(pv.canvas.errors)")
            if let rep = snapshot(pv.scrollView, scale: 2) { check(writePNG(rep, "\(sdir)/layers-toggled-2x.png"), "write png") }
            say("layers: \(ly.toggles) toggles; Extra \(ly.checked(1) == true ? "on" : "off"), English \(ly.checked(3) == true ? "on" : "off"), French \(ly.checked(4) == true ? "on" : "off"), Locked \(ly.checked(6) == true ? "on" : "off")")
            // Every open starts with the document's default state again.
            if let (od2, _) = openInSidebar(ocPath, pv, sb) {
                check(od2.layers == nil && ly.checked(1) == false, "a new open starts with the default layers state")
            }
        }

        // 5. Page modes: the panel each opens, the notes.
        let modes: [(String, String, safepdf_panel?, String?)] = [
            ("thumbs", "/PageMode /UseThumbs", SAFEPDF_PANEL_THUMBNAILS, nil),
            ("outlines", "/PageMode /UseOutlines", SAFEPDF_PANEL_OUTLINE, nil),
            ("usenone", "/PageMode /UseNone", nil, nil),
            ("oc-without", "/PageMode /UseOC", SAFEPDF_PANEL_OUTLINE, nil),
            ("fullscreen", "/PageMode /FullScreen /ViewerPreferences << /NonFullScreenPageMode /UseThumbs >>", nil, ViewNavNote.fullScreen),
        ]
        var lines: [String] = []
        for (name, cat, want, note) in modes {
            let path = "\(sdir)/mode-\(name).pdf"
            guard (try? settingsPDF(cat, title: "unused").write(to: URL(fileURLWithPath: path))) != nil,
                  let (md, panel) = openInSidebar(path, pv, sb) else { continue }
            lines.append("\(name): panel \(panel.map { String($0.rawValue) } ?? "closed"), pill \(pv.pill.message)")
            check(panel == want, "\(name): panel \(panel.map { String($0.rawValue) } ?? "closed"), expected \(want.map { String($0.rawValue) } ?? "closed")")
            check(!pv.pill.message.contains("sidebar panel"), "\(name): no sidebar-panel note any more")
            if let note { check(pv.pill.message.contains(note), "\(name): pill \(pv.pill.message)") }
            if name == "fullscreen" {
                check(SidebarRules.onLoad(pageMode: md.settings.nonFullScreenMode, sb.content) == SAFEPDF_PANEL_THUMBNAILS,
                      "leaving full screen opens /NonFullScreenPageMode's panel")
            }
        }
        for l in lines { say("page mode \(l)") }

        // 6. The identity line of a full-screen state (the strip, without entering full screen).
        let idl = IdentityLine(pages: pv)
        let url = URL(fileURLWithPath: attPath)
        let scrollBefore = pv.scrollView.frame
        idl.sync(show: true, url: url)
        let want = "SafePDF is showing att.pdf (\(attPath)) - this line is drawn by SafePDF, never by the document"
        check(idl.shown && idl.strip.text == want, "identity line: \(idl.strip.text)")
        check(idl.strip.superview === pv.view && pv.scrollView.frame.minY >= IdentityStrip.height - 0.5 &&
              !pv.scrollView.frame.intersects(idl.strip.frame), "the page area ends above the identity line: \(pv.scrollView.frame) / \(idl.strip.frame)")
        let tricky = IdentityLine.text(for: URL(fileURLWithPath: "/tmp/x\u{202E}fdp.pdf"))
        check(tricky.contains("x fdp.pdf") && !tricky.contains("\u{202E}"), "bidi override blanked: \(tricky)")
        if let rep = snapshot(pv.view, scale: 2) { check(writePNG(rep, "\(sdir)/identity-2x.png"), "write png") }
        idl.sync(show: false, url: nil)
        check(!idl.shown && idl.strip.superview == nil && pv.scrollView.frame == scrollBefore, "identity line removed")
        say("identity line: \(want)")
        pv.canvas.scaleOverride = 2
    }

    /// Page 1 of `doc` rendered at 1x under its current layers state (the bytes).
    private static func renderBytes(_ doc: Document) -> Data? {
        var result: RenderResult? = nil
        let id = Rendering.submit(doc, page: 0, key: ZoomKey(num: 1, den: 1, rotation: 0),
                                  priority: Int32(SAFEPDF_PRIO_CURRENT)) { result = $0 }
        guard id != 0 else { return nil }
        pump(limit: 60) { result != nil }
        return bytes(result?.image)
    }
}

/// The notes the self-test looks for.
enum ViewNavNote {
    static let fullScreen = OpenSettings.fullScreenNote
}
