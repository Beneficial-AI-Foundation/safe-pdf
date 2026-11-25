// SelfTestText.swift — the self-test's checks of task 11.3d1 (text and navigation parity, part
// 1): selection by drag, double / triple click and shift-click, the bands drawn in the accent
// colour, Select All and Copy (onto a private pasteboard, never the user's), the cursor, Find
// Next / Previous with wrap and highlight-all, the NEED path across pages on a generated
// three-page file, and links on pages/tree.pdf (internal jump with history; an external address
// goes to the confirmation sheet — built, never shown or opened). Plan.md §6 Phase 11;
// docs/macos-design.md §1–§3. Headless like SelfTest.swift: no window, Prohibited; nothing is
// ever opened (there is no NSWorkspace call in the app at all).

import AppKit
import SafePdfC

extension SelfTest {
    /// A three-page PDF with Helvetica text: "needle" once on page 1, never on page 2, twice on
    /// page 3 (the Find Next NEED path).
    static func textPDF() -> Data {
        let texts = ["(needle in a haystack) Tj", "(nothing to see here) Tj",
                     "(a needle and another) Tj 0 -40 Td (needle again) Tj"]
        var objs: [Int: String] = [
            1: "<< /Type /Catalog /Pages 2 0 R >>",
            2: "<< /Type /Pages /Kids [3 0 R 4 0 R 5 0 R] /Count 3 /MediaBox [0 0 612 792] >>",
            9: "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>",
        ]
        for i in 0..<3 {
            objs[3 + i] = "<< /Type /Page /Parent 2 0 R /Contents \(6 + i) 0 R /Resources << /Font << /F1 9 0 R >> >> >>"
            let c = "BT /F1 24 Tf 72 700 Td \(texts[i]) ET"
            objs[6 + i] = "<< /Length \(c.utf8.count) >>\nstream\n\(c)\nendstream"
        }
        var body = "%PDF-1.7\n"
        var offs: [Int: Int] = [:]
        for n in objs.keys.sorted() {
            offs[n] = body.utf8.count
            body += "\(n) 0 obj\n\(objs[n] ?? "")\nendobj\n"
        }
        let x = body.utf8.count
        body += "xref\n0 10\n0000000000 65535 f \n"
        for n in 1...9 { body += String(format: "%010d 00000 n \n", offs[n] ?? 0) }
        body += "trailer\n<< /Size 10 /Root 1 0 R >>\nstartxref\n\(x)\n%%EOF\n"
        return Data(body.utf8)
    }

    /// Waits for page `p`'s index (nil: none).
    private static func indexOf(_ t: TextController, _ p: Int) -> SelectPage? {
        var done: TextOutcome<SelectPage>? = nil
        t.store.withIndex(p, priority: Int32(SAFEPDF_PRIO_CURRENT)) { done = $0 }
        pump(limit: 60) { done != nil }
        if case .ready(let sp)? = done { return sp }
        if case .failed(let e)? = done { say("  page \(p + 1): no index: \(e)") }
        return nil
    }

    /// The view point of the centre of a page-space box.
    private static func centre(_ t: PageTransform, _ b: safepdf_box) -> CGPoint {
        t.view((b.llx + b.urx) / 2, (b.lly + b.ury) / 2)
    }

    /// The mean colour (r, g, b) of a canvas rectangle in a 2x snapshot of the scroll view.
    private static func meanColour(_ rep: NSBitmapImageRep, _ pv: PageViewController, _ r: CGRect)
        -> (r: CGFloat, g: CGFloat, b: CGFloat)?
    {
        let o = pv.scrollView.contentView.bounds.origin
        let x0 = Int(((r.minX - o.x) * 2).rounded(.up)), x1 = Int(((r.maxX - o.x) * 2).rounded(.down))
        let y0 = Int(((r.minY - o.y) * 2).rounded(.up)), y1 = Int(((r.maxY - o.y) * 2).rounded(.down))
        var sr: CGFloat = 0, sg: CGFloat = 0, sb: CGFloat = 0, n: CGFloat = 0
        for y in stride(from: max(0, y0), to: min(rep.pixelsHigh, y1), by: 1) {
            for x in stride(from: max(0, x0), to: min(rep.pixelsWide, x1), by: 1) {
                guard let c = rep.colorAt(x: x, y: y)?.usingColorSpace(.deviceRGB) else { continue }
                sr += c.redComponent
                sg += c.greenComponent
                sb += c.blueComponent
                n += 1
            }
        }
        return n > 0 ? (sr / n, sg / n, sb / n) : nil
    }

    private static func waitFind(_ t: TextController) {
        pump(limit: 60) { !t.find.searching }
    }

    static func textParity(_ doc: Document, _ pv: PageViewController, dir: String, path: String) {
        let t = pv.text
        let pb = NSPasteboard(name: NSPasteboard.Name("org.safe-pdf.selftest.\(getpid())"))
        defer { pb.releaseGlobally() }
        t.pasteboard = pb
        pv.canvas.scaleOverride = 2
        pv.show(doc)
        waitRenders(pv)
        let file = (path as NSString).lastPathComponent

        // Commands: Copy, Select All, Find are implemented; Copy needs a selection.
        for c in [SAFEPDF_CMD_COPY, SAFEPDF_CMD_SELECT_ALL, SAFEPDF_CMD_FIND] {
            check(Commands.implemented.contains(Commands.id(c)) && Commands.pendingTask(Commands.id(c)) == nil,
                  "command \(c.rawValue) not implemented")
        }
        func enabled(_ c: safepdf_cmd) -> Bool {
            Chrome.states(DocumentWindowController.context(pdf: doc, pages: pv))?.commandEnabled[Commands.id(c)] ?? false
        }
        check(!enabled(SAFEPDF_CMD_COPY) && enabled(SAFEPDF_CMD_SELECT_ALL) && enabled(SAFEPDF_CMD_FIND),
              "without a selection: Copy disabled, Select All and Find enabled")

        if let sp = indexOf(t, 0), sp.cellCount >= 10, let tr = pv.canvas.transform(ofPage: 0) {
            selection(t, pv, sp, tr, pb, dir: dir, file: file, enabled: enabled)
            find(t, pv, sp, dir: dir, single: doc.pageCount == 1)
        } else {
            say("text: page 1 has no text index with 10 cells: selection and single-page find checks skipped")
        }
        if file == "tree.pdf" { links(t, pv, doc, pb) }
        findAcrossPages(t, pv, dir: dir)
        t.pasteboard = .general
    }

    // MARK: selection, copy, cursor

    private static func selection(_ t: TextController, _ pv: PageViewController, _ sp: SelectPage,
                                  _ tr: PageTransform, _ pb: NSPasteboard, dir: String, file: String,
                                  enabled: (safepdf_cmd) -> Bool) {
        let n = sp.cellCount
        let b0 = sp.boxes[0], k = min(15, n - 1), bk = sp.boxes[k]
        let a = centre(tr, b0), z = centre(tr, bk)

        // Drag from glyph 0 to glyph k (through a midpoint): Select.dragRange of the two points.
        t.pointerDown(at: a, clicks: 1, shift: false)
        t.pointerDragged(at: CGPoint(x: (a.x + z.x) / 2, y: (a.y + z.y) / 2))
        t.pointerDragged(at: z)
        t.pointerUp(at: z)
        var want = safepdf_select_range()
        let ok = safepdf_select_drag(sp.handle, (b0.llx + b0.urx) / 2, (b0.lly + b0.ury) / 2,
                                     (bk.llx + bk.urx) / 2, (bk.lly + bk.ury) / 2, &want) == 0
        check(ok && t.selection == TextSelection(page: 0, first: want.first, last: want.last),
              "drag 0 -> \(k): selection \(String(describing: t.selection)), expected \(want.first)...\(want.last)")
        check(enabled(SAFEPDF_CMD_COPY), "Copy enabled with a selection")
        var uncovered = 0
        if let s = t.selection {
            for i in s.first...s.last {
                let c = sp.boxes[i]
                let inside = t.bands.contains { b in
                    b.llx <= c.llx + 1e-9 && b.lly <= c.lly + 1e-9 && c.urx <= b.urx + 1e-9 && c.ury <= b.ury + 1e-9
                }
                if !inside { uncovered += 1 }
            }
        }
        check(!t.bands.isEmpty && uncovered == 0,
              "bands of the drag cover every selected glyph box (\(t.bands.count) bands, \(uncovered) uncovered)")
        say("selection: drag glyph 0 -> \(k) on \(file): cells \(t.selection.map { "\($0.first)...\($0.last)" } ?? "none"), \(t.bands.count) bands; pill \"\(pv.pill.message)\"")
        check(pv.pill.message.hasPrefix("page 1: selected ") && pv.pill.message.hasSuffix("(⌘C copies)"),
              "selection status: \(pv.pill.message)")

        // Drawn: the band is tinted with the accent colour (blue dominates on white paper).
        pv.canvas.needsDisplay = true
        if let rep = snapshot(pv.scrollView, scale: 2), let band = t.bands.first {
            check(writePNG(rep, "\(dir)/text-selection-2x.png"), "write png")
            let r = pv.canvas.pixelAligned(tr.rect(band))
            if let m = meanColour(rep, pv, r) {
                let accent = TextController.selectionColor.usingColorSpace(.deviceRGB)
                say(String(format: "  selection band mean colour r %.2f g %.2f b %.2f (accent r %.2f g %.2f b %.2f at 35%%)",
                           m.r, m.g, m.b, accent?.redComponent ?? -1, accent?.greenComponent ?? -1,
                           accent?.blueComponent ?? -1))
                if let ac = accent {
                    // Over white paper the fill moves each channel towards the accent's.
                    let toward = (ac.blueComponent - ac.redComponent) * (m.b - m.r) > 0
                        || abs(ac.blueComponent - ac.redComponent) < 0.05
                    check(toward && (m.r < 0.98 || m.g < 0.98 || m.b < 0.98),
                          "the selection band is not tinted with the accent colour")
                }
            }
            // Dark mode: the paper stays white, the band keeps the (dark) accent tint.
            pv.scrollView.appearance = NSAppearance(named: .darkAqua)
            pv.canvas.needsDisplay = true
            if let dark = snapshot(pv.scrollView, scale: 2), let m = meanColour(dark, pv, r) {
                check(writePNG(dark, "\(dir)/text-selection-2x-dark.png"), "write png")
                say(String(format: "  dark mode: selection band mean colour r %.2f g %.2f b %.2f", m.r, m.g, m.b))
                check(m.b > m.r + 0.1, "the selection band is not tinted in dark mode")
            }
            pv.scrollView.appearance = nil
        }

        // Shift-click extends from where the selection started.
        let k2 = min(25, n - 1), b2 = sp.boxes[k2], z2 = centre(tr, b2)
        t.pointerDown(at: z2, clicks: 1, shift: true)
        t.pointerUp(at: z2)
        var ext = safepdf_select_range()
        _ = safepdf_select_drag(sp.handle, (b0.llx + b0.urx) / 2, (b0.lly + b0.ury) / 2,
                                (b2.llx + b2.urx) / 2, (b2.lly + b2.ury) / 2, &ext)
        check(t.selection == TextSelection(page: 0, first: ext.first, last: ext.last),
              "shift-click at glyph \(k2): \(String(describing: t.selection)), expected \(ext.first)...\(ext.last)")

        // Double click: the word (Select.wordAt); triple: the line (Select.lineAt).
        let w = min(8, n - 1), wp = centre(tr, sp.boxes[w])
        var near = 0
        let bw = sp.boxes[w]
        _ = safepdf_select_nearest(sp.handle, (bw.llx + bw.urx) / 2, (bw.lly + bw.ury) / 2, &near)
        t.pointerDown(at: wp, clicks: 1, shift: false)
        t.pointerUp(at: wp)
        check(t.selection == nil, "a click in place clears the selection")
        t.pointerDown(at: wp, clicks: 2, shift: false)
        t.pointerUp(at: wp)
        let word = safepdf_select_word_at(sp.handle, near)
        check(t.selection == TextSelection(page: 0, first: word.first, last: word.last),
              "double click at glyph \(w): \(String(describing: t.selection)), word \(word.first)...\(word.last)")
        let wordText = t.copy()
        t.pointerDown(at: wp, clicks: 3, shift: false)
        t.pointerUp(at: wp)
        let line = safepdf_select_line_at(sp.handle, near)
        check(t.selection == TextSelection(page: 0, first: line.first, last: line.last),
              "triple click at glyph \(w): \(String(describing: t.selection)), line \(line.first)...\(line.last)")
        let lineText = t.copy()
        say("double click: \"\(wordText ?? "")\"; triple click: \"\(lineText ?? "")\"")
        check((wordText?.isEmpty == false) && lineText.map { l in wordText.map { l.contains($0) } ?? false } == true,
              "the word lies in its line")

        // Select All and Copy: the page's text on the (private) pasteboard, the status counts it.
        t.selectAll()
        pump(limit: 5) { t.selection != nil }
        check(t.selection == TextSelection(page: 0, first: 0, last: n - 1), "select all: \(String(describing: t.selection))")
        let copied = t.copy()
        var expect = ""
        var hidden = 0
        if let c = safepdf_select_copy(sp.handle, 0, n - 1) {
            expect = Core.string(c.pointee.text)
            hidden = c.pointee.hidden_chars
            safepdf_select_free_copy_result(c)
        }
        check(copied == expect && pb.string(forType: .string) == expect,
              "copy after select all: the pasteboard holds the select-all text (\(expect.count) characters)")
        say("copy: \(expect.unicodeScalars.count) characters, \(hidden) hidden; pill \"\(pv.pill.message)\"")
        if file == "latin.pdf" {
            check(expect.unicodeScalars.count == 147 && hidden == 19, "latin.pdf: 147 characters, 19 hidden")
            check(pv.pill.message.contains("19 characters that are not visible"), "copy status names the hidden text")
            check(expect.hasPrefix("First line of text."), "latin.pdf copy starts with its first line")
        }

        // Nothing selected: Copy says how to select.
        let off = CGPoint(x: 1, y: 1)
        t.pointerDown(at: off, clicks: 1, shift: false)
        t.pointerUp(at: off)
        check(t.selection == nil && t.copy() == nil && pv.pill.message.hasPrefix("nothing selected"),
              "copy without a selection: \(pv.pill.message)")

        // The cursor: the I-beam over a glyph, the arrow off the text (Toolbar.cursorFor).
        t.pointerMoved(at: a)
        pump(limit: 10) { pv.text.store.pendingCount == 0 }
        t.pointerMoved(at: a)
        check(t.cursor == SAFEPDF_CURSOR_IBEAM.rawValue, "cursor over a glyph: \(t.cursor)")
        t.pointerMoved(at: off)
        check(t.cursor == SAFEPDF_CURSOR_ARROW.rawValue, "cursor off the text: \(t.cursor)")

        // Through the canvas's own mouse handlers (a synthetic click in place clears).
        t.selectAll()
        pump(limit: 5) { t.selection != nil }
        let loc = pv.canvas.convert(off, to: nil)
        for type in [NSEvent.EventType.leftMouseDown, .leftMouseUp] {
            if let ev = NSEvent.mouseEvent(with: type, location: loc, modifierFlags: [], timestamp: 0,
                                           windowNumber: 0, context: nil, eventNumber: 0, clickCount: 1,
                                           pressure: 1) {
                if type == .leftMouseDown { pv.canvas.mouseDown(with: ev) } else { pv.canvas.mouseUp(with: ev) }
            }
        }
        check(t.selection == nil, "a synthetic click on the canvas clears the selection")
    }

    // MARK: find on one page

    private static func find(_ t: TextController, _ pv: PageViewController, _ sp: SelectPage, dir: String,
                             single: Bool) {
        // The query: "e" (many hits), as macos/tests/select_test.c.
        let q = "E"
        let c = safepdf_select_count(sp.handle, q)
        guard c >= 2 else {
            say("find: fewer than two hits of \"e\" on page 1: skipped")
            return
        }
        pv.scroll(toPage: 0)
        var seen: [Int] = []
        for _ in 0..<c {
            t.find.step(raw: q, forward: true)
            waitFind(t)
            if let h = t.find.hit, h.page == 0 { seen.append(h.index) }
        }
        check(t.find.query == "e", "normalised query \"\(t.find.query)\"")
        check(seen == Array(0..<c), "find next walks the \(c) hits in order: \(seen)")
        check(t.find.lastMessage == "\"e\": hit \(c)/\(c) on page 1", "status: \(t.find.lastMessage)")
        t.find.step(raw: q, forward: true)
        waitFind(t)
        check(t.find.hit.map { $0.page == 0 && $0.index == 0 } == true, "find next wraps to the first hit")
        if single { check(t.find.lastMessage.hasSuffix("(wrapped)"), "wrap noted: \(t.find.lastMessage)") }
        t.find.step(raw: q, forward: false)
        waitFind(t)
        check(t.find.hit.map { $0.page == 0 && $0.index == c - 1 } == true, "find previous wraps to the last hit")
        say("find \"e\" on page 1: \(c) hits; next x\(c + 1) wraps; previous wraps; \(t.find.lastMessage)")

        // Highlight-all: the current hit orange, the others yellow (red and green over blue).
        pv.canvas.needsDisplay = true
        if let hs = t.find.hits(0), let tr = pv.canvas.transform(ofPage: 0),
           let rep = snapshot(pv.scrollView, scale: 2) {
            check(writePNG(rep, "\(dir)/text-find-2x.png"), "write png")
            check(hs.count == c, "highlight-all has \(hs.count) hits")
            if let cur = hs.last?.first, let m = meanColour(rep, pv, tr.rect(cur)) {
                say(String(format: "  current hit mean colour r %.2f g %.2f b %.2f", m.r, m.g, m.b))
                check(m.r > m.b + 0.2 && m.g < m.r, "the current hit is not orange")
            }
            if let other = hs.first?.first, let m = meanColour(rep, pv, tr.rect(other)) {
                say(String(format: "  other hit mean colour r %.2f g %.2f b %.2f", m.r, m.g, m.b))
                check(m.r > m.b + 0.2 && m.g > m.b + 0.2, "the other hits are not yellow")
            }
        }

        t.find.step(raw: "zzqqxj", forward: true)
        waitFind(t)
        check(t.find.hit == nil && t.find.lastMessage == "\"zzqqxj\": not found", "not found: \(t.find.lastMessage)")
        t.find.step(raw: "   ", forward: true)
        check(t.find.query.isEmpty && t.find.lastMessage == "search: empty query", "empty query: \(t.find.lastMessage)")
        t.find.step(raw: q, forward: true)
        waitFind(t)
        t.find.close()
        check(t.find.query.isEmpty && t.find.hit == nil, "close: no query, no hit")
    }

    // MARK: find across pages (the NEED path)

    private static func findAcrossPages(_ t: TextController, _ pv: PageViewController, dir: String) {
        let url = URL(fileURLWithPath: dir).appendingPathComponent("find-3pages.pdf")
        guard (try? textPDF().write(to: url)) != nil, let doc = try? Document(url: url) else {
            check(false, "generated three-page text file")
            return
        }
        pv.show(doc)
        waitRenders(pv)
        var steps: [String] = []
        func step(_ forward: Bool) -> (Int, Int)? {
            t.find.step(raw: "NEEDLE", forward: forward)
            waitFind(t)
            steps.append(t.find.lastMessage)
            return t.find.hit.map { ($0.page, $0.index) }
        }
        let h1 = step(true), r1 = t.store.indexRequests
        let h2 = step(true), r2 = t.store.indexRequests
        let h3 = step(true)
        let h4 = step(true)
        let h5 = step(false)
        check(h1.map { $0 == (0, 0) } == true && steps[0] == "\"needle\": hit 1/1 on page 1", "first: \(steps[0])")
        check(r1.contains(0), "the first step asked for page 1's index: \(r1)")
        check(h2.map { $0 == (2, 0) } == true && steps[1] == "\"needle\": hit 1/2 on page 3", "second: \(steps[1])")
        check(r2.contains(1) && r2.contains(2), "the NEED path asked for pages 2 and 3: \(r2)")
        check(pv.canvas.currentPage == 2 || h2 == nil, "the hit's page is current: \(pv.canvas.currentPage + 1)")
        check(h3.map { $0 == (2, 1) } == true, "third: \(steps[2])")
        check(h4.map { $0 == (0, 0) } == true && steps[3].hasSuffix("(wrapped)"), "fourth wraps: \(steps[3])")
        check(h5.map { $0 == (2, 1) } == true && steps[4].hasSuffix("(wrapped)"), "previous wraps: \(steps[4])")
        say("find across 3 pages: \(steps.joined(separator: " | ")); index requests \(t.store.indexRequests)")

        // A search whose index request is cancelled ends (it never asks again in a loop).
        pv.show(doc)
        t.find.step(raw: "needle", forward: false)
        t.store.cancelAll()
        let waited = pump(limit: 30) { !t.find.searching }
        let n = t.store.indexRequests.count
        check(!t.find.searching && n <= 3, "search after cancel: ended \(!t.find.searching), \(n) index requests")
        say(String(format: "search with cancelled requests: ended after %.0f ms with \"%@\" (%d index requests)",
                   waited, t.find.lastMessage, n))
        pv.show(nil)
    }

    // MARK: links (pages/tree.pdf)

    private static func links(_ t: TextController, _ pv: PageViewController, _ doc: Document, _ pb: NSPasteboard) {
        var got: TextOutcome<PageLinks>? = nil
        t.store.withLinks(0, priority: Int32(SAFEPDF_PRIO_CURRENT)) { got = $0 }
        pump(limit: 60) { got != nil }
        guard case .ready(let ls)? = got, ls.links.count == 2, let tr = pv.canvas.transform(ofPage: 0) else {
            check(false, "tree.pdf page 1: two links")
            return
        }
        check(ls.links[0].kind == SAFEPDF_ACTION_GOTO && ls.links[0].page == 3, "link 1 goes to page 4")
        check(ls.links[1].kind == SAFEPDF_ACTION_URI && ls.links[1].text == "http://x", "link 2 is http://x")
        check(ls.index(at: 55, 55) == 1 && ls.index(at: 30, 30) == 1 && ls.index(at: 5, 5) == nil,
              "link hit test (Links.linkAt, the topmost)")
        say("links: \(ls.describe(0, labels: doc.labels, pages: doc.pageCount)) | \(ls.describe(1, labels: doc.labels, pages: doc.pageCount))")
        check(ls.describe(0, labels: doc.labels, pages: doc.pageCount).hasPrefix("go to page "), "describe link 1")

        // Hover: the pointing hand and the target in the status.
        let v = tr.view(55, 55)
        t.pointerMoved(at: v)
        check(t.cursor == SAFEPDF_CURSOR_POINTING_HAND.rawValue, "cursor over a link: \(t.cursor)")
        check(pv.pill.message == "external link (click to copy the address): http://x", "hover status: \(pv.pill.message)")

        // A click on the external link (through the canvas's mouse handlers): the sheet, never
        // an open.
        let loc = pv.canvas.convert(v, to: nil)
        for type in [NSEvent.EventType.leftMouseDown, .leftMouseUp] {
            if let ev = NSEvent.mouseEvent(with: type, location: loc, modifierFlags: [], timestamp: 0,
                                           windowNumber: 0, context: nil, eventNumber: 0, clickCount: 1,
                                           pressure: 1) {
                if type == .leftMouseDown { pv.canvas.mouseDown(with: ev) } else { pv.canvas.mouseUp(with: ev) }
            }
        }
        pump(limit: 5) { t.links.pendingURI != nil }
        check(t.links.pendingURI == "http://x", "the external link asks first: \(t.links.pendingURI ?? "nothing")")
        if let a = t.links.pendingAlert {
            check(LinkController.shownAddress(a) == "http://x", "the sheet shows the exact address")
            check(a.buttons.map(\.title) == ["Copy Address", "Cancel"], "sheet buttons \(a.buttons.map(\.title))")
        }
        t.links.answer(copy: false, uri: "http://x")
        check(pv.pill.message == "external link not followed: http://x", "cancel: \(pv.pill.message)")
        t.links.confirm("http://x")
        t.links.answer(copy: true, uri: "http://x")
        check(pb.string(forType: .string) == "http://x" &&
              pv.pill.message == "copied the link address to the clipboard (not opened): http://x",
              "copy address: \(pv.pill.message)")

        // The internal link: a jump to page 4, recorded in the history.
        check(!pv.history.canBack, "no history before the jump")
        t.links.activate(ls, 0)
        check(pv.canvas.currentPage == 3 && pv.history.canBack, "internal link: page \(pv.canvas.currentPage + 1), back \(pv.history.canBack)")
        pv.historyMove(back: true)
        check(pv.canvas.currentPage == 0, "back after the link: page \(pv.canvas.currentPage + 1)")
        say("links on tree.pdf: hover hand, URI sheet (not opened; copy / cancel), internal jump to page 4 and back")
    }
}
