// SelfTestNav.swift — the self-test's checks of task 11.3c2 (viewing parity, part 2): the
// current-page rule, view modes and spreads, page-at-a-time wheel and keys, the page field,
// back/forward, the document's open settings, the subtitle, the status pill and the titlebar
// flags. Plan.md §6 Phase 11; docs/macos-design.md §1–§2. Headless like SelfTest.swift: no
// window, the activation policy stays Prohibited; open-settings fixtures are generated into the
// output directory (no golden has /PageLayout or /OpenAction), as the Tk smoke case 1s does.

import AppKit
import SafePdfC

extension SelfTest {
    /// A key-down event (no window needed).
    private static func navKey(_ chars: String, _ flags: NSEvent.ModifierFlags = []) -> NSEvent? {
        NSEvent.keyEvent(with: .keyDown, location: .zero, modifierFlags: flags, timestamp: 0,
                         windowNumber: 0, context: nil, characters: chars,
                         charactersIgnoringModifiers: chars, isARepeat: false, keyCode: 0)
    }

    /// A precise (pixel) scroll-wheel event of `dy` points (negative: down).
    private static func wheelEvent(dy: Int32) -> NSEvent? {
        guard let cg = CGEvent(scrollWheelEvent2Source: nil, units: .pixel, wheelCount: 1,
                               wheel1: dy, wheel2: 0, wheel3: 0) else { return nil }
        return NSEvent(cgEvent: cg)
    }

    /// A five-page PDF (612 x 792 pt) whose catalog adds `cat` (the Tk smoke case 1s's
    /// generator: pages 3–7, an outline, /Info /Title `title`).
    static func settingsPDF(_ cat: String, title: String) -> Data {
        var objs: [Int: String] = [
            1: "<< /Type /Catalog /Pages 2 0 R /Outlines 13 0 R \(cat) >>",
            2: "<< /Type /Pages /Kids [3 0 R 4 0 R 5 0 R 6 0 R 7 0 R] /Count 5 /MediaBox [0 0 612 792] >>",
        ]
        for i in 0..<5 {
            objs[3 + i] = "<< /Type /Page /Parent 2 0 R /Contents \(8 + i) 0 R >>"
            let c = "0.\(2 + i) g 72 72 \(100 + 60 * i) \(100 + 100 * i) re f"
            objs[8 + i] = "<< /Length \(c.utf8.count) >>\nstream\n\(c)\nendstream"
        }
        objs[13] = "<< /Type /Outlines /First 14 0 R /Last 15 0 R /Count 2 >>"
        objs[14] = "<< /Title (One) /Parent 13 0 R /Next 15 0 R /Dest [3 0 R /Fit] >>"
        objs[15] = "<< /Title (Four) /Parent 13 0 R /Prev 14 0 R /Dest [6 0 R /Fit] >>"
        objs[16] = "<< /Title (\(title)) >>"
        var body = "%PDF-1.7\n"
        var offs: [Int: Int] = [:]
        for n in objs.keys.sorted() {
            offs[n] = body.utf8.count
            body += "\(n) 0 obj\n\(objs[n] ?? "")\nendobj\n"
        }
        let x = body.utf8.count
        body += "xref\n0 17\n0000000000 65535 f \n"
        for n in 1...16 { body += String(format: "%010d 00000 n \n", offs[n] ?? 0) }
        body += "trailer\n<< /Size 17 /Root 1 0 R /Info 16 0 R >>\nstartxref\n\(x)\n%%EOF\n"
        return Data(body.utf8)
    }

    static func viewingParity(_ doc: Document, _ pv: PageViewController, dir: String) {
        let n = doc.pageCount
        pv.canvas.scaleOverride = 2
        pv.show(doc)
        pump(limit: 60) { pv.canvas.pendingCount == 0 }
        check(pv.canvas.modes == .start && pv.canvas.currentPage == 0, "a new document starts in continuous mode on page 1")

        // 1. The current-page rule (Viewer.viewChanged): Last page keeps the last page current
        // although it cannot scroll to its top; a scroll by the user makes the page under the
        // window centre current.
        if n > 1 {
            pv.goTo(n - 1)
            check(pv.canvas.currentPage == n - 1, "Last page: current page \(pv.canvas.currentPage + 1), expected \(n)")
            pv.refresh()
            check(pv.canvas.currentPage == n - 1, "the current page stays the last after a refresh in place")
            let clip = pv.scrollView.contentView
            let y0 = clip.bounds.origin.y
            clip.scroll(to: NSPoint(x: clip.bounds.origin.x, y: -pv.scrollView.contentInsets.top))
            pv.scrollView.reflectScrolledClipView(clip)
            if abs(clip.bounds.origin.y - y0) >= 0.5 {
                let centre = pv.canvas.page(at: pv.centreAnchor().doc) ?? -1
                check(pv.canvas.currentPage == centre && pv.ownTop == nil,
                      "after the user scrolled to the top the current page is \(pv.canvas.currentPage + 1), the centre's \(centre + 1)")
                say("current page: Last page -> \(n), user scroll to the top -> \(pv.canvas.currentPage + 1)")
            } else {
                check(pv.canvas.currentPage == n - 1, "the view did not move: the current page stays the last")
                say("current page: Last page -> \(n); the whole document fits, the view cannot move")
            }
        }

        // 2. View modes and spreads (Toolbar.ViewChoice, View.spreadPages, View.nextPage).
        var modeLog: [String] = []
        for c in Chrome.viewChoices() ?? [] {
            guard let m = pv.canvas.modes.choosing(c.choice) else { check(false, "choice \(c.key)"); continue }
            pv.setModes(m)
            pump(limit: 60) { pv.canvas.pendingCount == 0 }
            check(pv.canvas.modes.choice == c.choice, "view choice \(c.key): shows \(pv.canvas.modes.choice)")
            let info = pv.spreadInfo
            let want = pv.canvas.modes.continuous ? n : (info?.page_count ?? 0)
            check(pv.canvas.places.count == want, "\(c.key): \(pv.canvas.places.count) pages laid out, expected \(want)")
            check(pv.canvas.errors.isEmpty, "\(c.key): render errors \(pv.canvas.errors)")
            if m.spread == SAFEPDF_SPREAD_ODD.rawValue, n > 1, let a = pv.canvas.rect(ofPage: 0), let b = pv.canvas.rect(ofPage: 1) {
                check(abs(a.midY - b.midY) < 1 || a.minY == b.minY || a.maxX <= b.minX,
                      "\(c.key): pages 1 and 2 side by side (\(a), \(b))")
                check(a.maxX <= b.minX, "\(c.key): page 1 left of page 2")
            }
            if let rep = snapshot(pv.scrollView, scale: 2) { check(writePNG(rep, "\(dir)/mode-\(c.key)-2x.png"), "write png") }
            modeLog.append("\(c.key): \(pv.canvas.places.count) laid out")
        }
        say("view modes: \(modeLog.joined(separator: "; "))")
        // Next and Previous by spreads (facing: two pages on), the first / last spread rules.
        pv.setModes(ViewModes(scroll: SAFEPDF_SCROLL_PAGE.rawValue, spread: SAFEPDF_SPREAD_ODD.rawValue))
        pv.show(page: 0, .top)
        let ctx0 = DocumentWindowController.context(pdf: doc, pages: pv)
        check(ctx0.on_first && (n > 2) != ctx0.on_last, "facing, page 1: on_first \(ctx0.on_first) on_last \(ctx0.on_last)")
        if n > 2 {
            _ = DocumentWindowController.perform(Commands.id(SAFEPDF_CMD_NEXT_PAGE), pages: pv)
            check(pv.canvas.currentPage == 2, "facing: Next from page 1 goes to page \(pv.canvas.currentPage + 1), expected 3")
            check(pv.canvas.places.map(\.page).contains(2), "facing: the spread of page 3 is laid out")
            _ = DocumentWindowController.perform(Commands.id(SAFEPDF_CMD_PREV_PAGE), pages: pv)
            check(pv.canvas.currentPage == 0, "facing: Previous back to page 1")
        }
        // Right to left: page 1 to the right of page 2.
        if n > 1 {
            pv.setModes(ViewModes(scroll: SAFEPDF_SCROLL_PAGE.rawValue, spread: SAFEPDF_SPREAD_ODD.rawValue, rtl: true))
            if let a = pv.canvas.rect(ofPage: 0), let b = pv.canvas.rect(ofPage: 1) {
                check(a.minX >= b.maxX, "right to left: page 1 \(a) right of page 2 \(b)")
            }
        }
        // The View menu's radio entries (Menu.Cmd.radio) and the commands that set the modes.
        _ = DocumentWindowController.perform(Commands.id(SAFEPDF_CMD_SCROLL_VERTICAL), pages: pv)
        _ = DocumentWindowController.perform(Commands.id(SAFEPDF_CMD_SPREAD_EVEN), pages: pv)
        check(pv.canvas.modes.scroll == SAFEPDF_SCROLL_VERTICAL.rawValue && pv.canvas.modes.spread == SAFEPDF_SPREAD_EVEN.rawValue,
              "View menu: vertical scrolling, even spreads")
        check(DocumentWindowController.radioOn(Commands.id(SAFEPDF_CMD_SPREAD_EVEN), modes: pv.canvas.modes) == true &&
              DocumentWindowController.radioOn(Commands.id(SAFEPDF_CMD_SPREAD_ODD), modes: pv.canvas.modes) == false &&
              DocumentWindowController.radioOn(Commands.id(SAFEPDF_CMD_ZOOM_IN), modes: pv.canvas.modes) == nil,
              "radio states of the view-mode entries")
        // A mode change keeps the current page, shown from its top (Viewer.setViewMode); so does
        // a zoom change (the anchored scroll is the viewer's own).
        if n > 1 {
            let keep = min(2, n - 1)
            pv.setModes(ViewModes(scroll: SAFEPDF_SCROLL_PAGE.rawValue, spread: SAFEPDF_SPREAD_NONE.rawValue))
            pv.show(page: keep, .top)
            pv.setModes(.start)
            check(pv.canvas.currentPage == keep, "page -> vertical scrolling keeps page \(keep + 1): \(pv.canvas.currentPage + 1)")
            if let r = pv.canvas.rect(ofPage: keep), !pv.lastScrollClamped {
                check(abs(pv.visibleTop - r.minY + 4) <= 1, "the kept page shows from its top (\(pv.visibleTop) vs \(r.minY))")
            }
            pv.setZoom(ZoomModel.percent(50))
            pv.setZoom(ZoomModel.percent(400))
            check(pv.canvas.currentPage == keep, "zoom changes keep page \(keep + 1): \(pv.canvas.currentPage + 1)")
            pv.setZoom(ZoomModel.auto)
        }
        if let two = ViewModes(spread: SAFEPDF_SPREAD_EVEN.rawValue).choosing(SAFEPDF_VIEW_TWO.rawValue) {
            check(two.spread == SAFEPDF_SPREAD_EVEN.rawValue && two.scroll == SAFEPDF_SCROLL_PAGE.rawValue,
                  "Two Pages keeps Even Spreads (ViewChoice.modes)")
        }

        // 3. Page-at-a-time: the wheel pushed past the edge and space at the end turn the page
        // (single page, Page Fit: the page fits, no room to scroll).
        if n > 1 {
            pv.setModes(ViewModes(scroll: SAFEPDF_SCROLL_PAGE.rawValue, spread: SAFEPDF_SPREAD_NONE.rawValue))
            pv.setZoom(safepdf_zoom_choice(kind: SAFEPDF_ZOOM_PAGE_FIT.rawValue, pct: 0))
            pv.show(page: 0, .top)
            var events = 0
            if wheelEvent(dy: -30) != nil {
                while pv.canvas.currentPage == 0 && events < 60, let e = wheelEvent(dy: -30) {
                    pv.scrollView.scrollWheel(with: e)
                    events += 1
                }
                check(pv.canvas.currentPage == 1, "page mode: \(events) wheel events down did not turn to page 2")
                say("page mode: the wheel turned to page \(pv.canvas.currentPage + 1) after \(events) events of 30 pt")
                var up = 0
                while pv.canvas.currentPage == 1 && up < 60, let e = wheelEvent(dy: 30) {
                    pv.scrollView.scrollWheel(with: e)
                    up += 1
                }
                check(pv.canvas.currentPage == 0, "page mode: wheel up did not turn back to page 1")
            } else {
                say("page mode: no CGEvent scroll events here; wheel check skipped")
            }
            pv.show(page: 0, .top)
            if let space = navKey(" ") {
                pv.canvas.keyDown(with: space)
                check(pv.canvas.currentPage == 1, "page mode: space at the end of page 1 shows page \(pv.canvas.currentPage + 1)")
            }
            if let up = navKey(function(NSUpArrowFunctionKey), [.function]) {
                pv.canvas.keyDown(with: up)
                check(pv.canvas.currentPage == 0, "page mode: Up at the top of page 2 shows page \(pv.canvas.currentPage + 1)")
            }
            // Continuous mode: the wheel is the scroll view's own (not taken).
            pv.setModes(.start)
            if let e = wheelEvent(dy: -30) {
                let before = pv.canvas.currentPage
                pv.scrollView.scrollWheel(with: e)
                check(pv.canvas.currentPage == before || pv.canvas.modes.continuous, "continuous wheel")
            }
        }

        // 4. Page field (Toolbar.pageEntry) and 5. history (Links.History).
        pv.setZoom(ZoomModel.auto)
        pv.show(page: 0, .top)
        if let tb = DocumentToolbar(identifier: "org.safe-pdf.selftest.nav") {
            for id in tb.identifiers where id != .flexibleSpace && id != .sidebarTrackingSeparator { _ = tb.makeItem(id) }
            tb.onPageEntry = { pv.pageEntry($0) }
            let f = PageText.field(labels: doc.labels, page: 0, pages: n)
            tb.setPage(entry: f.entry, of: f.of)
            check(tb.pageTexts.entry == "1" && tb.pageTexts.of == "of \(n)", "page field: \(tb.pageTexts)")
            if n > 1 {
                let before = pv.currentLoc()
                tb.typePage("2", commit: true)
                check(pv.canvas.currentPage == 1, "page field 2: current page \(pv.canvas.currentPage + 1)")
                check(pv.history.canBack && !pv.history.canForward, "a page-field jump is recorded in the history")
                let ctx = DocumentWindowController.context(pdf: doc, pages: pv)
                check(ctx.can_back && !ctx.can_forward, "Back enabled, Forward disabled after a jump")
                pv.historyMove(back: true)
                check(pv.canvas.currentPage == 0 && pv.currentLoc() == before,
                      "Back returns to page 1 at the same place: \(pv.currentLoc()) vs \(before)")
                check(pv.history.canForward, "Forward enabled after Back")
                pv.historyMove(back: false)
                check(pv.canvas.currentPage == 1, "Forward returns to page 2")
                pv.historyMove(back: false)
                check(pv.pill.message == "nothing to go forward to", "pill: \(pv.pill.message)")
                // First / Last page are not recorded (Viewer.goTo).
                let backs = pv.history.back.count
                _ = DocumentWindowController.perform(Commands.id(SAFEPDF_CMD_FIRST_PAGE), pages: pv)
                check(pv.history.back.count == backs && pv.canvas.currentPage == 0, "First page is not a history entry")
            }
            tb.typePage("zz9", commit: true)
            check(pv.pill.message.hasPrefix("no page \"zz9\""), "invalid page entry: pill \(pv.pill.message)")
            say("page field: \(tb.pageTexts.entry) \(tb.pageTexts.of); history back \(pv.history.back.count), forward \(pv.history.forward.count)")
        } else {
            check(false, "toolbar for the page field")
        }
        check(PageText.of(labels: ["i", "ii", "iii"], page: 2, pages: 120) == "page iii (3/120)", "page text with labels")

        // 6. Subtitle with the document's labels (asynchronous).
        var labelsCame = false
        doc.loadLabels { labelsCame = true }
        pump(limit: 10) { labelsCame }
        let sub = DocumentWindowController.subtitle(pdf: doc, pages: pv)
        let wantSub = PageText.of(labels: doc.labels, page: pv.canvas.currentPage, pages: n) +
            (pv.shownPct.map { " · \($0)%" } ?? "")
        check(sub == wantSub && sub.hasPrefix("page "), "subtitle \(sub), expected \(wantSub)")
        say("subtitle: \(sub)\(labelsCame ? "" : " (labels did not come)"); labels: \(doc.labels.prefix(4))")

        // 7. Status pill: the 10 Mpx cap (12.3b) at 800 %, the subtitle shows the capped zoom.
        pv.setZoom(ZoomModel.percent(800))
        if let note = pv.capNote {
            check(pv.pill.message.contains(note) && note.hasPrefix("zoom limited to "), "cap pill: \(pv.pill.message)")
            check((pv.shownPct ?? 800) < 800, "subtitle shows the capped zoom: \(pv.shownPct ?? 0)%")
            say("pill at 800 %: \(pv.pill.message); subtitle \(DocumentWindowController.subtitle(pdf: doc, pages: pv))")
        } else {
            say("800 % is not capped for this page (small page)")
        }
        waitRenders(pv)
        pv.setZoom(ZoomModel.auto)
        check(pv.pill.glass == ProcessInfo.processInfo.isOperatingSystemAtLeast(OperatingSystemVersion(majorVersion: 26, minorVersion: 0, patchVersion: 0)),
              "pill material: glass \(pv.pill.glass)")

        // 8. Titlebar flags.
        check(DocumentWindowController.flagsView(repaired: false, encrypted: false) == nil &&
              DocumentWindowController.flagsView(repaired: true, encrypted: true) != nil, "titlebar flags view")

        openSettings(pv, dir: dir)
    }

    /// The open settings (task 9.r8) on generated files: each opens as its settings say, and
    /// nothing carries over to the next open.
    private static func openSettings(_ pv: PageViewController, dir: String) {
        let osDir = "\(dir)/opensettings"
        try? FileManager.default.createDirectory(atPath: osDir, withIntermediateDirectories: true)
        let cases: [(String, String, String)] = [
            ("xyz", "/OpenAction [5 0 R /XYZ 0 792 1.5]", "unused"),
            ("r2l", "/PageLayout /TwoPageLeft /ViewerPreferences << /Direction /R2L >>", "unused"),
            ("layout-TwoColumnRight", "/PageLayout /TwoColumnRight", "unused"),
            ("named", "/OpenAction << /S /GoTo /D (four) >> /Names << /Dests << /Names [(four) [6 0 R /FitH 792]] >> >>", "unused"),
            ("js", "/OpenAction << /S /JavaScript /JS (app.alert\\(1\\)) >>", "unused"),
            ("prefs", "/ViewerPreferences << /HideToolbar true /HideMenubar true /HideWindowUI true /DisplayDocTitle true >>",
             "Open Settings Test"),
            ("none", "", "unused"),
        ]
        var lines: [String] = []
        for (name, cat, title) in cases {
            let path = "\(osDir)/\(name).pdf"
            guard (try? settingsPDF(cat, title: title).write(to: URL(fileURLWithPath: path))) != nil else {
                check(false, "write \(path)")
                continue
            }
            let doc: Document
            do { doc = try Document(url: URL(fileURLWithPath: path)) } catch {
                check(false, "open \(name): \(error.message)")
                continue
            }
            // The user's changes to the previous file never carry over (every open starts afresh).
            pv.rotate(clockwise: true)
            pv.setModes(ViewModes(scroll: SAFEPDF_SCROLL_PAGE.rawValue, spread: SAFEPDF_SPREAD_EVEN.rawValue))
            pv.show(doc)
            pump(limit: 60) { pv.canvas.pendingCount == 0 }
            let c = pv.canvas
            let off = c.rect(ofPage: c.currentPage).map { pv.visibleTop - $0.minY } ?? -1
            let xs = c.places.prefix(2).map { "\($0.page)@\(Int($0.pixels.minX))" }.joined(separator: ",")
            lines.append("\(name): scroll=\(c.modes.scroll) spread=\(c.modes.spread) rtl=\(c.modes.rtl) zoom=\(ZoomModel.label(c.zoomChoice)) page=\(c.currentPage + 1) rot=\(c.userRotation) off=\(Int(off)) xs=\(xs) title=\(doc.settings.title ?? "-") pill=\(pv.pill.message)")
            check(c.userRotation == 0, "\(name): the rotation carried over")
            check(c.errors.isEmpty, "\(name): render errors \(c.errors)")
            switch name {
            case "xyz":
                check(c.modes == .start && c.currentPage == 2 && c.zoomChoice.kind == SAFEPDF_ZOOM_PERCENT.rawValue &&
                      c.zoomChoice.pct == 150, "xyz: page 3 at 150 % in continuous mode")
                check(abs(off) <= 1 || pv.lastScrollClamped, "xyz: the page top at the view top (offset \(off))")
                check(pv.ownTop != nil, "xyz: the destination is the viewer's own place")
            case "r2l":
                check(c.modes.scroll == SAFEPDF_SCROLL_PAGE.rawValue && c.modes.spread == SAFEPDF_SPREAD_ODD.rawValue &&
                      c.modes.rtl, "r2l: two pages, right to left")
                if let a = c.rect(ofPage: 0), let b = c.rect(ofPage: 1) {
                    check(a.minX >= b.maxX, "r2l: page 1 right of page 2")
                }
            case "layout-TwoColumnRight":
                check(c.modes.scroll == SAFEPDF_SCROLL_VERTICAL.rawValue && c.modes.spread == SAFEPDF_SPREAD_EVEN.rawValue,
                      "TwoColumnRight: continuous, even spreads")
            case "named":
                check(c.currentPage == 3 && c.zoomChoice.kind == SAFEPDF_ZOOM_PAGE_WIDTH.rawValue,
                      "named destination: page 4 at Page Width")
            case "js":
                check(pv.pill.message.contains("not executed") && c.currentPage == 0, "js: noted, not run: \(pv.pill.message)")
            case "prefs":
                check(doc.settings.title == "Open Settings Test", "prefs: document title \(doc.settings.title ?? "-")")
                check(pv.pill.message.contains("not honoured"), "prefs: pill says what was not honoured: \(pv.pill.message)")
            default:
                check(c.modes == .start && ZoomModel.same(c.zoomChoice, ZoomModel.auto) && c.currentPage == 0 &&
                      pv.pill.message.isEmpty, "none: the default view, nothing carried over, no note")
            }
        }
        try? (lines.joined(separator: "\n") + "\n").write(toFile: "\(osDir)/opensettings.txt", atomically: true, encoding: .utf8)
        for l in lines { say("open settings \(l)") }
    }
}
