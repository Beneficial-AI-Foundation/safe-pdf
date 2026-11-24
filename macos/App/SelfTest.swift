// SelfTest.swift — the headless self-test of the native shell (task 11.3b; the contract of the
// 11.1 spike, macos/selftest.sh). Plan.md §6 Phase 11; docs/macos-design.md §5 (first page
// visible fast). Never activates the app and never creates a window: the activation policy is
// Prohibited (main.swift) and the views are drawn off screen into bitmaps.
//
// Checks: the chrome tables build (every command in the menubar, every toolbar item), open and
// its error path, page 1 rendered through safepdf_doc_render at 1x and 2x with the expected
// pixel size, pages 1-10 at 2x, the real scroll view and page canvas at 1x and 2x backing
// (layout through safepdf_view_layout), scrolling to page 2, and dark mode (canvas changes,
// paper stays white). Task 11.3c1: the exact page geometry, the page view's keys, the zoom
// drop-down, zoom steps and presets anchored at the centre (C2), a pinch committed to a
// quantised zoom, the cross-fade of sharp renders, rotation both ways, and a backing-scale
// change. Task 11.3c2 (SelfTestNav.swift): the current-page rule, view modes and spreads,
// page-at-a-time wheel and keys, the page field, back/forward, open settings on generated
// files, the subtitle, the status pill and the titlebar flags. Writes PNGs and timings.txt to
// DIR; prints `failures: N`.

import AppKit
import SafePdfC

@MainActor enum SelfTest {
    private static var log = ""
    private static var failures = 0

    static func say(_ s: String) {
        log += s + "\n"
        FileHandle.standardError.write(Data((s + "\n").utf8))
    }

    static func check(_ ok: Bool, _ what: @autoclosure () -> String) {
        if !ok {
            failures += 1
            say("FAIL: " + what())
        }
    }

    /// Runs the main run loop until `done()` or `limit` seconds; returns the time waited (ms).
    @discardableResult
    static func pump(limit: Double, until done: () -> Bool) -> Double {
        let t0 = Core.nowMs()
        while !done() && Core.nowMs() - t0 < limit * 1000 {
            RunLoop.main.run(mode: .default, before: Date(timeIntervalSinceNow: 0.005))
        }
        return Core.nowMs() - t0
    }

    static func writePNG(_ rep: NSBitmapImageRep, _ path: String) -> Bool {
        guard let data = rep.representation(using: .png, properties: [:]) else { return false }
        return (try? data.write(to: URL(fileURLWithPath: path))) != nil
    }

    /// Draws `view` off screen at `scale` pixels per point.
    static func snapshot(_ view: NSView, scale: CGFloat) -> NSBitmapImageRep? {
        let r = view.bounds
        guard let rep = NSBitmapImageRep(
            bitmapDataPlanes: nil, pixelsWide: Int(r.width * scale), pixelsHigh: Int(r.height * scale),
            bitsPerSample: 8, samplesPerPixel: 4, hasAlpha: true, isPlanar: false,
            colorSpaceName: .deviceRGB, bytesPerRow: 0, bitsPerPixel: 0) else { return nil }
        rep.size = r.size
        view.cacheDisplay(in: r, to: rep)
        return rep
    }

    /// Renders one page through safepdf_doc_render and waits for it.
    private static func renderOnce(_ doc: Document, page: Int, num: UInt32, den: UInt32) -> RenderResult? {
        var result: RenderResult? = nil
        let id = Rendering.submit(doc, page: page, key: ZoomKey(num: num, den: den, rotation: 0),
                                  priority: Int32(SAFEPDF_PRIO_CURRENT)) { result = $0 }
        guard id != 0 else { return nil }
        pump(limit: 60) { result != nil }
        return result
    }

    private static func luminance(_ rep: NSBitmapImageRep, x: Int, y: Int) -> CGFloat? {
        guard let c = rep.colorAt(x: x, y: y)?.usingColorSpace(.deviceRGB) else { return nil }
        return (c.redComponent + c.greenComponent + c.blueComponent) / 3
    }

    static func run(dir: String, path: String, processStartMs: Double) -> Int32 {
        try? FileManager.default.createDirectory(atPath: dir, withIntermediateDirectories: true)
        say(String(format: "startup (process start to core initialised): %.1f ms", Core.nowMs() - processStartMs))
        say("activation policy: \(NSApp.activationPolicy() == .prohibited ? "prohibited" : "NOT prohibited")")
        check(NSApp.activationPolicy() == .prohibited, "activation policy is not Prohibited")

        // 1. Chrome tables.
        if let (_, stats) = MainMenu.build() {
            say("menubar: \(stats.menus) menus, \(stats.items) items, \(stats.keyEquivalents) key equivalents, \(stats.hiddenAlternates) hidden alternates")
            if !stats.skippedKeys.isEmpty {
                say("keys left to the page view (PageKeys): \(stats.skippedKeys.joined(separator: ", "))")
            }
            check(stats.commandsPresent.count == Chrome.commandCount,
                  "menubar has \(stats.commandsPresent.count) of \(Chrome.commandCount) commands")
        } else {
            check(false, "menubar tables")
        }
        if let tb = DocumentToolbar(identifier: "org.safe-pdf.selftest") {
            let ids = tb.identifiers.filter { $0 != .flexibleSpace && $0 != .sidebarTrackingSeparator }
            let built = ids.compactMap { tb.makeItem($0) }
            say("toolbar: \(ids.count) items (\(tb.identifiers.count) with spaces), built \(built.count)")
            check(built.count == ids.count && ids.count == 17, "toolbar items \(built.count)/\(ids.count), expected 17")
            tb.setZoom(ZoomModel.percent(137))
            check(tb.zoomTitle == "137%", "zoom drop-down title \(tb.zoomTitle ?? "nil"), expected 137%")
            tb.setZoom(ZoomModel.auto)
            say("zoom drop-down: \(tb.zoomPresets.map(\.label).joined(separator: ", ")); title \(tb.zoomTitle ?? "nil")")
        } else {
            check(false, "toolbar table")
        }

        // 2. Worker and open.
        if let problem = Core.configureWorker() {
            check(false, problem)
            return 1
        }
        say("worker: \(Core.workerPath() ?? "?")")
        do {
            _ = try Document(url: URL(fileURLWithPath: "/nonexistent/x.pdf"))
            check(false, "open of a missing file succeeded")
        } catch {
            say("missing-file error text: \(error.message)")
        }
        let t0 = Core.nowMs()
        let doc: Document
        do {
            doc = try Document(url: URL(fileURLWithPath: path))
        } catch {
            check(false, "open \(path): \(error.message)")
            say("failures: \(failures)")
            return 1
        }
        let n = doc.pageCount
        say(String(format: "open %@: %.1f ms; pages: %d; page 1: %.2f x %.2f pt%@%@",
                   (path as NSString).lastPathComponent, Core.nowMs() - t0, n,
                   Double(doc.pageSizes.first?.width ?? 0), Double(doc.pageSizes.first?.height ?? 0),
                   doc.repaired ? " (repaired)" : "", doc.encrypted ? " (encrypted)" : ""))
        check(n > 0, "no pages")
        guard n > 0 else { return 1 }

        // 3. The C API v2 render path: page 1 at 1x and 2x, pages 1-10 at 2x.
        let size = doc.pageSizes[0]
        for s in 1...2 {
            guard let r = renderOnce(doc, page: 0, num: UInt32(s), den: 1) else {
                check(false, "render page 1 at \(s)x not submitted")
                continue
            }
            check(r.image != nil, "render page 1 at \(s)x: \(r.error ?? (r.cancelled ? "cancelled" : "?"))")
            guard let img = r.image else { continue }
            say(String(format: "C API render page 1 at %dx: %d x %d px, %.1f ms", s, img.width, img.height, r.ms))
            let ew = Int((Double(size.width) * Double(s)).rounded()), eh = Int((Double(size.height) * Double(s)).rounded())
            check(abs(img.width - ew) <= 1 && abs(img.height - eh) <= 1,
                  "image \(img.width) x \(img.height) at \(s)x, expected about \(ew) x \(eh)")
            check(writePNG(NSBitmapImageRep(cgImage: img), "\(dir)/capi-page1-\(s)x.png"), "write png")
        }
        let m = min(n, 10)
        var total = 0.0, worst = 0.0
        for i in 0..<m {
            guard let r = renderOnce(doc, page: i, num: 2, den: 1), r.image != nil else {
                check(false, "render page \(i + 1) at 2x")
                continue
            }
            total += r.ms
            worst = max(worst, r.ms)
        }
        say(String(format: "C API render at 2x, pages 1-%d: mean %.1f ms/page, worst %.1f ms", m, total / Double(m), worst))

        // 4. The real page area, off screen: scroll view + canvas at 1x and 2x backing.
        let pv = PageViewController(frame: NSRect(x: 0, y: 0, width: 700, height: 900))
        let root = pv.view
        root.layoutSubtreeIfNeeded()
        pv.scrollView.tile()
        var firstMs = -1.0
        var requested = Core.nowMs()
        pv.canvas.onRender = { res in
            if firstMs < 0 && res.image != nil { firstMs = Core.nowMs() - requested }
            say(String(format: "  view render page %d at %u/%u px/pt: %.1f ms%@", res.page + 1, res.key.num,
                       res.key.den, res.ms, res.error.map { " error: " + $0 } ?? (res.cancelled ? " (cancelled)" : "")))
        }
        var lightTop: NSBitmapImageRep? = nil
        for s in [1, 2] {
            pv.canvas.scaleOverride = CGFloat(s)
            firstMs = -1
            requested = Core.nowMs()
            pv.show(doc)
            let waited = pump(limit: 60) { pv.canvas.pendingCount == 0 }
            say(String(format: "view at %dx: %d pages laid out, first page drawn after %.1f ms, all visible pages after %.1f ms",
                       s, pv.canvas.places.count, firstMs, waited))
            if let p = pv.canvas.places.first, let raw = pv.canvas.layout?.raw {
                say("  layout: region \(raw.region_w) x \(raw.region_h) px, page 1 at \(p.pixels); canvas \(pv.canvasSize) pt, document view \(pv.canvas.frame.size) pt")
            }
            check(pv.canvas.places.count == n, "layout has \(pv.canvas.places.count) of \(n) pages")
            check(pv.canvas.errors.isEmpty, "render errors: \(pv.canvas.errors)")
            check(firstMs >= 0, "no page drawn at \(s)x")
            if let rep = snapshot(pv.scrollView, scale: CGFloat(s)) {
                check(writePNG(rep, "\(dir)/view-top-\(s)x.png"), "write png")
                if s == 2 { lightTop = rep }
            } else {
                check(false, "snapshot at \(s)x")
            }
        }

        // 5. Scroll to page 2 (the Next page command's path).
        if n > 1 {
            pv.scroll(toPage: 1)
            pump(limit: 60) { pv.canvas.pendingCount == 0 }
            say(String(format: "scrolled to y = %.1f pt; current page %d", pv.scrollView.contentView.bounds.origin.y,
                       pv.canvas.currentPage + 1))
            check(pv.canvas.currentPage == 1, "current page after scrolling is \(pv.canvas.currentPage + 1), expected 2")
            if let rep = snapshot(pv.scrollView, scale: 2) {
                check(writePNG(rep, "\(dir)/view-scroll-2x.png"), "write png")
            }
            pv.scroll(toPage: 0)
            pump(limit: 60) { pv.canvas.pendingCount == 0 }
        }

        // 6. Dark mode: the canvas around the pages follows the appearance, the paper stays white.
        if let light = lightTop, let pageRect = pv.canvas.rect(ofPage: 0) {
            pv.scrollView.appearance = NSAppearance(named: .darkAqua)
            pv.scrollView.needsDisplay = true
            if let dark = snapshot(pv.scrollView, scale: 2) {
                check(writePNG(dark, "\(dir)/view-top-2x-dark.png"), "write png")
                let origin = pv.scrollView.contentView.bounds.origin
                let px = Int((pageRect.minX - origin.x + 2) * 2), py = Int((pageRect.minY - origin.y + 2) * 2)
                let bx = 1 // the margin left of the page
                let paperLight = luminance(light, x: px, y: py), paperDark = luminance(dark, x: px, y: py)
                let bgLight = luminance(light, x: bx, y: 2), bgDark = luminance(dark, x: bx, y: 2)
                say(String(format: "dark mode: paper %.2f -> %.2f, canvas %.2f -> %.2f",
                           paperLight ?? -1, paperDark ?? -1, bgLight ?? -1, bgDark ?? -1))
                check((paperDark ?? 0) > 0.95, "the paper is not white in dark mode")
                check((bgDark ?? 1) < (bgLight ?? 0), "the canvas does not darken in dark mode")
            }
            pv.scrollView.appearance = nil
        }

        zoomAndRotation(doc, pv, dir: dir)
        viewingParity(doc, pv, dir: dir)
        sidebarChecks(doc, pv, dir: dir) // task 11.3d2 (SelfTestSidebar.swift)

        pv.show(nil)
        say(String(format: "total self-test time: %.0f ms; failures: %d", Core.nowMs() - processStartMs, failures))
        try? log.write(toFile: "\(dir)/timings.txt", atomically: true, encoding: .utf8)
        return failures == 0 ? 0 : 1
    }

    // MARK: task 11.3c1 — geometry, keys, zoom, pinch, cross-fade, rotation, backing scale

    /// A key-down event for the page view's key handling (no window needed).
    private static func key(_ chars: String, _ flags: NSEvent.ModifierFlags = []) -> NSEvent? {
        NSEvent.keyEvent(with: .keyDown, location: .zero, modifierFlags: flags, timestamp: 0,
                         windowNumber: 0, context: nil, characters: chars,
                         charactersIgnoringModifiers: chars, isARepeat: false, keyCode: 0)
    }

    static func function(_ code: Int) -> String {
        Unicode.Scalar(code).map { String(Character($0)) } ?? ""
    }

    /// The page point (page units on the displayed page, rotation as laid out) under the
    /// centre of the visible area.
    private static func centrePoint(_ pv: PageViewController) -> (page: Int, x: Double, y: Double)? {
        guard let a = pv.canvas.anchor(at: pv.centreAnchor().doc) else { return nil }
        let z = ZoomModel.double(a.zoom)
        guard z > 0 else { return nil }
        return (a.page, Double(a.q.x) / z, Double(a.q.y) / z)
    }

    static func waitRenders(_ pv: PageViewController) {
        pump(limit: 60) { pv.canvas.pendingCount == 0 }
    }

    static func zoomAndRotation(_ doc: Document, _ pv: PageViewController, dir: String) {
        let n = doc.pageCount

        // Geometry: the exact CropBox and /Rotate agree with the displayed sizes.
        var rotates: [UInt32] = []
        for i in 0..<n {
            var g = doc.geometry[i]
            var info = safepdf_rotation_info()
            guard safepdf_view_rotation(g.rotate, &g.box, &info) == 0 else {
                check(false, "rotation info of page \(i + 1)")
                continue
            }
            rotates.append(g.rotate)
            let w = ZoomModel.double(info.width), h = ZoomModel.double(info.height)
            let s = doc.pageSizes[i]
            check(abs(w - Double(s.width)) < 1e-6 && abs(h - Double(s.height)) < 1e-6,
                  "page \(i + 1): geometry \(w) x \(h) vs displayed size \(s)")
        }
        let g0 = doc.geometry[0].box
        say("geometry: page 1 CropBox [\(g0.llx.num)/\(g0.llx.den) \(g0.lly.num)/\(g0.lly.den) \(g0.urx.num)/\(g0.urx.den) \(g0.ury.num)/\(g0.ury.den)], /Rotate of pages 1-\(min(n, 8)): \(rotates.prefix(8).map(String.init).joined(separator: " "))")

        // Keys of the page view, through the exported key table.
        let keys = PageKeys.shared
        let expect: [(String, NSEvent.ModifierFlags, safepdf_cmd?)] = [
            ("+", [.shift], SAFEPDF_CMD_ZOOM_IN), ("-", [], SAFEPDF_CMD_ZOOM_OUT),
            ("0", [], SAFEPDF_CMD_ACTUAL_SIZE), ("f", [], SAFEPDF_CMD_FIT_PAGE),
            ("w", [], SAFEPDF_CMD_FIT_WIDTH), ("r", [], SAFEPDF_CMD_ROTATE_CW),
            ("R", [.shift], SAFEPDF_CMD_ROTATE_CCW),
            (function(NSHomeFunctionKey), [.function], SAFEPDF_CMD_FIRST_PAGE),
            (function(NSEndFunctionKey), [.function], SAFEPDF_CMD_LAST_PAGE),
            ("r", [.command], nil), ("x", [], nil), ("f", [.shift], nil),
        ]
        var keyLog: [String] = []
        for (c, f, want) in expect {
            guard let ev = key(c, f) else { check(false, "key event \(c)"); continue }
            let got = keys.command(for: ev)
            let shown = (c.unicodeScalars.first?.value ?? 0) < 0xF700 ? c : "fn"
            keyLog.append("\(shown)\(f.contains(.shift) ? "⇧" : "")\(f.contains(.command) ? "⌘" : "")→\(got.map(String.init) ?? "-")")
            check(got == want.map { Commands.id($0) }, "key \(c) \(f.rawValue): command \(got.map(String.init) ?? "none"), expected \(want.map { String(Commands.id($0)) } ?? "none")")
        }
        say("page-view keys: \(keyLog.joined(separator: " "))")
        if let sp = key(" "), let ss = key(" ", [.shift]), let dn = key(function(NSDownArrowFunctionKey), [.function]) {
            check(PageKeys.scroll(for: sp).map { $0 == (0, 1, true) } == true, "space scrolls a view down")
            check(PageKeys.scroll(for: ss).map { $0 == (0, -1, true) } == true, "shift-space scrolls a view up")
            check(PageKeys.scroll(for: dn).map { $0 == (0, 1, false) } == true, "down arrow scrolls a line")
        }
        // Through the canvas: a key runs the command callback.
        var ran: [Int] = []
        pv.canvas.onKeyCommand = { ran.append($0); return true }
        if let ev = key("r") { pv.canvas.keyDown(with: ev) }
        check(ran == [Commands.id(SAFEPDF_CMD_ROTATE_CW)], "canvas keyDown r ran \(ran)")
        pv.canvas.onKeyCommand = nil

        // Zoom (scale 2): 200 % (the centre well inside page 1, so the anchored scroll is not
        // clamped at an edge), a step in and out, anchored at the centre.
        pv.canvas.scaleOverride = 2
        pv.show(doc)
        waitRenders(pv)
        let s2 = ZoomModel.scaling(2)
        guard let z100 = ZoomModel.pctZoom(100, scaling: s2),
              let z100at1 = ZoomModel.pctZoom(100, scaling: ZoomModel.scaling(1)) else {
            check(false, "pctZoom")
            return
        }
        check(ZoomModel.same(pv.canvas.zoomChoice, ZoomModel.auto), "a new document starts at Automatic Zoom")
        pv.setZoom(ZoomModel.percent(100))
        check(pv.canvas.baseZoom.map { ZoomModel.same($0, z100) } == true,
              "100 % at 2x: base zoom \(pv.canvas.baseZoom.map(ZoomModel.double) ?? -1)")
        pv.setZoom(ZoomModel.percent(200))
        pv.scroll(toPage: 0)
        waitRenders(pv)
        guard let before = centrePoint(pv) else {
            check(false, "no page under the centre")
            return
        }
        let swaps0 = pv.canvas.sharpSwaps, fades0 = pv.crossFades
        let t0 = Core.nowMs()
        check(pv.step(zoomIn: true), "zoom in from 200 %")
        let pctIn = pv.canvas.zoomChoice.pct
        let inClamped = pv.lastScrollClamped
        check(pv.canvas.zoomChoice.kind == SAFEPDF_ZOOM_PERCENT.rawValue && pctIn > 200,
              "zoom in: choice \(pv.canvas.zoomChoice.kind)/\(pctIn)")
        if inClamped {
            say("zoom in: the anchored scroll was clamped at the document's edge (small pages); centre check skipped")
        } else if let after = centrePoint(pv), let z = pv.canvas.baseZoom.map(ZoomModel.double) {
            let tol = 1.5 / z
            check(after.page == before.page && abs(after.x - before.x) < tol && abs(after.y - before.y) < tol,
                  "zoom in kept the centre's page point: \(before) -> \(after)")
            say(String(format: "zoom in 200%% -> %u%%: centre page point (%.2f, %.2f) -> (%.2f, %.2f) pt on page %d",
                       pctIn, before.x, before.y, after.x, after.y, after.page + 1))
        } else {
            check(false, "no page under the centre after zooming in")
        }
        waitRenders(pv)
        say(String(format: "  sharp renders after the step: %.0f ms; %d swapped from a scaled image, %d cross-fades",
                   Core.nowMs() - t0, pv.canvas.sharpSwaps - swaps0, pv.crossFades - fades0))
        check(pv.canvas.sharpSwaps > swaps0, "no sharp render replaced a scaled image after zooming in")
        check(pv.crossFades > fades0, "no cross-fade after zooming in")
        check(pv.canvas.errors.isEmpty, "render errors after zooming: \(pv.canvas.errors)")
        if let rep = snapshot(pv.scrollView, scale: 2) { check(writePNG(rep, "\(dir)/zoom-in-2x.png"), "write png") }
        check(pv.step(zoomIn: false), "zoom out")
        check(pv.canvas.zoomChoice.pct < pctIn, "zoom out: \(pv.canvas.zoomChoice.pct) not below \(pctIn)")
        if let back = centrePoint(pv), let z = pv.canvas.baseZoom.map(ZoomModel.double), !pv.lastScrollClamped {
            check(abs(back.x - before.x) < 2 / z && abs(back.y - before.y) < 2 / z,
                  "zoom out kept the centre's page point: \(before) -> \(back)")
        }
        // The end of the range: no step past View.maxPct.
        if let k = ZoomModel.constants {
            pv.setZoom(ZoomModel.percent(k.max_pct))
            check(!pv.step(zoomIn: true), "zoom in at \(k.max_pct) % changed the zoom")
            pv.setZoom(ZoomModel.percent(k.min_pct))
            check(!pv.step(zoomIn: false), "zoom out at \(k.min_pct) % changed the zoom")
        }

        // Fit modes: the page whose size picked the zoom fits the visible area / its width
        // (unless the pixel cap lowered its zoom).
        pv.setZoom(safepdf_zoom_choice(kind: SAFEPDF_ZOOM_PAGE_FIT.rawValue, pct: 0))
        if let r = pv.canvas.rect(ofPage: pv.canvas.laidOutPage) {
            check(r.height <= pv.canvasSize.height + 0.5 && r.width <= pv.canvasSize.width + 0.5,
                  "page fit: page \(pv.canvas.laidOutPage + 1) \(r.size) in \(pv.canvasSize)")
        }
        pv.setZoom(safepdf_zoom_choice(kind: SAFEPDF_ZOOM_PAGE_WIDTH.rawValue, pct: 0))
        // (View.fitZoom keeps the zoom at most 8 px per page unit: a narrow page stays narrower.)
        if let r = pv.canvas.rect(ofPage: pv.canvas.laidOutPage), let k = ZoomModel.constants,
           let pl = pv.canvas.place(ofPage: pv.canvas.laidOutPage), !pl.capped, ZoomModel.double(pl.zoom) < 8 {
            let room = pv.canvasSize.width
            check(r.width <= room + 0.5 && r.width >= room - 4 * CGFloat(k.margin),
                  "page width: page \(pv.canvas.laidOutPage + 1) \(r.width) pt in \(room) pt")
        }

        // Pinch: live magnification 1.5 at the centre, committed to a quantised percentage.
        pv.setZoom(ZoomModel.percent(100))
        waitRenders(pv)
        let mid = pv.centreAnchor().doc
        pv.scrollView.setMagnification(1.5, centeredAt: mid)
        let pinchBefore = centrePoint(pv)
        pv.commitMagnification(anchor: pv.centreAnchor())
        let want = ZoomModel.pinchPct(base: z100, magnification: 1.5, scaling: s2)
        check(pv.scrollView.magnification == 1, "magnification after the pinch: \(pv.scrollView.magnification)")
        check(pv.canvas.zoomChoice.kind == SAFEPDF_ZOOM_PERCENT.rawValue && pv.canvas.zoomChoice.pct == want,
              "pinch to 1.5x: \(pv.canvas.zoomChoice.pct) %, expected \(want.map(String.init) ?? "?")")
        if let a = pinchBefore, let b = centrePoint(pv), let z = pv.canvas.baseZoom.map(ZoomModel.double),
           !pv.lastScrollClamped {
            check(abs(a.x - b.x) < 2 / z && abs(a.y - b.y) < 2 / z, "pinch kept the centre's page point: \(a) -> \(b)")
        }
        let fades1 = pv.crossFades
        waitRenders(pv)
        say("pinch 1.5x at 100 %: committed at \(pv.canvas.zoomChoice.pct) %, \(pv.crossFades - fades1) cross-fades")
        check(pv.crossFades > fades1, "no cross-fade after the pinch")

        // Rotation: clockwise, the pages turn by 90° more than their /Rotate; back again (at
        // 200 %, so that the centre is not at an edge of the scroll range).
        pv.setZoom(ZoomModel.percent(200))
        pv.scroll(toPage: 0)
        waitRenders(pv)
        let originBefore = pv.scrollView.contentView.bounds.origin
        let rectBefore = pv.canvas.rect(ofPage: 0)
        pv.rotate(clockwise: true)
        var rotClamped = pv.lastScrollClamped
        check(pv.canvas.userRotation == 90, "rotate right: user rotation \(pv.canvas.userRotation)")
        for pl in pv.canvas.places where pl.page < doc.geometry.count {
            let want = (doc.geometry[pl.page].rotate + 90) % 360
            check(pl.rotation == want && pl.key?.rotation == 1,
                  "page \(pl.page + 1): rotation \(pl.rotation) key \(pl.key?.rotation ?? 9), expected \(want) / 1")
        }
        if let r0 = rectBefore, let r1 = pv.canvas.rect(ofPage: 0) {
            check(abs(r0.width - r1.height) < 1 && abs(r0.height - r1.width) < 1, "rotated page 1: \(r0.size) -> \(r1.size)")
        }
        waitRenders(pv)
        check(pv.canvas.errors.isEmpty, "render errors after rotating: \(pv.canvas.errors)")
        if let rep = snapshot(pv.scrollView, scale: 2) { check(writePNG(rep, "\(dir)/rotate-cw-2x.png"), "write png") }
        pv.rotate(clockwise: false)
        rotClamped = rotClamped || pv.lastScrollClamped
        check(pv.canvas.userRotation == 0, "rotate left back: user rotation \(pv.canvas.userRotation)")
        let originAfter = pv.scrollView.contentView.bounds.origin
        if !rotClamped {
            check(abs(originAfter.x - originBefore.x) <= 1 && abs(originAfter.y - originBefore.y) <= 1,
                  "rotate right then left restores the scroll position: \(originBefore) -> \(originAfter)")
        }
        pv.rotate(clockwise: false)
        check(pv.canvas.userRotation == 270, "rotate left from 0: \(pv.canvas.userRotation)")
        for _ in 0..<3 { pv.rotate(clockwise: true) }
        check(pv.canvas.userRotation == 180, "three right turns from 270: \(pv.canvas.userRotation)")
        pv.rotate(clockwise: true)
        pv.rotate(clockwise: true)
        check(pv.canvas.userRotation == 0, "full turn: \(pv.canvas.userRotation)")
        waitRenders(pv)
        say("rotation: right/left, page 1 \(rectBefore?.size ?? .zero) pt; scroll origin \(originBefore) -> \(originAfter)\(rotClamped ? " (clamped at an edge: restore check skipped)" : "")")

        // Backing scale 2 -> 1 -> 2 (Retina <-> non-Retina): new pixels, same zoom in points,
        // the centre's page point kept.
        pv.setZoom(ZoomModel.percent(100))
        waitRenders(pv)
        let pointRect = pv.canvas.rect(ofPage: 0)
        let centreBefore = centrePoint(pv)
        pv.canvas.scaleOverride = 1
        pv.backingChanged()
        if let a = centreBefore, let b = centrePoint(pv), !pv.lastScrollClamped {
            check(a.page == b.page && abs(a.x - b.x) < 2 && abs(a.y - b.y) < 2,
                  "backing change kept the centre's page point: \(a) -> \(b)")
        }
        check(pv.canvas.baseZoom.map { ZoomModel.same($0, z100at1) } == true,
              "100 % at 1x after the backing change: \(pv.canvas.baseZoom.map(ZoomModel.double) ?? -1)")
        check(pv.canvas.places.first?.key.map { $0.num == 1 && $0.den == 1 } == true,
              "render key at 1x: \(String(describing: pv.canvas.places.first?.key))")
        if let a = pointRect, let b = pv.canvas.rect(ofPage: 0) {
            check(abs(a.width - b.width) < 1 && abs(a.height - b.height) < 1, "page 1 in points at 1x: \(a.size) vs \(b.size)")
        }
        waitRenders(pv)
        check(pv.canvas.errors.isEmpty, "render errors at 1x: \(pv.canvas.errors)")
        pv.canvas.scaleOverride = 2
        pv.backingChanged()
        waitRenders(pv)
        say("backing change 2x -> 1x -> 2x: base zoom \(pv.canvas.baseZoom.map(ZoomModel.double) ?? -1) px/pt")
    }
}
