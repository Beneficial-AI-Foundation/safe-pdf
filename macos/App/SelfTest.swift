// SelfTest.swift — the headless self-test of the native shell (task 11.3b; the contract of the
// 11.1 spike, macos/selftest.sh). Plan.md §6 Phase 11; docs/macos-design.md §5 (first page
// visible fast). Never activates the app and never creates a window: the activation policy is
// Prohibited (main.swift) and the views are drawn off screen into bitmaps.
//
// Checks: the chrome tables build (every command in the menubar, every toolbar item), open and
// its error path, page 1 rendered through safepdf_doc_render at 1x and 2x with the expected
// pixel size, pages 1-10 at 2x, the real scroll view and page canvas at 1x and 2x backing
// (layout through safepdf_view_layout), scrolling to page 2, and dark mode (canvas changes,
// paper stays white). Writes PNGs and timings.txt to DIR; prints `failures: N`.

import AppKit
import SafePdfC

@MainActor enum SelfTest {
    private static var log = ""
    private static var failures = 0

    private static func say(_ s: String) {
        log += s + "\n"
        FileHandle.standardError.write(Data((s + "\n").utf8))
    }

    private static func check(_ ok: Bool, _ what: @autoclosure () -> String) {
        if !ok {
            failures += 1
            say("FAIL: " + what())
        }
    }

    /// Runs the main run loop until `done()` or `limit` seconds; returns the time waited (ms).
    @discardableResult
    private static func pump(limit: Double, until done: () -> Bool) -> Double {
        let t0 = Core.nowMs()
        while !done() && Core.nowMs() - t0 < limit * 1000 {
            RunLoop.main.run(mode: .default, before: Date(timeIntervalSinceNow: 0.005))
        }
        return Core.nowMs() - t0
    }

    private static func writePNG(_ rep: NSBitmapImageRep, _ path: String) -> Bool {
        guard let data = rep.representation(using: .png, properties: [:]) else { return false }
        return (try? data.write(to: URL(fileURLWithPath: path))) != nil
    }

    /// Draws `view` off screen at `scale` pixels per point.
    private static func snapshot(_ view: NSView, scale: CGFloat) -> NSBitmapImageRep? {
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
                say("keys left to the page view (11.3c): \(stats.skippedKeys.joined(separator: ", "))")
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

        pv.show(nil)
        say(String(format: "total self-test time: %.0f ms; failures: %d", Core.nowMs() - processStartMs, failures))
        try? log.write(toFile: "\(dir)/timings.txt", atomically: true, encoding: .utf8)
        return failures == 0 ? 0 : 1
    }
}
