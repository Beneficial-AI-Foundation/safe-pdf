// FindController.swift — Find, Find Next / Previous and highlight-all on the page view
// (task 11.3d1). Plan.md §6 Phase 11; docs/macos-design.md §2 (NSSearchToolbarItem, ⌘F, ⌘G /
// ⇧⌘G) and §3 decision 1: the query is normalised by Select.normQuery, hits are
// PageIndex.hits (findAll, sound by findAll_sound) with their Select.rangeBoxes, the order of
// Find Next / Previous is Select.searchStep (the Tk viewer's nextHit order over the hit counts
// known so far) and the work allowance is Budget.Allowance (task 12.3) — all through
// safepdf_select.h. This file runs the loop: a step that NEEDs a page's index asks for it (low
// priority) and steps again when it comes; an index that fails counts as no hits; a request
// that is CANCELLED ends the search (it is never asked for again in the same search, so the
// loop cannot spin — the 11.3a4 gotcha).
//
// Messages are the Tk viewer's (Viewer.find): "\"q\": hit k/c on page p (wrapped)",
// "\"q\": not found", "search: empty query", the allowance's stop note. Highlight-all draws
// every hit on the visible pages whose index is there (yellow, 50 %) and the current hit in
// orange (Viewer.drawOverlay's Tint.hit / Tint.cur).

import AppKit
import SafePdfC

@MainActor final class FindController {
    private unowned let text: TextController
    /// The normalised query ("" : no search, nothing highlighted).
    private(set) var query = ""
    /// The current hit: page and its index among the page's hits.
    private(set) var hit: (page: Int, index: Int)?
    /// Hit counts per page for `query` (pages whose index is known).
    private var counts: [Int: Int] = [:]
    /// Hit boxes per page for `query` (page space; one list per hit).
    private var hitBoxes: [Int: [[safepdf_box]]] = [:]
    /// The running search (bumped by every step, close and reset).
    private var generation = 0
    /// Whether a search waits for a page's index.
    private(set) var searching = false
    /// The last message (the self-test reads it).
    private(set) var lastMessage = ""
    /// Searches stopped by the work allowance.
    private(set) var stops = 0

    init(_ text: TextController) { self.text = text }

    /// A new document: no search.
    func reset() {
        generation += 1
        query = ""
        hit = nil
        counts = [:]
        hitBoxes = [:]
        searching = false
        lastMessage = ""
    }

    private func say(_ s: String) {
        lastMessage = s
        text.status(s)
    }

    private func redrawVisible() {
        guard let c = text.canvas else { return }
        for p in c.visiblePages() { text.redraw(p) }
    }

    /// Escape in the search field, or its clear button (Viewer.find close): no query, no
    /// highlights.
    func close() {
        generation += 1
        searching = false
        guard !query.isEmpty || hit != nil else { return }
        query = ""
        hit = nil
        counts = [:]
        hitBoxes = [:]
        redrawVisible()
    }

    /// The hit count of page `p` for the current query, when its index is known (a page whose
    /// index failed has none).
    private func count(_ p: Int) -> Int? {
        if let c = counts[p] { return c }
        if let sp = text.store.index(p) {
            let c = safepdf_select_count(sp.handle, query)
            counts[p] = c
            return c
        }
        if text.store.indexError(p) != nil {
            counts[p] = 0
            return 0
        }
        return nil
    }

    /// The hits of page `p` (boxes per hit), when its index is known.
    func hits(_ p: Int) -> [[safepdf_box]]? {
        if let h = hitBoxes[p] { return h }
        guard !query.isEmpty, let sp = text.store.index(p) else { return nil }
        var out: [[safepdf_box]] = []
        if let l = safepdf_select_find(sp.handle, query) {
            if let hs = l.pointee.hits {
                for i in 0..<l.pointee.count {
                    let h = hs[i]
                    var bs: [safepdf_box] = []
                    if let b = h.boxes { for j in 0..<h.box_count { bs.append(b[j]) } }
                    out.append(bs)
                }
            }
            safepdf_select_free_hit_list(l)
        }
        hitBoxes[p] = out
        counts[p] = out.count
        return out
    }

    /// Find Next (`forward`) or Previous with the search field's text `raw` (Return / ⇧Return,
    /// ⌘G / ⇧⌘G; Viewer.find): from the current hit on the current page, else from the current
    /// page's start (end).
    func step(raw: String, forward: Bool) {
        guard let doc = text.document, let canvas = text.canvas else { return }
        let q = Core.take(safepdf_select_normalize_query(raw)) ?? ""
        generation += 1
        let gen = generation
        if q.isEmpty {
            searching = false
            close()
            say("search: empty query")
            return
        }
        if q != query {
            query = q
            hit = nil
            counts = [:]
            hitBoxes = [:]
            redrawVisible()
        }
        let start = canvas.currentPage
        let cur: Int64 = hit.flatMap { $0.page == start ? Int64($0.index) : nil } ?? -1
        var allowance = safepdf_select_allowance()
        safepdf_select_allowance_start(Self.nowMs(), &allowance)
        searching = true
        loop(gen: gen, n: doc.pageCount, start: start, cur: cur, forward: forward, allowance: allowance, spent: 0)
    }

    private static func nowMs() -> UInt64 { UInt64(max(0, Core.nowMs())) }

    /// One step of the search (Select.searchStep over the counts known so far).
    private func loop(gen: Int, n: Int, start: Int, cur: Int64, forward: Bool,
                      allowance: safepdf_select_allowance, spent: Int) {
        guard gen == generation, n > 0 else { return }
        var cs = [Int64](repeating: -1, count: n)
        for p in 0..<n { if let c = count(p) { cs[p] = Int64(c) } }
        var s = safepdf_select_step()
        guard safepdf_select_next_hit(cs, n, start, cur, forward ? 1 : 0, &s) == 0 else {
            searching = false
            return
        }
        switch s.kind {
        case SAFEPDF_SELECT_STEP_HIT:
            searching = false
            show(page: s.page, index: s.index, count: s.count, wrapped: s.wrapped != 0)
        case SAFEPDF_SELECT_STEP_NEED:
            var a = allowance
            guard safepdf_select_allowance_spend(&a, Self.nowMs()) == 0 else {
                searching = false
                stops += 1
                redrawVisible()
                say("\"\(query)\": not found in the \(spent) pages searched so far (this search's work allowance is used up); search again to go on")
                return
            }
            let p = s.page
            let q = query
            text.store.withIndex(p, priority: Int32(SAFEPDF_PRIO_THUMBNAIL)) { [weak self] outcome in
                guard let self, gen == self.generation else { return }
                if case .cancelled = outcome {
                    // Never asked for again in this search: it ends here.
                    self.searching = false
                    self.say("\"\(q)\": search stopped (the text of page \(p + 1) was not read)")
                    return
                }
                self.loop(gen: gen, n: n, start: start, cur: cur, forward: forward, allowance: a, spent: spent + 1)
            }
        default:
            searching = false
            hit = nil
            redrawVisible()
            say("\"\(query)\": not found")
        }
    }

    /// Shows hit `index` of `count` on `page`: the page (Viewer.goTo when it is another one),
    /// the hit scrolled into view, the status.
    private func show(page: Int, index: Int, count: Int, wrapped: Bool) {
        let old = hit
        hit = (page, index)
        if let o = old { text.redraw(o.page) }
        if let pv = text.pageView, let c = text.canvas {
            if page != c.currentPage { pv.goTo(page) }
            if let hs = hits(page), index < hs.count, let t = c.transform(ofPage: page) {
                var u: CGRect? = nil
                for b in hs[index] { let r = t.rect(b); u = u.map { $0.union(r) } ?? r }
                if let u { pv.reveal(u) }
            }
        }
        text.redraw(page)
        say("\"\(query)\": hit \(index + 1)/\(count) on page \(page + 1)\(wrapped ? " (wrapped)" : "")")
    }

    /// The visible area changed: with a query, ask for the visible pages' indexes (their hits
    /// are highlighted when they come).
    func visibleChanged() {
        guard !query.isEmpty, let c = text.canvas else { return }
        for p in c.visiblePages() where !text.store.indexKnown(p) {
            text.store.withIndex(p, priority: Int32(SAFEPDF_PRIO_VISIBLE))
        }
    }

    /// A page's index arrived: its hits can be drawn.
    func indexArrived(_ page: Int) {
        if !query.isEmpty { text.redraw(page) }
    }

    /// Highlight-all of page `page` (yellow at 50 %, the current hit orange at 50 %).
    func draw(_ page: Int, _ t: PageTransform, _ c: PageCanvasView) {
        guard !query.isEmpty, let hs = hits(page), !hs.isEmpty,
              let cg = NSGraphicsContext.current?.cgContext else { return }
        cg.saveGState()
        for (i, bs) in hs.enumerated() {
            let current = hit.map { $0.page == page && $0.index == i } ?? false
            cg.setFillColor(current ? Self.currentColor : Self.hitColor)
            for b in bs { cg.fill(c.pixelOutward(t.rect(b))) }
        }
        cg.restoreGState()
    }

    /// Tint.hit: yellow at 50 %.
    static let hitColor = CGColor(srgbRed: 1, green: 1, blue: 0, alpha: 0.5)
    /// Tint.cur: orange at 50 %.
    static let currentColor = CGColor(srgbRed: 1, green: 165.0 / 255.0, blue: 0, alpha: 0.5)
}
