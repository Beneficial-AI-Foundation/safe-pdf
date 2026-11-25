// TextStore.swift — the per-document cache of page text indexes and links for selection, find
// and links (task 11.3d1). Plan.md §6 Phase 11; docs/macos-design.md §3 decisions 1, 2 and 4:
// indexes and links come from the confined worker (safepdf_doc_page_index / safepdf_doc_links,
// callbacks on the main queue); each index becomes one immutable `safepdf_select_page` handle
// (safepdf_select_page_new) that every selection and search query uses.
//
// Requests are asynchronous; a page's request is made once and every caller waiting for it is
// told when it ends. An index that failed is kept as failed (the page has no text for this
// document, as in the Tk viewer); a request that was CANCELLED is not cached, and its waiters are
// told so — a caller that loops over pages must stop on it (the 11.3a4 gotcha: a step loop must
// not re-request a cancelled index forever).

import AppKit
import SafePdfC

/// A page's selection handle (one reference owned; released with the object), plus the glyph
/// boxes and line count of its index (the self-test's coverage checks).
@MainActor final class SelectPage {
    nonisolated(unsafe) let handle: OpaquePointer
    let cellCount: Int
    /// The cells' boxes in page space (reading order).
    let boxes: [safepdf_box]

    init(handle: OpaquePointer, boxes: [safepdf_box]) {
        self.handle = handle
        self.boxes = boxes
        cellCount = safepdf_select_cell_count(handle)
    }

    deinit { safepdf_select_page_release(handle) }
}

/// One link of a page, copied out of its `safepdf_link_list`.
struct LinkInfo {
    let box: safepdf_box
    let kind: safepdf_action_kind
    let page: Int
    let left: Double?
    let top: Double?
    let text: String
}

/// A page's links: the C list (owned; freed with the object: the C calls on links read it) and
/// a Swift copy.
@MainActor final class PageLinks {
    nonisolated(unsafe) let list: UnsafeMutablePointer<safepdf_link_list>
    let links: [LinkInfo]

    init(taking list: UnsafeMutablePointer<safepdf_link_list>) {
        self.list = list
        var ls: [LinkInfo] = []
        if let p = list.pointee.links {
            for i in 0..<list.pointee.count {
                let a = p[i].action
                ls.append(LinkInfo(box: p[i].box, kind: a.kind, page: a.page,
                                   left: a.has_left != 0 ? a.left : nil,
                                   top: a.has_top != 0 ? a.top : nil, text: Core.string(a.text)))
            }
        }
        links = ls
    }

    /// The link at page point (x, y) (Links.linkAt through safepdf_select_link_at).
    func index(at x: Double, _ y: Double) -> Int? {
        var i = 0
        return safepdf_select_link_at(list, x, y, &i) == 0 && i < links.count ? i : nil
    }

    /// Links.describe of link `i` with the document's page labels.
    func describe(_ i: Int, labels: [String], pages: Int) -> String {
        guard i >= 0, i < links.count, let p = list.pointee.links else { return "" }
        var action = p[i].action
        return PageText.withCStrings(labels) { ptrs, n in
            Core.take(safepdf_select_link_describe(&action, ptrs, n, pages))
        } ?? ""
    }

    deinit { safepdf_free_links(list) }
}

/// How a request for a page's data ended.
enum TextOutcome<T> {
    case ready(T)
    case failed(String)
    case cancelled
}

/// Who gets a request's result (retained across the C call, released once by the callback).
@MainActor final class TextTicket {
    let deliver: @MainActor (safepdf_status, String?, UInt) -> Void

    init(deliver: @escaping @MainActor (safepdf_status, String?, UInt) -> Void) { self.deliver = deliver }
}

/// The text indexes and links of one document's pages.
@MainActor final class TextStore {
    private(set) var document: Document?
    /// Bumped on every document change: late callbacks of the old document are dropped.
    private var epoch = 0

    private enum Slot<T> {
        case ready(T)
        case failed(String)
    }

    private var indexes: [Int: Slot<SelectPage>] = [:]
    private var indexInflight: [Int: (id: safepdf_request_id, priority: Int32)] = [:]
    private var indexWaiters: [Int: [(TextOutcome<SelectPage>) -> Void]] = [:]
    private var linkLists: [Int: Slot<PageLinks>] = [:]
    private var linkInflight: [Int: (id: safepdf_request_id, priority: Int32)] = [:]
    private var linkWaiters: [Int: [(TextOutcome<PageLinks>) -> Void]] = [:]

    /// Called when a page's index arrived (ready or failed): the page view redraws it.
    var onIndex: ((Int) -> Void)?
    /// Pages whose index was requested, in order (the self-test checks the Find Next path).
    private(set) var indexRequests: [Int] = []

    /// Requests in flight (the self-test waits for zero).
    var pendingCount: Int { indexInflight.count + linkInflight.count }

    /// Drops everything of the previous document and cancels its requests.
    func reset(_ doc: Document?) {
        if let old = document {
            for (_, r) in indexInflight { safepdf_doc_cancel(old.handle, r.id) }
            for (_, r) in linkInflight { safepdf_doc_cancel(old.handle, r.id) }
        }
        epoch += 1
        let iw = indexWaiters, lw = linkWaiters
        indexes = [:]
        indexInflight = [:]
        indexWaiters = [:]
        linkLists = [:]
        linkInflight = [:]
        linkWaiters = [:]
        indexRequests = []
        document = doc
        for (_, ws) in iw { for w in ws { w(.cancelled) } }
        for (_, ws) in lw { for w in ws { w(.cancelled) } }
    }

    /// Cancels the outstanding requests (their waiters are told CANCELLED when the callbacks
    /// come), keeping what arrived.
    func cancelAll() {
        guard let doc = document else { return }
        for (_, r) in indexInflight { safepdf_doc_cancel(doc.handle, r.id) }
        for (_, r) in linkInflight { safepdf_doc_cancel(doc.handle, r.id) }
    }

    // MARK: indexes

    /// The page's index when it has arrived.
    func index(_ page: Int) -> SelectPage? {
        if case .ready(let p)? = indexes[page] { return p }
        return nil
    }

    /// Why the page has no index (it failed), nil when it has one or it is not known yet.
    func indexError(_ page: Int) -> String? {
        if case .failed(let e)? = indexes[page] { return e }
        return nil
    }

    /// Whether the page's index has arrived or failed (no request needed).
    func indexKnown(_ page: Int) -> Bool { indexes[page] != nil }

    /// Calls `then` with the page's index: at once when it is known, else when its request
    /// ends (made now at `priority` if none is in flight; a request in flight is made more
    /// urgent).
    func withIndex(_ page: Int, priority: Int32, _ then: ((TextOutcome<SelectPage>) -> Void)? = nil) {
        switch indexes[page] {
        case .ready(let p)?: then?(.ready(p)); return
        case .failed(let e)?: then?(.failed(e)); return
        case nil: break
        }
        guard let doc = document, page >= 0, page < doc.pageCount else {
            then?(.failed("no such page"))
            return
        }
        if let then { indexWaiters[page, default: []].append(then) }
        if let r = indexInflight[page] {
            if priority < r.priority {
                safepdf_doc_raise(doc.handle, r.id, priority)
                indexInflight[page] = (r.id, priority)
            }
            return
        }
        let e = epoch
        let ticket = TextTicket { [weak self] status, error, bits in
            let index = UnsafeMutablePointer<safepdf_page_index>(bitPattern: bits)
            guard let self, self.epoch == e else {
                safepdf_free_page_index(index)
                return
            }
            self.indexDone(page, status: status, error: error, index: index)
        }
        let ctx = Unmanaged.passRetained(ticket).toOpaque()
        // Under the document's layers state, as the renders (Tk `applyLayers`; nil: default).
        let id: safepdf_request_id
        if let layers = doc.layers {
            id = layers.withC { st in
                safepdf_doc_page_index(doc.handle, page, st, priority, DispatchQueue.main,
                                       TextStore.indexCallback, ctx)
            }
        } else {
            id = safepdf_doc_page_index(doc.handle, page, nil, priority, DispatchQueue.main,
                                        TextStore.indexCallback, ctx)
        }
        if id == 0 {
            Unmanaged<TextTicket>.fromOpaque(ctx).release()
            let ws = indexWaiters.removeValue(forKey: page) ?? []
            for w in ws { w(.failed("the request could not be submitted")) }
            return
        }
        indexRequests.append(page)
        indexInflight[page] = (id, priority)
    }

    private func indexDone(_ page: Int, status: safepdf_status, error: String?,
                           index: UnsafeMutablePointer<safepdf_page_index>?) {
        indexInflight[page] = nil
        let outcome: TextOutcome<SelectPage>
        if status == SAFEPDF_STATUS_OK, let index {
            var err: UnsafeMutablePointer<CChar>? = nil
            if let h = safepdf_select_page_new(index, &err) {
                var boxes: [safepdf_box] = []
                if let cells = index.pointee.cells {
                    boxes.reserveCapacity(index.pointee.cell_count)
                    for i in 0..<index.pointee.cell_count { boxes.append(cells[i].box) }
                }
                let sp = SelectPage(handle: h, boxes: boxes)
                indexes[page] = .ready(sp)
                outcome = .ready(sp)
            } else {
                let msg = Core.take(err) ?? "the page index could not be read"
                indexes[page] = .failed(msg)
                outcome = .failed(msg)
            }
            safepdf_free_page_index(index)
        } else if status == SAFEPDF_STATUS_CANCELLED {
            safepdf_free_page_index(index)
            outcome = .cancelled // not cached: a later request asks again
        } else {
            safepdf_free_page_index(index)
            let msg = error ?? "the page text could not be read"
            indexes[page] = .failed(msg)
            outcome = .failed(msg)
        }
        let ws = indexWaiters.removeValue(forKey: page) ?? []
        if case .cancelled = outcome {} else { onIndex?(page) }
        for w in ws { w(outcome) }
    }

    /// The C callback: runs on the main queue (the queue passed above).
    private static let indexCallback: safepdf_page_index_fn = { context, _, status, error, index in
        guard let context else {
            safepdf_free_page_index(index)
            return
        }
        let text = error.map { String(cString: $0) }
        let ctxBits = UInt(bitPattern: context)
        let bits = UInt(bitPattern: index)
        MainActor.assumeIsolated {
            guard let ctx = UnsafeMutableRawPointer(bitPattern: ctxBits) else { return }
            Unmanaged<TextTicket>.fromOpaque(ctx).takeRetainedValue().deliver(status, text, bits)
        }
    }

    // MARK: links

    /// The page's links when they have arrived.
    func links(_ page: Int) -> PageLinks? {
        if case .ready(let l)? = linkLists[page] { return l }
        return nil
    }

    /// Whether the page's links have arrived or failed.
    func linksKnown(_ page: Int) -> Bool { linkLists[page] != nil }

    /// As `withIndex`, for the page's links.
    func withLinks(_ page: Int, priority: Int32, _ then: ((TextOutcome<PageLinks>) -> Void)? = nil) {
        switch linkLists[page] {
        case .ready(let l)?: then?(.ready(l)); return
        case .failed(let e)?: then?(.failed(e)); return
        case nil: break
        }
        guard let doc = document, page >= 0, page < doc.pageCount else {
            then?(.failed("no such page"))
            return
        }
        if let then { linkWaiters[page, default: []].append(then) }
        if let r = linkInflight[page] {
            if priority < r.priority {
                safepdf_doc_raise(doc.handle, r.id, priority)
                linkInflight[page] = (r.id, priority)
            }
            return
        }
        let e = epoch
        let ticket = TextTicket { [weak self] status, error, bits in
            let list = UnsafeMutablePointer<safepdf_link_list>(bitPattern: bits)
            guard let self, self.epoch == e else {
                safepdf_free_links(list)
                return
            }
            self.linksDone(page, status: status, error: error, list: list)
        }
        let ctx = Unmanaged.passRetained(ticket).toOpaque()
        let id = safepdf_doc_links(doc.handle, page, priority, DispatchQueue.main, TextStore.linksCallback, ctx)
        if id == 0 {
            Unmanaged<TextTicket>.fromOpaque(ctx).release()
            let ws = linkWaiters.removeValue(forKey: page) ?? []
            for w in ws { w(.failed("the request could not be submitted")) }
            return
        }
        linkInflight[page] = (id, priority)
    }

    private func linksDone(_ page: Int, status: safepdf_status, error: String?,
                           list: UnsafeMutablePointer<safepdf_link_list>?) {
        linkInflight[page] = nil
        let outcome: TextOutcome<PageLinks>
        if status == SAFEPDF_STATUS_OK, let list {
            let l = PageLinks(taking: list)
            linkLists[page] = .ready(l)
            outcome = .ready(l)
        } else if status == SAFEPDF_STATUS_CANCELLED {
            safepdf_free_links(list)
            outcome = .cancelled
        } else {
            safepdf_free_links(list)
            let msg = error ?? "the page's links could not be read"
            linkLists[page] = .failed(msg)
            outcome = .failed(msg)
        }
        let ws = linkWaiters.removeValue(forKey: page) ?? []
        for w in ws { w(outcome) }
    }

    private static let linksCallback: safepdf_links_fn = { context, _, status, error, list in
        guard let context else {
            safepdf_free_links(list)
            return
        }
        let text = error.map { String(cString: $0) }
        let ctxBits = UInt(bitPattern: context)
        let bits = UInt(bitPattern: list)
        MainActor.assumeIsolated {
            guard let ctx = UnsafeMutableRawPointer(bitPattern: ctxBits) else { return }
            Unmanaged<TextTicket>.fromOpaque(ctx).takeRetainedValue().deliver(status, text, bits)
        }
    }
}
