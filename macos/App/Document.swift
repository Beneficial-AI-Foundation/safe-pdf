// Document.swift — an open PDF over the C API v2 (task 11.3b; exact page geometry, 11.3c1;
// open settings and page labels, 11.3c2).
// Plan.md §6 Phase 11; docs/macos-design.md §3 decision 4 (rendering through the confined
// document worker; the GUI only reads the file through the capped read and holds the handle).

import CoreGraphics
import Foundation
import SafePdfC

/// An open document: a `safepdf_document` reference, released when this object goes away
/// (the last release cancels and drains outstanding requests, see safepdf_core.h).
@MainActor final class Document {
    /// The C handle (one reference owned by this object).
    nonisolated(unsafe) let handle: OpaquePointer
    let url: URL
    let pageCount: Int
    /// Displayed page sizes in points (CropBox, /Rotate applied).
    let pageSizes: [CGSize]
    /// The pages' geometry for `safepdf_view_layout`, read once at open: each page's exact
    /// CropBox and /Rotate (`safepdf_doc_page_geom`, task 11.3c1). A page whose geometry the C
    /// API cannot give (a coordinate beyond 64 bits) falls back to its displayed size as a box at
    /// the origin, rounded to 1/64 pt, with rotation 0.
    let geometry: [safepdf_page_geom]
    let repaired: Bool
    let encrypted: Bool
    /// The document's open settings (safepdf_doc_open_settings, read at open; none when the
    /// call fails).
    private(set) var settings = OpenSettings.none
    /// The page labels (safepdf_doc_page_labels, asynchronous: empty until they arrive; one per
    /// page, "" where the document gives none).
    private(set) var labels: [String] = []
    /// The layers state renders use (task 11.3d2; nil: the document's default state). The
    /// layers panel sets it; every open starts with the default (9.r8).
    var layers: LayersState?

    /// Why an open failed.
    struct OpenError: Error {
        let message: String
    }

    /// Opens `url` through `safepdf_doc_open_file` (the capped read; worker path set earlier by
    /// `Core.configureWorker`).
    init(url: URL) throws(OpenError) {
        var err: UnsafeMutablePointer<CChar>? = nil
        guard let h = safepdf_doc_open_file(url.path, nil, &err) else {
            throw OpenError(message: Core.take(err) ?? "the file could not be opened")
        }
        if let err { free(err) }
        handle = h
        self.url = url
        let n = safepdf_doc_page_count(h)
        pageCount = n
        var sizes: [CGSize] = []
        sizes.reserveCapacity(n)
        for i in 0..<n {
            var w = 0.0, hgt = 0.0
            if safepdf_doc_page_size(h, i, &w, &hgt) == 0 {
                sizes.append(CGSize(width: w, height: hgt))
            } else {
                sizes.append(CGSize(width: 612, height: 792))
            }
        }
        pageSizes = sizes
        var geoms: [safepdf_page_geom] = []
        geoms.reserveCapacity(n)
        for i in 0..<n {
            var g = safepdf_page_geom()
            if safepdf_doc_page_geom(h, i, &g) != 0 {
                let zero = safepdf_rat(num: 0, den: 1)
                g = safepdf_page_geom(box: safepdf_rat_box(llx: zero, lly: zero,
                                                           urx: Core.rat(Double(sizes[i].width)),
                                                           ury: Core.rat(Double(sizes[i].height))),
                                      rotate: 0)
            }
            geoms.append(g)
        }
        geometry = geoms
        repaired = safepdf_doc_is_repaired(h) != 0
        encrypted = safepdf_doc_is_encrypted(h) != 0
        settings = OpenSettings.read(self) ?? .none
    }

    /// Requests the page labels; `done` runs on the main queue once they are stored (not when
    /// the request fails: the page field then shows numbers, as without labels).
    func loadLabels(_ done: @escaping @MainActor () -> Void) {
        let ticket = LabelsTicket { [weak self] labels in
            guard let self, labels.count == self.pageCount else { return }
            self.labels = labels
            done()
        }
        let ctx = Unmanaged.passRetained(ticket).toOpaque()
        if safepdf_doc_page_labels(handle, DispatchQueue.main, Document.labelsCallback, ctx) == 0 {
            Unmanaged<LabelsTicket>.fromOpaque(ctx).release()
        }
    }

    /// The C callback: runs on the main queue (the queue passed above).
    private static let labelsCallback: safepdf_labels_fn = { context, _, status, _, list in
        var copied: [String] = []
        if status == SAFEPDF_STATUS_OK, let list, let ls = list.pointee.labels {
            for i in 0..<list.pointee.count { copied.append(ls[i].map { String(cString: $0) } ?? "") }
        }
        safepdf_free_labels(list)
        guard let context else { return }
        let ok = status == SAFEPDF_STATUS_OK
        let bits = UInt(bitPattern: context)
        let labels = copied
        MainActor.assumeIsolated {
            guard let ctx = UnsafeMutableRawPointer(bitPattern: bits) else { return }
            let ticket = Unmanaged<LabelsTicket>.fromOpaque(ctx).takeRetainedValue()
            if ok { ticket.deliver(labels) }
        }
    }

    deinit {
        safepdf_doc_release(handle)
    }
}

/// Who gets the page labels (retained across the C call, released once by the callback).
@MainActor final class LabelsTicket {
    let deliver: @MainActor ([String]) -> Void

    init(deliver: @escaping @MainActor ([String]) -> Void) { self.deliver = deliver }
}
