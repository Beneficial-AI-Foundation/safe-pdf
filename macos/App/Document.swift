// Document.swift — an open PDF over the C API v2 (task 11.3b; exact page geometry, 11.3c1).
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
    }

    deinit {
        safepdf_doc_release(handle)
    }
}
