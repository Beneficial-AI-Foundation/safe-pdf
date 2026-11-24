// Rendering.swift — asynchronous page renders through safepdf_doc_render (task 11.3b).
// Plan.md §6 Phase 11; docs/macos-design.md §3 decisions 3 and 4 (pixels: one memcpy in the
// shim, then zero-copy into a CGImage; completion callbacks on the main queue).

import CoreGraphics
import Foundation
import SafePdfC

/// A finished render.
struct RenderResult {
    let id: safepdf_request_id
    let page: Int
    let key: ZoomKey
    let image: CGImage?
    let error: String?
    let cancelled: Bool
    let ms: Double
}

/// The exact render zoom of a request (pixels per point as a rational, as passed to the core).
struct ZoomKey: Hashable {
    let num: UInt32
    let den: UInt32
    let rotation: UInt32
}

/// The context of one request: who gets the result. Retained across the C call and released
/// exactly once by the callback (the C API calls back exactly once per submitted request).
@MainActor final class RenderTicket {
    let page: Int
    let key: ZoomKey
    let started: Double
    let deliver: @MainActor (RenderResult) -> Void

    init(page: Int, key: ZoomKey, deliver: @escaping @MainActor (RenderResult) -> Void) {
        self.page = page
        self.key = key
        self.started = Core.nowMs()
        self.deliver = deliver
    }
}

enum Rendering {
    /// Submits a render of `page` at `key` with `priority`; the result arrives on the main
    /// queue. Returns the request id (0: not submitted, `deliver` is never called).
    @MainActor static func submit(_ doc: Document, page: Int, key: ZoomKey, priority: Int32,
                                  deliver: @escaping @MainActor (RenderResult) -> Void) -> safepdf_request_id {
        let ticket = RenderTicket(page: page, key: key, deliver: deliver)
        let ctx = Unmanaged.passRetained(ticket).toOpaque()
        let id = safepdf_doc_render(doc.handle, page, key.num, key.den, key.rotation, nil, priority,
                                    DispatchQueue.main, renderCallback, ctx)
        if id == 0 { Unmanaged<RenderTicket>.fromOpaque(ctx).release() }
        return id
    }

    /// The C callback: runs on the main queue (the queue passed above).
    private static let renderCallback: safepdf_render_fn = { context, requestId, status, error, image in
        guard let context else {
            safepdf_free_image(image)
            return
        }
        let errorText = error.map { String(cString: $0) }
        // The pointers cross into the main-actor closure as integers: this callback already
        // runs on the main queue, and the ticket and image are owned by this call alone.
        let contextBits = UInt(bitPattern: context)
        let imageBits = UInt(bitPattern: image)
        MainActor.assumeIsolated {
            guard let ctx = UnsafeMutableRawPointer(bitPattern: contextBits) else { return }
            let ticket = Unmanaged<RenderTicket>.fromOpaque(ctx).takeRetainedValue()
            let image = UnsafeMutablePointer<safepdf_image>(bitPattern: imageBits)
            var cg: CGImage? = nil
            if status == SAFEPDF_STATUS_OK, let image {
                cg = cgImage(taking: image)
            } else {
                safepdf_free_image(image)
            }
            ticket.deliver(RenderResult(id: requestId, page: ticket.page, key: ticket.key, image: cg,
                                        error: status == SAFEPDF_STATUS_ERROR ? (errorText ?? "render failed") : nil,
                                        cancelled: status == SAFEPDF_STATUS_CANCELLED,
                                        ms: Core.nowMs() - ticket.started))
        }
    }

    /// Wraps a rendered image without copying: the CGDataProvider owns the C struct and frees
    /// it with safepdf_free_image when the image is gone.
    static func cgImage(taking img: UnsafeMutablePointer<safepdf_image>) -> CGImage? {
        let w = img.pointee.width, h = img.pointee.height, stride = img.pointee.stride
        guard let data = img.pointee.rgba, w > 0, h > 0, stride >= 4 * w,
              let space = CGColorSpace(name: CGColorSpace.sRGB) else {
            safepdf_free_image(img)
            return nil
        }
        guard let provider = CGDataProvider(
            dataInfo: UnsafeMutableRawPointer(img), data: data, size: stride * h,
            releaseData: { info, _, _ in
                if let info { safepdf_free_image(info.assumingMemoryBound(to: safepdf_image.self)) }
            })
        else {
            safepdf_free_image(img)
            return nil
        }
        return CGImage(width: w, height: h, bitsPerComponent: 8, bitsPerPixel: 32, bytesPerRow: stride,
                       space: space, bitmapInfo: CGBitmapInfo(rawValue: CGImageAlphaInfo.noneSkipLast.rawValue),
                       provider: provider, decode: nil, shouldInterpolate: true, intent: .defaultIntent)
    }
}
