// MarksPreview.swift — the preview of edited saved marks (task 11.3e2; the Tk viewer's
// `State.view` and `updatePreview`, task 9.5g). Plan.md §6 Phases 9–11; docs/macos-design.md
// §3 decisions 1 and 4.
//
// While saved marks are changed or deleted, the Tk viewer renders its pages from
// `Save.preview`: the document with only those changes applied, built in memory by the same
// writer as Save and reopened strictly, so a recoloured or deleted saved mark shows at once
// (new marks are drawn by the viewer itself). It sends those bytes to its document worker.
// Here the same bytes come from `safepdf_marks_preview` (the exported `Save.preview`), built on
// a background queue from a snapshot of the store, and are opened with `safepdf_doc_open_bytes`
// as a second document over its own confined worker: the page canvas sends its renders there
// (`PageCanvasView.setRenderSource`); layout, text and links stay with the opened document, as
// in Tk. A newer edit supersedes a preview still being built; an error leaves the pages as they
// are and the pill says why (Save would report the same error).

import Foundation
import SafePdfC

/// A document opened from preview bytes: only its handle is used (renders). Released off the
/// main thread (the last release drains the worker's outstanding requests).
final class PreviewSource: @unchecked Sendable {
    /// One reference to the C document, owned by this object.
    let handle: OpaquePointer

    init(handle: OpaquePointer) { self.handle = handle }

    deinit {
        let bits = UInt(bitPattern: handle)
        MarksPreview.queue.async {
            if let h = OpaquePointer(bitPattern: bits) { safepdf_doc_release(h) }
        }
    }
}

/// Builds the preview after every change of the marks and hands it to the page canvas.
@MainActor final class MarksPreview {
    /// The serial queue previews are built on (and preview documents released on).
    nonisolated static let queue = DispatchQueue(label: "org.safe-pdf.marks-preview", qos: .userInitiated)

    /// The preview the pages are rendered from now (nil: the document itself).
    private(set) var source: PreviewSource?
    /// The store version the current rendering source reflects (`source`, or the document when
    /// nothing saved is edited); nil while a newer preview is being built.
    private(set) var shownVersion: Int?
    /// Previews built so far (the self-test counts them).
    private(set) var built = 0
    /// The last preview error (nil: none).
    private(set) var lastError: String?
    private var generation = 0
    private var running = 0

    /// The new rendering source (nil: the document itself).
    var onSource: ((PreviewSource?) -> Void)?
    /// A message for the pill.
    var onStatus: ((String) -> Void)?

    /// Whether a preview is being built.
    var busy: Bool { running > 0 }

    /// Whether the pages show the store's current state of its saved marks.
    func isCurrent(_ model: MarksModel) -> Bool { shownVersion == model.version }

    /// A new document: no preview.
    func reset() {
        generation += 1
        source = nil
        shownVersion = 0
        lastError = nil
    }

    /// After an edit of the marks (Viewer.updatePreview): when saved marks are changed or
    /// deleted, builds the preview and renders from it once it is there; else renders from the
    /// document itself again (when a preview was shown).
    func update(_ model: MarksModel) {
        let st = model.state
        let edited = st.changed_count > 0 || st.deleted_saved_count > 0
        generation += 1
        let gen = generation
        let version = model.version
        guard edited else {
            shownVersion = version
            if source != nil {
                source = nil
                onSource?(nil)
            }
            return
        }
        shownVersion = nil
        running += 1
        let store = UInt(bitPattern: safepdf_marks_retain(model.handle))
        Self.queue.async {
            safepdf_thread_enter()
            var docBits: UInt = 0
            var message: String? = nil
            if let m = OpaquePointer(bitPattern: store) {
                var bytes = safepdf_marks_bytes()
                var err: UnsafeMutablePointer<CChar>? = nil
                if safepdf_marks_preview(m, nil, &bytes, &err) != 0 {
                    message = Core.take(err) ?? "the preview failed"
                } else if let data = bytes.data, bytes.size > 0 {
                    var oerr: UnsafeMutablePointer<CChar>? = nil
                    if let d = safepdf_doc_open_bytes(data, bytes.size, nil, &oerr) {
                        docBits = UInt(bitPattern: d)
                        if let oerr { free(oerr) }
                    } else {
                        message = Core.take(oerr) ?? "the preview does not open"
                    }
                }
                safepdf_free_marks_bytes(&bytes)
            }
            let msg = message
            let bits = docBits
            DispatchQueue.main.async {
                MainActor.assumeIsolated {
                    // The store's reference is dropped where the store lives (the main thread).
                    safepdf_marks_release(OpaquePointer(bitPattern: store))
                    let doc = OpaquePointer(bitPattern: bits).map { PreviewSource(handle: $0) }
                    MarksPreview.deliver(self, gen: gen, version: version, source: doc, error: msg)
                }
            }
        }
    }

    /// A preview arrived on the main queue: kept unless a newer edit superseded it.
    private static func deliver(_ p: MarksPreview, gen: Int, version: Int, source: PreviewSource?, error: String?) {
        p.running -= 1
        guard gen == p.generation else { return } // superseded: `source` is released
        if let error {
            p.lastError = error
            p.onStatus?("cannot show the change of a saved mark: \(error)")
            return
        }
        p.lastError = nil
        p.built += 1
        p.source = source
        p.shownVersion = version
        p.onSource?(source)
    }
}
