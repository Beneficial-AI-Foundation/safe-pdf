// LinkController.swift — following links on the page view (task 11.3d1). Plan.md §6 Phase 11;
// docs/macos-design.md §2 ("NSAlert as document-modal sheets (... external link ...)") and §3
// decision 1: the link under a point is Links.linkAt and its status text Links.describe
// (safepdf_select_link_at / _describe); the links come from the worker (safepdf_doc_links).
//
// As the Tk viewer (Viewer.activate / confirmUri, docs/viewer.md "URI links are never
// opened"): an internal destination jumps there through the page view's jump (recorded in the
// back/forward history, Links.History); an external address shows a confirmation sheet with
// the exact address and two buttons, Copy Address and Cancel — Copy Address puts the address on
// the clipboard, nothing is ever opened; any other action (a page not in the document, an
// unknown named destination, Launch / GoToR / JavaScript …) is not followed and the status
// says so.

import AppKit
import SafePdfC

@MainActor final class LinkController {
    private unowned let text: TextController
    /// The external-link sheet last built (the self-test reads it; nil once answered).
    private(set) var pendingAlert: NSAlert?
    /// The address the pending sheet shows.
    private(set) var pendingURI: String?
    /// Bumped by every click and reset: a click waiting for its page's links belongs to it.
    private var clicks = 0

    init(_ text: TextController) { self.text = text }

    func reset() {
        clicks += 1
        pendingAlert = nil
        pendingURI = nil
    }

    /// A click in place at page point (x, y) of `page`: follows the link there, if any (the
    /// page's links are asked for first when they have not arrived).
    func click(page: Int, x: Double, y: Double) {
        clicks += 1
        let token = clicks
        text.store.withLinks(page, priority: Int32(SAFEPDF_PRIO_CURRENT)) { [weak self] outcome in
            guard let self, self.clicks == token, case .ready(let ls) = outcome,
                  let i = ls.index(at: x, y) else { return }
            self.activate(ls, i)
        }
    }

    /// Activates link `i` of `ls` (Viewer.activate).
    func activate(_ ls: PageLinks, _ i: Int) {
        guard i >= 0, i < ls.links.count, let pv = text.pageView, let doc = text.document else { return }
        let l = ls.links[i]
        switch l.kind {
        case SAFEPDF_ACTION_GOTO:
            pv.jump(to: l.page, left: l.left.map(Core.rat), top: l.top.map(Core.rat))
        case SAFEPDF_ACTION_URI:
            confirm(l.text)
        default:
            text.status(ls.describe(i, labels: doc.labels, pages: doc.pageCount))
        }
    }

    /// The external-link sheet (Viewer.confirmUri / ::safepdf::askUri): the exact address,
    /// Copy Address or Cancel. Shown on the document window; without one (the self-test) it is
    /// only built and kept in `pendingAlert`.
    func confirm(_ uri: String) {
        let alert = Self.alert(for: uri)
        pendingAlert = alert
        pendingURI = uri
        if let w = text.sheetWindow?(), w.isVisible {
            alert.beginSheetModal(for: w) { [weak self] response in
                self?.answer(copy: response == .alertFirstButtonReturn, uri: uri)
            }
        }
    }

    /// The answer to the sheet: Copy Address copies the address (it is not opened); Cancel
    /// leaves it. The status says which.
    func answer(copy: Bool, uri: String) {
        pendingAlert = nil
        pendingURI = nil
        if copy {
            text.pasteboard.clearContents()
            text.pasteboard.setString(uri, forType: .string)
            text.status("copied the link address to the clipboard (not opened): \(uri)")
        } else {
            text.status("external link not followed: \(uri)")
        }
    }

    /// The sheet's alert: the Tk dialog's text and the address in a read-only, selectable,
    /// scrollable field (shown in full, wrapped at any character).
    static func alert(for uri: String) -> NSAlert {
        let alert = NSAlert()
        alert.alertStyle = .informational
        alert.messageText = "External link"
        alert.informativeText = "This link points outside the document, to the address below. "
            + "SafePDF never opens it; it can copy the address to the clipboard."
        alert.addButton(withTitle: "Copy Address")
        alert.addButton(withTitle: "Cancel") // Escape and ⌘. press it
        let scroll = NSScrollView(frame: NSRect(x: 0, y: 0, width: 360, height: 72))
        scroll.hasVerticalScroller = true
        scroll.borderType = .bezelBorder
        let tv = NSTextView(frame: scroll.contentView.bounds)
        tv.isEditable = false
        tv.isSelectable = true
        tv.isRichText = false
        tv.font = .monospacedSystemFont(ofSize: NSFont.smallSystemFontSize, weight: .regular)
        tv.textContainer?.widthTracksTextView = true
        tv.textContainer?.lineBreakMode = .byCharWrapping
        tv.autoresizingMask = [.width]
        tv.string = uri
        tv.setAccessibilityLabel("Link address")
        scroll.documentView = tv
        alert.accessoryView = scroll
        return alert
    }

    /// The address an alert shows (the self-test checks the sheet).
    static func shownAddress(_ alert: NSAlert) -> String? {
        ((alert.accessoryView as? NSScrollView)?.documentView as? NSTextView)?.string
    }
}
