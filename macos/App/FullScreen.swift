// FullScreen.swift — native full screen with the trusted file-identity line (task 11.3d2; the
// Tk viewer's 9.r8 full screen and 12.5 `.ident`). Plan.md §6 Phases 11–12 ("Honest UI for
// degraded/hidden content"); docs/macos-design.md §2 ("native full screen"; "the full-screen
// identity line stays as its own overlay (12.5 requires it)"); docs/viewer.md "Honest UI for
// hidden content".
//
// While the document holds the screen without chrome (native full screen: the toolbar and the
// title bar hide), a dark strip at the bottom of the page area reads the identity line
// (Viewer.identityLine through safepdf_identity_line: the cleaned file name and path, never the
// document's /Title). The strip belongs to the window, outside the page area: the page view's
// scroll view ends above it, so nothing the document draws can cover or imitate it in place. It
// is shown before the window enters full screen and removed after it leaves (Viewer.setFullScreen
// / syncIdentity). A document's `/PageMode /FullScreen` enters full screen on open (as the Tk
// viewer does), with the note "full screen (Escape leaves)"; Escape leaves, and the sidebar then
// follows `/NonFullScreenPageMode` (Sidebar.onLoad).

import AppKit

/// The identity strip over the bottom of the page area.
final class IdentityStrip: NSView {
    let label = NSTextField(labelWithString: "")
    /// The strip's height in points.
    static let height: CGFloat = 26

    override init(frame: NSRect) {
        super.init(frame: frame)
        wantsLayer = true
        // Opaque and the same in light and dark mode: it is the viewer's, not the document's.
        layer?.backgroundColor = NSColor(white: 0.12, alpha: 1).cgColor
        label.font = .systemFont(ofSize: NSFont.smallSystemFontSize + 1, weight: .medium)
        label.textColor = .white
        label.lineBreakMode = .byTruncatingMiddle
        label.alignment = .center
        label.translatesAutoresizingMaskIntoConstraints = false
        label.setContentCompressionResistancePriority(.defaultLow, for: .horizontal)
        addSubview(label)
        NSLayoutConstraint.activate([
            label.leadingAnchor.constraint(equalTo: leadingAnchor, constant: 12),
            label.trailingAnchor.constraint(equalTo: trailingAnchor, constant: -12),
            label.centerYAnchor.constraint(equalTo: centerYAnchor),
        ])
        setAccessibilityRole(.staticText)
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    var text: String {
        get { label.stringValue }
        set {
            label.stringValue = newValue
            toolTip = newValue
            setAccessibilityLabel(newValue)
        }
    }
}

/// The identity line of a page view (Viewer.syncIdentity): shown while the window is in full
/// screen with a document, else hidden.
@MainActor final class IdentityLine {
    let strip = IdentityStrip(frame: NSRect(x: 0, y: 0, width: 400, height: IdentityStrip.height))
    private weak var pages: PageViewController?
    /// Whether the strip is shown (the self-test reads it).
    private(set) var shown = false

    init(pages: PageViewController) {
        self.pages = pages
    }

    /// The line for a document's file (nil: no document).
    static func text(for url: URL?) -> String {
        SidebarRules.identityLine(path: url?.path)
    }

    /// Shows the strip with the line for `url` (the page area ends above it), or hides it.
    func sync(show: Bool, url: URL?) {
        guard let pv = pages else { return }
        let container = pv.view
        if show, let url {
            strip.text = Self.text(for: url)
            if !shown {
                strip.frame = NSRect(x: 0, y: 0, width: container.bounds.width, height: IdentityStrip.height)
                strip.autoresizingMask = [.width, .maxYMargin]
                container.addSubview(strip, positioned: .above, relativeTo: nil)
                var f = container.bounds
                f.origin.y = IdentityStrip.height
                f.size.height = max(1, f.height - IdentityStrip.height)
                pv.scrollView.frame = f
                movePill(by: IdentityStrip.height)
                shown = true
                pv.relayout()
            }
        } else if shown {
            strip.removeFromSuperview()
            pv.scrollView.frame = container.bounds
            movePill(by: -IdentityStrip.height)
            shown = false
            pv.relayout()
        }
    }

    /// Keeps the status pill above the strip (its bottom constraint moves up by `dy`).
    private func movePill(by dy: CGFloat) {
        guard let pv = pages else { return }
        for c in pv.view.constraints where (c.firstItem as? NSView) === pv.pill && c.firstAttribute == .bottom {
            c.constant -= dy
        }
    }
}
