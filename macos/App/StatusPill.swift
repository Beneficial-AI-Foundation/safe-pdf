// StatusPill.swift — the transient status pill over the page area (task 11.3c2).
// Plan.md §6 Phase 11; docs/macos-design.md §2 ("no status bar ...: render notes, open-settings
// notes, 'zoom limited to 10 Mpx', errors appear as a transient glass pill overlay (bottom
// centre, fades out)"): NSGlassEffectView on macOS 26, an NSVisualEffectView material on 14/15.
// It shows what the Tk viewer's status line adds to the page (notes, errors); page and zoom live
// in the window's subtitle.

import AppKit

final class StatusPill: NSView {
    private let label = NSTextField(labelWithString: "")
    private var hideWork: DispatchWorkItem?
    /// Seconds a message stays before it fades.
    static let seconds: TimeInterval = 4
    /// The message shown now ("" when hidden; the self-test reads it).
    private(set) var message = ""
    /// Messages shown so far (the self-test reads them).
    private(set) var history: [String] = []
    /// Whether the glass material (macOS 26) is used.
    private(set) var glass = false

    override init(frame: NSRect) {
        super.init(frame: frame)
        translatesAutoresizingMaskIntoConstraints = false
        label.font = .systemFont(ofSize: NSFont.smallSystemFontSize + 1, weight: .medium)
        label.textColor = .labelColor
        label.lineBreakMode = .byTruncatingMiddle
        label.maximumNumberOfLines = 2
        label.alignment = .center
        label.translatesAutoresizingMaskIntoConstraints = false
        label.setContentCompressionResistancePriority(.defaultLow, for: .horizontal)

        let content = NSView()
        content.translatesAutoresizingMaskIntoConstraints = false
        content.addSubview(label)
        NSLayoutConstraint.activate([
            label.leadingAnchor.constraint(equalTo: content.leadingAnchor, constant: 14),
            label.trailingAnchor.constraint(equalTo: content.trailingAnchor, constant: -14),
            label.topAnchor.constraint(equalTo: content.topAnchor, constant: 7),
            label.bottomAnchor.constraint(equalTo: content.bottomAnchor, constant: -7),
        ])
        let background = Self.material(content)
        background.translatesAutoresizingMaskIntoConstraints = false
        addSubview(background)
        NSLayoutConstraint.activate([
            background.leadingAnchor.constraint(equalTo: leadingAnchor),
            background.trailingAnchor.constraint(equalTo: trailingAnchor),
            background.topAnchor.constraint(equalTo: topAnchor),
            background.bottomAnchor.constraint(equalTo: bottomAnchor),
        ])
        #if compiler(>=6.2)
        if #available(macOS 26, *) { glass = true }
        #endif
        alphaValue = 0
        isHidden = true
        setAccessibilityRole(.staticText)
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    /// The pill's background holding `content`: glass on macOS 26, else a HUD material.
    private static func material(_ content: NSView) -> NSView {
        #if compiler(>=6.2) // the macOS 26 SDK
        if #available(macOS 26, *) {
            let g = NSGlassEffectView()
            g.cornerRadius = 16
            g.contentView = content
            return g
        }
        #endif
        let v = NSVisualEffectView()
        v.material = .hudWindow
        v.blendingMode = .withinWindow
        v.state = .active
        v.wantsLayer = true
        v.layer?.cornerRadius = 16
        v.layer?.masksToBounds = true
        v.addSubview(content)
        NSLayoutConstraint.activate([
            content.leadingAnchor.constraint(equalTo: v.leadingAnchor),
            content.trailingAnchor.constraint(equalTo: v.trailingAnchor),
            content.topAnchor.constraint(equalTo: v.topAnchor),
            content.bottomAnchor.constraint(equalTo: v.bottomAnchor),
        ])
        return v
    }

    /// Shows `text` (several notes joined by "; ") for `StatusPill.seconds`, then fades out.
    func show(_ text: String) {
        guard !text.isEmpty else { return }
        message = text
        history.append(text)
        label.stringValue = text
        setAccessibilityLabel(text)
        hideWork?.cancel()
        isHidden = false
        NSAnimationContext.runAnimationGroup { ctx in
            ctx.duration = 0.15
            animator().alphaValue = 1
        }
        let work = DispatchWorkItem { [weak self] in self?.fadeOut() }
        hideWork = work
        DispatchQueue.main.asyncAfter(deadline: .now() + Self.seconds, execute: work)
    }

    /// Hides the pill (a fade; at once when `animated` is false).
    func fadeOut(animated: Bool = true) {
        hideWork?.cancel()
        hideWork = nil
        message = ""
        guard animated else {
            alphaValue = 0
            isHidden = true
            return
        }
        NSAnimationContext.runAnimationGroup({ ctx in
            ctx.duration = 0.4
            animator().alphaValue = 0
        }, completionHandler: { [weak self] in
            MainActor.assumeIsolated {
                if self?.message.isEmpty == true { self?.isHidden = true }
            }
        })
    }
}
