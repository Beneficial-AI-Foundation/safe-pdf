// SidebarViewController.swift — the sidebar item with its four panels, empty for now
// (task 11.3b). Plan.md §6 Phase 11; docs/macos-design.md §2 ("NSSplitViewController with a
// sidebar item — glass/vibrancy material automatic; a segmented control (SF Symbols) switches
// thumbnails / outline / attachments / layers"). The panels' contents are task 11.3d.

import AppKit

final class SidebarViewController: NSViewController {
    /// The four panels (Tk 9.r9), in order: title and SF Symbol.
    static let panels: [(title: String, symbol: String)] = [
        ("Thumbnails", "square.grid.2x2"),
        ("Outline", "list.bullet.indent"),
        ("Attachments", "paperclip"),
        ("Layers", "square.3.layers.3d"),
    ]

    private let switcher = NSSegmentedControl()
    private let placeholder = NSTextField(labelWithString: "")

    override func loadView() {
        let v = NSView(frame: NSRect(x: 0, y: 0, width: 220, height: 600))
        switcher.segmentCount = Self.panels.count
        switcher.trackingMode = .selectOne
        for (i, p) in Self.panels.enumerated() {
            switcher.setImage(NSImage(systemSymbolName: p.symbol, accessibilityDescription: p.title),
                              forSegment: i)
            switcher.setToolTip(p.title, forSegment: i)
            switcher.setWidth(36, forSegment: i)
        }
        switcher.selectedSegment = 0
        switcher.target = self
        switcher.action = #selector(panelChanged(_:))
        switcher.translatesAutoresizingMaskIntoConstraints = false

        placeholder.textColor = .tertiaryLabelColor
        placeholder.alignment = .center
        placeholder.translatesAutoresizingMaskIntoConstraints = false

        v.addSubview(switcher)
        v.addSubview(placeholder)
        NSLayoutConstraint.activate([
            switcher.topAnchor.constraint(equalTo: v.safeAreaLayoutGuide.topAnchor, constant: 8),
            switcher.centerXAnchor.constraint(equalTo: v.centerXAnchor),
            placeholder.centerXAnchor.constraint(equalTo: v.centerXAnchor),
            placeholder.centerYAnchor.constraint(equalTo: v.centerYAnchor),
            placeholder.leadingAnchor.constraint(greaterThanOrEqualTo: v.leadingAnchor, constant: 8),
        ])
        view = v
        showPanel(0)
    }

    @objc private func panelChanged(_ sender: NSSegmentedControl) {
        showPanel(sender.selectedSegment)
    }

    /// TODO(11.3d): NSCollectionView thumbnails, NSOutlineView outline, attachments, layers.
    private func showPanel(_ i: Int) {
        guard Self.panels.indices.contains(i) else { return }
        placeholder.stringValue = Self.panels[i].title
    }
}
