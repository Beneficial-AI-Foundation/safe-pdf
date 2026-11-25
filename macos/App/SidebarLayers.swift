// SidebarLayers.swift — the layers panel (task 11.3d2; the Tk viewer's 9.r11b panel). Plan.md §6
// Phase 11; docs/viewer.md "Layers panel". The rows come from the in-process parse
// (safepdf_doc_layers: Sidebar.layerRows — /Order as a tree, headings, "Additional Layers" in
// italics and collapsed, locked groups with a disabled checkbox) with the document's default
// state; a checkbox click is Sidebar.layerToggle through safepdf_layers_toggle (radio-button
// groups turn the others off, locked groups never change); every checkbox is then set from the
// new state and the document is shown again under it: the page view re-renders its pages, the
// thumbnails are rendered again (`onChanged`). The state is never written to the file.

import AppKit
import SafePdfC

/// A layers panel row copied from the C struct.
struct LayerRow {
    let depth: Int
    let label: String
    let group: safepdf_oc_key?
    let italic: Bool
    let locked: Bool
}

final class LayersPanel: NSView, NSOutlineViewDataSource, NSOutlineViewDelegate {
    let scroll = NSScrollView()
    let tree = NSOutlineView()
    private(set) var rows: [LayerRow] = []
    private var roots: [TreeNode] = []
    private(set) var nodes: [TreeNode] = []
    private(set) weak var document: Document?
    /// The state the checkboxes show (the document's default until a toggle).
    private(set) var state = LayersState()
    /// The layers state changed (the window re-renders the pages and thumbnails).
    var onChanged: (() -> Void)?
    var onStatus: ((String) -> Void)?
    /// Toggles applied (the self-test counts them).
    private(set) var toggles = 0
    static let column = NSUserInterfaceItemIdentifier("org.safe-pdf.layers")

    override init(frame: NSRect) {
        super.init(frame: frame)
        let col = NSTableColumn(identifier: Self.column)
        col.resizingMask = .autoresizingMask
        tree.addTableColumn(col)
        tree.outlineTableColumn = col
        tree.headerView = nil
        tree.style = .sourceList
        tree.usesAutomaticRowHeights = true
        tree.columnAutoresizingStyle = .uniformColumnAutoresizingStyle
        tree.indentationPerLevel = 14
        tree.dataSource = self
        tree.delegate = self
        tree.setAccessibilityLabel("Layers")
        scroll.documentView = tree
        scroll.hasVerticalScroller = true
        scroll.autohidesScrollers = true
        scroll.drawsBackground = false
        scroll.frame = bounds
        scroll.autoresizingMask = [.width, .height]
        addSubview(scroll)
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    /// Lists the layers of `doc` (nil: none); `done(hasLayers)` once they arrived. Every open
    /// starts with the document's default state (9.r8).
    func load(_ doc: Document?, done: @escaping @MainActor (Bool) -> Void) {
        document = doc
        setRows([], state: LayersState())
        guard let doc else { done(false); return }
        let ticket = LayersTicket { [weak self, weak doc] result in
            guard let self, let doc, self.document === doc else { return }
            // The reopen after a save keeps the layers' state (task 11.3e2, Tk 9.r11b): the
            // document then carries it already; else the default state.
            if let (rs, st) = result { self.setRows(rs, state: doc.layers ?? st) }
            done(!self.rows.isEmpty)
        }
        let ctx = Unmanaged.passRetained(ticket).toOpaque()
        if safepdf_doc_layers(doc.handle, DispatchQueue.main, Self.callback, ctx) == 0 {
            Unmanaged<LayersTicket>.fromOpaque(ctx).release()
            done(false)
        }
    }

    private static let callback: safepdf_layers_fn = { context, _, status, _, layers in
        var result: ([LayerRow], LayersState)? = nil
        if status == SAFEPDF_STATUS_OK, let l = layers {
            var rs: [LayerRow] = []
            if let r = l.pointee.rows {
                for i in 0..<l.pointee.count {
                    let x = r[i]
                    rs.append(LayerRow(depth: x.depth, label: Core.string(x.label),
                                       group: x.has_group != 0 ? x.group : nil, italic: x.italic != 0,
                                       locked: x.locked != 0))
                }
            }
            result = (rs, LayersState(l.pointee.initial))
        }
        safepdf_free_layers(layers)
        guard let context else { return }
        let bits = UInt(bitPattern: context)
        let copied = result
        MainActor.assumeIsolated {
            guard let ctx = UnsafeMutableRawPointer(bitPattern: bits) else { return }
            Unmanaged<LayersTicket>.fromOpaque(ctx).takeRetainedValue().deliver(copied)
        }
    }

    private func setRows(_ rs: [LayerRow], state st: LayersState) {
        rows = rs
        state = st
        // Every heading starts open except "Additional Layers" (Sidebar.layerEntries).
        let t = TreeNode.build(depths: rs.map(\.depth), open: rs.map { !$0.italic })
        roots = t.roots
        nodes = t.all
        tree.reloadData()
        expandInitial(roots)
    }

    private func expandInitial(_ ns: [TreeNode]) {
        for n in ns where n.hasKids {
            if n.open { tree.expandItem(n) }
            expandInitial(n.children)
        }
    }

    /// Whether row `i`'s checkbox is checked now (nil for a heading).
    func checked(_ i: Int) -> Bool? {
        guard rows.indices.contains(i), let g = rows[i].group else { return nil }
        return state.isOn(g)
    }

    /// Toggles row `i` (Sidebar.layerToggle through safepdf_layers_toggle): the document gets the
    /// new state and the view is shown again under it. Returns whether the state changed.
    @discardableResult
    func toggle(_ i: Int) -> Bool {
        guard let doc = document, rows.indices.contains(i), rows[i].group != nil else { return false }
        if rows[i].locked {
            onStatus?("layer \(rows[i].label) is locked")
            return false
        }
        var out = safepdf_layers_state()
        var err: UnsafeMutablePointer<CChar>? = nil
        let rc = state.withC { safepdf_layers_toggle(doc.handle, $0, i, &out, &err) }
        defer { safepdf_free_layers_state(&out) }
        if rc != 0 {
            onStatus?("cannot change the layer: \(Core.take(err) ?? "error")")
            return false
        }
        if let err { free(err) }
        let new = LayersState(out)
        let changed = !new.same(state)
        state = new
        doc.layers = new
        toggles += 1
        refreshChecks()
        if changed { onChanged?() }
        return changed
    }

    /// Sets every checkbox from the state (Viewer.applyLayers).
    private func refreshChecks() {
        for r in 0..<tree.numberOfRows {
            guard let n = tree.item(atRow: r) as? TreeNode,
                  let cell = tree.view(atColumn: 0, row: r, makeIfNecessary: false),
                  let box = cell.subviews.compactMap({ $0 as? NSButton }).first,
                  let on = checked(n.index) else { continue }
            box.state = on ? .on : .off
        }
    }

    @objc private func boxClicked(_ sender: NSButton) {
        toggle(sender.tag)
        // The checkbox shows the state, not its own click (a radio partner or a refusal).
        if let on = checked(sender.tag) { sender.state = on ? .on : .off }
    }

    // MARK: data source and delegate

    func outlineView(_ outlineView: NSOutlineView, numberOfChildrenOfItem item: Any?) -> Int {
        (item as? TreeNode)?.children.count ?? roots.count
    }

    func outlineView(_ outlineView: NSOutlineView, child index: Int, ofItem item: Any?) -> Any {
        (item as? TreeNode)?.children[index] ?? roots[index]
    }

    func outlineView(_ outlineView: NSOutlineView, isItemExpandable item: Any) -> Bool {
        (item as? TreeNode)?.hasKids ?? false
    }

    func outlineView(_ outlineView: NSOutlineView, shouldSelectItem item: Any) -> Bool { false }

    func outlineView(_ outlineView: NSOutlineView, viewFor tableColumn: NSTableColumn?, item: Any) -> NSView? {
        guard let n = item as? TreeNode, rows.indices.contains(n.index) else { return nil }
        let r = rows[n.index]
        let cell = NSTableCellView()
        let view: NSView
        if r.group != nil {
            let box = NSButton(checkboxWithTitle: r.label, target: self, action: #selector(boxClicked(_:)))
            box.tag = n.index
            box.state = checked(n.index) == true ? .on : .off
            box.isEnabled = !r.locked
            box.lineBreakMode = .byTruncatingTail
            box.toolTip = r.locked ? "\(r.label) (locked)" : r.label
            view = box
        } else {
            let t = NSTextField(labelWithString: r.label)
            let size = NSFont.systemFontSize
            if r.italic {
                t.font = NSFontManager.shared.convert(.systemFont(ofSize: size), toHaveTrait: .italicFontMask)
            } else {
                t.font = .boldSystemFont(ofSize: size)
            }
            t.lineBreakMode = .byTruncatingTail
            t.toolTip = r.label
            view = t
        }
        view.translatesAutoresizingMaskIntoConstraints = false
        cell.addSubview(view)
        NSLayoutConstraint.activate([
            view.leadingAnchor.constraint(equalTo: cell.leadingAnchor, constant: 2),
            view.trailingAnchor.constraint(lessThanOrEqualTo: cell.trailingAnchor, constant: -2),
            view.topAnchor.constraint(equalTo: cell.topAnchor, constant: 2),
            view.bottomAnchor.constraint(equalTo: cell.bottomAnchor, constant: -2),
        ])
        return cell
    }
}

/// Who gets the layers panel (retained across the C call, released once by the callback).
@MainActor final class LayersTicket {
    let deliver: @MainActor (([LayerRow], LayersState)?) -> Void

    init(deliver: @escaping @MainActor (([LayerRow], LayersState)?) -> Void) { self.deliver = deliver }
}
