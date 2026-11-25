// SidebarOutline.swift — the outline panel and the tree both tree panels use (task 11.3d2; the
// Tk viewer's outline panel, task 9.7). Plan.md §6 Phase 11; docs/macos-design.md §2
// ("NSOutlineView outline"); docs/viewer.md "Outline panel". The outline comes from the worker
// (safepdf_doc_outline, at the current-page priority); its rows become a tree by Sidebar.rows
// (each row's parent) and start expanded as Sidebar.initialOpen says (a positive /Count); long
// titles wrap; clicking a title activates its destination (the window's jump, recorded in the
// history) and marks the row. The Tk viewer has no current-section highlight; neither has this.

import AppKit
import SafePdfC

/// A row of a tree panel (the outline's entries, the layers' rows): its index in the flat
/// list, its children and whether it starts open.
final class TreeNode {
    let index: Int
    var children: [TreeNode] = []
    var open = false
    var hasKids = false

    init(index: Int) { self.index = index }

    /// Builds the tree of `n` rows from their depths and initial open flags through
    /// Sidebar.rows (SidebarRules.tree). Returns the roots and every node by index.
    @MainActor static func build(depths: [Int], open: [Bool]) -> (roots: [TreeNode], all: [TreeNode]) {
        let all = depths.indices.map { TreeNode(index: $0) }
        var roots: [TreeNode] = []
        guard let rows = SidebarRules.tree(depths: depths, open: open) else {
            return (all, all) // flat, as a fallback
        }
        for (i, r) in rows.enumerated() {
            all[i].open = r.open
            all[i].hasKids = r.has_kids
            if r.parent >= 0, Int(r.parent) < i {
                all[Int(r.parent)].children.append(all[i])
            } else {
                roots.append(all[i])
            }
        }
        return (roots, all)
    }
}

/// An outline row copied from the C struct.
struct OutlineRow {
    let title: String
    let depth: Int
    let open: Bool
    let action: NavAction
}

final class OutlinePanel: NSView, NSOutlineViewDataSource, NSOutlineViewDelegate {
    let scroll = NSScrollView()
    let tree = NSOutlineView()
    private(set) var rows: [OutlineRow] = []
    private var roots: [TreeNode] = []
    private(set) var nodes: [TreeNode] = []
    /// Activates an outline item's action (the window: jump, or what the item is).
    var onActivate: ((NavAction) -> Void)?
    private var request: (doc: Document, id: safepdf_request_id)?
    static let column = NSUserInterfaceItemIdentifier("org.safe-pdf.outline.title")

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
        tree.target = self
        tree.action = #selector(clicked(_:))
        tree.setAccessibilityLabel("Document outline")
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

    /// Requests the outline of `doc` (nil: none); `done(hasOutline)` runs once it arrived (or
    /// failed: no outline).
    func load(_ doc: Document?, done: @escaping @MainActor (Bool) -> Void) {
        if let r = request { safepdf_doc_cancel(r.doc.handle, r.id) }
        request = nil
        setRows([])
        guard let doc else { done(false); return }
        let ticket = OutlineTicket { [weak self, weak doc] rows in
            guard let self, let doc, self.request?.doc === doc else { return }
            self.request = nil
            self.setRows(rows ?? [])
            done(!(rows ?? []).isEmpty)
        }
        let ctx = Unmanaged.passRetained(ticket).toOpaque()
        let id = safepdf_doc_outline(doc.handle, Int32(SAFEPDF_PRIO_CURRENT), DispatchQueue.main,
                                     Self.callback, ctx)
        if id == 0 {
            Unmanaged<OutlineTicket>.fromOpaque(ctx).release()
            done(false)
        } else {
            request = (doc, id)
        }
    }

    /// The C callback: runs on the main queue.
    private static let callback: safepdf_outline_fn = { context, _, status, _, outline in
        var rows: [OutlineRow]? = nil
        if status == SAFEPDF_STATUS_OK, let o = outline, let items = o.pointee.items {
            var rs: [OutlineRow] = []
            for i in 0..<o.pointee.count {
                let it = items[i]
                rs.append(OutlineRow(title: Core.string(it.title), depth: it.depth, open: it.is_open != 0,
                                     action: NavAction(it.action)))
            }
            rows = rs
        }
        safepdf_free_outline(outline)
        guard let context else { return }
        let bits = UInt(bitPattern: context)
        let copied = rows
        MainActor.assumeIsolated {
            guard let ctx = UnsafeMutableRawPointer(bitPattern: bits) else { return }
            Unmanaged<OutlineTicket>.fromOpaque(ctx).takeRetainedValue().deliver(copied)
        }
    }

    /// Shows `rs` as the tree (Sidebar.rows; open as Sidebar.initialOpen).
    func setRows(_ rs: [OutlineRow]) {
        rows = rs
        let t = TreeNode.build(depths: rs.map(\.depth), open: rs.map(\.open))
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

    /// The rows shown now (indices into `rows`), in order.
    var visibleIndices: [Int] {
        (0..<tree.numberOfRows).compactMap { (tree.item(atRow: $0) as? TreeNode)?.index }
    }

    /// Activates row `i` of `rows` (a click on its title): marks it and runs its action.
    func activate(_ i: Int) {
        guard rows.indices.contains(i) else { return }
        let r = tree.row(forItem: nodes[i])
        if r >= 0 { tree.selectRowIndexes(IndexSet(integer: r), byExtendingSelection: false) }
        onActivate?(rows[i].action)
    }

    @objc private func clicked(_ sender: Any?) {
        let r = tree.clickedRow
        guard r >= 0, let n = tree.item(atRow: r) as? TreeNode else { return }
        activate(n.index)
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

    func outlineView(_ outlineView: NSOutlineView, viewFor tableColumn: NSTableColumn?, item: Any) -> NSView? {
        guard let n = item as? TreeNode, rows.indices.contains(n.index) else { return nil }
        let id = NSUserInterfaceItemIdentifier("org.safe-pdf.outline.cell")
        let cell = (outlineView.makeView(withIdentifier: id, owner: nil) as? NSTableCellView) ?? {
            let c = NSTableCellView()
            c.identifier = id
            let t = NSTextField(wrappingLabelWithString: "")
            t.translatesAutoresizingMaskIntoConstraints = false
            t.lineBreakMode = .byWordWrapping
            t.setContentCompressionResistancePriority(.defaultLow, for: .horizontal)
            c.addSubview(t)
            c.textField = t
            NSLayoutConstraint.activate([
                t.leadingAnchor.constraint(equalTo: c.leadingAnchor, constant: 2),
                t.trailingAnchor.constraint(equalTo: c.trailingAnchor, constant: -2),
                t.topAnchor.constraint(equalTo: c.topAnchor, constant: 3),
                t.bottomAnchor.constraint(equalTo: c.bottomAnchor, constant: -3),
            ])
            return c
        }()
        let row = rows[n.index]
        cell.textField?.stringValue = row.title
        cell.toolTip = row.title
        return cell
    }
}

/// Who gets the outline (retained across the C call, released once by the callback).
@MainActor final class OutlineTicket {
    let deliver: @MainActor ([OutlineRow]?) -> Void

    init(deliver: @escaping @MainActor ([OutlineRow]?) -> Void) { self.deliver = deliver }
}
