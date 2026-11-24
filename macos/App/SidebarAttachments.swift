// SidebarAttachments.swift — the attachments panel (task 11.3d2; the Tk viewer's 9.r10 panel).
// Plan.md §6 Phase 11 and §1 (embedded files are never executed); docs/viewer.md "Attachments
// panel". The list comes from the in-process parse (safepdf_doc_attachments: listing decodes
// nothing): name, the size known without decoding (Attach.sizeColumn) and a tooltip with the
// description, type, dates, page and problem (Attach.tooltip). Save attachment as… (double-click,
// Return, or the context menu) decodes the file first (safepdf_doc_attachment_bytes; an error is
// reported and no panel opens), then asks with an NSSavePanel starting in the opened file's folder
// with the sanitized name (Attachments.fileNameOf), refuses what Attach.targetProblem refuses (a
// folder, the opened PDF, a read-only file, a folder that is not writable) and writes exactly the
// decoded bytes atomically. There is no open, open-with or quick-look action: nothing launches,
// opens or interprets an attachment's bytes.

import AppKit
import SafePdfC

/// An attachment row copied from the C struct.
struct AttachmentRow {
    let name: String
    let fileName: String
    var sizeText: String
    let tooltip: String
    let problem: Int
    let problemText: String
    let hasSize: Bool
    let size: UInt64
    let hasStream: Bool
    let page: Int?

    init(_ a: safepdf_attachment) {
        name = Core.string(a.name)
        fileName = Core.string(a.file_name)
        sizeText = Core.string(a.size_text)
        tooltip = Core.string(a.tooltip)
        problem = Int(a.problem)
        problemText = Core.string(a.problem_text)
        hasSize = a.has_size != 0
        size = a.size
        hasStream = a.has_stream != 0
        page = a.has_page != 0 ? a.page : nil
    }

    /// The C struct for safepdf_attachment_size_after (only the size fields matter).
    var sizeFields: safepdf_attachment {
        var a = safepdf_attachment()
        a.has_size = hasSize ? 1 : 0
        a.size = size
        a.has_stream = hasStream ? 1 : 0
        return a
    }
}

final class AttachmentsPanel: NSView, NSTableViewDataSource, NSTableViewDelegate, NSMenuDelegate {
    let scroll = NSScrollView()
    let table = AttachmentTableView()
    private(set) var rows: [AttachmentRow] = []
    private(set) weak var document: Document?
    /// A status message (the pill).
    var onStatus: ((String) -> Void)?
    private static let nameColumn = NSUserInterfaceItemIdentifier("name")
    private static let sizeColumn = NSUserInterfaceItemIdentifier("size")

    override init(frame: NSRect) {
        super.init(frame: frame)
        let name = NSTableColumn(identifier: Self.nameColumn)
        name.title = "Name"
        name.resizingMask = .autoresizingMask
        let size = NSTableColumn(identifier: Self.sizeColumn)
        size.title = "Size"
        size.width = 64
        size.resizingMask = []
        table.addTableColumn(name)
        table.addTableColumn(size)
        table.headerView = nil
        table.style = .sourceList
        table.columnAutoresizingStyle = .firstColumnOnlyAutoresizingStyle
        table.dataSource = self
        table.delegate = self
        table.target = self
        table.doubleAction = #selector(doubleClicked(_:))
        table.onReturn = { [weak self] in self?.saveSelected() }
        let menu = NSMenu()
        menu.delegate = self
        table.menu = menu
        table.setAccessibilityLabel("Attachments")
        scroll.documentView = table
        scroll.hasVerticalScroller = true
        scroll.autohidesScrollers = true
        scroll.drawsBackground = false
        scroll.frame = bounds
        scroll.autoresizingMask = [.width, .height]
        addSubview(scroll)
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    /// Lists the attachments of `doc` (nil: none); `done(hasAttachments)` once they arrived.
    func load(_ doc: Document?, done: @escaping @MainActor (Bool) -> Void) {
        document = doc
        rows = []
        table.reloadData()
        guard let doc else { done(false); return }
        let ticket = AttachmentsTicket { [weak self, weak doc] rs in
            guard let self, let doc, self.document === doc else { return }
            self.rows = rs ?? []
            self.table.reloadData()
            done(!self.rows.isEmpty)
        }
        let ctx = Unmanaged.passRetained(ticket).toOpaque()
        if safepdf_doc_attachments(doc.handle, DispatchQueue.main, Self.listCallback, ctx) == 0 {
            Unmanaged<AttachmentsTicket>.fromOpaque(ctx).release()
            done(false)
        }
    }

    private static let listCallback: safepdf_attachments_fn = { context, _, status, _, list in
        var rows: [AttachmentRow]? = nil
        if status == SAFEPDF_STATUS_OK, let l = list, let items = l.pointee.items {
            rows = (0..<l.pointee.count).map { AttachmentRow(items[$0]) }
        }
        safepdf_free_attachments(list)
        guard let context else { return }
        let bits = UInt(bitPattern: context)
        let copied = rows
        MainActor.assumeIsolated {
            guard let ctx = UnsafeMutableRawPointer(bitPattern: bits) else { return }
            Unmanaged<AttachmentsTicket>.fromOpaque(ctx).takeRetainedValue().deliver(copied)
        }
    }

    // MARK: saving (Viewer.saveAttachment)

    /// Decodes attachment `i` (never opened or run); `done` gets the bytes or the status text.
    func decode(_ i: Int, done: @escaping @MainActor (Data?, String?) -> Void) {
        guard let doc = document, rows.indices.contains(i) else { done(nil, "no attachment"); return }
        let row = rows[i]
        if row.problem != 0 {
            done(nil, "cannot save attachment \(row.name): \(row.problemText)")
            return
        }
        let ticket = BytesTicket { [weak self] data, error in
            guard let self else { return }
            if self.rows.indices.contains(i) {
                let fields = self.rows[i].sizeFields
                let after = withUnsafePointer(to: fields) {
                    Core.take(safepdf_attachment_size_after($0, data != nil, UInt64(data?.count ?? 0)))
                }
                if let after { self.rows[i].sizeText = after }
                self.table.reloadData(forRowIndexes: IndexSet(integer: i), columnIndexes: IndexSet(integer: 1))
            }
            if let data { done(data, nil) } else { done(nil, "cannot save attachment \(row.name): \(error ?? "decoding failed")") }
        }
        let ctx = Unmanaged.passRetained(ticket).toOpaque()
        if safepdf_doc_attachment_bytes(doc.handle, i, DispatchQueue.main, Self.bytesCallback, ctx) == 0 {
            Unmanaged<BytesTicket>.fromOpaque(ctx).release()
            done(nil, "cannot save attachment \(row.name): the request was not accepted")
        }
    }

    private static let bytesCallback: safepdf_bytes_fn = { context, _, status, error, bytes in
        var data: Data? = nil
        if status == SAFEPDF_STATUS_OK, let b = bytes {
            data = b.pointee.len == 0 ? Data() : b.pointee.data.map { Data(bytes: $0, count: b.pointee.len) }
        }
        safepdf_free_bytes(bytes)
        let err = status == SAFEPDF_STATUS_CANCELLED ? "cancelled" : error.map { String(cString: $0) }
        guard let context else { return }
        let bits = UInt(bitPattern: context)
        let copied = data
        MainActor.assumeIsolated {
            guard let ctx = UnsafeMutableRawPointer(bitPattern: bits) else { return }
            Unmanaged<BytesTicket>.fromOpaque(ctx).takeRetainedValue().deliver(copied, err)
        }
    }

    /// Writes decoded `data` of attachment `i` to `url` (Attach.targetProblem's refusals; an
    /// atomic write of exactly the bytes). Returns the status text.
    func write(_ data: Data, of i: Int, to url: URL) -> String {
        guard let doc = document, rows.indices.contains(i) else { return "no attachment" }
        let name = url.lastPathComponent
        if let problem = SidebarRules.targetProblem(url, opened: doc.url) {
            return "cannot save attachment: \(problem)"
        }
        do {
            try data.write(to: url, options: .atomic)
            return "saved attachment \(rows[i].name) (\(data.count) bytes) to \(name)"
        } catch {
            return "cannot save attachment to \(name): \(error.localizedDescription)"
        }
    }

    /// Decodes attachment `i` and saves it to `url` without a panel (the self-test's path).
    func save(_ i: Int, to url: URL, done: @escaping @MainActor (String) -> Void) {
        decode(i) { [weak self] data, error in
            guard let self, let data else { done(error ?? "decoding failed"); return }
            done(self.write(data, of: i, to: url))
        }
    }

    /// Save attachment as…: decodes first, then asks where (a sheet on the window).
    func saveInteractive(_ i: Int) {
        decode(i) { [weak self] data, error in
            guard let self, let data, let doc = self.document, self.rows.indices.contains(i) else {
                if let error { self?.onStatus?(error) }
                return
            }
            let panel = NSSavePanel()
            panel.title = "Save attachment as"
            panel.nameFieldStringValue = self.rows[i].fileName
            panel.directoryURL = doc.url.deletingLastPathComponent()
            panel.canCreateDirectories = true
            let finish: @MainActor (NSApplication.ModalResponse) -> Void = { [weak self] response in
                guard let self, response == .OK, let url = panel.url else { return }
                self.onStatus?(self.write(data, of: i, to: url))
            }
            if let w = self.window {
                panel.beginSheetModal(for: w) { r in MainActor.assumeIsolated { finish(r) } }
            } else {
                finish(panel.runModal())
            }
        }
    }

    @objc private func doubleClicked(_ sender: Any?) {
        let r = table.clickedRow
        if rows.indices.contains(r) { saveInteractive(r) }
    }

    private func saveSelected() {
        let r = table.selectedRow
        if rows.indices.contains(r) { saveInteractive(r) }
    }

    @objc private func saveFromMenu(_ sender: NSMenuItem) {
        if rows.indices.contains(sender.tag) { saveInteractive(sender.tag) }
    }

    /// The context menu: only Save attachment as… (never an open action).
    func menuNeedsUpdate(_ menu: NSMenu) {
        menu.removeAllItems()
        let r = table.clickedRow
        guard rows.indices.contains(r) else { return }
        let item = NSMenuItem(title: "Save Attachment As…", action: #selector(saveFromMenu(_:)), keyEquivalent: "")
        item.target = self
        item.tag = r
        menu.addItem(item)
    }

    /// Selects row `i` (a click on its icon on the page; the window opens the panel).
    func select(_ i: Int) {
        guard rows.indices.contains(i) else { return }
        table.selectRowIndexes(IndexSet(integer: i), byExtendingSelection: false)
        table.scrollRowToVisible(i)
    }

    // MARK: data source and delegate

    func numberOfRows(in tableView: NSTableView) -> Int { rows.count }

    func tableView(_ tableView: NSTableView, viewFor tableColumn: NSTableColumn?, row: Int) -> NSView? {
        guard rows.indices.contains(row), let col = tableColumn else { return nil }
        let id = NSUserInterfaceItemIdentifier("org.safe-pdf.att.\(col.identifier.rawValue)")
        let cell = (tableView.makeView(withIdentifier: id, owner: nil) as? NSTableCellView) ?? {
            let c = NSTableCellView()
            c.identifier = id
            let t = NSTextField(labelWithString: "")
            t.translatesAutoresizingMaskIntoConstraints = false
            t.lineBreakMode = .byTruncatingMiddle
            c.addSubview(t)
            c.textField = t
            NSLayoutConstraint.activate([
                t.leadingAnchor.constraint(equalTo: c.leadingAnchor, constant: 2),
                t.trailingAnchor.constraint(equalTo: c.trailingAnchor, constant: -2),
                t.centerYAnchor.constraint(equalTo: c.centerYAnchor),
            ])
            return c
        }()
        let r = rows[row]
        if col.identifier == Self.sizeColumn {
            cell.textField?.stringValue = r.sizeText
            cell.textField?.alignment = .right
            cell.textField?.textColor = .secondaryLabelColor
        } else {
            cell.textField?.stringValue = r.name
            cell.textField?.textColor = r.problem != 0 ? .secondaryLabelColor : .labelColor
        }
        cell.toolTip = r.tooltip.isEmpty ? nil : r.tooltip
        return cell
    }
}

/// The attachments table: Return saves the selected row.
final class AttachmentTableView: NSTableView {
    var onReturn: (() -> Void)?

    override func keyDown(with event: NSEvent) {
        if let c = event.charactersIgnoringModifiers, c == "\r" || c == "\u{3}" {
            onReturn?()
            return
        }
        super.keyDown(with: event)
    }
}

/// Who gets the attachment list (retained across the C call, released once by the callback).
@MainActor final class AttachmentsTicket {
    let deliver: @MainActor ([AttachmentRow]?) -> Void

    init(deliver: @escaping @MainActor ([AttachmentRow]?) -> Void) { self.deliver = deliver }
}

/// Who gets an attachment's bytes.
@MainActor final class BytesTicket {
    let deliver: @MainActor (Data?, String?) -> Void

    init(deliver: @escaping @MainActor (Data?, String?) -> Void) { self.deliver = deliver }
}
