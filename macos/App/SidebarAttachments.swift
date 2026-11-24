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
//
// Task 11.3f: a click on a file attachment annotation's icon on the page selects its row
// (`iconAt`, Attach.iconAt: the topmost icon, last in /Annots order; the sidebar opens the panel,
// Viewer.attSelect). When a row's tooltip is about to show and its size is not known without
// decoding (a filtered stream: the "?" column), the file is decoded once in the background
// (Viewer.attProbe) and the size column shows the decoded size (safepdf_attachment_size_after);
// the result is kept per row, one probe runs at a time, and the bytes are dropped at once.
// Deviation: the Tk probe lowers the per-stream cap to 16 MB (Attach.probeLimit);
// safepdf_doc_attachment_bytes has no cap parameter, so a probe here decodes under the viewer's
// own limits (as Save attachment as... does) and a file larger than 16 MB shows its decoded size
// instead of "> 16 MB". The tooltip text itself is the C API's (Attach.tooltip without a probe
// outcome).

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

/// A file attachment annotation's icon (safepdf_attachment_icon): page, rectangle, row.
struct AttachmentIcon {
    let page: Int
    let rect: safepdf_box
    let entry: Int
}

final class AttachmentsPanel: NSView, NSTableViewDataSource, NSTableViewDelegate, NSMenuDelegate,
    NSViewToolTipOwner {
    let scroll = NSScrollView()
    let table = AttachmentTableView()
    private(set) var rows: [AttachmentRow] = []
    /// The file attachment annotations' icons (task 11.3f).
    private(set) var icons: [AttachmentIcon] = []
    /// Rows whose decoding was tried (a probe or a save) and whether it worked (task 11.3f).
    private(set) var decoded: [Int: Bool] = [:]
    /// Decoding errors by row (the status text of a selected row).
    private var decodeErrors: [Int: String] = [:]
    /// The probe in flight: its row and request id.
    private(set) var probing: (row: Int, id: safepdf_request_id)?
    /// Probes started so far (the self-test counts them).
    private(set) var probes = 0
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
        if let p = probing, let old = document { safepdf_doc_cancel(old.handle, p.id) }
        probing = nil
        decoded = [:]
        decodeErrors = [:]
        document = doc
        rows = []
        icons = []
        table.reloadData()
        guard let doc else { done(false); return }
        let ticket = AttachmentsTicket { [weak self, weak doc] rs, ics in
            guard let self, let doc, self.document === doc else { return }
            self.rows = rs ?? []
            self.icons = ics.filter { self.rows.indices.contains($0.entry) }
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
        var icons: [AttachmentIcon] = []
        if status == SAFEPDF_STATUS_OK, let l = list, let items = l.pointee.items {
            rows = (0..<l.pointee.count).map { AttachmentRow(items[$0]) }
            if let ics = l.pointee.icons {
                icons = (0..<l.pointee.icon_count).map {
                    AttachmentIcon(page: ics[$0].page, rect: ics[$0].rect, entry: ics[$0].entry)
                }
            }
        }
        safepdf_free_attachments(list)
        guard let context else { return }
        let bits = UInt(bitPattern: context)
        let copied = rows
        let copiedIcons = icons
        MainActor.assumeIsolated {
            guard let ctx = UnsafeMutableRawPointer(bitPattern: bits) else { return }
            Unmanaged<AttachmentsTicket>.fromOpaque(ctx).takeRetainedValue().deliver(copied, copiedIcons)
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
        let ticket = BytesTicket { [weak self, weak doc] data, error in
            guard let self, let doc, self.document === doc else { return }
            self.record(i, data: data, error: error)
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

    /// Keeps what decoding row `i` gave (Viewer.attRecord): its size column after decoding
    /// (safepdf_attachment_size_after) and whether it worked. A cancelled request is not kept.
    private func record(_ i: Int, data: Data?, error: String?) {
        guard rows.indices.contains(i), data != nil || error != "cancelled" else { return }
        decoded[i] = data != nil
        if data == nil { decodeErrors[i] = error ?? "decoding failed" }
        let fields = rows[i].sizeFields
        let after = withUnsafePointer(to: fields) {
            Core.take(safepdf_attachment_size_after($0, data != nil, UInt64(data?.count ?? 0)))
        }
        if let after { rows[i].sizeText = after }
        table.reloadData(forRowIndexes: IndexSet(integer: i), columnIndexes: IndexSet(integer: 1))
    }

    // MARK: the tooltip's size probe (Viewer.attProbe, task 11.3f)

    /// Whether row `i`'s size is unknown until it is decoded: an embedded stream without a listed
    /// size, no problem, not decoded yet.
    func needsProbe(_ i: Int) -> Bool {
        guard rows.indices.contains(i) else { return false }
        let r = rows[i]
        return r.hasStream && !r.hasSize && r.problem == 0 && decoded[i] == nil
    }

    /// Row `i`'s tooltip is about to show: decodes it once in the background when its size is
    /// unknown (one probe at a time; the bytes are dropped, only the size is kept). Returns
    /// whether a probe started.
    @discardableResult
    func probe(_ i: Int) -> Bool {
        guard probing == nil, needsProbe(i), let doc = document else { return false }
        let ticket = BytesTicket { [weak self, weak doc] data, error in
            guard let self else { return }
            if self.probing?.row == i { self.probing = nil }
            guard let doc, self.document === doc else { return }
            self.record(i, data: data, error: error)
        }
        let ctx = Unmanaged.passRetained(ticket).toOpaque()
        let id = safepdf_doc_attachment_bytes(doc.handle, i, DispatchQueue.main, Self.bytesCallback, ctx)
        if id == 0 {
            Unmanaged<BytesTicket>.fromOpaque(ctx).release()
            return false
        }
        probing = (i, id)
        probes += 1
        return true
    }

    /// NSViewToolTipOwner: the tooltip of a row's cell, asked for when it is about to show; starts
    /// the size probe of that row.
    func view(_ view: NSView, stringForToolTip tag: NSView.ToolTipTag, point: NSPoint,
              userData data: UnsafeMutableRawPointer?) -> String {
        let r = table.row(for: view)
        guard rows.indices.contains(r) else { return "" }
        probe(r)
        return rows[r].tooltip
    }

    // MARK: icons on the page and the selected row's text (task 11.3f)

    /// The row of the topmost file attachment annotation icon on `page` containing page point
    /// (x, y) (Attach.iconAt: the last in /Annots order wins; bounds inclusive).
    func iconAt(page: Int, x: Double, y: Double) -> Int? {
        var hit: Int? = nil
        for ic in icons where ic.page == page &&
            ic.rect.llx <= x && x <= ic.rect.urx && ic.rect.lly <= y && y <= ic.rect.ury {
            hit = ic.entry
        }
        return hit
    }

    /// The status text of a selected row (Attach.selectedText): its name, size column, and its
    /// problem, decoding error or how to save it.
    func selectedText(_ i: Int) -> String {
        guard rows.indices.contains(i) else { return "" }
        let r = rows[i]
        let what: String
        if r.problem != 0 {
            what = r.problemText
        } else if decoded[i] == false {
            what = "cannot be decoded: \(decodeErrors[i] ?? "decoding failed")"
        } else {
            what = "double-click or right-click → Save attachment as… to save it"
        }
        return "attachment \(r.name) (\(r.sizeText)): \(what)"
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
        // The tooltip is asked for when it is about to show (it starts the size probe).
        cell.removeAllToolTips()
        cell.toolTip = nil
        if !r.tooltip.isEmpty || needsProbe(row) {
            cell.addToolTip(NSRect(x: 0, y: 0, width: 4096, height: 256), owner: self, userData: nil)
        }
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
    let deliver: @MainActor ([AttachmentRow]?, [AttachmentIcon]) -> Void

    init(deliver: @escaping @MainActor ([AttachmentRow]?, [AttachmentIcon]) -> Void) { self.deliver = deliver }
}

/// Who gets an attachment's bytes.
@MainActor final class BytesTicket {
    let deliver: @MainActor (Data?, String?) -> Void

    init(deliver: @escaping @MainActor (Data?, String?) -> Void) { self.deliver = deliver }
}
