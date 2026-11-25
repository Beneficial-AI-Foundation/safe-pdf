// MarksModel.swift — the marks store of one document over safepdf_marks.h (task 11.3e1).
// Plan.md §6 Phases 9–11; docs/macos-design.md §3 decision 1: the store, its undo/redo history,
// the note anchoring and closing rules, hit testing and the tool rules are the Tk viewer's own
// Lean code (SafePdf/Shell/App/Marks.lean, Bubble.lean, Toolbar.lean through FfiMarks); this
// file only moves values between Swift and the C API. Unverified shell code (Plan.md §8).
//
// The store is created from the bytes the document was opened from (safepdf_doc_bytes: the
// capped read's bytes, kept by the core), so the marks already saved in the file are listed as
// saved, exactly as the Tk viewer restores them on open.

import AppKit
import SafePdfC

/// One mark, copied out of a `safepdf_mark` (page space, points, y up).
struct Mark: Equatable {
    let id: UInt64
    let kind: Int32
    let page: Int
    let color: Int32
    let rgb: (r: UInt8, g: UInt8, b: UInt8)
    let state: Int32
    let isComment: Bool
    let text: String
    let size: UInt32
    let opacity: UInt32
    let point: CGPoint?
    let rect: safepdf_box?
    let quads: [safepdf_box]
    let strokes: [[CGPoint]]

    static func == (a: Mark, b: Mark) -> Bool {
        a.id == b.id && a.kind == b.kind && a.page == b.page && a.color == b.color && a.rgb == b.rgb
            && a.state == b.state && a.isComment == b.isComment && a.text == b.text && a.size == b.size
            && a.opacity == b.opacity && a.point == b.point && a.strokes == b.strokes
            && a.quads.count == b.quads.count
            && zip(a.quads, b.quads).allSatisfy { MarksModel.same($0, $1) }
    }

    var isHighlight: Bool { kind == Int32(SAFEPDF_MARK_HIGHLIGHT) }
    var isNote: Bool { kind == Int32(SAFEPDF_MARK_NOTE) }
    var isFreeText: Bool { kind == Int32(SAFEPDF_MARK_FREETEXT) }
    var isInk: Bool { kind == Int32(SAFEPDF_MARK_INK) }
    /// Free text or ink (the Add text / Draw editors' marks).
    var isEditor: Bool { isFreeText || isInk }
    var isSaved: Bool { state != Int32(SAFEPDF_MARK_NEW) }

    /// The colour to draw it in.
    var nsColor: NSColor {
        NSColor(srgbRed: CGFloat(rgb.r) / 255, green: CGFloat(rgb.g) / 255, blue: CGFloat(rgb.b) / 255, alpha: 1)
    }

    /// What the status line calls it (Viewer.markName).
    var name: String {
        switch kind {
        case Int32(SAFEPDF_MARK_NOTE): return "note"
        case Int32(SAFEPDF_MARK_HIGHLIGHT): return "\(MarksPalette.name(color)) highlight"
        case Int32(SAFEPDF_MARK_FREETEXT): return "text box"
        default: return "drawing"
        }
    }

    init(_ m: safepdf_mark) {
        id = m.id
        kind = m.kind
        page = m.page
        color = m.color
        rgb = (m.r, m.g, m.b)
        state = m.state
        isComment = m.is_comment != 0
        if let t = m.text {
            text = String(decoding: UnsafeRawBufferPointer(start: t, count: m.text_len), as: UTF8.self)
        } else {
            text = ""
        }
        size = m.size
        opacity = m.opacity
        point = m.has_point != 0 ? CGPoint(x: m.point.x, y: m.point.y) : nil
        rect = m.has_rect != 0 ? m.rect : nil
        var qs: [safepdf_box] = []
        if let q = m.quads { for i in 0..<m.quad_count { qs.append(q[i]) } }
        quads = qs
        var ss: [[CGPoint]] = []
        if let lens = m.stroke_lengths, let pts = m.points {
            var k = 0
            for i in 0..<m.stroke_count {
                var s: [CGPoint] = []
                for _ in 0..<lens[i] where k < m.point_count {
                    s.append(CGPoint(x: pts[k].x, y: pts[k].y))
                    k += 1
                }
                ss.append(s)
            }
        }
        strokes = ss
    }
}

/// The tools' constants (safepdf_marks_tool_params: the palettes, slider ranges and defaults,
/// the free-text metrics), read once.
@MainActor enum MarksPalette {
    static let params: safepdf_tool_params? = {
        var p = safepdf_tool_params()
        return safepdf_marks_tool_params(&p) == 0 ? p : nil
    }()

    /// The highlight colours' names (Marks.Color.label), SAFEPDF_COLOR_* order.
    nonisolated static let labels = ["Yellow", "Green", "Blue", "Pink", "Red"]

    nonisolated static func name(_ c: Int32) -> String {
        c >= 0 && Int(c) < labels.count ? labels[Int(c)].lowercased() : "?"
    }

    /// Palette colour `c` (SAFEPDF_COLOR_*).
    static func color(_ c: Int32) -> NSColor {
        guard let p = params, c >= 0, c < 5 else { return .systemYellow }
        let t = withUnsafeBytes(of: p.highlight_rgb) { Array($0) }
        let i = Int(c) * 3
        return NSColor(srgbRed: CGFloat(t[i]) / 255, green: CGFloat(t[i + 1]) / 255,
                       blue: CGFloat(t[i + 2]) / 255, alpha: 1)
    }

    /// The Add text / Draw palette as 0xRRGGBB words.
    static var editorColors: [UInt32] {
        guard let p = params else { return [0] }
        let t: [UInt8] = withUnsafeBytes(of: p.editor_rgb) { Array($0) }
        var out: [UInt32] = []
        for i in 0..<min(p.editor_count, 8) {
            let r = UInt32(t[3 * i]), g = UInt32(t[3 * i + 1]), b = UInt32(t[3 * i + 2])
            out.append((r << 16) | (g << 8) | b)
        }
        return out
    }

    static func nsColor(rgb: UInt32, alpha: CGFloat = 1) -> NSColor {
        NSColor(srgbRed: CGFloat((rgb >> 16) & 0xFF) / 255, green: CGFloat((rgb >> 8) & 0xFF) / 255,
                blue: CGFloat(rgb & 0xFF) / 255, alpha: alpha)
    }
}

/// The marks store of one open document (`safepdf_marks`), released with it.
@MainActor final class MarksModel {
    /// The C store (one reference owned by this object).
    nonisolated(unsafe) let handle: OpaquePointer
    /// Bumped on every change (the canvas's cached lists follow it).
    private(set) var version = 0
    private var cache: [Int: [Mark]] = [:]
    /// Called after every change (undo / redo included): the window's edited dot and menus.
    var onChange: (() -> Void)?
    /// The size of the bytes the store was created from (the changed-on-disk check reads at most
    /// one byte more, task 11.3e2).
    let originalSize: Int

    /// Why the store could not be created.
    struct CreateError: Error { let message: String }

    /// The store of `doc`, from the bytes it was opened from.
    init(document doc: Document) throws(CreateError) {
        guard let bytes = safepdf_doc_bytes(doc.handle) else {
            throw CreateError(message: "the document's bytes are not available")
        }
        defer { safepdf_free_bytes(bytes) }
        var err: UnsafeMutablePointer<CChar>? = nil
        guard let data = bytes.pointee.data,
              let m = safepdf_marks_create(data, bytes.pointee.len, &err) else {
            throw CreateError(message: Core.take(err) ?? "the marks could not be read")
        }
        handle = m
        originalSize = bytes.pointee.len
    }

    /// A store of PDF bytes (the self-test's reopen of a saved file).
    init(bytes: Data) throws(CreateError) {
        var err: UnsafeMutablePointer<CChar>? = nil
        let m: OpaquePointer? = bytes.withUnsafeBytes { raw in
            guard let p = raw.bindMemory(to: UInt8.self).baseAddress else { return nil }
            return safepdf_marks_create(p, raw.count, &err)
        }
        guard let m else { throw CreateError(message: Core.take(err) ?? "the marks could not be read") }
        handle = m
        originalSize = bytes.count
    }

    deinit { safepdf_marks_release(handle) }

    // MARK: queries

    /// The store's state.
    var state: safepdf_marks_state {
        var s = safepdf_marks_state()
        safepdf_marks_get_state(handle, &s)
        return s
    }

    /// The marks of `page`, oldest first (cached until the next change).
    func list(_ page: Int) -> [Mark] {
        if let c = cache[page] { return c }
        var l = safepdf_mark_list()
        var err: UnsafeMutablePointer<CChar>? = nil
        guard safepdf_marks_list(handle, page, &l, &err) == 0 else {
            if let err { free(err) }
            return []
        }
        defer { safepdf_free_mark_list(&l) }
        var out: [Mark] = []
        if let ms = l.marks { for i in 0..<l.count { out.append(Mark(ms[i])) } }
        cache[page] = out
        return out
    }

    /// Every mark of the document, oldest first.
    func listAll() -> [Mark] {
        var l = safepdf_mark_list()
        var err: UnsafeMutablePointer<CChar>? = nil
        guard safepdf_marks_list_all(handle, &l, &err) == 0 else {
            if let err { free(err) }
            return []
        }
        defer { safepdf_free_mark_list(&l) }
        var out: [Mark] = []
        if let ms = l.marks { for i in 0..<l.count { out.append(Mark(ms[i])) } }
        return out
    }

    /// Mark `id` on `page` (nil: none).
    func find(_ id: UInt64, page: Int? = nil) -> Mark? {
        if let page { return list(page).first { $0.id == id } }
        return listAll().first { $0.id == id }
    }

    /// The topmost mark of `page` under page point (x, y) (Store.hitAt; note icons first).
    func hit(page: Int, x: Double, y: Double) -> UInt64? {
        guard x.isFinite, y.isFinite else { return nil }
        let id = safepdf_marks_hit_at(handle, page, x, y)
        return id == 0 ? nil : id
    }

    /// Where a new note anchors (Marks.noteAnchor) for selection boxes `sel` and a click.
    static func noteAnchor(sel: [safepdf_box], click: CGPoint?) -> Int32 {
        var s = sel
        var c = safepdf_point(x: Double(click?.x ?? 0), y: Double(click?.y ?? 0))
        if click != nil {
            return safepdf_marks_note_anchor(&s, s.count, &c)
        }
        return safepdf_marks_note_anchor(&s, s.count, nil)
    }

    /// What closing note `id`'s popup without Save does (SAFEPDF_NOTE_*).
    func noteClose(_ id: UInt64, shown: String) -> Int32 {
        safepdf_marks_note_close(handle, id, shown)
    }

    // MARK: edits (each returns nil on success, else the error message)

    private func changed() {
        version += 1
        cache.removeAll()
        if grouping > 0 {
            changedInGroup = true
            return
        }
        onChange?()
    }

    private var grouping = 0
    private var changedInGroup = false

    /// Runs `body`'s edits as ONE undo step (safepdf_marks_begin_group / _end_group, task
    /// 11.6a: Paste); `onChange` runs once at the end.
    func group<T>(_ body: () -> T) -> T {
        if grouping == 0 { safepdf_marks_begin_group(handle) }
        grouping += 1
        let r = body()
        grouping -= 1
        guard grouping == 0 else { return r }
        safepdf_marks_end_group(handle)
        if changedInGroup {
            changedInGroup = false
            onChange?()
        }
        return r
    }

    /// Runs an edit call; on success the lists are dropped and `onChange` runs.
    @discardableResult
    private func edit(_ call: (UnsafeMutablePointer<UnsafeMutablePointer<CChar>?>) -> Int32) -> String? {
        var err: UnsafeMutablePointer<CChar>? = nil
        let rc = call(&err)
        if rc != 0 { return Core.take(err) ?? "the edit failed" }
        if let err { free(err) }
        changed()
        return nil
    }

    /// Adds a highlight; returns its id (nil and `error` on failure).
    func addHighlight(page: Int, color: Int32, quads: [safepdf_box]) -> Result<UInt64, EditError> {
        var q = quads
        var id: UInt64 = 0
        if let e = edit({ safepdf_marks_add_highlight(handle, page, color, &q, q.count, &id, $0) }) {
            return .failure(EditError(message: e))
        }
        return .success(id)
    }

    func addNote(page: Int, color: Int32, text: String, anchor: Int32, point: CGPoint?,
                 quads: [safepdf_box]) -> Result<UInt64, EditError> {
        var q = quads
        var p = safepdf_point(x: Double(point?.x ?? 0), y: Double(point?.y ?? 0))
        var id: UInt64 = 0
        if let e = edit({ safepdf_marks_add_note(handle, page, color, text, anchor, &p, &q, q.count, &id, $0) }) {
            return .failure(EditError(message: e))
        }
        return .success(id)
    }

    /// The comment of highlight `highlight` (its existing one, else a new note on its quads).
    func addComment(_ highlight: UInt64, text: String) -> Result<UInt64, EditError> {
        var id: UInt64 = 0
        if let e = edit({ safepdf_marks_add_comment(handle, highlight, text, &id, $0) }) {
            return .failure(EditError(message: e))
        }
        return .success(id)
    }

    func addFreeText(page: Int, text: String, at p: CGPoint, size: UInt32, rgb: UInt32) -> Result<UInt64, EditError> {
        var id: UInt64 = 0
        if let e = edit({ safepdf_marks_add_free_text(handle, page, text, Double(p.x), Double(p.y), size, rgb, &id, $0) }) {
            return .failure(EditError(message: e))
        }
        return .success(id)
    }

    func addInk(page: Int, points: [CGPoint], width: UInt32, opacity: UInt32, rgb: UInt32) -> Result<UInt64, EditError> {
        var pts = points.map { safepdf_point(x: Double($0.x), y: Double($0.y)) }
        var id: UInt64 = 0
        if let e = edit({ safepdf_marks_add_ink(handle, page, &pts, pts.count, width, opacity, rgb, &id, $0) }) {
            return .failure(EditError(message: e))
        }
        return .success(id)
    }

    @discardableResult
    func addStroke(_ id: UInt64, points: [CGPoint]) -> String? {
        var pts = points.map { safepdf_point(x: Double($0.x), y: Double($0.y)) }
        return edit { safepdf_marks_add_stroke(handle, id, &pts, pts.count, $0) }
    }

    @discardableResult
    func setText(_ id: UInt64, _ text: String) -> String? {
        edit { safepdf_marks_set_text(handle, id, text, $0) }
    }

    @discardableResult
    func recolor(_ id: UInt64, _ color: Int32) -> String? {
        edit { safepdf_marks_recolor(handle, id, color, $0) }
    }

    @discardableResult
    func setRgb(_ id: UInt64, _ rgb: UInt32, merge: Bool = false) -> String? {
        edit { safepdf_marks_set_rgb(handle, id, rgb, merge ? 1 : 0, $0) }
    }

    @discardableResult
    func setSize(_ id: UInt64, _ size: UInt32, merge: Bool) -> String? {
        edit { safepdf_marks_set_size(handle, id, size, merge ? 1 : 0, $0) }
    }

    @discardableResult
    func setOpacity(_ id: UInt64, _ opacity: UInt32, merge: Bool) -> String? {
        edit { safepdf_marks_set_opacity(handle, id, opacity, merge ? 1 : 0, $0) }
    }

    @discardableResult
    func translate(_ id: UInt64, dx: Double, dy: Double, merge: Bool = false) -> String? {
        guard dx.isFinite, dy.isFinite else { return "not a finite distance" }
        return edit { safepdf_marks_translate(handle, id, dx, dy, merge ? 1 : 0, $0) }
    }

    /// Ends the current slider drag's undo step.
    func seal() { safepdf_marks_seal(handle) }

    @discardableResult
    func delete(_ id: UInt64) -> String? {
        edit { safepdf_marks_delete(handle, id, $0) }
    }

    /// Imports XFDF `bytes` (safepdf_marks_xfdf_import; one undo step when marks were added).
    /// The report's status text (Xfdf.importStatus for `name`) and the number added, or the error.
    func importXfdf(_ bytes: Data, name: String) -> Result<(status: String, added: Int), EditError> {
        var r = safepdf_xfdf_import()
        var err: UnsafeMutablePointer<CChar>? = nil
        let rc: Int32 = bytes.withUnsafeBytes { raw in
            let p = raw.bindMemory(to: UInt8.self).baseAddress
            return safepdf_marks_xfdf_import(handle, p, raw.count, &r, &err)
        }
        if rc != 0 { return .failure(EditError(message: Core.take(err) ?? "the file was refused")) }
        if let err { free(err) }
        defer { safepdf_free_xfdf_import(&r) }
        let text = Core.take(safepdf_marks_import_status(name, &r)) ?? ""
        let added = r.added
        if added > 0 { changed() }
        return .success((text, added))
    }

    @discardableResult
    func undo() -> String? { edit { safepdf_marks_undo(handle, $0) } }

    @discardableResult
    func redo() -> String? { edit { safepdf_marks_redo(handle, $0) } }

    /// Two page-space boxes are the same (exactly).
    nonisolated static func same(_ a: safepdf_box, _ b: safepdf_box) -> Bool {
        a.llx == b.llx && a.lly == b.lly && a.urx == b.urx && a.ury == b.ury
    }
}

/// An edit the store refused.
struct EditError: Error { let message: String }
