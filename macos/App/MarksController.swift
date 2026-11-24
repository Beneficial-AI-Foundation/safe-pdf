// MarksController.swift — marks on the page view: the tools (Select text, Highlight, Add
// comment, Add text, Draw), highlights and notes, free text and drawings, selecting, moving,
// recolouring and deleting marks, undo/redo, the selection bubble and Escape (task 11.3e1).
// Plan.md §6 Phases 9–11; docs/macos-design.md §1–§3. Behaviour of the Tk viewer
// (SafePdf/Shell/App/Viewer.lean: highlight, addNote, noteClose, deleteMark, selectMarkAt,
// press / dragTo / selectWord in the editor modes, inkBegin / inkEnd, moveDrag, commitFt,
// undoRedo, escape, drawMarks, drawBubble; docs/viewer.md 9.4, 9.5g, 9.8, 9.9, 10.6, 10.7,
// 10.17). Every rule is a call into the exported Lean code (safepdf_marks.h: the store, its
// history, noteAnchor, note_close, hit_at, the tool state steps, the bubble's kind, layout and
// place, Escape's order); Swift converts coordinates, keeps the transient UI state and draws.
//
// Saved marks are painted by the renderer. While saved marks are edited or deleted, the pages
// are rendered from the preview (task 11.3e2, MarksPreview: Save.preview, as the Tk viewer's
// `State.view`), so an edited or deleted saved mark shows as it will be saved; until that
// preview is there (it is built off the main thread), an edited saved mark is drawn from the
// store's list on top of the file's picture.

import AppKit
import SafePdfC

/// An open free-text box (Viewer's FtEdit): the mark it edits (nil: a new one), its page, the
/// box's upper-left corner (page space), font size and colour.
struct FreeTextEdit {
    let id: UInt64?
    let page: Int
    let pos: CGPoint
    var size: UInt32
    var rgb: UInt32
}

/// A cut mark on the app's mark clipboard (task 11.6a): the mark as listed and, for a
/// highlight, its comment note.
struct MarkClip {
    let mark: Mark
    let comment: Mark?
}

@MainActor final class MarksController: CanvasPointer {
    private weak var pages: PageViewController?
    /// The document's marks store (nil: no document, or its marks could not be read).
    private(set) var model: MarksModel?
    /// The tool state (Bubble.Ui), stepped by safepdf_marks_ui_step.
    private(set) var ui = safepdf_tool_ui()
    /// The active tool (Toolbar.Mode.of): SAFEPDF_MODE_*.
    private(set) var mode = UInt32(SAFEPDF_MODE_SELECT.rawValue)
    /// The current highlight colour (SAFEPDF_COLOR_*).
    private(set) var hlColor = Int32(SAFEPDF_COLOR_YELLOW)
    /// The selected mark.
    private(set) var markSel: UInt64?
    /// The stroke being drawn: its page and points (page space).
    private(set) var inkStroke: (page: Int, points: [CGPoint])?
    /// The drawing of this session (strokes join it until Escape or the end of the mode).
    private(set) var inkSession: UInt64?
    /// A free text or drawing being moved: its id, page, where the drag started and is now.
    private var moveFrom: (id: UInt64, page: Int, p0: CGPoint, last: CGPoint)?
    /// The open free-text box.
    private(set) var ftEdit: FreeTextEdit?
    /// The note whose editor is open.
    private(set) var noteOpen: UInt64?
    /// Where the current press goes.
    private enum Route { case none, text, ink, move, consumed }
    private var route = Route.none
    private var press: (page: Int, x: Double, y: Double, view: CGPoint, moved: Bool)?
    /// Whether a slider drag of a pop-over is going on (its steps are one undo step).
    private var sliding = false

    let bubble = BubbleView()
    let picker = BubbleView()
    let noteEditor = NoteEditor()
    let freeText = FreeTextBox()
    let popovers = ToolPopovers()
    /// The preview of edited saved marks (task 11.3e2).
    let preview = MarksPreview()

    /// Called after a change of the marks, the selected mark or the tool state (the window's
    /// edited dot, menus and toolbar).
    var onChange: (() -> Void)?
    /// The toolbar item a tool's pop-over anchors to (nil: none, e.g. the self-test).
    var toolbarItem: ((Int32) -> NSToolbarItem?)?

    var text: TextController? { pages?.text }
    var canvas: PageCanvasView? { pages?.canvas }

    init() {
        var u = safepdf_tool_ui()
        mode = UInt32(max(0, safepdf_marks_ui_step(nil, Int32(SAFEPDF_UI_INIT), 0, &u, nil)))
        ui = u
    }

    /// Connects to the page view: the canvas's pointer, the overlays, the cursor's mark test.
    func attach(_ pv: PageViewController) {
        pages = pv
        pv.canvas.pointer = self
        pv.text.drawMarks = { [weak self] page, t, c in self?.draw(page, t, c) }
        pv.text.markAt = { [weak self] page, x, y in self?.hitVisible(page: page, x: x, y: y) != nil }
        pv.text.onSelectionFinished = { [weak self] in self?.selectionFinished() }
        let prevSel = pv.text.onSelectionChange
        pv.text.onSelectionChange = { [weak self] in
            prevSel?()
            self?.placeBubble()
        }
        pv.canvas.onLayout = { [weak self] in self?.layoutChanged() }
        pv.canvas.contextMenu = { [weak self] v in self?.contextMenu(at: v) }
        for v in [bubble, picker] as [NSView] {
            v.isHidden = true
            pv.canvas.addSubview(v)
        }
        freeText.isHidden = true
        pv.canvas.addSubview(freeText)
        freeText.onCommit = { [weak self] in _ = self?.commitFreeText() }
        bubble.onButton = { [weak self] b, arg in self?.bubbleButton(b, arg) }
        picker.onButton = { [weak self] b, arg in self?.bubbleButton(b, arg) }
        noteEditor.onSave = { [weak self] text in self?.noteSave(text) }
        noteEditor.onClose = { [weak self] shown in self?.noteCloseWithoutSave(shown) }
        noteEditor.onDelete = { [weak self] in
            guard let self, let id = self.noteOpen else { return }
            self.noteEditor.close()
            self.noteOpen = nil
            self.deleteMark(id)
        }
        preview.onSource = { [weak pv] s in pv?.canvas.setRenderSource(s) }
        preview.onStatus = { [weak self] s in self?.status(s) }
        popovers.onColor = { [weak self] c in self?.popoverColor(c) }
        popovers.onShowAll = { [weak self] in self?.toggleShowAll() }
        popovers.onEditorColor = { [weak self] rgb in self?.editorColor(rgb) }
        popovers.onSlider = { [weak self] row, v, ended in self?.slide(row: row, value: v, ended: ended) }
        popovers.onClosed = { [weak self] editor in
            guard let self else { return }
            if editor { self.ui.ed_pop = 0 } else { self.ui.popover = 0 }
            self.onChange?()
        }
    }

    /// A new document (nil: none): its store, no selected mark, the tools as they were (the Tk
    /// viewer keeps the tool state across opens).
    func reset(_ doc: Document?) {
        noteEditor.close()
        noteOpen = nil
        freeText.close()
        ftEdit = nil
        markSel = nil
        inkStroke = nil
        inkSession = nil
        moveFrom = nil
        press = nil
        route = .none
        model = nil
        preview.reset()
        if let doc {
            do {
                let m = try MarksModel(document: doc)
                m.onChange = { [weak self] in self?.marksChanged() }
                model = m
            } catch {
                status("marks: \(error.message)")
            }
        }
        placeBubble()
        onChange?()
    }

    private func status(_ s: String) { pages?.pill.show(s) }

    private func redrawAll() { canvas?.needsDisplay = true }

    /// The store changed (an edit, undo or redo): redraw, place the bubble, update the chrome.
    private func marksChanged() {
        if let id = markSel, model?.find(id) == nil { markSel = nil }
        if let m = model { preview.update(m) }
        redrawAll()
        placeBubble()
        onChange?()
    }

    private func layoutChanged() {
        placeBubble()
        placeFreeText()
        if let id = noteOpen { openNoteEditor(id) }
    }

    // MARK: geometry

    /// The page and page point under view point `v` (View.pageAt).
    private func pagePoint(_ v: CGPoint) -> (page: Int, p: CGPoint)? {
        guard let (page, x, y) = text?.pagePoint(at: v) else { return nil }
        return (page, CGPoint(x: x, y: y))
    }

    /// The point of page `page` at view point `v` (also outside its image).
    private func pagePoint(on page: Int, _ v: CGPoint) -> CGPoint? {
        guard let t = canvas?.transform(ofPage: page), let q = t.page(v) else { return nil }
        return CGPoint(x: q.x, y: q.y)
    }

    /// View points per page unit on a page.
    static func scale(_ t: PageTransform) -> CGFloat { CGFloat(hypot(t.ax, t.ay)) }

    /// Backing pixels per page unit of `page` (the Tk viewer's zoom).
    private func pixelsPerUnit(_ page: Int) -> CGFloat {
        guard let c = canvas, let t = c.transform(ofPage: page) else { return 1 }
        return Self.scale(t) * c.laidOutBacking
    }

    /// A page-space box (llx lly urx ury) of an origin and a size.
    static func box(_ r: safepdf_box) -> safepdf_box { r }

    // MARK: queries

    /// The marks of `page` that are shown (all, or only notes and editors while Show all is
    /// off; Viewer.visibleMarks).
    func visible(_ page: Int) -> [Mark] {
        guard let m = model else { return [] }
        let ms = m.list(page)
        return ui.show_all != 0 ? ms : ms.filter { !$0.isHighlight }
    }

    /// The topmost shown mark under a page point.
    func hitVisible(page: Int, x: Double, y: Double) -> UInt64? {
        guard let m = model, let id = m.hit(page: page, x: x, y: y) else { return nil }
        if ui.show_all == 0, m.find(id, page: page)?.isHighlight == true { return nil }
        return id
    }

    /// The free text or drawing under a page point (Viewer.editorAt).
    private func editorAt(page: Int, _ p: CGPoint) -> Mark? {
        guard let id = hitVisible(page: page, x: Double(p.x), y: Double(p.y)),
              let m = model?.find(id, page: page), m.isEditor else { return nil }
        return m
    }

    /// The selected mark.
    var selectedMark: Mark? { markSel.flatMap { model?.find($0) } }

    /// Whether there are unsaved changes (the window's edited dot).
    var dirty: Bool { (model?.state.dirty ?? 0) != 0 }

    // MARK: tool state

    /// Applies a tool-state step (safepdf_marks_ui_step); returns whether the Highlight button
    /// highlights the selection instead.
    @discardableResult
    private func step(_ op: Int32, _ arg: Int32 = 0) -> Bool {
        var u = ui
        var hl: Int32 = 0
        let m = safepdf_marks_ui_step(&ui, op, arg, &u, &hl)
        guard m >= 0 else { return false }
        if hl != 0 { return true }
        ui = u
        mode = UInt32(m)
        text?.mode = mode
        syncPopovers()
        text?.updateCursor(at: nil)
        onChange?()
        return false
    }

    /// The pop-overs follow the tool state (shown only in a window).
    private func syncPopovers() {
        let window = canvas?.window
        if ui.popover != 0, model != nil, window != nil, let item = toolbarItem?(Int32(SAFEPDF_TOOL_HIGHLIGHT.rawValue)) {
            popovers.showHighlight(at: item, color: hlColor, showAll: ui.show_all != 0)
        } else {
            popovers.closeHighlight()
        }
        if ui.ed_pop != 0, ui.editor != Int32(SAFEPDF_EDITOR_NONE), model != nil, window != nil,
           let item = toolbarItem?(ui.editor == Int32(SAFEPDF_EDITOR_DRAW) ? Int32(SAFEPDF_TOOL_DRAW.rawValue)
                                                                          : Int32(SAFEPDF_TOOL_TEXT.rawValue)) {
            popovers.showEditor(at: item, draw: ui.editor == Int32(SAFEPDF_EDITOR_DRAW), ui: ui)
        } else {
            popovers.closeEditor()
        }
    }

    /// The toolbar's tool buttons (Toolbar.Tool): Select text, Highlight, Add comment, Add text,
    /// Draw (Viewer.tool); Add image and Print are not available.
    func tool(_ t: Int32) {
        guard model != nil else { return }
        switch t {
        case Int32(SAFEPDF_TOOL_SELECT.rawValue):
            _ = commitFreeText()
            inkSession = nil
            step(Int32(SAFEPDF_UI_SELECT_TOOL))
            status("Select text: drag over the text to select it; click a link to follow it, a mark to select it")
        case Int32(SAFEPDF_TOOL_HIGHLIGHT.rawValue):
            if step(Int32(SAFEPDF_UI_TOOL_CLICK), text?.selection != nil ? 1 : 0) {
                highlight(nil)
            } else {
                toolStatus()
            }
        case Int32(SAFEPDF_TOOL_COMMENT.rawValue):
            addNote(at: nil)
        case Int32(SAFEPDF_TOOL_TEXT.rawValue), Int32(SAFEPDF_TOOL_DRAW.rawValue):
            _ = commitFreeText()
            inkSession = nil
            let e = t == Int32(SAFEPDF_TOOL_DRAW.rawValue) ? SAFEPDF_EDITOR_DRAW : SAFEPDF_EDITOR_TEXT
            step(Int32(SAFEPDF_UI_SELECT_EDITOR), Int32(e))
            editorStatus()
        default:
            status("not available yet")
        }
    }

    /// Edit → Highlight tool (Ui.toggleTool).
    func toggleHighlightTool() {
        guard model != nil else { return }
        step(Int32(SAFEPDF_UI_TOGGLE_TOOL))
        toolStatus()
    }

    private func toolStatus() {
        if ui.tool != 0 {
            status("Highlight tool on: choose the highlight colour, then select text (it is highlighted at once)")
        } else {
            status("Highlight tool off")
        }
    }

    private func editorStatus() {
        switch ui.editor {
        case Int32(SAFEPDF_EDITOR_TEXT):
            status("Add text: click on the page to place a text box (font colour and size in the pop-over)")
        case Int32(SAFEPDF_EDITOR_DRAW):
            status("Draw: drag on the page to draw (the strokes until Escape or the end of the mode form one drawing)")
        default:
            status("Add text / Draw off")
        }
    }

    /// Show all highlights (Viewer.toggleShowAll): a hidden highlight cannot stay selected.
    func toggleShowAll() {
        ui.show_all = ui.show_all != 0 ? 0 : 1
        if ui.show_all == 0, selectedMark?.isHighlight == true { markSel = nil }
        redrawAll()
        placeBubble()
        syncPopovers()
        onChange?()
        status(ui.show_all != 0 ? "highlights shown" : "highlights hidden (Show all is off)")
    }

    /// The pressed toolbar tool (Toolbar.Mode.tool).
    var pressedTool: UInt32 { safepdf_view_mode_tool(mode) }

    // MARK: highlights and notes

    /// Sets the current highlight colour.
    func setColor(_ c: Int32) {
        hlColor = c
        if ui.popover != 0 { syncPopovers() }
    }

    /// Highlight [COLOR] (Viewer.highlight): with a selection, highlights its line runs' boxes
    /// (Select.rangeBoxes) in COLOR or the current colour and selects the new mark; else with a
    /// selected mark and a colour, recolours it; else only makes COLOR the current colour.
    func highlight(_ color: Int32?) {
        guard let m = model, let t = text else { return }
        let c = color ?? hlColor
        setColor(c)
        if let s = t.selection {
            let quads = t.selectionBoxes()
            guard !quads.isEmpty else { status("nothing to highlight"); return }
            switch m.addHighlight(page: s.page, color: c, quads: quads) {
            case .success(let id):
                markSel = id
                t.setSelection(nil)
                status("page \(s.page + 1): highlighted in \(MarksPalette.name(c)) (click it to select it; Delete removes it)")
            case .failure(let e):
                status("highlight: \(e.message)")
            }
            placeBubble()
            onChange?()
            return
        }
        if let id = markSel, let color, let mk = model?.find(id) {
            if mk.isEditor {
                status("highlight colour: \(MarksPalette.name(color)) (a text box or drawing takes its colour from its own pop-over)")
            } else if let e = m.recolor(id, color) {
                status("recolour: \(e)")
            } else {
                status("mark recoloured: \(MarksPalette.name(color))")
            }
        } else if let color {
            status("highlight colour: \(MarksPalette.name(color)) (select text, then Highlight)")
        } else {
            status("select text first (drag over it or double-click a word), then Highlight")
        }
    }

    /// A drag, double or triple click finished selecting text: with the Highlight tool on it is
    /// highlighted at once (Ui.highlightOnRelease); the bubble shows.
    private func selectionFinished() {
        if ui.tool != 0, text?.selection != nil { highlight(nil) }
        placeBubble()
    }

    /// Add note… (Viewer.addNote). `v` nil: from the menu, the toolbar or the bubble — a note on
    /// the selection, else the selected highlight's comment, else a note at the window centre;
    /// with a view point (the context menu, 10.17) a note there, unless the point is inside the
    /// selection's highlight boxes (Marks.noteAnchor), which comments on the selection.
    func addNote(at v: CGPoint?) {
        guard let m = model, let t = text, let c = canvas else { return }
        var anchor = Int32(SAFEPDF_ANCHOR_NONE)
        var page = c.currentPage
        var point: CGPoint? = nil
        var quads: [safepdf_box] = []
        let selQs = t.selectionBoxes()
        let selPage = t.selection?.page ?? c.currentPage
        if let v, let (pg, p) = pagePoint(v) {
            let qs = pg == selPage ? selQs : []
            anchor = MarksModel.noteAnchor(sel: qs, click: p)
            if anchor == Int32(SAFEPDF_ANCHOR_QUADS) {
                page = selPage
                quads = qs
            } else {
                page = pg
                point = p
            }
        } else if v == nil {
            anchor = MarksModel.noteAnchor(sel: selQs, click: nil)
            page = selPage
            quads = selQs
        }
        var color = Int32(SAFEPDF_COLOR_YELLOW)
        if anchor == Int32(SAFEPDF_ANCHOR_NONE), v == nil, let mk = selectedMark, c.isLaidOut(mk.page),
           !mk.isNote, !mk.quads.isEmpty {
            // The edit bubble's Comment: the highlight's note, or a new one on its quads.
            let before = m.state.mark_count
            switch m.addComment(mk.id, text: "") {
            case .success(let id):
                if m.state.mark_count == before {
                    status("page \(mk.page + 1): comment of the \(MarksPalette.name(mk.color)) highlight")
                } else {
                    markSel = id
                    status("page \(mk.page + 1): comment added (type its text, then Save)")
                }
                t.setSelection(nil)
                openNote(id)
            case .failure(let e):
                status("comment: \(e.message)")
            }
            return
        }
        _ = color
        if anchor == Int32(SAFEPDF_ANCHOR_NONE) {
            let ctr = pages?.centreAnchor().doc ?? CGPoint(x: c.visibleRect.midX, y: c.visibleRect.midY)
            if let (pg, p) = pagePoint(ctr) {
                anchor = Int32(SAFEPDF_ANCHOR_POINT)
                page = pg
                point = p
            }
        }
        guard anchor != Int32(SAFEPDF_ANCHOR_NONE) else { return }
        color = Int32(SAFEPDF_COLOR_YELLOW)
        switch m.addNote(page: page, color: color, text: "", anchor: anchor, point: point, quads: quads) {
        case .success(let id):
            markSel = id
            t.setSelection(nil)
            status("page \(page + 1): note added (type its text, then Save)")
            openNote(id)
        case .failure(let e):
            status("note: \(e.message)")
        }
    }

    /// Opens the editor of note `id` next to its icon (headless: the state only).
    func openNote(_ id: UInt64) {
        guard let mk = model?.find(id), mk.isNote else { return }
        noteOpen = id
        noteEditor.text = mk.text
        openNoteEditor(id)
        onChange?()
    }

    private func openNoteEditor(_ id: UInt64) {
        guard let mk = model?.find(id), let c = canvas, c.window != nil, let r = mk.rect,
              let t = c.transform(ofPage: mk.page) else { return }
        noteEditor.show(relativeTo: t.rect(r), of: c, title: mk.isComment ? "Comment" : "Note")
    }

    /// The note editor's Save (⌘Return): the typed text into the note (unchanged: nothing).
    func noteSave(_ text: String) {
        guard let id = noteOpen, let m = model else { return }
        noteEditor.close()
        noteOpen = nil
        guard let mk = m.find(id) else { return }
        if mk.text == text {
            status("note unchanged")
        } else if let e = m.setText(id, text) {
            status("note: \(e)")
        } else {
            status("note saved (\(text.count) characters)")
        }
        onChange?()
    }

    /// The note editor closed without Save (Escape, ⌘., a click away; Viewer.noteClose):
    /// Store.onUnsavedClose keeps the stored text, saves a new note's typed text, or deletes an
    /// empty note (a highlight's comment goes, the highlight stays).
    func noteCloseWithoutSave(_ shown: String) {
        guard let id = noteOpen, let m = model else { return }
        noteEditor.close()
        noteOpen = nil
        switch m.noteClose(id, shown: shown) {
        case Int32(SAFEPDF_NOTE_SAVE):
            _ = m.setText(id, shown)
            status("note saved (\(shown.count) characters)")
        case Int32(SAFEPDF_NOTE_DELETE):
            deleteMark(id)
            status("empty note removed")
        default:
            if m.find(id) != nil { status("note edits discarded") }
        }
        onChange?()
    }

    /// Removes mark `id` (a highlight's comment goes with it; Viewer.deleteMark).
    func deleteMark(_ id: UInt64) {
        guard let m = model, let mk = m.find(id) else { return }
        if markSel == id { markSel = nil }
        if inkSession == id { inkSession = nil }
        if let e = m.delete(id) {
            status("delete: \(e)")
            return
        }
        if let n = noteOpen, m.find(n) == nil {
            noteEditor.close()
            noteOpen = nil
        }
        status("\(mk.name) deleted")
    }

    /// Delete / Edit → Delete mark: the selected mark.
    func deleteSelected() {
        if let id = markSel { deleteMark(id) } else if model != nil {
            status("no mark selected (click a highlight or note)")
        }
    }

    /// Selects the mark under a page point (a note also opens its editor when `openIt`).
    @discardableResult
    func selectMark(page: Int, at p: CGPoint, openIt: Bool) -> Bool {
        guard let id = hitVisible(page: page, x: Double(p.x), y: Double(p.y)), let mk = model?.find(id, page: page)
        else { return false }
        markSel = id
        ui.picker = 0
        redrawAll()
        placeBubble()
        status("\(mk.name) selected (Delete removes it; a colour in the Highlight menu recolours it)")
        if openIt && mk.isNote { openNote(id) }
        onChange?()
        return true
    }

    // MARK: cut and paste (task 11.6a)

    /// The app's mark clipboard: the mark last cut (⌘X) and, for a highlight, its comment. ⌘V
    /// pastes it as a new mark, as often as wanted; it outlives the document it came from.
    static var clipboard: MarkClip?

    /// Whether Cut can cut a mark now (a mark is selected).
    var canCut: Bool { model != nil && selectedMark != nil }

    /// Whether Paste can paste a mark now (one was cut, a document is open).
    var canPaste: Bool { model != nil && Self.clipboard != nil && (canvas?.document?.pageCount ?? 0) > 0 }

    /// The comment of highlight `h` as listed (Store.noteOn: the newest note of its page anchored
    /// to exactly its quads, which the store lists with `is_comment`).
    private func comment(of h: Mark) -> Mark? {
        guard h.isHighlight, let m = model else { return nil }
        return m.list(h.page).last {
            $0.isNote && $0.isComment && $0.quads.count == h.quads.count
                && zip($0.quads, h.quads).allSatisfy { MarksModel.same($0.0, $0.1) }
        }
    }

    /// Cut (⌘X) of the selected mark (highlight, note, free text, drawing): it is deleted in one
    /// undo step (a highlight's comment with it, Viewer.deleteMark) and kept on the mark
    /// clipboard; its text — a note's or free text's, or the highlighted text — goes on the
    /// pasteboard as plain text.
    func cutSelected() {
        _ = commitFreeText()
        guard let m = model, let mk = selectedMark else {
            if model != nil { status("no mark selected (click a highlight, note, text box or drawing)") }
            return
        }
        let cm = comment(of: mk)
        let text = mk.isHighlight ? (self.text?.text(under: mk.quads, page: mk.page) ?? "") : mk.text
        deleteMark(mk.id)
        guard m.find(mk.id) == nil else { return }
        Self.clipboard = MarkClip(mark: mk, comment: cm)
        if !text.isEmpty, let pb = self.text?.pasteboard {
            pb.clearContents()
            pb.setString(text, forType: .string)
        }
        status("\(mk.name) cut\(cm != nil ? " with its comment" : "") (⌘V pastes it on the current page)")
        onChange?()
    }

    /// Paste (⌘V) of the cut mark as a new mark on the current page, in one undo step: at the
    /// same place on its own page, else at the same page coordinates moved inside the page's
    /// CropBox (`pasteOffset`). It becomes the selected mark.
    func paste() {
        guard let m = model, let c = canvas, let doc = c.document, doc.pageCount > 0,
              let clip = Self.clipboard else { return }
        _ = commitFreeText()
        let page = min(max(0, c.currentPage), doc.pageCount - 1)
        let d = page == clip.mark.page ? CGVector(dx: 0, dy: 0)
            : Self.pasteOffset(clip.mark, into: doc.geometry.indices.contains(page) ? doc.geometry[page].box : nil)
        let before = m.version
        let r = m.group { Self.recreate(clip, page: page, dx: Double(d.dx), dy: Double(d.dy), in: m) }
        switch r {
        case .success(let id):
            markSel = id
            inkSession = nil
            ui.picker = 0
            status("\(clip.mark.name) pasted on page \(page + 1)")
        case .failure(let e):
            // A part made before the failure goes with one undo (the group is one step).
            if m.version != before { _ = m.undo() }
            status("paste: \(e.message)")
        }
        redrawAll()
        placeBubble()
        onChange?()
    }

    /// The page-space box a mark covers: its /Rect, quads, point and stroke points.
    static func extent(_ mk: Mark) -> CGRect? {
        var r: CGRect?
        func add(_ q: CGRect) { r = r.map { $0.union(q) } ?? q }
        if let b = mk.rect { add(CGRect(x: b.llx, y: b.lly, width: b.urx - b.llx, height: b.ury - b.lly)) }
        for b in mk.quads { add(CGRect(x: b.llx, y: b.lly, width: b.urx - b.llx, height: b.ury - b.lly)) }
        if let p = mk.point { add(CGRect(origin: p, size: .zero)) }
        for s in mk.strokes { for p in s { add(CGRect(origin: p, size: .zero)) } }
        return r
    }

    /// The move that puts a mark pasted at its own page coordinates inside page box `box`
    /// (CropBox, page space): none when it fits; else the least move, along an axis where it is
    /// larger than the box its left and top edges at the box's.
    static func pasteOffset(_ mk: Mark, into box: safepdf_rat_box?) -> CGVector {
        guard let box, let e = extent(mk) else { return CGVector(dx: 0, dy: 0) }
        let x0 = ZoomModel.double(box.llx), y0 = ZoomModel.double(box.lly)
        let x1 = ZoomModel.double(box.urx), y1 = ZoomModel.double(box.ury)
        func axis(_ a: Double, _ b: Double, _ lo: Double, _ hi: Double, startAtLow: Bool) -> Double {
            if b - a > hi - lo { return startAtLow ? lo - a : hi - b }
            if a < lo { return lo - a }
            if b > hi { return hi - b }
            return 0
        }
        return CGVector(dx: axis(e.minX, e.maxX, min(x0, x1), max(x0, x1), startAtLow: true),
                        dy: axis(e.minY, e.maxY, min(y0, y1), max(y0, y1), startAtLow: false))
    }

    /// Re-creates a cut mark on `page` moved by (dx, dy) through the store's add calls (with its
    /// colour, size, opacity, text, and a highlight's comment on its quads); the new mark's id.
    static func recreate(_ clip: MarkClip, page: Int, dx: Double, dy: Double,
                         in m: MarksModel) -> Result<UInt64, EditError> {
        let mk = clip.mark
        func q(_ b: safepdf_box) -> safepdf_box {
            safepdf_box(llx: b.llx + dx, lly: b.lly + dy, urx: b.urx + dx, ury: b.ury + dy)
        }
        func p(_ v: CGPoint) -> CGPoint { CGPoint(x: Double(v.x) + dx, y: Double(v.y) + dy) }
        let rgb = (UInt32(mk.rgb.r) << 16) | (UInt32(mk.rgb.g) << 8) | UInt32(mk.rgb.b)
        switch mk.kind {
        case Int32(SAFEPDF_MARK_HIGHLIGHT):
            let quads = mk.quads.map(q)
            let r = m.addHighlight(page: page, color: mk.color, quads: quads)
            guard case .success = r, let cm = clip.comment else { return r }
            if case .failure(let e) = m.addNote(page: page, color: cm.color, text: cm.text,
                                                anchor: Int32(SAFEPDF_ANCHOR_QUADS), point: nil, quads: quads) {
                return .failure(e)
            }
            return r
        case Int32(SAFEPDF_MARK_NOTE):
            if !mk.quads.isEmpty {
                return m.addNote(page: page, color: mk.color, text: mk.text, anchor: Int32(SAFEPDF_ANCHOR_QUADS),
                                 point: nil, quads: mk.quads.map(q))
            }
            guard let pt = mk.point else { return .failure(EditError(message: "the note has no anchor")) }
            return m.addNote(page: page, color: mk.color, text: mk.text, anchor: Int32(SAFEPDF_ANCHOR_POINT),
                             point: p(pt), quads: [])
        case Int32(SAFEPDF_MARK_FREETEXT):
            guard let pt = mk.point else { return .failure(EditError(message: "the text box has no position")) }
            return m.addFreeText(page: page, text: mk.text, at: p(pt), size: mk.size, rgb: rgb)
        default:
            guard let first = mk.strokes.first, !first.isEmpty else {
                return .failure(EditError(message: "the drawing has no stroke"))
            }
            let r = m.addInk(page: page, points: first.map(p), width: mk.size, opacity: mk.opacity, rgb: rgb)
            guard case .success(let id) = r else { return r }
            for s in mk.strokes.dropFirst() where !s.isEmpty {
                if let e = m.addStroke(id, points: s.map(p)) { return .failure(EditError(message: e)) }
            }
            return r
        }
    }

    // MARK: undo / redo

    /// Undo or Redo of a mark edit (Viewer.undoRedo): an open text box is committed first; the
    /// selection is kept when its mark is still there; a drawing session ends; an open note
    /// editor whose note is gone or changed closes.
    func undoRedo(undo: Bool) {
        guard let m = model else { return }
        _ = commitFreeText()
        let noteText = noteOpen.flatMap { m.find($0)?.text }
        inkSession = nil
        moveFrom = nil
        if let e = undo ? m.undo() : m.redo() {
            status(e)
            return
        }
        if let n = noteOpen, m.find(n)?.text != noteText {
            noteEditor.close()
            noteOpen = nil
        }
        let st = m.state
        let undoKey = TextController.keyText(SAFEPDF_CMD_UNDO), redoKey = TextController.keyText(SAFEPDF_CMD_REDO)
        if undo {
            status("undone (\(st.undo_depth) more to undo, \(st.redo_depth) to redo with \(redoKey))")
        } else {
            status("redone (\(st.redo_depth) more to redo, \(st.undo_depth) to undo with \(undoKey))")
        }
    }

    // MARK: Add text and Draw

    /// Opens the free-text box on page `page` with its upper-left corner at `pos` (page space).
    func ftOpen(id: UInt64?, page: Int, pos: CGPoint, text initial: String, size: UInt32, rgb: UInt32) {
        ftEdit = FreeTextEdit(id: id, page: page, pos: pos, size: size, rgb: rgb)
        text?.setSelection(nil)
        freeText.string = initial
        placeFreeText()
        if let c = canvas, c.window != nil { c.window?.makeFirstResponder(freeText.textView) }
        redrawAll()
        placeBubble()
        status("page \(page + 1): type the text (a click elsewhere or Escape finishes it)")
    }

    /// Places the text box over its page position (font size at the page's zoom).
    private func placeFreeText() {
        guard let fe = ftEdit, let c = canvas, let t = c.transform(ofPage: fe.page),
              let p = MarksPalette.params else {
            freeText.isHidden = true
            return
        }
        let s = Self.scale(t)
        let corner = t.view(Double(fe.pos.x) + p.ft_pad, Double(fe.pos.y) - p.ft_pad)
        freeText.place(at: corner, fontSize: CGFloat(fe.size) * s, color: MarksPalette.nsColor(rgb: fe.rgb),
                       lineFactor: CGFloat(p.line_factor))
    }

    /// The typed text of the open box (the self-test types into it).
    var freeTextString: String {
        get { freeText.string }
        set { freeText.string = newValue }
    }

    /// Commits the open text box (Viewer.commitFt): a new box becomes a free-text mark (dropped
    /// when empty); an edited one gets the new text (deleted when emptied). Returns whether a
    /// box was open.
    @discardableResult
    func commitFreeText() -> Bool {
        guard let fe = ftEdit else { return false }
        let raw = freeText.string
        ftEdit = nil
        freeText.close()
        if let c = canvas, c.window?.firstResponder === freeText.textView { c.window?.makeFirstResponder(c) }
        var t = raw
        while t.hasSuffix("\n") { t.removeLast() }
        let blank = t.allSatisfy { $0.isWhitespace }
        guard let m = model else { return true }
        if let id = fe.id {
            if blank {
                if markSel == id { markSel = nil }
                _ = m.delete(id)
                status("text box deleted (emptied)")
            } else if m.find(id)?.text == t {
                status("text unchanged")
            } else {
                _ = m.setText(id, t)
                markSel = id
                status("text edited (\(t.count) characters)")
            }
        } else if blank {
            status("empty text box discarded")
        } else {
            switch m.addFreeText(page: fe.page, text: t, at: fe.pos, size: fe.size, rgb: fe.rgb) {
            case .success(let id):
                markSel = id
                status("page \(fe.page + 1): text added (\(t.count) characters; drag it to move it, double-click to edit, Delete removes it)")
            case .failure(let e):
                status("text: \(e.message)")
            }
        }
        redrawAll()
        placeBubble()
        onChange?()
        return true
    }

    /// Starts a stroke at page point `p` (Viewer.inkBegin).
    private func inkBegin(page: Int, _ p: CGPoint) {
        inkStroke = (page, [p])
        text?.setSelection(nil)
        placeBubble()
        redrawAll()
    }

    /// A drag while a stroke is drawn: adds the point when it is at least a pixel away from the
    /// last one (Viewer.inkMove); on release the stroke ends.
    private func inkMove(_ v: CGPoint, final: Bool) {
        if let (page, pts) = inkStroke, let p = pagePoint(on: page, v), let last = pts.last {
            let d = pixelsPerUnit(page) * (abs(p.x - last.x) + abs(p.y - last.y))
            if d >= 1 { inkStroke = (page, pts + [p]) }
            redrawAll()
        }
        if final { inkEnd() }
    }

    /// Ends the stroke: it joins the session's drawing when that is still unsaved and on the same
    /// page (one undo step per stroke, `_add_stroke`), else it starts a new drawing.
    private func inkEnd() {
        guard let (page, pts) = inkStroke, let m = model else { return }
        inkStroke = nil
        var n = 1
        if let sid = inkSession, let mk = m.find(sid), mk.page == page, !mk.isSaved, mk.isInk {
            if let e = m.addStroke(sid, points: pts) { status("drawing: \(e)"); return }
            n = mk.strokes.count + 1
            markSel = sid
        } else {
            switch m.addInk(page: page, points: pts, width: ui.ink_thick, opacity: ui.ink_opacity, rgb: ui.ink_rgb) {
            case .success(let id):
                inkSession = id
                markSel = id
            case .failure(let e):
                status("drawing: \(e.message)")
                return
            }
        }
        status("page \(page + 1): drawing with \(n) stroke(s) (Escape ends it; Delete removes it)")
    }

    /// A drag of a free text or drawing: drawn where it is dragged; on release it is moved by
    /// the distance dragged (Store.translate) when that is at least 2 pixels (Viewer.moveDrag).
    private func moveDrag(_ v: CGPoint, final: Bool) {
        guard let mf = moveFrom, let p = pagePoint(on: mf.page, v) else { return }
        moveFrom = final ? nil : (mf.id, mf.page, mf.p0, p)
        redrawAll()
        guard final, let m = model else { return }
        let dx = Double(p.x - mf.p0.x), dy = Double(p.y - mf.p0.y)
        if Double(pixelsPerUnit(mf.page)) * (abs(dx) + abs(dy)) >= 2 {
            if let e = m.translate(mf.id, dx: dx, dy: dy) { status("move: \(e)") } else {
                status("\(m.find(mf.id)?.name ?? "mark") moved")
            }
        }
        placeBubble()
    }

    /// Moves free text or a drawing by (dx, dy) page units at once (the self-test's path).
    func move(_ id: UInt64, dx: Double, dy: Double) -> String? {
        model?.translate(id, dx: dx, dy: dy)
    }

    // MARK: pop-overs (Highlight colour, Add text / Draw)

    /// A swatch of the Highlight pop-over: the current colour; recolours a selected highlight.
    func popoverColor(_ c: Int32) {
        setColor(c)
        if let mk = selectedMark, mk.isHighlight, let m = model {
            if let e = m.recolor(mk.id, c) { status("recolour: \(e)") } else {
                status("highlight recoloured: \(MarksPalette.name(c))")
            }
        } else {
            status("highlight colour: \(MarksPalette.name(c))")
        }
    }

    /// A colour of the Add text / Draw pop-over: new marks of the mode, the selected mark of the
    /// mode's kind and an open text box take it (Viewer.edClick).
    func editorColor(_ rgb: UInt32) {
        let draw = ui.editor == Int32(SAFEPDF_EDITOR_DRAW)
        if draw { ui.ink_rgb = rgb } else {
            ui.ft_rgb = rgb
            ftEdit?.rgb = rgb
            placeFreeText()
        }
        if let mk = selectedMark, draw ? mk.isInk : mk.isFreeText { _ = model?.setRgb(mk.id, rgb) }
        status(String(format: "colour #%06X", rgb))
        onChange?()
    }

    /// A slider of the Add text / Draw pop-over (row 1: font size or thickness, 2: opacity): the
    /// steps of one drag are one undo step (merge, then seal when it ends; task 10.7).
    func slide(row: Int, value: UInt32, ended: Bool) {
        guard let m = model else { return }
        if !sliding {
            m.seal()
            sliding = true
        }
        let draw = ui.editor == Int32(SAFEPDF_EDITOR_DRAW)
        let mk = selectedMark
        if draw && row == 2 {
            ui.ink_opacity = value
            if let mk, mk.isInk, mk.opacity != value { _ = m.setOpacity(mk.id, value, merge: true) }
            status("opacity \(value)%")
        } else if draw {
            ui.ink_thick = value
            if let mk, mk.isInk, mk.size != value { _ = m.setSize(mk.id, value, merge: true) }
            status("thickness \(value)")
        } else {
            ui.ft_size = value
            ftEdit?.size = value
            placeFreeText()
            if let mk, mk.isFreeText, mk.size != value { _ = m.setSize(mk.id, value, merge: true) }
            status("font size \(value)")
        }
        if ended {
            m.seal()
            sliding = false
        }
        onChange?()
    }

    // MARK: Escape

    /// Escape (Viewer.escape, Toolbar.onEscape): closes the topmost open transient (the note
    /// editor, the colour picker, a pop-over); an open text box is committed. Every Escape also
    /// dismisses the bubble (the text selection and the selected mark are cleared) and ends a
    /// drawing session; the tool stays. Returns whether a transient was closed (else the window
    /// leaves full screen).
    @discardableResult
    func escape() -> Bool {
        let committed = commitFreeText()
        var opened: UInt32 = 0
        if noteOpen != nil { opened |= UInt32(SAFEPDF_TRANSIENT_NOTE) }
        if ui.picker != 0 { opened |= UInt32(SAFEPDF_TRANSIENT_PICKER) }
        if ui.popover != 0 && model != nil { opened |= UInt32(SAFEPDF_TRANSIENT_HL_POP) }
        if ui.ed_pop != 0 && ui.editor != Int32(SAFEPDF_EDITOR_NONE) && model != nil {
            opened |= UInt32(SAFEPDF_TRANSIENT_ED_POP)
        }
        let closes = safepdf_marks_escape_closes(opened)
        if closes & UInt32(SAFEPDF_TRANSIENT_NOTE) != 0 { noteCloseWithoutSave(noteEditor.text) }
        if closes & UInt32(SAFEPDF_TRANSIENT_PICKER) != 0 { ui.picker = 0 }
        if closes & UInt32(SAFEPDF_TRANSIENT_HL_POP) != 0 { ui.popover = 0 }
        if closes & UInt32(SAFEPDF_TRANSIENT_ED_POP) != 0 { ui.ed_pop = 0 }
        ui.picker = 0
        text?.setSelection(nil)
        markSel = nil
        inkStroke = nil
        inkSession = nil
        moveFrom = nil
        syncPopovers()
        redrawAll()
        placeBubble()
        onChange?()
        return closes != 0 || committed
    }

    // MARK: pointer (CanvasPointer): the marks' share of a press, the rest to the text

    func pointerDown(at v: CGPoint, clicks: Int, shift: Bool) {
        guard model != nil, let t = text else {
            text?.pointerDown(at: v, clicks: clicks, shift: shift)
            return
        }
        moveFrom = nil
        press = nil
        // A click elsewhere commits an open text box (and does nothing else, as PDF.js).
        if commitFreeText() {
            route = .consumed
            return
        }
        if ui.picker != 0 {
            ui.picker = 0
            placeBubble()
        }
        let pp = pagePoint(v)
        if mode == SAFEPDF_MODE_DRAW.rawValue {
            route = .consumed
            if let (pg, p) = pp {
                inkBegin(page: pg, p)
                route = .ink
            }
            return
        }
        if clicks >= 2, let (pg, p) = pp, let mk = editorAt(page: pg, p) {
            // A double click on a text box edits it.
            route = .consumed
            if mk.isFreeText, let pos = mk.point {
                markSel = mk.id
                ftOpen(id: mk.id, page: pg, pos: pos, text: mk.text, size: mk.size,
                       rgb: UInt32(mk.rgb.r) << 16 | UInt32(mk.rgb.g) << 8 | UInt32(mk.rgb.b))
            }
            return
        }
        if clicks < 2, let (pg, p) = pp, let mk = editorAt(page: pg, p) {
            // A press on a free text or drawing selects it and starts moving it.
            t.setSelection(nil)
            markSel = mk.id
            moveFrom = (mk.id, pg, p, p)
            route = .move
            redrawAll()
            placeBubble()
            status("\(mk.name) selected (drag to move it; Delete removes it\(mk.isFreeText ? "; double-click edits it" : ""))")
            onChange?()
            return
        }
        if markSel != nil {
            markSel = nil
            redrawAll()
            onChange?()
        }
        // The release of a double or triple click is not a click in place (Viewer.selectWord
        // clears the press point).
        if let (pg, p) = pp { press = (pg, Double(p.x), Double(p.y), v, clicks >= 2) }
        route = .text
        if mode != SAFEPDF_MODE_TEXT.rawValue { t.pointerDown(at: v, clicks: clicks, shift: shift) }
        placeBubble()
    }

    func pointerDragged(at v: CGPoint) {
        switch route {
        case .ink: inkMove(v, final: false)
        case .move: moveDrag(v, final: false)
        case .text:
            if let p = press, hypot(v.x - p.view.x, v.y - p.view.y) > TextController.clickSlop {
                press = (p.page, p.x, p.y, p.view, true)
            }
            if mode != SAFEPDF_MODE_TEXT.rawValue {
                text?.pointerDragged(at: v)
                placeBubble()
            }
        default: break
        }
    }

    func pointerUp(at v: CGPoint) {
        let r = route
        route = .none
        switch r {
        case .ink: inkMove(v, final: true)
        case .move: moveDrag(v, final: true)
        case .text:
            let p = press
            press = nil
            if let p, !p.moved {
                // A click in place: the mark under it (marks lie above links), then in Add text
                // mode a text box, else the text controller follows a link.
                let q = pagePoint(on: p.page, v) ?? CGPoint(x: p.x, y: p.y)
                if selectMark(page: p.page, at: q, openIt: true) {
                    text?.cancelPress()
                    return
                }
                if mode == SAFEPDF_MODE_TEXT.rawValue {
                    text?.cancelPress()
                    ftOpen(id: nil, page: p.page, pos: q, text: "", size: ui.ft_size, rgb: ui.ft_rgb)
                    return
                }
            }
            if mode != SAFEPDF_MODE_TEXT.rawValue { text?.pointerUp(at: v) }
            placeBubble()
        default: break
        }
    }

    func pointerMoved(at v: CGPoint?) {
        guard route == .none else { return }
        text?.pointerMoved(at: v)
    }

    // MARK: context menu (the Tk viewer's mark menu: colours, Add note…, Delete mark)

    private var contextPoint: CGPoint?

    private func contextMenu(at v: CGPoint) -> NSMenu? {
        guard model != nil else { return nil }
        contextPoint = v
        if let (pg, p) = pagePoint(v), !selectMark(page: pg, at: p, openIt: false), markSel != nil {
            markSel = nil
            redrawAll()
            placeBubble()
        }
        let menu = NSMenu(title: "Marks")
        let colors = NSMenuItem(title: "Highlight Color", action: nil, keyEquivalent: "")
        colors.submenu = MarksMenus.colorMenu(target: menuTarget, action: #selector(MarksMenuTarget.contextColor(_:)),
                                              current: hlColor)
        menu.addItem(colors)
        let note = NSMenuItem(title: "Add Note…", action: #selector(MarksMenuTarget.contextNote(_:)), keyEquivalent: "")
        note.target = menuTarget
        menu.addItem(note)
        let del = NSMenuItem(title: "Delete Mark", action: markSel != nil ? #selector(MarksMenuTarget.contextDelete(_:)) : nil,
                             keyEquivalent: "")
        del.target = menuTarget
        menu.addItem(del)
        return menu
    }

    private lazy var menuTarget = MarksMenuTarget(self)

    fileprivate func contextNote() { addNote(at: contextPoint) }

    // MARK: the bubble (Bubble.kindFor / layout / place)

    /// Shows, hides or places the bubble (Viewer.drawBubble): after a text selection (not while
    /// dragging) the float bubble; on a selected highlight the edit bubble (and its colour
    /// picker when open); on a selected free text or drawing the editor bubble with Delete.
    func placeBubble() {
        guard let c = canvas, let t = text, model != nil else {
            bubble.hide()
            picker.hide()
            return
        }
        var selRects: [safepdf_box] = []
        if let s = t.selection, !t.isPressing, let tr = c.transform(ofPage: s.page) {
            selRects = t.selectionBoxes().map { Self.canvasBox(tr.rect($0)) }
        }
        let mk = selectedMark
        var markRects: [safepdf_box] = []
        var edRects: [safepdf_box] = []
        if let mk, let tr = c.transform(ofPage: mk.page) {
            if mk.isHighlight { markRects = mk.quads.map { Self.canvasBox(tr.rect($0)) } }
            if mk.isEditor, let r = mk.rect { edRects = [Self.canvasBox(tr.rect(r))] }
        }
        var kind: Int32 = -1
        var rects: [safepdf_box] = []
        if selRects.isEmpty && !edRects.isEmpty && ftEdit == nil && inkStroke == nil && moveFrom == nil {
            kind = Int32(SAFEPDF_BUBBLE_EDITOR)
            rects = edRects
        } else {
            kind = safepdf_marks_bubble_kind(selRects.isEmpty ? 0 : 1, markRects.isEmpty ? 0 : 1, ui.show_all)
            rects = kind == Int32(SAFEPDF_BUBBLE_FLOAT) ? selRects : markRects
        }
        guard kind >= 0, !rects.isEmpty else {
            bubble.hide()
            picker.hide()
            return
        }
        var layout = safepdf_bubble_layout()
        guard safepdf_marks_bubble_layout(kind, &layout) == 0 else { bubble.hide(); return }
        bubble.configure(kind: kind, layout: layout, markColor: mk?.color ?? hlColor, pickerOpen: ui.picker != 0)
        let size = bubble.fittingSize
        var area = Self.canvasBox(c.bounds)
        var out = safepdf_box()
        guard safepdf_marks_bubble_place(&rects, rects.count, Double(size.width), Double(size.height), &area, &out) == 1
        else { bubble.hide(); return }
        bubble.frame = CGRect(x: out.llx, y: out.lly, width: out.urx - out.llx, height: out.ury - out.lly)
        bubble.isHidden = false
        if kind == Int32(SAFEPDF_BUBBLE_EDIT), ui.picker != 0 {
            picker.configurePicker(current: mk?.color ?? hlColor)
            let ps = picker.fittingSize
            let below = bubble.frame.maxY + 4
            let y = below + ps.height <= c.bounds.maxY ? below : bubble.frame.minY - 4 - ps.height
            picker.frame = CGRect(x: bubble.frame.minX, y: y, width: ps.width, height: ps.height)
            picker.isHidden = false
        } else {
            picker.hide()
        }
    }

    /// A view rectangle as a canvas box (llx/lly = left/top, urx/ury = right/bottom; y down).
    static func canvasBox(_ r: CGRect) -> safepdf_box {
        safepdf_box(llx: Double(r.minX), lly: Double(r.minY), urx: Double(r.maxX), ury: Double(r.maxY))
    }

    /// The kind of bubble shown (nil: none).
    var bubbleKind: Int32? { bubble.isHidden ? nil : bubble.kind }

    /// A bubble button: highlight (in a colour), the colour picker, Comment / Add note, Copy,
    /// Delete (Bubble.Btn.cmd?: the same commands as the menu).
    func bubbleButton(_ b: BubbleView.Action, _ color: Int32) {
        switch b {
        case .highlight: highlight(color)
        case .color:
            ui.picker = ui.picker != 0 ? 0 : 1
            placeBubble()
        case .pick:
            ui.picker = 0
            highlight(color)
            placeBubble()
        case .comment: addNote(at: nil)
        case .copy: text?.copy()
        case .delete: deleteSelected()
        }
        onChange?()
    }

    // MARK: drawing (Viewer.drawMarks, drawEditorMark; highlights multiplied as Marks.composite)

    private static let anchorColor = NSColor(srgbRed: 0xC9 / 255.0, green: 0x9A / 255.0, blue: 0, alpha: 1)
    private static let selColor = NSColor(srgbRed: 0, green: 0x60 / 255.0, blue: 0xDF / 255.0, alpha: 1)

    /// Draws the marks of `page` (under the search hits and the selection): unsaved highlights
    /// multiplied into the page (saved ones are in the rendered page), note anchors and icons,
    /// free text and drawings, the stroke being drawn, the selected mark's outline.
    func draw(_ page: Int, _ t: PageTransform, _ c: PageCanvasView) {
        guard let cg = NSGraphicsContext.current?.cgContext, model != nil else { return }
        let s = Self.scale(t)
        // Saved marks the renderer paints: all of them while the pages show the store's state of
        // the saved marks (the file, or the preview); else edited ones are drawn here too.
        let previewShown = model.map { preview.isCurrent($0) } ?? false
        for mk in visible(page) {
            let shift = moveFrom.flatMap { mf -> CGSize? in
                mf.id == mk.id ? CGSize(width: mf.last.x - mf.p0.x, height: mf.last.y - mf.p0.y) : nil
            }
            let tt = shift.map { PageTransform(ox: t.ox + t.ax * Double($0.width) + t.bx * Double($0.height),
                                               oy: t.oy + t.ay * Double($0.width) + t.by * Double($0.height),
                                               ax: t.ax, ay: t.ay, bx: t.bx, by: t.by) } ?? t
            let changed = mk.state == Int32(SAFEPDF_MARK_SAVED_CHANGED) && !previewShown
            let drawn = !mk.isSaved || changed
            switch mk.kind {
            case Int32(SAFEPDF_MARK_HIGHLIGHT):
                if drawn {
                    cg.saveGState()
                    cg.setBlendMode(.multiply)
                    cg.setFillColor(mk.nsColor.cgColor)
                    for q in mk.quads { cg.fill(c.pixelAligned(tt.rect(q))) }
                    cg.restoreGState()
                }
            case Int32(SAFEPDF_MARK_NOTE):
                cg.saveGState()
                cg.setStrokeColor(Self.anchorColor.cgColor)
                cg.setLineWidth(1)
                cg.setLineDash(phase: 0, lengths: [4, 2])
                for q in mk.quads { cg.stroke(c.pixelOutward(tt.rect(q))) }
                cg.restoreGState()
                if (!mk.isSaved || mk.isComment || changed), let r = mk.rect {
                    NoteIcon.draw(in: c.pixelOutward(tt.rect(r)), color: MarksPalette.color(mk.color), cg: cg)
                }
            default:
                if drawn && ftEdit?.id != mk.id { drawEditorMark(mk, tt, s, cg) }
            }
            if markSel == mk.id {
                var boxes: [safepdf_box] = []
                if mk.isNote || mk.isEditor { if let r = mk.rect { boxes = [r] } } else { boxes = mk.quads }
                cg.saveGState()
                cg.setStrokeColor(Self.selColor.cgColor)
                cg.setLineWidth(2)
                for b in boxes { cg.stroke(c.pixelOutward(tt.rect(b)).insetBy(dx: -2, dy: -2)) }
                cg.restoreGState()
            }
        }
        if let (pg, pts) = inkStroke, pg == page {
            Self.strokePath(pts, t, width: max(1, CGFloat(ui.ink_thick) * s),
                            color: MarksPalette.nsColor(rgb: ui.ink_rgb, alpha: CGFloat(ui.ink_opacity) / 100), cg: cg)
        }
    }

    /// Free text (one line per text line, the first baseline `ftPad` + size below the box's
    /// top, as the appearance Save writes; turned with the page) or a drawing (a path per
    /// stroke, a dot for a one-point stroke; its opacity as alpha).
    private func drawEditorMark(_ mk: Mark, _ t: PageTransform, _ s: CGFloat, _ cg: CGContext) {
        guard let p = MarksPalette.params else { return }
        if mk.isFreeText, let pos = mk.point {
            let size = CGFloat(mk.size)
            let font = NSFont(name: "Helvetica", size: max(1, size * s)) ?? .systemFont(ofSize: max(1, size * s))
            let angle = atan2(t.ay, t.ax)
            for (i, line) in mk.text.components(separatedBy: "\n").enumerated() {
                let base = t.view(Double(pos.x) + p.ft_pad,
                                  Double(pos.y) - p.ft_pad - Double(size) - Double(i) * p.line_factor * Double(size))
                let str = NSAttributedString(string: line, attributes: [.font: font, .foregroundColor: mk.nsColor])
                let ct = CTLineCreateWithAttributedString(str)
                cg.saveGState()
                cg.translateBy(x: base.x, y: base.y)
                cg.rotate(by: CGFloat(angle))
                cg.scaleBy(x: 1, y: -1)
                cg.textPosition = .zero
                CTLineDraw(ct, cg)
                cg.restoreGState()
            }
        } else if mk.isInk {
            let color = mk.nsColor.withAlphaComponent(CGFloat(mk.opacity) / 100)
            for st in mk.strokes {
                Self.strokePath(st, t, width: max(1, CGFloat(mk.size) * s), color: color, cg: cg)
            }
        }
    }

    private static func strokePath(_ pts: [CGPoint], _ t: PageTransform, width: CGFloat, color: NSColor, cg: CGContext) {
        guard let first = pts.first else { return }
        cg.saveGState()
        if pts.count == 1 {
            let v = t.view(Double(first.x), Double(first.y))
            cg.setFillColor(color.cgColor)
            cg.fillEllipse(in: CGRect(x: v.x - width / 2, y: v.y - width / 2, width: width, height: width))
        } else {
            let path = CGMutablePath()
            path.move(to: t.view(Double(first.x), Double(first.y)))
            for q in pts.dropFirst() { path.addLine(to: t.view(Double(q.x), Double(q.y))) }
            cg.addPath(path)
            cg.setStrokeColor(color.cgColor)
            cg.setLineWidth(width)
            cg.setLineCap(.round)
            cg.setLineJoin(.round)
            cg.strokePath()
        }
        cg.restoreGState()
    }
}

/// The Objective-C target of the context menu's entries.
@MainActor @objc final class MarksMenuTarget: NSObject {
    private weak var owner: MarksController?

    init(_ owner: MarksController) { self.owner = owner }

    @objc func contextColor(_ sender: NSMenuItem) { owner?.highlight(Int32(sender.tag)) }
    @objc func contextNote(_ sender: NSMenuItem) { owner?.contextNote() }
    @objc func contextDelete(_ sender: NSMenuItem) { owner?.deleteSelected() }
}

/// Menus of the highlight colours (the Edit menu's colour submenu, the context menu).
@MainActor enum MarksMenus {
    /// The five colours (Marks.Color.all) with swatch images; tag = SAFEPDF_COLOR_*.
    static func colorMenu(target: AnyObject?, action: Selector, current: Int32?) -> NSMenu {
        let menu = NSMenu(title: "Highlight Color")
        for (i, label) in MarksPalette.labels.enumerated() {
            let item = NSMenuItem(title: label, action: action, keyEquivalent: "")
            item.tag = i
            item.target = target
            item.image = swatch(MarksPalette.color(Int32(i)))
            if let current { item.state = current == Int32(i) ? .on : .off }
            menu.addItem(item)
        }
        return menu
    }

    /// A round swatch image.
    static func swatch(_ color: NSColor, size: CGFloat = 12) -> NSImage {
        NSImage(size: NSSize(width: size, height: size), flipped: false) { r in
            color.setFill()
            NSBezierPath(ovalIn: r.insetBy(dx: 0.5, dy: 0.5)).fill()
            NSColor.black.withAlphaComponent(0.35).setStroke()
            NSBezierPath(ovalIn: r.insetBy(dx: 0.5, dy: 0.5)).stroke()
            return true
        }
    }
}

/// The note icon (Tk's `::safepdf::noteIcon`): a speech bubble in the note's colour with lines.
@MainActor enum NoteIcon {
    static func draw(in r: CGRect, color: NSColor, cg: CGContext) {
        cg.saveGState()
        let body = CGRect(x: r.minX + 1, y: r.minY + 1, width: r.width - 2, height: r.height * 0.72)
        let path = CGMutablePath()
        path.addRoundedRect(in: body, cornerWidth: min(3, body.width / 4), cornerHeight: min(3, body.height / 4))
        path.move(to: CGPoint(x: body.minX + body.width * 0.25, y: body.maxY))
        path.addLine(to: CGPoint(x: body.minX + body.width * 0.2, y: r.maxY - 1))
        path.addLine(to: CGPoint(x: body.minX + body.width * 0.45, y: body.maxY))
        cg.addPath(path)
        cg.setFillColor(color.cgColor)
        cg.setStrokeColor(NSColor(white: 0.25, alpha: 1).cgColor)
        cg.setLineWidth(1)
        cg.drawPath(using: .fillStroke)
        cg.setStrokeColor(NSColor(white: 0.25, alpha: 0.8).cgColor)
        for k in 1...3 {
            let y = body.minY + body.height * CGFloat(k) / 4
            cg.move(to: CGPoint(x: body.minX + body.width * 0.2, y: y))
            cg.addLine(to: CGPoint(x: body.maxX - body.width * 0.2, y: y))
        }
        cg.strokePath()
        cg.restoreGState()
    }
}
