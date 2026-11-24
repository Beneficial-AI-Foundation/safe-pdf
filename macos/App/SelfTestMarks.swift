// SelfTestMarks.swift — the self-test's checks of task 11.3e1 (marks parity, on the page):
// the store created from the document's bytes; a highlight from a selection through the real
// pointer path and the bubble (quads = the selection's Select.rangeBoxes, as the Tk viewer's);
// its pixels multiplied into the page; recolouring through the picker; a comment on the
// highlight and notes anchored by Marks.noteAnchor (point vs the selection's quads), saved and
// closed per note_close; free text added, edited and moved; ink strokes joining one drawing; a
// slider drag as one undo step; undo / redo and the dirty state; deleting a highlight with its
// comment; the bubble's items and its dismissal by Escape; the tools' modes, pressed buttons and
// cursors; the enabled states of the Edit commands; and the saved marks of a file written by
// safepdf_marks_save_build (into the self-test's directory only) listed as saved when reopened.
// Plan.md §6 Phase 11; docs/macos-design.md §1–§3. Headless like SelfTest.swift: no window, no
// popover or panel is ever shown (the controllers' state is driven directly).

import AppKit
import SafePdfC

extension SelfTest {
    private static func marksIndex(_ t: TextController, _ p: Int) -> SelectPage? {
        var done: TextOutcome<SelectPage>? = nil
        t.store.withIndex(p, priority: Int32(SAFEPDF_PRIO_CURRENT)) { done = $0 }
        pump(limit: 60) { done != nil }
        if case .ready(let sp)? = done { return sp }
        return nil
    }

    /// The mean colour of a canvas rectangle in a 2x snapshot of the scroll view.
    private static func meanRGB(_ rep: NSBitmapImageRep, _ pv: PageViewController, _ r: CGRect)
        -> (r: CGFloat, g: CGFloat, b: CGFloat)?
    {
        let o = pv.scrollView.contentView.bounds.origin
        let x0 = Int(((r.minX - o.x) * 2).rounded(.up)), x1 = Int(((r.maxX - o.x) * 2).rounded(.down))
        let y0 = Int(((r.minY - o.y) * 2).rounded(.up)), y1 = Int(((r.maxY - o.y) * 2).rounded(.down))
        var sr: CGFloat = 0, sg: CGFloat = 0, sb: CGFloat = 0, n: CGFloat = 0
        for y in stride(from: max(0, y0), to: min(rep.pixelsHigh, y1), by: 1) {
            for x in stride(from: max(0, x0), to: min(rep.pixelsWide, x1), by: 1) {
                guard let c = rep.colorAt(x: x, y: y)?.usingColorSpace(.sRGB) else { continue }
                sr += c.redComponent
                sg += c.greenComponent
                sb += c.blueComponent
                n += 1
            }
        }
        return n > 0 ? (sr / n, sg / n, sb / n) : nil
    }

    private static func sameBoxes(_ a: [safepdf_box], _ b: [safepdf_box]) -> Bool {
        a.count == b.count && zip(a, b).allSatisfy { MarksModel.same($0, $1) }
    }

    private static func near(_ a: CGFloat, _ b: CGFloat, _ eps: CGFloat = 1e-6) -> Bool { abs(a - b) <= eps }

    static func marksParity(_ doc: Document, _ pv: PageViewController, dir: String, path: String) {
        let mc = pv.marks
        let t = pv.text
        let pb = NSPasteboard(name: NSPasteboard.Name("org.safe-pdf.selftest.marks.\(getpid())"))
        defer { pb.releaseGlobally() }
        t.pasteboard = pb
        pv.canvas.scaleOverride = 2
        pv.show(doc)
        waitRenders(pv)
        guard let m = mc.model else {
            check(false, "marks: no store for the document")
            return
        }
        let st0 = m.state
        say("marks: store of \(st0.page_count) pages, \(st0.mark_count) saved marks, dirty \(st0.dirty)")
        check(st0.dirty == 0 && st0.can_undo == 0, "a fresh store is clean")
        check(mc.mode == SAFEPDF_MODE_SELECT.rawValue && mc.pressedTool == SAFEPDF_TOOL_SELECT.rawValue,
              "the default tool is Select text")
        for c in [SAFEPDF_CMD_UNDO, SAFEPDF_CMD_REDO, SAFEPDF_CMD_HIGHLIGHT, SAFEPDF_CMD_ADD_NOTE,
                  SAFEPDF_CMD_DELETE_MARK, SAFEPDF_CMD_HL_TOOL, SAFEPDF_CMD_SHOW_ALL] {
            check(Commands.implemented.contains(Commands.id(c)), "command \(c.rawValue) implemented")
        }
        for c in [SAFEPDF_CMD_SAVE, SAFEPDF_CMD_SAVE_AS, SAFEPDF_CMD_IMPORT_XFDF, SAFEPDF_CMD_EXPORT_XFDF] {
            check(Commands.implemented.contains(Commands.id(c)), "command \(c.rawValue) implemented (11.3e2)")
        }
        func enabled(_ c: safepdf_cmd) -> Bool {
            Chrome.states(DocumentWindowController.context(pdf: doc, pages: pv))?.commandEnabled[Commands.id(c)] ?? false
        }
        check(!enabled(SAFEPDF_CMD_UNDO) && !enabled(SAFEPDF_CMD_REDO) && !enabled(SAFEPDF_CMD_DELETE_MARK)
              && enabled(SAFEPDF_CMD_ADD_NOTE) && enabled(SAFEPDF_CMD_HL_TOOL),
              "fresh: Undo, Redo, Delete mark disabled; Add note, Highlight tool enabled")
        guard let pr = pv.canvas.rect(ofPage: 0), let tr = pv.canvas.transform(ofPage: 0) else {
            check(false, "marks: page 1 not laid out")
            return
        }
        let vis = pr.intersection(pv.canvas.visibleRect)
        // An empty spot near the visible part's lower right, and one for drawing near its left.
        let empty = CGPoint(x: vis.maxX - 30, y: vis.maxY - 30)
        let inkAt = CGPoint(x: vis.minX + 30, y: vis.maxY - 60)

        var hlId: UInt64? = nil
        var commentId: UInt64? = nil
        if let sp = marksIndex(t, 0), sp.cellCount >= 10 {
            (hlId, commentId) = highlightChecks(mc, t, pv, sp, tr, dir: dir, enabled: enabled)
        } else {
            say("marks: page 1 has no text index with 10 cells: highlight checks skipped")
        }
        noteChecks(mc, t, pv, tr, empty: empty)
        freeTextChecks(mc, pv, tr, empty: empty)
        inkChecks(mc, pv, tr, at: inkAt, dir: dir)
        undoChecks(mc, m)
        if let hlId, let commentId {
            mc.selectMark(page: 0, at: centreOf(m.find(hlId)?.quads.first), openIt: false)
            check(mc.markSel == hlId, "click selects the highlight")
            check(enabled(SAFEPDF_CMD_DELETE_MARK), "Delete mark enabled with a selected mark")
            mc.deleteSelected()
            check(m.find(hlId) == nil && m.find(commentId) == nil, "deleting the highlight removed its comment")
            mc.undoRedo(undo: true)
            check(m.find(hlId) != nil && m.find(commentId) != nil, "undo restored the highlight and its comment")
        }
        savedChecks(mc, pv, doc, dir: dir)
        t.pasteboard = .general
    }

    private static func centreOf(_ b: safepdf_box?) -> CGPoint {
        guard let b else { return .zero }
        return CGPoint(x: (b.llx + b.urx) / 2, y: (b.lly + b.ury) / 2)
    }

    // MARK: highlight, bubble, picker, comment, pixels, Escape

    private static func highlightChecks(_ mc: MarksController, _ t: TextController, _ pv: PageViewController,
                                        _ sp: SelectPage, _ tr: PageTransform, dir: String,
                                        enabled: (safepdf_cmd) -> Bool) -> (UInt64?, UInt64?) {
        guard let m = mc.model else { return (nil, nil) }
        let k = min(15, sp.cellCount - 1)
        func centre(_ b: safepdf_box) -> CGPoint { tr.view((b.llx + b.urx) / 2, (b.lly + b.ury) / 2) }
        let a = centre(sp.boxes[0]), z = centre(sp.boxes[k])
        mc.pointerDown(at: a, clicks: 1, shift: false)
        mc.pointerDragged(at: CGPoint(x: (a.x + z.x) / 2, y: (a.y + z.y) / 2))
        mc.pointerDragged(at: z)
        mc.pointerUp(at: z)
        check(t.selection != nil, "drag through the marks controller selects text")
        let quads = t.selectionBoxes()
        check(!quads.isEmpty, "the selection has highlight boxes")
        check(mc.bubbleKind == Int32(SAFEPDF_BUBBLE_FLOAT), "the float bubble shows after a selection")
        let items = mc.bubble.items.map { "\($0.action)\($0.color >= 0 ? "\($0.color)" : "")" }
        say("marks: float bubble \(items.joined(separator: " ")) at \(mc.bubble.frame)")
        check(items == ["highlight0", "highlight1", "highlight2", "highlight3", "highlight4", "comment", "copy"],
              "float bubble items \(items)")
        if let sel = t.selection {
            var lastY = -Double.infinity, lastX = -Double.infinity
            for q in quads {
                let r = tr.rect(q)
                if Double(r.maxY) > lastY || (Double(r.maxY) == lastY && Double(r.maxX) > lastX) {
                    lastY = Double(r.maxY)
                    lastX = Double(r.maxX)
                }
            }
            // Bubble.place: the right edge at the last point, clamped into the canvas.
            let w = Double(mc.bubble.frame.width)
            let want = min(max(lastX - w, Double(pv.canvas.bounds.minX)), Double(pv.canvas.bounds.maxX) - w) + w
            check(abs(Double(mc.bubble.frame.maxX) - want) < 0.5,
                  "the bubble's right edge is at the selection's last point (\(mc.bubble.frame.maxX) vs \(want))")
            _ = sel
        }
        // Copy from the bubble.
        if let ci = mc.bubble.items.firstIndex(where: { $0.action == .copy }) {
            mc.bubble.press(ci)
            check(!(t.pasteboard.string(forType: .string) ?? "").isEmpty, "the bubble's Copy copies")
        }
        // Highlight in green through the bubble.
        mc.bubble.press(1)
        let hls = m.list(0).filter { $0.isHighlight }
        check(hls.count == 1, "one highlight after the bubble's Highlight (\(hls.count))")
        guard let hl = hls.first else { return (nil, nil) }
        check(hl.color == Int32(SAFEPDF_COLOR_GREEN) && sameBoxes(hl.quads, quads),
              "highlight in green over the selection's quads (Select.rangeBoxes)")
        check(hl.state == Int32(SAFEPDF_MARK_NEW), "the highlight is new (unsaved)")
        check(mc.markSel == hl.id && t.selection == nil, "the new highlight is selected, the text selection cleared")
        check(mc.bubbleKind == Int32(SAFEPDF_BUBBLE_EDIT), "the edit bubble shows on the selected highlight")
        check(mc.dirty && enabled(SAFEPDF_CMD_UNDO) && !enabled(SAFEPDF_CMD_REDO),
              "dirty, Undo enabled after the highlight")
        let editItems = mc.bubble.items.map { "\($0.action)" }
        check(editItems == ["color", "comment", "delete"], "edit bubble items \(editItems)")

        // Pixels: the highlight is multiplied into the page in its colour.
        pv.canvas.needsDisplay = true
        if let rep = snapshot(pv.scrollView, scale: 2), let q = hl.quads.first {
            _ = writePNG(rep, "\(dir)/marks-highlight-2x.png")
            let r = pv.canvas.pixelAligned(tr.rect(q)).insetBy(dx: 1, dy: 1)
            if let c = meanRGB(rep, pv, r) {
                say(String(format: "marks: highlight pixels mean r %.2f g %.2f b %.2f", c.r, c.g, c.b))
                check(c.g - c.r > 0.15 && c.g > 0.45, "the highlight's pixels are green")
            } else {
                check(false, "highlight pixels")
            }
        }

        // Recolour through the picker: the colour button opens it, a swatch recolours.
        let depth = m.state.undo_depth
        mc.bubble.press(0)
        check(mc.ui.picker != 0 && !mc.picker.isHidden && mc.picker.items.count == 5, "the colour picker opens")
        mc.picker.press(4)
        check(m.find(hl.id)?.color == Int32(SAFEPDF_COLOR_RED) && m.state.undo_depth == depth + 1 && mc.ui.picker == 0,
              "the picker recoloured the highlight red (one undo step)")

        // A comment on the highlight (the edit bubble's Comment): a note on exactly its quads.
        mc.bubble.press(1)
        let notes = m.list(0).filter { $0.isNote }
        check(notes.count == 1, "one note after Comment")
        guard let c = notes.first else { return (hl.id, nil) }
        check(sameBoxes(c.quads, hl.quads) && c.color == Int32(SAFEPDF_COLOR_RED),
              "the comment is anchored to the highlight's quads, in its colour (quads \(sameBoxes(c.quads, hl.quads)), colour \(c.color))")
        check(mc.noteOpen == c.id && !mc.noteEditor.isShown, "the comment's editor is open (state only, headless)")
        mc.noteSave("a comment")
        // Store.isComment: a note on exactly a highlight's quads, with text.
        check(m.find(c.id)?.text == "a comment" && m.find(c.id)?.isComment == true && mc.noteOpen == nil,
              "⌘Return saves the comment; it is the highlight's comment")
        // Comment again: the existing comment opens, nothing is added.
        mc.selectMark(page: 0, at: centreOf(hl.quads.first), openIt: false)
        let count = m.state.mark_count
        mc.addNote(at: nil)
        check(m.state.mark_count == count && mc.noteOpen == c.id, "Comment on a commented highlight opens its comment")
        mc.noteCloseWithoutSave("a comment")
        check(m.find(c.id)?.text == "a comment", "closing an unchanged comment keeps it")

        // The Highlight tool: a selection is highlighted on release; Escape keeps the tool.
        mc.tool(Int32(SAFEPDF_TOOL_HIGHLIGHT.rawValue))
        check(mc.mode == SAFEPDF_MODE_HIGHLIGHT.rawValue && mc.ui.tool != 0 && mc.ui.popover != 0,
              "the Highlight button without a selection turns the tool and its pop-over on")
        check(mc.pressedTool == SAFEPDF_TOOL_HIGHLIGHT.rawValue, "the Highlight button shows pressed")
        mc.setColor(Int32(SAFEPDF_COLOR_BLUE))
        let k2 = min(sp.cellCount - 1, k + 8)
        let a2 = centre(sp.boxes[k + 1 <= k2 ? k + 1 : k]), z2 = centre(sp.boxes[k2])
        let before = m.list(0).filter { $0.isHighlight }.count
        mc.pointerDown(at: a2, clicks: 1, shift: false)
        mc.pointerDragged(at: z2)
        mc.pointerUp(at: z2)
        let after = m.list(0).filter { $0.isHighlight }
        check(after.count == before + 1 && after.last?.color == Int32(SAFEPDF_COLOR_BLUE),
              "with the Highlight tool on, the release highlights in the current colour")
        check(mc.escape() && mc.ui.popover == 0 && mc.ui.tool != 0, "Escape closes the pop-over; the tool stays")
        check(mc.markSel == nil && mc.bubbleKind == nil, "Escape dismisses the bubble")
        mc.tool(Int32(SAFEPDF_TOOL_SELECT.rawValue))
        check(mc.mode == SAFEPDF_MODE_SELECT.rawValue && mc.ui.tool == 0, "Select text turns the Highlight tool off")
        if let extra = after.last { mc.deleteMark(extra.id) }

        // Escape with only a selection: the bubble goes, nothing transient was open.
        mc.pointerDown(at: a, clicks: 2, shift: false)
        mc.pointerUp(at: a)
        pump(limit: 5) { t.selection != nil }
        check(t.selection != nil && mc.bubbleKind == Int32(SAFEPDF_BUBBLE_FLOAT), "double click selects a word, the bubble shows")
        check(!mc.escape() && t.selection == nil && mc.bubbleKind == nil, "Escape dismisses the bubble and the selection")

        // Cursor over the highlight: the pointing hand (Toolbar.cursorFor .select .mark).
        t.updateCursor(at: tr.view(centreOf(hl.quads.first).x, centreOf(hl.quads.first).y))
        check(t.cursor == SAFEPDF_CURSOR_POINTING_HAND.rawValue, "the cursor over a mark is the pointing hand")
        return (hl.id, c.id)
    }

    // MARK: notes (Marks.noteAnchor; note_close)

    private static func noteChecks(_ mc: MarksController, _ t: TextController, _ pv: PageViewController,
                                   _ tr: PageTransform, empty: CGPoint) {
        guard let m = mc.model, let q = tr.page(empty) else { return }
        let click = CGPoint(x: q.x, y: q.y)
        // The rules: a click inside the selection's boxes comments on it, elsewhere a point.
        let box = safepdf_box(llx: q.x - 5, lly: q.y - 5, urx: q.x + 5, ury: q.y + 5)
        check(MarksModel.noteAnchor(sel: [box], click: click) == Int32(SAFEPDF_ANCHOR_QUADS)
              && MarksModel.noteAnchor(sel: [box], click: CGPoint(x: q.x + 50, y: q.y)) == Int32(SAFEPDF_ANCHOR_POINT)
              && MarksModel.noteAnchor(sel: [box], click: nil) == Int32(SAFEPDF_ANCHOR_QUADS)
              && MarksModel.noteAnchor(sel: [], click: nil) == Int32(SAFEPDF_ANCHOR_NONE),
              "note anchoring rules (Marks.noteAnchor)")
        t.setSelection(nil)
        _ = mc.escape()
        // A note at a point (the context menu's Add note… at an empty spot).
        mc.addNote(at: empty)
        guard let id = mc.noteOpen, let n = m.find(id) else {
            check(false, "Add note at a point opened no note")
            return
        }
        check(n.isNote && n.quads.isEmpty && n.point.map { near($0.x, click.x, 1e-3) && near($0.y, click.y, 1e-3) } == true,
              "the note is anchored at the clicked point")
        // Closing a new note without text deletes it (Store.onUnsavedClose).
        mc.noteCloseWithoutSave("")
        check(m.find(id) == nil, "an empty new note closed without Save is removed")
        mc.addNote(at: empty)
        if let id2 = mc.noteOpen {
            mc.noteCloseWithoutSave("typed, not saved")
            check(m.find(id2)?.text == "typed, not saved", "a new note's typed text is kept when it closes")
            // Escape closes the note editor first (the topmost transient).
            mc.openNote(id2)
            mc.noteEditor.text = "typed, not saved"
            check(mc.escape() && mc.noteOpen == nil, "Escape closes the note editor")
            mc.deleteMark(id2)
        }
    }

    // MARK: free text

    private static func freeTextChecks(_ mc: MarksController, _ pv: PageViewController, _ tr: PageTransform,
                                       empty: CGPoint) {
        guard let m = mc.model else { return }
        mc.tool(Int32(SAFEPDF_TOOL_TEXT.rawValue))
        check(mc.mode == SAFEPDF_MODE_TEXT.rawValue && mc.pressedTool == SAFEPDF_TOOL_TEXT.rawValue && mc.ui.ed_pop != 0,
              "Add text: the mode, its button and its pop-over")
        pv.text.updateCursor(at: empty)
        check(pv.text.cursor == SAFEPDF_CURSOR_IBEAM.rawValue, "the Add text cursor is the I-beam")
        let at = CGPoint(x: empty.x - 120, y: empty.y - 60)
        mc.pointerDown(at: at, clicks: 1, shift: false)
        mc.pointerUp(at: at)
        check(mc.ftEdit != nil && !mc.freeText.isHidden, "a click places a text box")
        mc.freeTextString = "Boxed"
        mc.commitFreeText()
        guard let ft = m.list(0).last, ft.isFreeText else {
            check(false, "no free text after the commit")
            return
        }
        check(ft.text == "Boxed" && ft.size == mc.ui.ft_size && mc.markSel == ft.id, "free text added with the pop-over's size")
        if let p = tr.page(at), let pt = ft.point {
            check(near(pt.x, p.x, 1e-3) && near(pt.y, p.y, 1e-3), "the box's corner is at the click")
        }
        // Edit in place: a double click opens it with its text.
        guard let r = ft.rect else { return }
        let mid = tr.view((r.llx + r.urx) / 2, (r.lly + r.ury) / 2)
        mc.pointerDown(at: mid, clicks: 2, shift: false)
        mc.pointerUp(at: mid)
        check(mc.ftEdit?.id == ft.id && mc.freeTextString == "Boxed", "a double click edits the text box")
        mc.freeTextString = "Boxed 2"
        mc.commitFreeText()
        check(m.find(ft.id)?.text == "Boxed 2", "the edited text is stored")
        // Move by dragging: one translate on release.
        let depth = m.state.undo_depth
        mc.pointerDown(at: mid, clicks: 1, shift: false)
        check(mc.markSel == ft.id, "a press on the text box selects it (\(String(describing: mc.markSel)) at \(mid), box \(r))")
        mc.pointerDragged(at: CGPoint(x: mid.x + 15, y: mid.y))
        mc.pointerDragged(at: CGPoint(x: mid.x + 30, y: mid.y))
        mc.pointerUp(at: CGPoint(x: mid.x + 30, y: mid.y))
        // The page-space distance of 30 view points to the right (the page may be rotated).
        if let p0 = ft.point, let p1 = m.find(ft.id)?.point, let a = tr.page(mid),
           let b = tr.page(CGPoint(x: mid.x + 30, y: mid.y)) {
            let dx = CGFloat(b.x - a.x), dy = CGFloat(b.y - a.y)
            check(near(p1.x - p0.x, dx, 1e-3) && near(p1.y - p0.y, dy, 1e-3) && m.state.undo_depth == depth + 1,
                  "the drag moved the text box by 30 pt (\(p1.x - p0.x), \(p1.y - p0.y) page units, expected \(dx), \(dy); undo \(depth) -> \(m.state.undo_depth))")
        }
        _ = mc.escape()
        mc.tool(Int32(SAFEPDF_TOOL_TEXT.rawValue))
        check(mc.mode == SAFEPDF_MODE_SELECT.rawValue, "the Add text button again ends the mode")
    }

    // MARK: ink

    private static func inkChecks(_ mc: MarksController, _ pv: PageViewController, _ tr: PageTransform,
                                  at: CGPoint, dir: String) {
        guard let m = mc.model else { return }
        mc.tool(Int32(SAFEPDF_TOOL_DRAW.rawValue))
        check(mc.mode == SAFEPDF_MODE_DRAW.rawValue && mc.pressedTool == SAFEPDF_TOOL_DRAW.rawValue, "Draw mode")
        pv.text.updateCursor(at: at)
        check(pv.text.cursor == SAFEPDF_CURSOR_CROSSHAIR.rawValue, "the Draw cursor is the crosshair")
        let red: UInt32 = MarksPalette.editorColors.count > 1 ? MarksPalette.editorColors[1] : 0xD70022
        mc.editorColor(red)
        mc.slide(row: 1, value: 4, ended: true)
        func stroke(_ dy: CGFloat) {
            let p0 = CGPoint(x: at.x, y: at.y + dy)
            mc.pointerDown(at: p0, clicks: 1, shift: false)
            for i in 1...6 { mc.pointerDragged(at: CGPoint(x: p0.x + CGFloat(i) * 10, y: p0.y)) }
            mc.pointerUp(at: CGPoint(x: p0.x + 60, y: p0.y))
        }
        let depth = m.state.undo_depth
        stroke(0)
        guard let ink = m.list(0).last, ink.isInk else {
            check(false, "no drawing after a stroke")
            return
        }
        check(ink.strokes.count == 1 && ink.size == 4 && ink.opacity == mc.ui.ink_opacity && mc.inkSession == ink.id,
              "one stroke, the pop-over's thickness and opacity")
        stroke(12)
        check(m.find(ink.id)?.strokes.count == 2 && m.list(0).filter({ $0.isInk }).count == 1
              && m.state.undo_depth == depth + 2,
              "the second stroke joins the drawing (one undo step per stroke)")
        // Pixels: the stroke in the chosen colour.
        pv.canvas.needsDisplay = true
        if let rep = snapshot(pv.scrollView, scale: 2) {
            _ = writePNG(rep, "\(dir)/marks-ink-2x.png")
            let r = CGRect(x: at.x + 20, y: at.y - 1, width: 20, height: 2)
            if let c = meanRGB(rep, pv, r) {
                say(String(format: "marks: ink pixels mean r %.2f g %.2f b %.2f", c.r, c.g, c.b))
                check(c.r > 0.6 && c.g < 0.35 && c.b < 0.4, "the stroke's pixels are red")
            }
        }
        // A slider drag (several steps) is one undo step.
        let d2 = m.state.undo_depth
        mc.slide(row: 1, value: 6, ended: false)
        mc.slide(row: 1, value: 8, ended: false)
        mc.slide(row: 1, value: 9, ended: true)
        check(m.find(ink.id)?.size == 9 && m.state.undo_depth == d2 + 1, "a thickness drag is one undo step")
        mc.undoRedo(undo: true)
        check(m.find(ink.id)?.size == 4, "undo restores the thickness")
        _ = mc.escape()
        check(mc.inkSession == nil && mc.mode == SAFEPDF_MODE_DRAW.rawValue, "Escape ends the drawing session, the mode stays")
        stroke(30)
        check(m.list(0).filter({ $0.isInk }).count == 2, "after Escape a stroke starts a new drawing")
        mc.tool(Int32(SAFEPDF_TOOL_SELECT.rawValue))
    }

    // MARK: undo / redo

    private static func undoChecks(_ mc: MarksController, _ m: MarksModel) {
        let all = m.listAll()
        let st = m.state
        say("marks: \(all.count) marks, undo depth \(st.undo_depth), pending \(st.pending)")
        var n = 0
        while m.state.can_undo != 0 && n < 200 {
            mc.undoRedo(undo: true)
            n += 1
        }
        let clean = m.state
        check(clean.dirty == 0 && m.listAll().isEmpty && clean.can_redo != 0,
              "undo all: clean, no marks (\(m.listAll().count)), redo possible")
        var k = 0
        while m.state.can_redo != 0 && k < 200 {
            mc.undoRedo(undo: false)
            k += 1
        }
        check(k == n && m.listAll() == all && m.state.dirty != 0, "redo all restores every mark (\(k) of \(n) steps)")
    }

    // MARK: saved marks (a file written by safepdf_marks_save_build, reopened)

    private static func savedChecks(_ mc: MarksController, _ pv: PageViewController, _ doc: Document, dir: String) {
        guard let m = mc.model else { return }
        let count = m.listAll().count
        var r = safepdf_save_result()
        var err: UnsafeMutablePointer<CChar>? = nil
        var seed = [UInt8](repeating: 7, count: 64)
        let rc = safepdf_marks_save_build(m.handle, &seed, seed.count, "D:20261124120000Z", 0, &r, &err)
        guard rc == Int32(SAFEPDF_SAVE_OK), let bytes = r.bytes else {
            check(false, "save build: \(rc) \(Core.take(err) ?? "")")
            return
        }
        if let err { free(err) }
        let data = Data(bytes: bytes, count: r.size)
        safepdf_free_save_result(&r)
        let out = "\(dir)/marks-saved.pdf"
        guard (try? data.write(to: URL(fileURLWithPath: out))) != nil else {
            check(false, "write \(out)")
            return
        }
        let saved: Document
        do {
            saved = try Document(url: URL(fileURLWithPath: out))
        } catch {
            check(false, "reopen \(out): \(error.message)")
            return
        }
        pv.show(saved)
        waitRenders(pv)
        guard let m2 = mc.model else {
            check(false, "no store for the saved file")
            return
        }
        let ms = m2.listAll()
        say("marks: saved file: \(ms.count) marks listed, states \(Set(ms.map(\.state)))")
        check(ms.count == count && ms.allSatisfy({ $0.state == Int32(SAFEPDF_MARK_SAVED) }) && m2.state.dirty == 0,
              "the saved file's \(count) marks are listed as saved (\(ms.count))")
        if let h = ms.first(where: { $0.isHighlight }) {
            _ = m2.recolor(h.id, Int32(SAFEPDF_COLOR_PINK))
            check(m2.find(h.id)?.state == Int32(SAFEPDF_MARK_SAVED_CHANGED) && mc.dirty,
                  "a recoloured saved highlight is saved-changed, the document dirty")
            mc.undoRedo(undo: true)
            check(!mc.dirty, "undo back to the file's state is clean")
        }
        pv.show(doc)
        waitRenders(pv)
    }
}
