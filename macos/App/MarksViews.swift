// MarksViews.swift — the views of the marks (task 11.3e1): the selection bubble and its colour
// picker (a small glass bar, NSGlassEffectView on macOS 26, a material elsewhere), the note
// editor (an NSPopover), the free-text box edited in place, and the tools' pop-overs (Highlight
// colour; Add text / Draw parameters). Plan.md §6 Phases 9–11; docs/macos-design.md §2 (native
// controls) and the Tk viewer's Bubble.lean (items, order, tooltips; placement by
// safepdf_marks_bubble_place). Nothing here decides what a button does: each one calls back
// into MarksController, which calls the exported rules.

import AppKit
import SafePdfC

// MARK: - the bubble

/// The selection bubble / edit bubble / editor bubble, or (`configurePicker`) the colour picker
/// under the edit bubble. A subview of the page canvas, so it scrolls with the page.
final class BubbleView: NSView {
    /// What a button does.
    enum Action: Equatable { case highlight, color, pick, comment, copy, delete }

    /// Called with a button's action and its colour (highlight, pick) or -1.
    var onButton: ((Action, Int32) -> Void)?
    /// The kind shown (SAFEPDF_BUBBLE_*; -1 for the picker).
    private(set) var kind: Int32 = -1
    /// The buttons, left to right: action, colour, tooltip.
    private(set) var items: [(action: Action, color: Int32, tip: String)] = []
    private var signature = ""
    private let stack = NSStackView()
    private var background: NSView?
    static let pad: CGFloat = 3
    static let button: CGFloat = 28
    static let spacing: CGFloat = 2

    override var isFlipped: Bool { true }

    init() {
        super.init(frame: .zero)
        stack.orientation = .horizontal
        stack.spacing = Self.spacing
        stack.edgeInsets = NSEdgeInsets(top: Self.pad, left: Self.pad, bottom: Self.pad, right: Self.pad)
        let bg: NSView
        #if compiler(>=6.2) // the macOS 26 SDK: Liquid Glass
        if #available(macOS 26, *) {
            let g = NSGlassEffectView()
            g.cornerRadius = (Self.button + 2 * Self.pad) / 2
            g.contentView = stack
            bg = g
        } else {
            bg = Self.material(stack)
        }
        #else
        bg = Self.material(stack)
        #endif
        bg.translatesAutoresizingMaskIntoConstraints = true
        bg.autoresizingMask = [.width, .height]
        addSubview(bg)
        background = bg
        setAccessibilityElement(true)
        setAccessibilityRole(.toolbar)
        setAccessibilityLabel("Selection bubble")
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    /// The fallback before macOS 26: a popover material with rounded corners and a hairline.
    private static func material(_ content: NSView) -> NSView {
        let v = NSVisualEffectView()
        v.material = .popover
        v.blendingMode = .withinWindow
        v.state = .active
        v.wantsLayer = true
        v.layer?.cornerRadius = 8
        v.layer?.masksToBounds = true
        v.layer?.borderWidth = 1
        v.layer?.borderColor = NSColor.separatorColor.cgColor
        content.translatesAutoresizingMaskIntoConstraints = true
        content.autoresizingMask = [.width, .height]
        v.addSubview(content)
        return v
    }

    override func resizeSubviews(withOldSize oldSize: NSSize) {
        super.resizeSubviews(withOldSize: oldSize)
        background?.frame = bounds
        if !(background is NSVisualEffectView) { return }
        stack.frame = bounds
    }

    /// Shows the buttons of bubble `kind` (its layout's buttons in order: Highlight as the five
    /// colours, the colour swatch of the edit bubble, Comment, Delete; Copy after the float
    /// bubble's, the native shell's addition).
    func configure(kind: Int32, layout: safepdf_bubble_layout, markColor: Int32, pickerOpen: Bool) {
        var its: [(Action, Int32, String)] = []
        let buttons = withUnsafeBytes(of: layout.buttons) { raw in
            Array(raw.bindMemory(to: safepdf_bubble_button.self).prefix(layout.count))
        }
        for b in buttons {
            let tip = withUnsafeBytes(of: b.tip) { raw in
                String(decoding: raw.prefix { $0 != 0 }, as: UTF8.self)
            }
            switch b.button {
            case Int32(SAFEPDF_BTN_HIGHLIGHT):
                for c in 0..<5 { its.append((.highlight, Int32(c), "\(tip): \(MarksPalette.labels[c])")) }
            case Int32(SAFEPDF_BTN_COLOR): its.append((.color, markColor, tip))
            case Int32(SAFEPDF_BTN_COMMENT): its.append((.comment, -1, tip))
            case Int32(SAFEPDF_BTN_DELETE): its.append((.delete, -1, tip))
            default: break
            }
        }
        if kind == Int32(SAFEPDF_BUBBLE_FLOAT) { its.append((.copy, -1, "Copy")) }
        build(kind: kind, its, extra: pickerOpen ? "open" : "")
    }

    /// Shows the colour picker (Bubble.pickerSwatches: the five colours, the current one ringed).
    func configurePicker(current: Int32) {
        build(kind: -1, (0..<5).map { (.pick, Int32($0), MarksPalette.labels[$0]) }, extra: "\(current)", ring: current)
    }

    private func build(kind: Int32, _ its: [(Action, Int32, String)], extra: String, ring: Int32 = -1) {
        let sig = "\(kind)|\(extra)|" + its.map { "\($0.0):\($0.1)" }.joined(separator: ",")
        self.kind = kind
        items = its.map { (action: $0.0, color: $0.1, tip: $0.2) }
        guard sig != signature else { return }
        signature = sig
        for v in stack.arrangedSubviews { stack.removeArrangedSubview(v); v.removeFromSuperview() }
        for (i, it) in its.enumerated() {
            if i > 0, it.0 != its[i - 1].0 { // dividers between groups (Bubble.Kind.dividers)
                let d = NSBox()
                d.boxType = .separator
                d.widthAnchor.constraint(equalToConstant: 1).isActive = true
                d.heightAnchor.constraint(equalToConstant: Self.button - 8).isActive = true
                stack.addArrangedSubview(d)
            }
            let b = NSButton(image: image(it.0, it.1, ring: ring == it.1), target: self, action: #selector(pressed(_:)))
            b.isBordered = false
            b.bezelStyle = .accessoryBarAction
            b.tag = i
            b.toolTip = it.2
            b.setAccessibilityLabel(it.2)
            b.imageScaling = .scaleNone
            b.widthAnchor.constraint(equalToConstant: it.0 == .color ? 40 : Self.button).isActive = true
            b.heightAnchor.constraint(equalToConstant: Self.button).isActive = true
            stack.addArrangedSubview(b)
        }
    }

    private func image(_ a: Action, _ color: Int32, ring: Bool) -> NSImage {
        func symbol(_ name: String) -> NSImage {
            NSImage(systemSymbolName: name, accessibilityDescription: nil) ?? NSImage()
        }
        switch a {
        case .highlight, .pick:
            let base = MarksMenus.swatch(MarksPalette.color(color), size: 16)
            guard ring else { return base }
            return NSImage(size: NSSize(width: 22, height: 22), flipped: false) { r in
                NSColor.controlAccentColor.setStroke()
                let p = NSBezierPath(ovalIn: r.insetBy(dx: 1, dy: 1))
                p.lineWidth = 2
                p.stroke()
                base.draw(in: r.insetBy(dx: 3, dy: 3))
                return true
            }
        case .color:
            let sw = MarksMenus.swatch(MarksPalette.color(color), size: 16)
            let chev = symbol("chevron.down")
            return NSImage(size: NSSize(width: 34, height: 16), flipped: false) { _ in
                sw.draw(in: NSRect(x: 2, y: 0, width: 16, height: 16))
                chev.draw(in: NSRect(x: 22, y: 3, width: 10, height: 10))
                return true
            }
        case .comment: return symbol("text.bubble")
        case .copy: return symbol("doc.on.doc")
        case .delete: return symbol("trash")
        }
    }

    @objc private func pressed(_ sender: NSButton) {
        guard sender.tag >= 0, sender.tag < items.count else { return }
        let it = items[sender.tag]
        onButton?(it.action, it.color)
    }

    /// Presses button `i` (the self-test's click).
    func press(_ i: Int) {
        guard i >= 0, i < items.count else { return }
        onButton?(items[i].action, items[i].color)
    }

    /// The width and height the buttons need.
    override var fittingSize: NSSize {
        var w = 2 * Self.pad
        for (i, it) in items.enumerated() {
            if i > 0 { w += Self.spacing }
            if i > 0, it.action != items[i - 1].action { w += 1 + Self.spacing }
            w += it.action == .color ? 40 : Self.button
        }
        return NSSize(width: w, height: Self.button + 2 * Self.pad)
    }

    func hide() { isHidden = true }
}

// MARK: - the note editor

/// The note editor: an NSPopover anchored at the note's icon, with the text, Delete, Cancel and
/// Save (⌘Return). Closing it without Save (Escape, ⌘., a click away) reports the text shown.
@MainActor final class NoteEditor: NSObject, NSPopoverDelegate {
    var onSave: ((String) -> Void)?
    var onClose: ((String) -> Void)?
    var onDelete: (() -> Void)?
    private var popover: NSPopover?
    private let textView = NSTextView(frame: NSRect(x: 0, y: 0, width: 260, height: 120))
    private let titleLabel = NSTextField(labelWithString: "Note")
    private var closingQuietly = false

    /// The text shown (kept also while no popover is shown: the headless self-test).
    var text: String {
        get { textView.string }
        set { textView.string = newValue }
    }

    var isShown: Bool { popover?.isShown ?? false }

    private func makePopover() -> NSPopover {
        if let p = popover { return p }
        let vc = NoteEditorController()
        vc.onCancel = { [weak self] in self?.closeWithoutSave() }
        let root = NSView(frame: NSRect(x: 0, y: 0, width: 284, height: 190))
        titleLabel.font = .boldSystemFont(ofSize: NSFont.systemFontSize)
        let scroll = NSScrollView()
        scroll.hasVerticalScroller = true
        scroll.borderType = .bezelBorder
        textView.isRichText = false
        textView.allowsUndo = true
        textView.font = .systemFont(ofSize: NSFont.systemFontSize)
        textView.isVerticallyResizable = true
        textView.autoresizingMask = [.width]
        textView.setAccessibilityLabel("Note text")
        scroll.documentView = textView
        let save = NSButton(title: "Save", target: self, action: #selector(saveClicked))
        save.keyEquivalent = "\r"
        save.keyEquivalentModifierMask = [.command]
        save.toolTip = "Save (⌘Return)"
        let cancel = NSButton(title: "Cancel", target: self, action: #selector(cancelClicked))
        cancel.keyEquivalent = "\u{1b}"
        let delete = NSButton(title: "Delete", target: self, action: #selector(deleteClicked))
        let buttons = NSStackView(views: [delete, NSView(), cancel, save])
        buttons.orientation = .horizontal
        let stack = NSStackView(views: [titleLabel, scroll, buttons])
        stack.orientation = .vertical
        stack.alignment = .leading
        stack.edgeInsets = NSEdgeInsets(top: 10, left: 12, bottom: 10, right: 12)
        stack.translatesAutoresizingMaskIntoConstraints = false
        root.addSubview(stack)
        NSLayoutConstraint.activate([
            stack.leadingAnchor.constraint(equalTo: root.leadingAnchor),
            stack.trailingAnchor.constraint(equalTo: root.trailingAnchor),
            stack.topAnchor.constraint(equalTo: root.topAnchor),
            stack.bottomAnchor.constraint(equalTo: root.bottomAnchor),
            scroll.widthAnchor.constraint(equalTo: stack.widthAnchor, constant: -24),
            scroll.heightAnchor.constraint(equalToConstant: 110),
            buttons.widthAnchor.constraint(equalTo: scroll.widthAnchor),
        ])
        vc.view = root
        let p = NSPopover()
        p.contentViewController = vc
        p.behavior = .transient
        p.delegate = self
        popover = p
        return p
    }

    /// Shows the editor next to `rect` (canvas points) of `view`. Never called headless.
    func show(relativeTo rect: CGRect, of view: NSView, title: String) {
        guard view.window != nil else { return }
        let p = makePopover()
        titleLabel.stringValue = title
        if !p.isShown { p.show(relativeTo: rect, of: view, preferredEdge: .maxX) }
        p.contentViewController?.view.window?.makeFirstResponder(textView)
    }

    /// Closes the popover without reporting anything (the controller already acted).
    func close() {
        guard let p = popover, p.isShown else { return }
        closingQuietly = true
        p.performClose(nil)
        closingQuietly = false
    }

    private func closeWithoutSave() {
        let shown = text
        close()
        onClose?(shown)
    }

    @objc private func saveClicked() {
        let t = text
        onSave?(t)
    }

    @objc private func cancelClicked() { closeWithoutSave() }

    @objc private func deleteClicked() { onDelete?() }

    /// A click away (or the system) closes the popover: as closing without Save.
    func popoverDidClose(_ notification: Notification) {
        if !closingQuietly { onClose?(text) }
    }
}

/// The note editor's view controller: ⌘. (cancelOperation) closes without Save.
final class NoteEditorController: NSViewController {
    var onCancel: (() -> Void)?

    override func cancelOperation(_ sender: Any?) { onCancel?() }
}

// MARK: - the free-text box

/// The text box of Add text, edited in place over the page (PDF.js's FreeText editor): a
/// borderless text view with a dashed outline; Escape commits it (as a click elsewhere).
final class FreeTextBox: NSView, NSTextViewDelegate {
    let textView = FreeTextView(frame: NSRect(x: 0, y: 0, width: 40, height: 20))
    var onCommit: (() -> Void)?
    private var lineFactor: CGFloat = 1.35
    private var fontSize: CGFloat = 10

    override var isFlipped: Bool { true }

    init() {
        super.init(frame: .zero)
        textView.isRichText = false
        textView.drawsBackground = false
        textView.allowsUndo = true
        textView.textContainerInset = .zero
        textView.textContainer?.lineFragmentPadding = 0
        textView.isHorizontallyResizable = true
        textView.isVerticallyResizable = true
        textView.delegate = self
        textView.onEscape = { [weak self] in self?.onCommit?() }
        textView.setAccessibilityLabel("Text box")
        addSubview(textView)
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) { fatalError("init(coder:) is not used") }

    var string: String {
        get { textView.string }
        set {
            textView.string = newValue
            fit()
        }
    }

    /// Places the box with its text's top-left corner at `corner` (canvas points).
    func place(at corner: CGPoint, fontSize: CGFloat, color: NSColor, lineFactor: CGFloat) {
        self.lineFactor = lineFactor
        self.fontSize = max(1, fontSize)
        let font = NSFont(name: "Helvetica", size: self.fontSize) ?? .systemFont(ofSize: self.fontSize)
        textView.font = font
        textView.textColor = color
        textView.insertionPointColor = color
        let para = NSMutableParagraphStyle()
        para.minimumLineHeight = self.fontSize * lineFactor
        para.maximumLineHeight = self.fontSize * lineFactor
        textView.defaultParagraphStyle = para
        textView.typingAttributes = [.font: font, .foregroundColor: color, .paragraphStyle: para]
        frame.origin = CGPoint(x: corner.x - 2, y: corner.y - 2)
        isHidden = false
        fit()
    }

    private func fit() {
        let lines = max(1, textView.string.components(separatedBy: "\n").count)
        let font = textView.font ?? .systemFont(ofSize: fontSize)
        var w = fontSize * 2
        for l in textView.string.components(separatedBy: "\n") {
            w = max(w, (l as NSString).size(withAttributes: [.font: font]).width + fontSize)
        }
        let h = CGFloat(lines) * fontSize * lineFactor + 2
        textView.frame = CGRect(x: 2, y: 2, width: w, height: h)
        setFrameSize(CGSize(width: w + 4, height: h + 4))
        needsDisplay = true
    }

    func textDidChange(_ notification: Notification) { fit() }

    func close() {
        isHidden = true
        textView.string = ""
    }

    override func draw(_ dirtyRect: NSRect) {
        let p = NSBezierPath(rect: bounds.insetBy(dx: 0.5, dy: 0.5))
        p.setLineDash([4, 2], count: 2, phase: 0)
        NSColor.controlAccentColor.setStroke()
        p.stroke()
    }
}

/// The text view of the free-text box: Escape commits.
final class FreeTextView: NSTextView {
    var onEscape: (() -> Void)?

    override func cancelOperation(_ sender: Any?) { onEscape?() }

    override func complete(_ sender: Any?) { onEscape?() }
}

// MARK: - the tools' pop-overs

/// The Highlight pop-over ("Highlight color" swatches, the current one ringed; "Show all") and
/// the Add text / Draw pop-over (colours, Font size / Thickness, Opacity), anchored to their
/// toolbar buttons (NSPopover, transient: a click away closes them, as Toolbar.Transient).
@MainActor final class ToolPopovers: NSObject, NSPopoverDelegate {
    var onColor: ((Int32) -> Void)?
    var onShowAll: (() -> Void)?
    var onEditorColor: ((UInt32) -> Void)?
    var onSlider: ((Int, UInt32, Bool) -> Void)?
    /// A pop-over closed by itself (true: the Add text / Draw one).
    var onClosed: ((Bool) -> Void)?
    private var hl: NSPopover?
    private var ed: NSPopover?
    private var edDraw = false
    private var quiet = false

    func showHighlight(at item: NSToolbarItem, color: Int32, showAll: Bool) {
        let p = hl ?? NSPopover()
        p.behavior = .transient
        p.delegate = self
        p.contentViewController = highlightContent(color: color, showAll: showAll)
        hl = p
        if !p.isShown { p.show(relativeTo: item) }
    }

    func closeHighlight() { close(hl) }

    func showEditor(at item: NSToolbarItem, draw: Bool, ui: safepdf_tool_ui) {
        if let e = ed, e.isShown, edDraw != draw { close(e) }
        let p = ed ?? NSPopover()
        p.behavior = .transient
        p.delegate = self
        p.contentViewController = editorContent(draw: draw, ui: ui)
        edDraw = draw
        ed = p
        if !p.isShown { p.show(relativeTo: item) }
    }

    func closeEditor() { close(ed) }

    private func close(_ p: NSPopover?) {
        guard let p, p.isShown else { return }
        quiet = true
        p.performClose(nil)
        quiet = false
    }

    func popoverDidClose(_ notification: Notification) {
        guard !quiet, let p = notification.object as? NSPopover else { return }
        onClosed?(p === ed)
    }

    private func label(_ s: String) -> NSTextField {
        let l = NSTextField(labelWithString: s)
        l.font = .systemFont(ofSize: NSFont.smallSystemFontSize, weight: .semibold)
        l.textColor = .secondaryLabelColor
        return l
    }

    private func controller(_ views: [NSView]) -> NSViewController {
        let stack = NSStackView(views: views)
        stack.orientation = .vertical
        stack.alignment = .leading
        stack.spacing = 8
        stack.edgeInsets = NSEdgeInsets(top: 12, left: 12, bottom: 12, right: 12)
        let vc = NSViewController()
        vc.view = stack
        vc.preferredContentSize = NSSize(width: 220, height: stack.fittingSize.height)
        return vc
    }

    private func highlightContent(color: Int32, showAll: Bool) -> NSViewController {
        var swatches: [NSView] = []
        for c in 0..<5 {
            let b = NSButton(image: MarksMenus.swatch(MarksPalette.color(Int32(c)), size: c == Int(color) ? 24 : 20),
                             target: self, action: #selector(hlColor(_:)))
            b.isBordered = false
            b.tag = c
            b.toolTip = MarksPalette.labels[c]
            b.setAccessibilityLabel(MarksPalette.labels[c])
            if c == Int(color) { b.state = .on }
            swatches.append(b)
        }
        let row = NSStackView(views: swatches)
        row.spacing = 14
        let toggle = NSSwitch()
        toggle.state = showAll ? .on : .off
        toggle.target = self
        toggle.action = #selector(showAllToggled(_:))
        let showRow = NSStackView(views: [label("Show all"), NSView(), toggle])
        showRow.orientation = .horizontal
        return controller([label("Highlight color"), row, showRow])
    }

    private func editorContent(draw: Bool, ui: safepdf_tool_ui) -> NSViewController {
        let current = draw ? ui.ink_rgb : ui.ft_rgb
        var swatches: [NSView] = []
        for (i, rgb) in MarksPalette.editorColors.enumerated() {
            let b = NSButton(image: MarksMenus.swatch(MarksPalette.nsColor(rgb: rgb), size: rgb == current ? 22 : 18),
                             target: self, action: #selector(edColor(_:)))
            b.isBordered = false
            b.tag = i
            b.toolTip = String(format: "#%06X", rgb)
            swatches.append(b)
        }
        let row = NSStackView(views: swatches)
        row.spacing = 10
        var views: [NSView] = [label(draw ? "Color" : "Font color"), row]
        guard let p = MarksPalette.params else { return controller(views) }
        func slider(_ row: Int, _ lo: UInt32, _ hi: UInt32, _ step: UInt32, _ v: UInt32) -> NSSlider {
            let s = NSSlider(value: Double(v), minValue: Double(lo), maxValue: Double(hi), target: self,
                             action: #selector(slid(_:)))
            s.tag = row
            s.isContinuous = true
            if step > 1 {
                s.numberOfTickMarks = Int((hi - lo) / step) + 1
                s.allowsTickMarkValuesOnly = true
            }
            s.widthAnchor.constraint(equalToConstant: 196).isActive = true
            return s
        }
        if draw {
            views += [label("Thickness"), slider(1, p.width_min, p.width_max, p.width_step, ui.ink_thick),
                      label("Opacity"), slider(2, p.opacity_min, p.opacity_max, p.opacity_step, ui.ink_opacity)]
        } else {
            views += [label("Font size"), slider(1, p.font_min, p.font_max, p.font_step, ui.ft_size)]
        }
        return controller(views)
    }

    @objc private func hlColor(_ sender: NSButton) { onColor?(Int32(sender.tag)) }

    @objc private func showAllToggled(_ sender: NSSwitch) { onShowAll?() }

    @objc private func edColor(_ sender: NSButton) {
        let cs = MarksPalette.editorColors
        guard sender.tag >= 0, sender.tag < cs.count else { return }
        onEditorColor?(cs[sender.tag])
    }

    @objc private func slid(_ sender: NSSlider) {
        let ended = NSApp.currentEvent?.type == .leftMouseUp
        let v = UInt32(clamping: Int(max(0, sender.doubleValue.rounded())))
        onSlider?(sender.tag, v, ended)
    }
}
