// SidebarModel.swift — the sidebar's rules through the C API (task 11.3d2): which panels a
// document shows, the panel a /PageMode opens, the toggle's pick, thumbnail sizes and the lazy
// thumbnail band, the outline tree, attachment save targets, the 12.5 identity line, and the
// layers state the renders use. Plan.md §6 Phase 11; docs/macos-design.md §3 decision 1: every
// rule is one call into the Lean function the Tk viewer uses (App.Sidebar, App.Attach,
// Viewer.identityLine through SafePdf/Shell/Ffi/Sidebar.lean); Swift only converts values.

import CoreGraphics
import Foundation
import SafePdfC

/// A layers state (optional content groups and those that are OFF) in Swift storage; passed to
/// the C API as a borrowed `safepdf_layers_state`.
struct LayersState {
    var known: [safepdf_oc_key] = []
    var off: [safepdf_oc_key] = []

    init(known: [safepdf_oc_key] = [], off: [safepdf_oc_key] = []) {
        self.known = known
        self.off = off
    }

    /// Copies a C state (the caller still frees it).
    init(_ c: safepdf_layers_state) {
        if let k = c.known { known = Array(UnsafeBufferPointer(start: k, count: c.known_count)) }
        if let o = c.off { off = Array(UnsafeBufferPointer(start: o, count: c.off_count)) }
    }

    /// Whether group `k` is ON (OptionalContent.State.isOn: not in the OFF list).
    func isOn(_ k: safepdf_oc_key) -> Bool { !off.contains { $0.num == k.num && $0.gen == k.gen } }

    /// The same groups OFF (order ignored).
    func same(_ o: LayersState) -> Bool {
        func set(_ ks: [safepdf_oc_key]) -> Set<String> { Set(ks.map { "\($0.num) \($0.gen)" }) }
        return set(known) == set(o.known) && set(off) == set(o.off)
    }

    /// Calls `body` with the state as a borrowed C struct.
    func withC<T>(_ body: (UnsafePointer<safepdf_layers_state>) -> T) -> T {
        var k = known, o = off
        return k.withUnsafeMutableBufferPointer { kp in
            o.withUnsafeMutableBufferPointer { op in
                var st = safepdf_layers_state(known: kp.baseAddress, known_count: kp.count,
                                              off: op.baseAddress, off_count: op.count)
                return withUnsafePointer(to: &st) { body($0) }
            }
        }
    }
}

/// What activating an outline item does, copied from a `safepdf_action`.
struct NavAction {
    let kind: safepdf_action_kind
    let page: Int
    let left: Double?
    let top: Double?
    let text: String

    init(_ a: safepdf_action) {
        kind = a.kind
        page = a.page
        left = a.has_left != 0 ? a.left : nil
        top = a.has_top != 0 ? a.top : nil
        text = Core.string(a.text)
    }
}

/// The sidebar's rules (App.Sidebar through safepdf_core.h's sidebar section).
@MainActor enum SidebarRules {
    /// The panels in switcher order: the panel, its SF Symbol, the tooltip (PDF.js's button
    /// titles, Sidebar.panels) and the heading.
    static let panels: [(panel: safepdf_panel, symbol: String, tip: String, title: String)] = [
        (SAFEPDF_PANEL_THUMBNAILS, "square.grid.2x2", "Show Thumbnails", "Thumbnails"),
        (SAFEPDF_PANEL_OUTLINE, "list.bullet.indent", "Show Document Outline", "Document outline"),
        (SAFEPDF_PANEL_ATTACHMENTS, "paperclip", "Show Attachments", "Attachments"),
        (SAFEPDF_PANEL_LAYERS, "square.3.layers.3d", "Show Layers", "Layers"),
    ]

    static func content(outline: Bool, attachments: Bool, layers: Bool) -> safepdf_sidebar_content {
        safepdf_sidebar_content(has_outline: outline, has_attachments: attachments, has_layers: layers)
    }

    /// Sidebar.onLoad: the panel the sidebar opens with (nil: closed).
    static func onLoad(pageMode: Int32, _ c: safepdf_sidebar_content) -> safepdf_panel? {
        let p = safepdf_sidebar_on_load(pageMode, c)
        return p == SAFEPDF_PANEL_NONE ? nil : p
    }

    /// Sidebar.buttons: whether a panel's switcher button shows.
    static func available(_ p: safepdf_panel, _ c: safepdf_sidebar_content) -> Bool {
        safepdf_sidebar_available(p, c)
    }

    /// Sidebar.pick: the panel the toggle opens.
    static func pick(last: safepdf_panel, _ c: safepdf_sidebar_content) -> safepdf_panel {
        safepdf_sidebar_pick(last, c)
    }

    /// The thumbnail constants (Sidebar.thumbW, …); PDF.js's values if the call fails.
    static let constants: safepdf_thumb_constants = {
        var k = safepdf_thumb_constants()
        if safepdf_sidebar_constants(&k) != 0 {
            k = safepdf_thumb_constants(width: 98, top: 12, label_h: 20, gap: 14, margin: 3, budget: 40)
        }
        return k
    }()

    /// A page's thumbnail size (pixels at 1x) and zoom (pixels per point at 1x).
    static func thumb(_ doc: Document, page: Int, quarters: UInt32) -> safepdf_thumb? {
        var t = safepdf_thumb()
        return safepdf_doc_thumb(doc.handle, page, quarters % 4, &t) == 0 ? t : nil
    }

    /// The thumbnail scale (0 full, 1 half, 2 quarter, 3 eighth zoom) of an image of w x h pixels.
    static func scale(w: Int, h: Int) -> Int {
        Int(safepdf_sidebar_thumb_scale(max(0, w), max(0, h)))
    }

    /// Sidebar.thumbLayout: each image's top and the panel's height.
    static func layout(heights: [UInt32]) -> (ys: [UInt64], total: UInt64)? {
        var ys = [UInt64](repeating: 0, count: heights.count)
        var total: UInt64 = 0
        let rc = heights.withUnsafeBufferPointer { hp in
            ys.withUnsafeMutableBufferPointer { yp in
                safepdf_sidebar_thumb_layout(hp.baseAddress, hp.count, constants.width, yp.baseAddress, &total)
            }
        }
        return rc == 0 ? (ys, total) : nil
    }

    /// Sidebar.thumbsWanted for the band [top, bottom) (pixels at 1x = points).
    static func wanted(heights: [UInt32], top: UInt64, bottom: UInt64) -> [Int] {
        var out: UnsafeMutablePointer<Int>? = nil
        var n = 0
        let rc = heights.withUnsafeBufferPointer { hp in
            safepdf_sidebar_thumbs_wanted(hp.baseAddress, hp.count, constants.width, top, bottom, &out, &n)
        }
        defer { free(out) }
        guard rc == 0, let out else { return [] }
        return Array(UnsafeBufferPointer(start: out, count: n))
    }

    /// Sidebar.thumbEvict: the thumbnails to drop, farthest first.
    static func evict(held: [Int], wanted: [Int], center: Int) -> [Int] {
        var out: UnsafeMutablePointer<Int>? = nil
        var n = 0
        let rc = held.withUnsafeBufferPointer { hp in
            wanted.withUnsafeBufferPointer { wp in
                safepdf_sidebar_thumb_evict(hp.baseAddress, hp.count, wp.baseAddress, wp.count, max(0, center), &out, &n)
            }
        }
        defer { free(out) }
        guard rc == 0, let out else { return [] }
        return Array(UnsafeBufferPointer(start: out, count: n))
    }

    /// Sidebar.rows / initialOpen: each row's parent, children and initial open state.
    static func tree(depths: [Int], open: [Bool]) -> [safepdf_tree_row]? {
        guard depths.count == open.count else { return nil }
        if depths.isEmpty { return [] }
        var rows = [safepdf_tree_row](repeating: safepdf_tree_row(), count: depths.count)
        let rc = depths.withUnsafeBufferPointer { dp in
            open.withUnsafeBufferPointer { op in
                rows.withUnsafeMutableBufferPointer { rp in
                    safepdf_sidebar_tree(dp.baseAddress, op.baseAddress, dp.count, rp.baseAddress)
                }
            }
        }
        return rc == 0 ? rows : nil
    }

    /// Attach.targetProblem for a chosen file (nil: it can take the attachment).
    static func targetProblem(_ url: URL, opened: URL) -> String? {
        let fm = FileManager.default
        var isDir: ObjCBool = false
        let exists = fm.fileExists(atPath: url.path, isDirectory: &isDir)
        let dir = url.deletingLastPathComponent().path
        let same = url.standardizedFileURL.resolvingSymlinksInPath().path ==
            opened.standardizedFileURL.resolvingSymlinksInPath().path
        return Core.take(safepdf_attachment_target_problem(
            url.lastPathComponent, exists && isDir.boolValue, exists,
            exists && fm.isWritableFile(atPath: url.path), fm.isWritableFile(atPath: dir), same))
    }

    /// Links.describe: what an action does, in words (an outline item that is not followed).
    static func describe(_ a: NavAction, labels: [String], pages: Int) -> String {
        a.text.withCString { t in
            var c = safepdf_action()
            c.kind = a.kind
            c.page = a.page
            c.text = t
            return PageText.withCStrings(labels) { ptrs, n in
                Core.take(safepdf_action_describe(&c, ptrs, n, pages))
            } ?? "link without a destination"
        }
    }

    /// The trusted identity line (Viewer.identityLine): the file's name and path, never /Title.
    static func identityLine(path: String?) -> String {
        Core.take(safepdf_identity_line(path, false)) ?? "SafePDF"
    }
}
