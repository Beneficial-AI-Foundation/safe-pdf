// ZoomModel.swift — the zoom and rotation rules of the Tk viewer, called through
// safepdf_view.h (task 11.3c1). Plan.md §6 Phase 11; docs/macos-design.md §1 ("the zoom model
// (ZoomChoice presets, Automatic Zoom, quantised 1/64 px/pt, View.stepInZ/stepOutZ, zoom
// anchored at the pointer or window centre — C2's View.reanchor) ... rotation") and §3
// decision 1 (nothing proven is reimplemented: every rule here is one C call into the Lean
// function the Tk viewer uses). Swift only converts numbers.

import CoreGraphics
import SafePdfC

/// Wrappers over the zoom, rotation and anchoring calls of `safepdf_view.h`. Each returns nil
/// when the C call fails (bad input or an unrepresentable result).
@MainActor enum ZoomModel {
    static let auto = safepdf_zoom_choice(kind: SAFEPDF_ZOOM_AUTO.rawValue, pct: 0)

    /// A zoom choice from a toolbar preset.
    static func choice(_ p: ZoomPresetSpec) -> safepdf_zoom_choice {
        safepdf_zoom_choice(kind: p.kind, pct: p.pct)
    }

    /// A fixed percentage.
    static func percent(_ pct: UInt32) -> safepdf_zoom_choice {
        safepdf_zoom_choice(kind: SAFEPDF_ZOOM_PERCENT.rawValue, pct: pct)
    }

    static func same(_ a: safepdf_zoom_choice, _ b: safepdf_zoom_choice) -> Bool {
        a.kind == b.kind && (a.kind != SAFEPDF_ZOOM_PERCENT.rawValue || a.pct == b.pct)
    }

    /// Equal rationals (the core returns them in lowest terms).
    static func same(_ a: safepdf_rat, _ b: safepdf_rat) -> Bool { a.num == b.num && a.den == b.den }

    /// The view constants (margin, zoom range, pixel cap).
    static let constants: safepdf_view_constants? = {
        var c = safepdf_view_constants()
        return safepdf_view_get_constants(&c) == 0 ? c : nil
    }()

    /// ZoomChoice.label ("Automatic Zoom", "33%").
    static func label(_ c: safepdf_zoom_choice) -> String {
        Core.take(safepdf_view_zoom_label(c)) ?? "Zoom"
    }

    /// The screen's pixels per point as an exact rational (backing scale factors are 1, 2 or 3
    /// in practice; 1/64 steps cover any other).
    static func scaling(_ backing: CGFloat) -> safepdf_rat { Core.rat(Double(backing)) }

    /// View.pctZoom.
    static func pctZoom(_ pct: UInt32, scaling: safepdf_rat) -> safepdf_rat? {
        var out = safepdf_rat()
        return safepdf_view_pct_zoom(pct, scaling, &out) == 0 ? out : nil
    }

    /// View.zoomPct (rounded to the nearest percent).
    static func zoomPct(_ z: safepdf_rat, scaling: safepdf_rat) -> UInt32? {
        var pct: UInt32 = 0
        return safepdf_view_zoom_pct(z, scaling, &pct) == 0 ? pct : nil
    }

    /// View.quant (down to a multiple of 1/64, at least 1/64).
    static func quant(_ z: safepdf_rat) -> safepdf_rat? {
        var out = safepdf_rat()
        return safepdf_view_quant(z, &out) == 0 ? out : nil
    }

    /// The zoom Zoom In / Zoom Out step from: the fixed percentage's zoom, or the one a fit
    /// mode came out at (`base`, the layout's) — Viewer.zoom's `cur`.
    static func current(_ c: safepdf_zoom_choice, base: safepdf_rat, scaling: safepdf_rat) -> safepdf_rat {
        if c.kind == SAFEPDF_ZOOM_PERCENT.rawValue, let z = pctZoom(c.pct, scaling: scaling) { return z }
        return base
    }

    /// View.stepInZ / stepOutZ: the percentage to go to, nil at the end of the range.
    static func step(in zoomIn: Bool, from z: safepdf_rat, scaling: safepdf_rat) -> UInt32? {
        var pct: UInt32 = 0
        let r = zoomIn ? safepdf_view_step_in(z, scaling, &pct) : safepdf_view_step_out(z, scaling, &pct)
        return r == 1 ? pct : nil
    }

    /// The percentage a pinch ends at: the layout's zoom times the gesture's magnification,
    /// quantised (View.quant) and shown as a percentage (View.zoomPct), kept in the zoom
    /// range [View.minPct, View.maxPct].
    static func pinchPct(base: safepdf_rat, magnification: CGFloat, scaling: safepdf_rat) -> UInt32? {
        let zb = Double(base.num) / Double(base.den)
        guard zb > 0, magnification.isFinite, magnification > 0,
              let z = quant(Core.rat(zb * Double(magnification))),
              let pct = zoomPct(z, scaling: scaling) else { return nil }
        let lo = constants?.min_pct ?? 25, hi = constants?.max_pct ?? 800
        return min(max(pct, lo), hi)
    }

    /// View.rotCw / rotCcw (degrees).
    static func rotate(_ deg: UInt32, clockwise: Bool) -> UInt32 {
        var info = safepdf_rotation_info()
        let zero = safepdf_rat(num: 0, den: 1), one = safepdf_rat(num: 1, den: 1)
        var box = safepdf_rat_box(llx: zero, lly: zero, urx: one, ury: one)
        guard safepdf_view_rotation(deg, &box, &info) == 0 else { return deg }
        return clockwise ? info.cw : info.ccw
    }

    /// View.reanchor (C2): where the page point shown at `q` (pixels from the page image's
    /// top-left) in view (z, rot) is shown in view (z2, rot2).
    static func reanchor(z: safepdf_rat, rot: UInt32, z2: safepdf_rat, rot2: UInt32,
                         box: safepdf_rat_box, q: CGPoint) -> CGPoint? {
        var b = box
        var out = safepdf_rat_point()
        let qp = safepdf_rat_point(x: Core.rat(Double(q.x)), y: Core.rat(Double(q.y)))
        guard safepdf_view_reanchor(z, rot, z2, rot2, &b, qp, &out) == 0,
              out.x.den > 0, out.y.den > 0 else { return nil }
        return CGPoint(x: Double(out.x.num) / Double(out.x.den), y: Double(out.y.num) / Double(out.y.den))
    }

    /// Geom.toScreen (C2, task 11.3c2): where page point (x, y) (page units) is shown at zoom `z`
    /// and rotation `rot` of `box`, in pixels from the page image's top-left (a destination).
    static func toScreen(z: safepdf_rat, rot: UInt32, box: safepdf_rat_box, x: safepdf_rat,
                         y: safepdf_rat) -> CGPoint? {
        var b = box
        var out = safepdf_rat_point()
        guard safepdf_view_to_screen(z, rot, &b, safepdf_rat_point(x: x, y: y), &out) == 0,
              out.x.den > 0, out.y.den > 0 else { return nil }
        return CGPoint(x: double(out.x), y: double(out.y))
    }

    static func double(_ q: safepdf_rat) -> Double { q.den > 0 ? Double(q.num) / Double(q.den) : 0 }
}
