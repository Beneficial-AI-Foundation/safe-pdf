import SafePdf.Api
import SafePdf.Shell.Fonts

/-!
# A first C ABI over `safe-pdf-core` (task 11.1, AppKit spike)

Plan.md §6 Phase 11 ("a minimal Cocoa window (open, render, scroll, zoom) over the C API")
and §8 (the shell is unverified and replaceable; the core as a library is the deliverable).

This Shell module (unverified; `IO` allowed) exports a handful of Lean functions with
`@[export safepdf_lean_…]` C names. They are **not** the public C API: `macos/safepdf_core.c`
wraps them into plain C functions (`macos/safepdf_core.h`: `const char *` paths, `double`
sizes, `malloc`ed RGBA buffers, error strings) and hides every `lean_object`. Ownership
follows Lean's default calling convention: every object parameter is **owned** — the callee
consumes one reference, so a caller that keeps the object (the document handle) calls
`lean_inc` before each call — and every result is owned by the caller (one reference,
released with `lean_dec`). Lean v4.36 rejects borrow annotations (`@&`) on `@[export]`
declarations, so there are none here.

The handle holds the opened `SafePdf.Api.Document` and the substitute fonts found on the
system (`SafePdf.Shell.Fonts.loadSubstFonts`, as the Tk viewer does), so non-embedded text is
painted the same way in both shells. Rendering is `Core.Raster.Glyph.renderDocPage`, the
verified renderer behind `SafePdf.Api.renderPage` and the Tk viewer (`App.Viewer.renderPage`).
-/

namespace SafePdf.Shell.Ffi

open SafePdf SafePdf.Core

/-- An open document as the C side sees it: an opaque `lean_object *`. -/
structure Handle where
  /-- The opened document (`SafePdf.Api.openFile`). -/
  doc : Api.Document
  /-- Substitute programs for non-embedded standard-14 fonts. -/
  subst : Raster.Subst.SubstFonts

/-- **Open** the PDF at `path`; throws an `IO.userError` with the English error text when the
file cannot be read or parsed. -/
@[export safepdf_lean_open]
def openPath (path : String) : IO Handle := do
  match ← Api.openFile path with
  | .error e => throw (IO.userError e.message)
  | .ok d =>
    let subst ← Fonts.loadSubstFonts d.limits
    return ⟨d, subst⟩

/-- Number of pages. -/
@[export safepdf_lean_page_count]
def pageCount (h : Handle) : USize := h.doc.pageCount.toUSize

/-- A rational as a `Float` (for display sizes only; never fed back into the core). -/
def ratToFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- Displayed width and height in points of page `i` (CropBox, `/Rotate` applied), as a
two-element `FloatArray`; empty when `i` is out of range. -/
@[export safepdf_lean_page_size]
def pageSize (h : Handle) (i : USize) : FloatArray :=
  match Api.pageInfo h.doc i.toNat with
  | .ok info => ⟨#[ratToFloat info.size.1, ratToFloat info.size.2]⟩
  | .error _ => FloatArray.empty

/-- **Render** page `i` at `num / den` pixels per point (1 = 72 dpi) onto its CropBox:
`4·w·h` RGBA bytes, rows from the top, white background (`SafePdf.Api.renderPage`'s
contract, with the handle's substitute fonts). Throws an `IO.userError` on a bad page, a zero
zoom, or a core error. The work runs when the `IO` action runs (`IO.lazyPure`), on the
calling thread. -/
@[export safepdf_lean_render]
def render (h : Handle) (i : USize) (num den : USize) : IO Api.Image := do
  if den == 0 || num == 0 then throw (IO.userError "zoom must be positive")
  let zoom : Rat := (num.toNat : Rat) / (den.toNat : Rat)
  match h.doc.page i.toNat with
  | .error e => throw (IO.userError e.message)
  | .ok p =>
    let d := h.doc
    let r ← IO.lazyPure fun _ =>
      (Raster.Glyph.renderDocPage d.limits d.doc p zoom .r0
        (Filter.Budget.init d.limits) (subst := h.subst)).1
    match r with
    | .ok img => return img
    | .error e => throw (IO.userError (Api.Error.pdf e).message)

/-- Width in pixels of a rendered image. -/
@[export safepdf_lean_image_width]
def imageWidth (img : Api.Image) : USize := img.w.toUSize

/-- Height in pixels of a rendered image. -/
@[export safepdf_lean_image_height]
def imageHeight (img : Api.Image) : USize := img.h.toUSize

/-- The RGBA bytes of a rendered image (shares the image's array: one more reference). -/
@[export safepdf_lean_image_data]
def imageData (img : Api.Image) : ByteArray := img.data

/-- The text of an `IO` error thrown by the functions above. -/
@[export safepdf_lean_error_text]
def errorText (e : IO.Error) : String := toString e

end SafePdf.Shell.Ffi
