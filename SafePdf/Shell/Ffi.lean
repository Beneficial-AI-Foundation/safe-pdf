import SafePdf.Shell.Ffi.V2
import SafePdf.Shell.Ffi.Sidebar

/-!
# The C ABI over `safe-pdf-core`: library root (tasks 11.1, 11.3a1, 11.3c1)

Plan.md §6 Phase 11 ("a minimal Cocoa window (open, render, scroll, zoom) over the C API")
and §8 (the shell is unverified and replaceable; the core as a library is the deliverable).

This Shell module (unverified; `IO` allowed) is the root of the `SafePdfFfi` library: it
imports the document layer of the C API v2 so that `lake build macosFfi` archives it, and
exports the one helper the C shim (`macos/safepdf_core.c`) uses for every `IO` error. The
exports are **not** the public C API: `macos/safepdf_core.c` wraps them into plain C functions
(`macos/safepdf_core.h`) and hides every `lean_object`. Every object parameter is **owned**
(Lean v4.36 rejects `@&` on `@[export]`), and every result is owned by the caller.

* `SafePdf.Shell.Ffi.V2` — the document layer over the confined worker (refcounted handles,
  asynchronous requests through `Worker.Session`, completion through the `safepdf_c_deliver`
  callback, page geometry for layout).
* `SafePdf.Shell.Ffi.Sidebar` — the sidebar's rules (panels, page mode, thumbnails, outline
  tree, attachment save targets) and the 12.5 identity line (task 11.3d2).
* `SafePdf.Shell.Ffi.Flat` — the pure conversions to the flat layout the C structs are copied
  from.

Task 11.3c1 retired the v1 exports of the 11.1 spike (in-process open and a synchronous render
on the calling thread): the Swift app (task 11.3b) replaced the spike's `macos/main.m`, and
nothing else called them. The C test that compared the asynchronous render with the v1 one
now compares it with `V2.testRender` (the same verified renderer, in this process).
-/

namespace SafePdf.Shell.Ffi

/-- The text of an `IO` error thrown by an export (every `IO` export of the C API). -/
@[export safepdf_lean_error_text]
def errorText (e : IO.Error) : String := toString e

end SafePdf.Shell.Ffi
