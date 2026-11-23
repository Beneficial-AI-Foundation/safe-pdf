/-!
# Tk shim bindings (task 8.2a; Plan.md §8 native app, §10 `SafePdf/Shell/`)

Lean side of `c/tk_shim.c` (trusted, unverified shell). Adapted from the sibling project
bib-lean's `BibLean/Gui/Shim.lean` (same author/organisation); `photoPut` is new.

The shim owns one Tcl interpreter per process, used only from the thread running `main`.
Every user event reaches Lean as the Tcl command `::safepdf::emit arg …`, which the shim
forwards to `guiDispatch` as the array of its argument words; `guiDispatch` calls the
handler installed with `setEmitHandler`. Strings coming back from Tcl have Tcl's NUL
encoding (`C0 80`) decoded.

These externs exist only in the `viewer` executable (the shim object is linked there and
nowhere else, see `lakefile.lean`); this module must not be imported by `SafePdf.lean`,
the inspector or the tests.
-/

namespace SafePdf.Shell.App.Shim

/-- Raw binding: creates the interpreter and loads Tcl and Tk (`Tcl_FindExecutable` with
`argv0`, `Tcl_CreateInterp`, `Tcl_Init`, `Tk_Init`). Idempotent. -/
@[extern "safepdf_tk_init"]
opaque tkInitRaw (argv0 : @& String) : IO Unit

/-- Raw binding: evaluates a script at global level and returns the Tcl status code
(`0` = `TCL_OK`, `1` = `TCL_ERROR`, …) with the interpreter's result string. -/
@[extern "safepdf_tcl_eval"]
opaque tclEvalRaw (script : @& String) : IO (UInt32 × String)

/-- Raw binding: defines the Tcl command `::safepdf::emit arg …`, which calls
`guiDispatch #[arg, …]`. -/
@[extern "safepdf_tk_register_emit"]
opaque registerEmit : IO Unit

/-- Replaces the pixels of the existing photo image `name` by a `w × h` RGBA buffer (rows top
to bottom, 4 bytes per pixel, at least `4·w·h` bytes); resizes the photo. -/
@[extern "safepdf_tk_photo_put"]
opaque photoPut (name : @& String) (w h : UInt32) (rgba : @& ByteArray) : IO Unit

/-- Runs the Tk event loop until the main window `.` is destroyed or `quit` is called. -/
@[extern "safepdf_tk_mainloop"]
opaque mainLoop : IO Unit

/-- Makes `mainLoop` return after the event being processed. -/
@[extern "safepdf_tk_quit"]
opaque quit : IO Unit

/-- The handler `guiDispatch` forwards every `::safepdf::emit` call to. -/
initialize emitHandler : IO.Ref (Array String → IO Unit) ← IO.mkRef fun _ => pure ()

/-- Installs the handler for `::safepdf::emit` calls, replacing the previous one. -/
def setEmitHandler (h : Array String → IO Unit) : IO Unit :=
  emitHandler.set h

/-- Called by the shim for every `::safepdf::emit arg …` (C name `safepdf_gui_dispatch`)
with the argument words. An exception becomes a Tcl error in the Tk callback that emitted
the message. -/
@[export safepdf_gui_dispatch]
def guiDispatch (args : Array String) : IO Unit := do
  (← emitHandler.get) args

/-- Creates the interpreter, loads Tk and registers `::safepdf::emit`. -/
def init : IO Unit := do
  tkInitRaw (← IO.appPath).toString
  registerEmit

/-- Evaluates a Tcl script, returning its result or throwing the Tcl error message. -/
def eval (script : String) : IO String := do
  let (status, result) ← tclEvalRaw script
  if status == 0 then return result
  throw <| IO.userError s!"Tcl error {status}: {result}"

end SafePdf.Shell.App.Shim
