/*
 * tk_shim.c — the Tcl/Tk shim of the safe-pdf viewer (trusted, hand-written, unverified;
 * task 8.2a, Plan.md §8 native app, ledger Decisions 8.1).
 *
 * Adapted from the sibling project bib-lean's `c/tk_shim.c` (same author/organisation):
 * interpreter, Tk init, script evaluation, the `emit` callback into Lean and the event loop
 * are that file's, renamed to the `safepdf_` prefix; the photo upload
 * (`safepdf_tk_photo_put`) is new.
 *
 * One Tcl interpreter per process, kept in a static and touched only from the thread that
 * runs Lean's `main`. The shim has no logic: it creates the interpreter, evaluates scripts,
 * forwards the Tcl command `::safepdf::emit arg ?arg ...?` to the exported Lean function
 * `safepdf_gui_dispatch : Array String → IO Unit`, copies an RGBA byte buffer into a Tk
 * photo image, and runs the event loop. No data is spliced into script text here: the
 * photo's pixels go through `Tk_PhotoPutBlock`, its name is looked up with
 * `Tk_FindPhoto`, and `emit` hands its argument words to Lean as separate strings.
 * `safepdf_close_fd3` (task 10.1b) is not Tk: it closes bib-lean's token pipe on file
 * descriptor 3; it lives here because this is the `viewer` executable's only C object.
 *
 * Lean calling conventions used here (Lean 4.36):
 *   - the IO world token is erased from compiled signatures: an `IO α` extern takes only
 *     its explicit arguments (`IO Unit` with none is `f(void)`);
 *   - it returns an IO result object: `lean_io_result_mk_ok(v)` / `lean_io_result_mk_error`;
 *   - `@&` arguments are borrowed (no dec_ref); other object arguments are owned;
 *     `UInt32` arguments arrive unboxed as `uint32_t`.
 *
 * Builds against Tcl/Tk 9.0 (Debian, Homebrew) and 8.6 (Ubuntu's `tk-dev`).
 */
#include <lean/lean.h>
#include <tcl.h>
#include <tk.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#ifndef TCL_SIZE_MAX /* Tcl 8.6 has no Tcl_Size; lengths are int there */
typedef int Tcl_Size;
#endif

/* The exported Lean handler (`SafePdf.Shell.App.Shim.guiDispatch`). Owns `args`
 * (an `Array String`). */
extern lean_obj_res safepdf_gui_dispatch(lean_obj_arg args);

#ifdef __APPLE__
/* Keep Lean's `main` on the process main thread (macOS only).
 *
 * Lean 4.36's generated C `main` calls `lean_run_main`, which by default runs the Lean
 * `main` on a fresh thread with a large stack. Cocoa (Tk's Aqua backend) must run on the
 * main thread: off it, `Tk_Init` deadlocks. `lean_run_main` reads `LEAN_MAIN_USE_THREAD`;
 * "0" makes it call `main` directly. This constructor runs before `main`; it does not
 * override a value the user set. Cost: Lean's `main` gets the main-thread stack (8 MiB).
 * On X11 Tk only needs one thread to use it, so Linux keeps Lean's big stack. */
__attribute__((constructor)) static void safepdf_keep_main_thread(void) {
  setenv("LEAN_MAIN_USE_THREAD", "0", 0);
}
#endif

static Tcl_Interp *interp = NULL;
static int quit_requested = 0;

static lean_obj_res io_ok_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

static lean_obj_res io_error(const char *msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/* Copies a Tcl string into a Lean string. Tcl's internal strings are UTF-8 except that
 * NUL is encoded as the overlong pair C0 80; the copy turns every C0 80 back into a NUL
 * byte. lean_mk_string_from_bytes replaces any remaining invalid sequence, so the result
 * is always a valid Lean string. */
static lean_obj_res tcl_to_lean(const char *s, Tcl_Size len) {
  if (memchr(s, 0xC0, (size_t)len) == NULL)
    return lean_mk_string_from_bytes(s, (size_t)len);
  char *buf = malloc((size_t)len + 1);
  if (buf == NULL) return lean_mk_string_from_bytes(s, (size_t)len);
  size_t n = 0;
  for (Tcl_Size i = 0; i < len; i++) {
    if ((unsigned char)s[i] == 0xC0 && i + 1 < len && (unsigned char)s[i + 1] == 0x80) {
      buf[n++] = 0;
      i++;
    } else {
      buf[n++] = s[i];
    }
  }
  lean_obj_res r = lean_mk_string_from_bytes(buf, n);
  free(buf);
  return r;
}

/* Copies the interpreter's current result into a Lean string (`tcl_to_lean`). */
static lean_obj_res interp_result(void) {
  Tcl_Size len = 0;
  const char *s = Tcl_GetStringFromObj(Tcl_GetObjResult(interp), &len);
  return tcl_to_lean(s, len);
}

/* safepdf_tk_init (argv0 : @& String) : IO Unit
 * Creates the interpreter and loads Tcl's and Tk's init scripts (this creates the main
 * window "."). Idempotent. */
LEAN_EXPORT lean_obj_res safepdf_tk_init(b_lean_obj_arg argv0) {
  if (interp != NULL) return io_ok_unit();
  Tcl_FindExecutable(lean_string_cstr(argv0));
  interp = Tcl_CreateInterp();
  if (interp == NULL) return io_error("Tcl_CreateInterp failed");
  if (Tcl_Init(interp) != TCL_OK || Tk_Init(interp) != TCL_OK) {
    lean_object *msg = interp_result();
    Tcl_DeleteInterp(interp);
    interp = NULL;
    return lean_io_result_mk_error(lean_mk_io_user_error(msg));
  }
  return io_ok_unit();
}

/* safepdf_tcl_eval (script : @& String) : IO (UInt32 × String)
 * Evaluates `script` at global level; returns the Tcl status code (TCL_OK = 0,
 * TCL_ERROR = 1, ...) and the interpreter result. */
LEAN_EXPORT lean_obj_res safepdf_tcl_eval(b_lean_obj_arg script) {
  if (interp == NULL) return io_error("safepdf_tcl_eval: Tk not initialised");
  int status = Tcl_EvalEx(interp, lean_string_cstr(script),
                          (Tcl_Size)(lean_string_size(script) - 1), TCL_EVAL_GLOBAL);
  lean_object *pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_box_uint32((uint32_t)status));
  lean_ctor_set(pair, 1, interp_result());
  return lean_io_result_mk_ok(pair);
}

/* The Tcl command `::safepdf::emit arg ?arg ...?`: hands its arguments to Lean as an
 * `Array String` (each word as Tcl passed it: no list parsing on either side). A Lean
 * exception becomes a Tcl error (reported by Tk's background-error handler). */
static int emit_cmd(void *cd, Tcl_Interp *ip, int objc, Tcl_Obj *const objv[]) {
  (void)cd;
  if (objc < 2) {
    Tcl_WrongNumArgs(ip, 1, objv, "arg ?arg ...?");
    return TCL_ERROR;
  }
  size_t n = (size_t)objc - 1;
  lean_object *arr = lean_alloc_array(n, n);
  for (size_t i = 0; i < n; i++) {
    Tcl_Size len = 0;
    const char *s = Tcl_GetStringFromObj(objv[i + 1], &len);
    lean_array_set_core(arr, i, tcl_to_lean(s, len));
  }
  lean_object *r = safepdf_gui_dispatch(arr);
  int ok = lean_io_result_is_ok(r);
  if (!ok) lean_io_result_show_error(r); /* prints "uncaught exception: ..." */
  lean_dec_ref(r);
  if (!ok) {
    Tcl_SetObjResult(ip, Tcl_NewStringObj("safepdf::emit: Lean handler failed", -1));
    return TCL_ERROR;
  }
  return TCL_OK;
}

/* safepdf_tk_register_emit : IO Unit — defines the Tcl command `::safepdf::emit`. */
LEAN_EXPORT lean_obj_res safepdf_tk_register_emit(void) {
  if (interp == NULL) return io_error("safepdf_tk_register_emit: Tk not initialised");
  if (Tcl_Eval(interp, "namespace eval ::safepdf {}") != TCL_OK)
    return io_error("safepdf_tk_register_emit: cannot create namespace ::safepdf");
  Tcl_CreateObjCommand(interp, "::safepdf::emit", emit_cmd, NULL, NULL);
  return io_ok_unit();
}

/* safepdf_tk_photo_put (name : @& String) (w h : UInt32) (rgba : @& ByteArray) : IO Unit
 * Resizes the existing photo image `name` to w×h and copies `rgba` (rows top to bottom,
 * 4 bytes per pixel R, G, B, A, no padding) into it, replacing its pixels. Fails when the
 * image does not exist, the buffer is shorter than 4·w·h bytes, or Tk runs out of memory. */
LEAN_EXPORT lean_obj_res safepdf_tk_photo_put(b_lean_obj_arg name, uint32_t w, uint32_t h,
                                              b_lean_obj_arg rgba) {
  if (interp == NULL) return io_error("safepdf_tk_photo_put: Tk not initialised");
  if (w == 0 || h == 0 || w > 65535 || h > 65535)
    return io_error("safepdf_tk_photo_put: image size out of range");
  size_t need = (size_t)w * (size_t)h * 4;
  if (lean_sarray_size(rgba) < need)
    return io_error("safepdf_tk_photo_put: pixel buffer too short");
  Tk_PhotoHandle ph = Tk_FindPhoto(interp, lean_string_cstr(name));
  if (ph == NULL) return io_error("safepdf_tk_photo_put: no such photo image");
  Tk_PhotoBlank(ph);
  if (Tk_PhotoSetSize(interp, ph, (int)w, (int)h) != TCL_OK)
    return io_error("safepdf_tk_photo_put: cannot resize photo");
  Tk_PhotoImageBlock block;
  block.pixelPtr = (unsigned char *)lean_sarray_cptr(rgba);
  block.width = (int)w;
  block.height = (int)h;
  block.pitch = (int)w * 4;
  block.pixelSize = 4;
  block.offset[0] = 0;
  block.offset[1] = 1;
  block.offset[2] = 2;
  block.offset[3] = 3;
  if (Tk_PhotoPutBlock(interp, ph, &block, 0, 0, (int)w, (int)h, TK_PHOTO_COMPOSITE_SET) !=
      TCL_OK)
    return io_error("safepdf_tk_photo_put: Tk_PhotoPutBlock failed");
  return io_ok_unit();
}

/* safepdf_tk_mainloop : IO Unit — processes events until the main window is destroyed or
 * safepdf_tk_quit is called. */
LEAN_EXPORT lean_obj_res safepdf_tk_mainloop(void) {
  if (interp == NULL) return io_error("safepdf_tk_mainloop: Tk not initialised");
  quit_requested = 0;
  while (!quit_requested && Tk_GetNumMainWindows() > 0) Tcl_DoOneEvent(0);
  return io_ok_unit();
}

/* safepdf_tk_quit : IO Unit — makes safepdf_tk_mainloop return after the current event. */
LEAN_EXPORT lean_obj_res safepdf_tk_quit(void) {
  quit_requested = 1;
  return io_ok_unit();
}

/* safepdf_close_fd3 : IO Unit — closes file descriptor 3 (task 10.1b; bib-lean's reader
 * contract §2: the viewer "SHOULD close fd 3 after" reading the token from it). Lean can only
 * open `/dev/fd/3` as a new descriptor, so the inherited one needs this call. Called by
 * `BibLean.Launch.openFromBibLean` only after a valid token was read from fd 3, i.e. while
 * fd 3 is known to be the inherited pipe and not a descriptor of the runtime. A failure
 * (fd 3 already closed) is not an error. */
LEAN_EXPORT lean_obj_res safepdf_close_fd3(void) {
  (void)close(3);
  return io_ok_unit();
}
