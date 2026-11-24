import Lake

open System Lake DSL

/-!
# safe-pdf build configuration

This file was `lakefile.toml` until task 8.2a. A TOML configuration cannot compile C
(custom `target`s and `extern_lib` exist only in the Lean DSL) and cannot ask `pkg-config`
for flags, so the Tcl/Tk shim of the native viewer (`c/tk_shim.c`, ledger Decisions 8.1)
forced the switch. Every setting of the TOML file is preserved below: package name and
version, the default targets `SafePdf` and `inspect`, `autoImplicit = false`,
`relaxedAutoImplicit = false`, lib `Tests` with every module under `Tests/`, and the
executables `inspect`, `tests`, `fuzz`.

**Tk stays out of the default build.** The shim is *not* an `extern_lib`: Lake links every
`extern_lib` of a package into every executable, so `inspect`, `tests` and `fuzz` would need
Tcl/Tk to link. Instead the shim is a custom `target tkShim` (an object file) attached only to
the `viewer` executable through its `moreLinkObjs`, with the Tk link flags in that
executable's `moreLinkArgs`. `lake build` (targets `SafePdf`, `SafePdfApp`, `inspect`) and
`lake build tests fuzz` therefore neither compile the shim nor run `pkg-config` for it;
only `lake build viewer` / `lake exe viewer` do. On a machine without Tk the link flags
come out empty (silently) and building `viewer` fails at the shim's compile step with
`pkg-config`'s message.

The pattern (pkg-config helper, macOS Homebrew keg paths, Linux system library directories
behind Lean's sysroot) is copied from the sibling project bib-lean's `lakefile.lean` (same
author/organisation), reduced to Tcl/Tk.
-/

/-- Runs `pkg-config` with `args` and splits its output into words. `none` when
`pkg-config` or the package is missing (with the error text when `loud`). On macOS,
Homebrew's keg directories for `tcl-tk` are appended to `PKG_CONFIG_PATH` in case the
formula is not linked into `/opt/homebrew/lib/pkgconfig`. -/
def pkgConfig (args : Array String) (loud : Bool := false) : IO (Option (Array String)) := do
  let kegs := #["/opt/homebrew/opt/tcl-tk/lib/pkgconfig", "/usr/local/opt/tcl-tk/lib/pkgconfig"]
  let old := (← IO.getEnv "PKG_CONFIG_PATH").getD ""
  let path := if System.Platform.isOSX then
      ":".intercalate ((if old.isEmpty then #[] else #[old]) ++ kegs).toList
    else old
  try
    let out ← IO.Process.output
      { cmd := "pkg-config", args, env := #[("PKG_CONFIG_PATH", some path)] }
    if out.exitCode != 0 then
      if loud then IO.eprintln s!"pkg-config {" ".intercalate args.toList} failed: {out.stderr}"
      return none
    return some <| (out.stdout.split Char.isWhitespace).toArray.filterMap fun w =>
      if w.isEmpty then none else some w.toString
  catch e =>
    if loud then IO.eprintln s!"could not run pkg-config: {e}"
    return none

/-- The library search directories of the system C compiler (`cc -print-search-dirs`) plus
Tk's `libdir`; only existing directories, resolved and deduplicated in order. Linux only
(see `tkLinkArgs`). -/
def systemLibDirs : IO (Array String) := do
  let mut cands : Array String := (← pkgConfig #["--variable=libdir", "tk"]).getD #[]
  try
    let out ← IO.Process.output { cmd := "cc", args := #["-print-search-dirs"] }
    for line in out.stdout.splitOn "\n" do
      if line.startsWith "libraries: =" then
        cands := cands ++ ((line.drop "libraries: =".length).toString.splitOn ":").toArray
  catch _ => pure ()
  let mut dirs : Array String := #[]
  for d in cands do
    if d.isEmpty then continue
    unless ← System.FilePath.isDir d do continue
    let r := (← IO.FS.realPath d).toString
    unless dirs.contains r do dirs := dirs.push r
  return dirs

/--
Link flags of the viewer's Tcl/Tk (`pkg-config --libs tk`), computed once when the lakefile
is elaborated (re-run with `lake -R` if Tk moves). Empty, silently, when Tk is missing:
only the `viewer` executable uses them.

On Linux Lean links with its bundled `clang` + `ld.lld` and `--sysroot <toolchain>`, whose
`lib/glibc` holds old glibc link stubs; the system library directories are not searched, so
`-ltk…` would fail with "unable to find library". The system directories are therefore added
as `-Wl,-L<dir>` (searched **after** the toolchain's own directories, so `-lc`, `-lm`, … keep
resolving to Lean's copies) and `--allow-shlib-undefined` lets the system Tk reference newer
glibc symbol versions, resolved by the system glibc at run time. (bib-lean docs/SPIKES.md.)
-/
def tkLinkArgs : Array String := run_io do
  let some libs ← pkgConfig #["--libs", "tk"] | return #[]
  if Platform.isOSX || Platform.isWindows then
    return libs
  let libs := libs.map fun a => if a.startsWith "-L" && a.length > 2 then s!"-Wl,{a}" else a
  let dirs ← systemLibDirs
  return libs ++ dirs.map (s!"-Wl,-L{·}") ++ #["-Wl,--allow-shlib-undefined"]

package «safe-pdf» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

/-- The verified core and the unverified shell modules it umbrella-imports (`SafePdf.lean`). -/
@[default_target] lean_lib SafePdf

/-- The pure, Tk-free part of the viewer shell: Tcl scripts as data and the proofs that
quoting is injection-free. A default target so that `scripts/axioms.lean` can audit its
theorems after a plain `lake build`. -/
@[default_target] lean_lib SafePdfApp where
  roots := #[`SafePdf.Shell.App.Tcl, `SafePdf.Shell.App.TclLemmas, `SafePdf.Shell.App.View, `SafePdf.Shell.App.Select, `SafePdf.Shell.App.Links, `SafePdf.Shell.App.Menu, `SafePdf.Shell.App.Icons, `SafePdf.Shell.App.Toolbar, `SafePdf.Shell.App.Sidebar, `SafePdf.Shell.App.BibLean.Http, `SafePdf.Shell.App.BibLean.Launch, `SafePdf.Shell.App.BibLean.Text, `SafePdf.Shell.App.BibLean.Annots, `SafePdf.Shell.App.BibLean.SelfTest, `SafePdf.Shell.App.Marks, `SafePdf.Shell.App.Bubble, `SafePdf.Shell.App.Save, `SafePdf.Shell.App.Xfdf, `SafePdf.Shell.App.Budget]

/-- `safe-pdf-core` (task 8.4, Plan.md §6 Phase 8): the public library API `SafePdf.Api` and
the verified core it imports, without the shell (inspector, viewer). A separate target so
that `lake build SafePdfCore` builds exactly what a client needs; clients import
`SafePdf.Api` (`docs/api.md`). -/
@[default_target] lean_lib SafePdfCore where
  roots := #[`SafePdf.Api]

/-- Example client of the library API: `lake exe extract [--render] FILE [PAGE]`
(`examples/Extract.lean`, `docs/api.md`). -/
@[default_target] lean_exe extract where
  srcDir := "examples"
  root := `Extract

/-- Test suites: every module under `Tests/` (TOML `globs = ["Tests.+"]`). -/
lean_lib Tests where
  globs := #[.submodules `Tests]

/-- The inspector CLI. -/
@[default_target] lean_exe inspect where
  root := `SafePdf.Shell.Main

/-- `c/worker_sandbox.c` (task 12.2b): the worker's confinement (macOS seatbelt, Linux
seccomp). Plain C with Lean's include directory; no pkg-config. Attached only to `worker`
(like `tkShim` to `viewer`: an `extern_lib` would be linked into every executable). -/
target workerSandbox pkg : FilePath := do
  let src ← inputTextFile <| pkg.dir / "c" / "worker_sandbox.c"
  let oFile := pkg.buildDir / "c" / "worker_sandbox.o"
  buildO oFile src #["-I", (← getLeanIncludeDir).toString] #["-fPIC", "-O2", "-Wall", "-Wextra"]
    "cc" getLeanTrace

/-- The same file compiled with `-DSAFEPDF_WORKER_PROBE` (adds the TCP probe), for the
test-only `worker-probe` executable. -/
target workerSandboxProbe pkg : FilePath := do
  let src ← inputTextFile <| pkg.dir / "c" / "worker_sandbox.c"
  let oFile := pkg.buildDir / "c" / "worker_sandbox_probe.o"
  buildO oFile src #["-I", (← getLeanIncludeDir).toString]
    #["-fPIC", "-O2", "-Wall", "-Wextra", "-DSAFEPDF_WORKER_PROBE"] "cc" getLeanTrace

/-- The document worker (tasks 12.2a, 12.2b): confines itself, then serves a document received
as bytes over stdin/stdout. -/
@[default_target] lean_exe worker where
  root := `SafePdf.Shell.Worker.Main
  moreLinkObjs := #[workerSandbox]

/-- Test-only (task 12.2b): the worker's startup and confinement followed by probes that must
fail (open a file, connect to 127.0.0.1, read the parent's environment, spawn a process).
A default target so that the `worker-confinement` suite always finds it after `lake build`;
`scripts/worker-confinement-test.sh` runs it verbosely. Never shipped: it is not the
`worker` the client starts. -/
@[default_target] lean_exe «worker-probe» where
  root := `SafePdf.Shell.Worker.Probe
  moreLinkObjs := #[workerSandboxProbe]

/-- The test runner. -/
lean_exe tests where
  root := `Tests.Main

/-- The fuzz driver. -/
lean_exe fuzz where
  root := `Tests.Fuzz.Main

/-! ## Native viewer (task 8.2a; not a default target) -/

/-- `c/tk_shim.c` compiled with the system C compiler, Lean's include directory and
`pkg-config --cflags tk` (asked when this target builds, so a Tk-less machine only fails
here). The flags are weak (not traced): they hold machine-specific include paths. -/
target tkShim pkg : FilePath := do
  let src ← inputTextFile <| pkg.dir / "c" / "tk_shim.c"
  let oFile := pkg.buildDir / "c" / "tk_shim.o"
  let some cflags ← pkgConfig #["--cflags", "tk"] (loud := true)
    | error "tk_shim: Tcl/Tk development files not found by pkg-config (Debian/Ubuntu: \
        apt-get install tk-dev; macOS: brew install tcl-tk)"
  let weak := #["-I", (← getLeanIncludeDir).toString] ++ cflags
  buildO oFile src weak #["-fPIC", "-O2", "-Wall", "-Wextra"] "cc" getLeanTrace

/-- The native viewer (Tcl/Tk shell; `docs/viewer.md`). Links the Tk shim and Tk itself. -/
lean_exe viewer where
  root := `SafePdf.Shell.App.Main
  moreLinkObjs := #[tkShim]
  moreLinkArgs := tkLinkArgs

/-! ## macOS AppKit spike (task 11.1; not a default target) -/

/-- The modules of the C API (`macos/README.md`): the first C ABI over the core
(`SafePdf.Shell.Ffi`, task 11.1), the view/chrome logic (`SafePdf.Shell.FfiView`, task 11.3a2),
the marks/save/XFDF exports (`SafePdf.Shell.FfiMarks`, task 11.3a3) and the selection and
search exports (`SafePdf.Shell.FfiSelect`, task 11.3a4). -/
def ffiModules : Array Lean.Name :=
  #[`SafePdf.Shell.Ffi, `SafePdf.Shell.FfiView, `SafePdf.Shell.FfiMarks, `SafePdf.Shell.FfiSelect]

/-- The C API's modules (`ffiModules`). Not a default
target: `lake build macosFfi` builds it. -/
lean_lib SafePdfFfi where
  roots := ffiModules

/-- `libsafepdfffi.a`: the object files of the `ffiModules` and of every module they import
(the closure Lake would link into an executable, without duplicates), for `macos/build.sh` to
link with Lean's runtime libraries. -/
target macosFfi pkg : FilePath := do
  let mut infos := #[]
  for n in ffiModules do
    let some mod ← findModule? n | error s!"module {n} not found"
    infos := infos.push (← mod.linkInfoNoExport.fetch)
  (Job.collectArray infos).bindM fun is => do
    let objs := is.foldl (fun acc i => i.objs.foldl
      (fun a o => if a.contains o then a else a.push o) acc) #[]
    buildStaticLib (pkg.staticLibDir / "libsafepdfffi.a") (objs.map pure)

/-! ## Platform viewer selection (task 11.4; not default targets)

`lake build macosApp` builds the native macOS shell (`macos/build/SafePdf.app`, Swift/AppKit,
`docs/macos-design.md` §3 decision 6) and fails with a clear message off macOS.
`lake build app` is the platform viewer: `macosApp` on macOS, the Tk `viewer` (plus the
`worker` it starts) elsewhere. The Tk `viewer` stays buildable on macOS by name
(`lake build viewer worker`). None of these is a default target: `lake build`,
`lake build tests fuzz` and `lake exe tests` compile neither Tk nor Swift. -/

/-- The native macOS app bundle `macos/build/SafePdf.app`. Lake builds `macosFfi` and `worker`,
then runs `macos/build.sh` with `SAFEPDF_MACOS_LAKE_DONE=1` (the script then skips its own
`lake build` step, so no `lake build` runs inside this one). `macos/build.sh` stays the single
source of the clang/swiftc flags; it also writes `macos/build/safepdf-mac`,
`macos/build/safepdf_core.o` and `macos/build/core_test`. Not traced: the script runs on every
`lake build macosApp`. Off macOS this target fails before building anything. -/
target macosApp pkg : FilePath := do
  unless Platform.isOSX do
    error "macosApp: the native shell (Swift/AppKit) builds on macOS only; \
      elsewhere use `lake build viewer worker` (Tcl/Tk) or `lake build app`"
  let ffi ← macosFfi.fetch
  let wrk ← worker.fetch
  (ffi.mix wrk).mapM fun _ => do
    let buildSh := pkg.dir / "macos" / "build.sh"
    proc { cmd := "bash", args := #[buildSh.toString], cwd := pkg.dir,
           env := #[("SAFEPDF_MACOS_LAKE_DONE", some "1")] }
    return pkg.dir / "macos" / "build" / "SafePdf.app"

/-- The platform viewer: on macOS the native app (`macosApp`; its output is the bundle's path),
elsewhere the Tk `viewer` executable together with the `worker` it starts (output: the viewer's
path; `lake build viewer` alone does not build `worker`). -/
target app : FilePath := do
  if Platform.isOSX then
    macosApp.fetch
  else
    return (← viewer.fetch).add (← worker.fetch)
