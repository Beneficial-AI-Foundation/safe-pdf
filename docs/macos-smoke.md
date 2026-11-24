# Native smoke and corpus session of the macOS app (task 11.5)

Plan.md §6 Phase 11 (milestone **M11**: the macOS app passes the M8/M9 corpus and session checks
natively — Cmd keys, momentum scroll, Retina, dark mode — and the Linux Tk build stays green and
unchanged). This is the macOS counterpart of the Tk smoke (`scripts/viewer-smoke.sh`,
docs/viewer.md "Smoke test") and of the Tk corpus check (`scripts/viewer-corpus.sh`,
docs/viewer-corpus.md). Neither Tk script is changed.

    macos/build.sh                                   # the app (macos/build/safepdf-mac)
    scripts/macos-smoke.sh [--no-build] [CASE ...]   # the cases below; CASE: a name prefix (1j)
    scripts/macos-corpus.sh [--no-build] [--corpus DIR] [--json OUT] [--out DIR] \
        [--timeout SEC] [--no-session] [--no-corpus] [--no-fetch] [FILE.pdf ...]

`SAFEPDF_SMOKE_KEEP=1` keeps the smoke's work directory (every session's `session.txt`, PNGs,
saved files), `SAFEPDF_SMOKE_VERBOSE=1` prints a failing session's whole log,
`SAFEPDF_SMOKE_BUNDLE=1` runs the bundle's binary in place (never through LaunchServices).

## Design: an in-process scripted session, not Accessibility

Driving the app through the Accessibility API (AXUIElement) needs the Accessibility permission
(TCC) granted to the *driving* process by the human in System Settings; a script cannot grant
it, and `AXIsProcessTrusted()` is false for a fresh terminal or agent. AX actions on a
background app whose activation policy is Prohibited are also not guaranteed (no menubar of its
own, no key window). The ledger's background discipline (10.16, 10.19) forbids activating the
app, showing a window and System Events (which needs an Automation prompt). So the smoke is an
**in-process scripted session** and no AX case was added (nothing to skip: with the permission
missing an AX case could not run, and with it granted it would have to show a window).

* `macos/App/SmokeSession.swift`, entered from `main.swift` when `SAFEPDF_MACOS_SESSION=SCRIPT`
  is set (output in `SAFEPDF_MACOS_SESSION_OUT`, inputs `$IN` = `SAFEPDF_SESSION_IN`): the
  activation policy is Prohibited before anything else (as the self-test), the app never calls
  `run`, `activate`, `showWindow` or `makeKeyAndOrderFront`.
* It drives the app's own `DocumentWindowController`: menu commands through `run` (the same
  path as a menu item or toolbar button, enabled states included), keys through the **menubar
  built from the exported table** (`MainMenu.build`: the item whose key equivalent matches,
  its validation, its action — what AppKit's `performKeyEquivalent` does) and otherwise the page
  view's `keyDown`, the zoom and view drop-downs' items, the colour and tool items, the page
  field, the sidebar panels, the marks controller's pointer, the `SaveController`.
* The window's content is hosted **off the window** (the split view is detached from it), so no
  popover, note editor, text-box editor or sheet can ever be ordered in: the controllers take
  their headless path (no window), as in the self-test. The window itself is never ordered in;
  its frame autosave is turned off (no defaults written). After every step the session fails
  if any of its windows is visible or the app is active.
* The save flow's questions and panels are answered by script (`ScriptedDialogs`, the
  self-test's); Copy and Copy Address go to a private pasteboard, never the user's; external
  addresses are never opened (the app has no NSWorkspace call); an outline item's external
  address is answered by the session (Copy Address / Cancel) as the window's sheet would.
* The front-app watcher of `macos/selftest.sh` runs around every session: `lsappinfo` every
  0.2 s; if the PID the script started is ever the front app or a Foreground app it is killed
  and the case fails. Only that PID is looked at.

Headless differences, each explicit in the session's log:

* AppKit scrolls an `NSScrollView` only in a window: in the continuous modes the session moves
  the clip view by each wheel event's precise delta (no momentum, no elasticity) after giving
  the event to the scroll view (which handles page-at-a-time wheel turning itself); the page
  view follows through its own bounds observer. **Momentum and elastic scrolling are AppKit's
  and are not exercised.**
* `NSWindow.close()` of a window that was closed before and not ordered in again does nothing
  (the app orders the window in on the next open with `showWindow`); when a close goes on and
  AppKit posted no `willClose`, the session posts it so the controller's `windowWillClose` runs.
* `/PageMode /FullScreen` and the 12.5 identity line need a window on screen (skipped).

## The command language

One command per line; `#` comments; `$OUT` and `$IN` are expanded. Every step and every check
goes to stderr and `session.txt`; the last line is
`session: N steps, F failures, S skipped steps, longest block … ms (…), T s`; exit 0 when no
check failed.

| command | what it does |
|---|---|
| `open PATH`, `open-nowait PATH` | the window controller's open (the unsaved-marks question first), then waits for renders, sidebar, labels |
| `open-error PATH` | the open path's `Document(url:)` must fail; `error` = its text |
| `cmd NAME`, `try NAME` | a Menu.Cmd by its exported name or label (`nextPage`, `zoom in`); `cmd` fails when disabled |
| `key SPEC` | `cmd+shift+s`, `ctrl+cmd+h`, `opt+cmd+g`, `pagedown`, `f9`, `delete`, `w` …: menubar key equivalent, else the page view's key |
| `zoom LABEL`, `zoompct N`, `view LABEL`, `goto TEXT` | zoom drop-down preset, a percentage, view-mode drop-down, page field |
| `size W H`, `scale S`, `dark on\|off` | page-area size (points), backing scale (Retina 2 / 1), appearance |
| `dblclick P G`, `click-glyph P G`, `drag P A B`, `dblclick-hit` | pointer on glyphs of page P (1-based), or on the current search hit |
| `find TEXT`, `find-next`, `find-prev`, `find-close` | the search field's Find (and ⌘G / ⇧⌘G's action) |
| `link P N`, `link-answer copy\|cancel` | click link N of page P (a point of it no later link covers), answer the external-link sheet |
| `outline N\|third\|last`, `outline-answer copy\|cancel` | activate an outline row; answer an external address |
| `panel NAME`, `thumb N`, `attach-save I PATH`, `layer I` | sidebar panels |
| `color NAME`, `tool NAME`, `note TEXT`, `note-at P X Y`, `note-left`, `note-save TEXT`, `note-close [TEXT]`, `select-mark first\|last`, `open-mark …`, `freetext P X Y TEXT`, `ink P X Y`, `escape` | marks |
| `answer KEY…`, `saveurl PATH`, `openurl PATH`, `seedless`, `seeded` | script the dialogs; fail the IV random source |
| `close`, `quit` | the close button (`closed`), the quit question (`quit`) |
| `wheel DY N`, `wheel-turn DY` | N precise wheel events of DY points; events until the page turns |
| `copy-file`, `append-file`, `chmod MODE PATH`, `prefix A B` | files; A's bytes a prefix of B (C7) |
| `measure`, `measure-ink`, `measure-paper`, `measure-mark`, `measure-selection`, `snapshot NAME`, `list-keys`, `remember NAME KEY` | measurements into keys |
| `expect KEY OP VALUE` | `=` `!=` `~` `!~` `^` `<` `>` `<=` `>=`, `near VALUE TOL`; `@NAME` a remembered value |
| `async on\|off`, `corpus-pass`, `skip REASON`, `stop` | no waiting; the M8 pass; a skipped step |

Keys `expect` reads: `page pages doc zoom choice scroll spread rtl rotation title subtitle pill
pills edited dirty marks saved undo-depth last-mark kinds mark-selected note-open tool selection
clipboard sidebar panel buttons outline-rows attachments layer-rows find hit uri uri-pending
history-back errors key backing encrypted repaired orient top centre-x centre-y centre-page
viewchoice page-w page-h page1-x page2-x laid-out visible-pages asked asked-count maxblock
last_ms policy visible-windows cursor doc-title`, `enabled:CMD`, `radio:CMD`, `layer:I`,
`size:PATH`, `file:PATH`, and whatever a command stored (`ink`, `paper.lum`, `mark.g`, `wheel_pages`,
`wheel_monotonic`, `via`, `ran`, `closed`, `quit`, `error`, `attach`, …).

## The cases (every Tk smoke case, one by one)

| Tk case | native | how / why not |
|---|---|---|
| 1 two-page PDF | ported | ink on page 1 at Page Fit, Next page to page 2 (/Rotate 90: landscape), title, subtitle |
| 1a zoom/rotation | ported | ⌘0 ⌘+ ⌘− (100 → 125 → 75 %), ⌘R / ⌘L swap the sides, ⌘9, `w` |
| 1b scrolling/anchoring | ported | 200 %, a zoom step keeps the centre's page point (C2), arrows and space scroll, Page Down / Up, ⌘↓ ⌘↑ |
| 1c odd file name | ported | spaces, brackets, braces, `$`, `ü` in the name and title |
| 1d text/select/search | ported | ⌘A ⌘C, double click a word, drag, Find across pages with wrap, not found; hidden text announced (12.5) |
| 1e nav | ported | page labels in the page field and subtitle, internal link + ⌘[ ⌘], external link asked (Cancel, Copy Address; never opened), outline jump and external item, ⌃⌘S and F9 |
| 1f menubar | ported | enabled states, Go / View commands, the wheel across page boundaries both ways (continuous scrolling emulated, see above) |
| 1g toolbar | ported | zoom and view drop-downs, page field, sidebar toggle without an outline (thumbnails) |
| 1h marks | ported | ⌃⌘H highlight (yellow pixels), recolour from the Highlight menu (red pixels), Delete, a note, marks kept across zoom / rotation / pages |
| 1i bubble | partly | tool-mode highlight on mouse-up and Show all (in 1h); the bubble's own buttons are skipped (views over the page; macos/selftest.sh drives them) |
| 1j save/reopen | ported | first-overwrite question (Cancel writes nothing), Overwrite, C7 prefix, reopen keeps the zoom, marks saved, second save asks nothing, mutool sees the annotations |
| 1j' edit | ported | saved marks recoloured and deleted, third revision (prefix), the revision-retention note (12.5) |
| 1j encrypted | ported | RC4-128 and AES-256 files saved by incremental update; RC4 note; refused without fresh random bytes (nothing written) |
| 1j'' xfdf | ported | export, delete all, import (one undo step), re-import adds nothing, the hostile samples of Tests/xfdf refused (store unchanged), the other samples imported, a missing file |
| 1j''' editors | ported | Add text and Draw, saved and reopened as saved marks, mutool sees FreeText and Ink |
| 1k view modes | ported | continuous, continuous facing (1\|2 side by side), facing (Next by two), even spreads, single page, radio states |
| 1l lockdown | n.a. | Tk `send` and X resources: the native app has no Tcl interpreter |
| 1m async | ported | a slow page 1: open, zoom and Last page return at once (< 250 ms), page 2 shown meanwhile |
| 1n m9 | n.a. here | the M9 paper run is `scripts/macos-corpus.sh`'s session (below) |
| 1o wheelflow | ported | small precise deltas cross pages without going back (continuous, emulated), page-at-a-time wheel turns |
| 1p keys | ported | every accelerator of the exported table reaches its own command through the menubar (27/27), ⌘G is Find next, ⌥⌘G Go to page, ⌘W closes; the icon sizes are skipped (the bundle's .icns) |
| 1q r4 | ported | the view-mode drop-down follows the View menu and the other way round |
| 1r savedlg | ported | Save As proposes STEM-annotated.pdf, refuses a folder, adds the extension; the XFDF export refuses a folder |
| 1s opensettings | ported | /OpenAction XYZ, R2L, TwoColumnRight, a named destination, JavaScript not run, ViewerPreferences (window title), /PageMode UseThumbs / UseNone, defaults again; /FullScreen skipped |
| 1t noteclose | ported | an empty new note goes, a typed one stays, a stored text survives a close without Save, an empty highlight comment goes |
| 1u thumbs | ported | the panel, a click jumps (history), rotation; thumbperf: the corpus timings are macos-corpus.sh's |
| 1v attach | ported | listed, saved exactly, the opened document refused as a target |
| 1w layers | ported | /UseOC, toggling re-renders, toggling back |
| 2 bad inputs | ported | a non-PDF, a truncated and a missing file give an error text; the app goes on |
| 1x undo | ported | ⌘Z / ⇧⌘Z (in 1h, 1j'') |
| 10.6 dismiss | n.a. here | the bubble and pop-overs are views over the page; Escape's order is macos/selftest.sh's (SelfTestMarks) |
| 10.10 tint | ported | as "dark mode": the selection tinted in light and dark |
| 10.8 tools | ported | tool states (in 1h, 1j''') |
| 12.5 honest | partly | hidden characters on copy (1d), the revision-retention note (1j'); the identity line in full screen is skipped (needs a window on screen) |
| 12.2c worker | partly | pages, text and links through the confined worker; the stalled-render test hook has no native counterpart |
| (M11) dark mode | new | paper stays white, the canvas darkens, the selection keeps its accent tint |
| (M11) Retina | new | backing scale 2 → 1 → 2: render key follows the pixels, zoom and page size in points stay |

## The corpus check (M8 / M9 natively)

`scripts/macos-corpus.sh` takes `corpus/files/*.pdf` (fetched when missing, `--no-fetch` to
skip; no network: reported as skipped, exit 0) or `--corpus DIR` (every file verified against
`corpus/manifest.json`'s SHA-256 and size first). Per file one headless session:
`size 1600 1000`, `open`, `corpus-pass` — the Tk check's setup (1600×1000, continuous view,
Automatic Zoom, the sidebar as the page mode says). Then the three-paper session (outline jump,
find, double click + copy, ⌃⌘H, a note left of the highlight with `[x] {y} $z \ ü`, the first
Save answered Save As `FILE-annotated.pdf`, ⌘W, reopen: marks saved and the highlight yellow from
the renderer, ⌘W; the C7 prefix; qpdf when installed). The thresholds are docs/viewer-corpus.md's.

Measured definitions (native): *time to display* = a page's first render at its current zoom,
from the request to its delivery on the main thread (through the worker); *wait after Next
page* = from the command until the new current page has its image and nothing is pending;
*open* = from the open until the current page is shown; *longest block* = the longest command
call or run-loop pass on the main thread (a hang is > 5 s); *peak footprint* = the lifetime
maximum physical footprint (`proc_pid_rusage`) of the app and of its worker processes, sampled
every 200 ms.

## What the runs cover for M11, and what needs the human

Covered by these scripts (headless, on the real controllers): the M8 corpus thresholds and the
three-paper session natively, the Cmd keys of the menubar, view modes, the save / XFDF /
encrypted paths, dark mode (paper and canvas colours, selection tint), the Retina backing change
(2 ↔ 1). The **human (task 11.6)** judges what only a window on screen shows: momentum and
elastic scrolling and the trackpad's feel (emulated here without momentum), pinch, moving the
window between a Retina and a non-Retina screen, sheets, pop-overs, the note editor, full
screen and the identity line, the look of dark mode and Liquid Glass, VoiceOver.
