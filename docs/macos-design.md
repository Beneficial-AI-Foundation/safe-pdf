# The native macOS shell — design and port plan (Phase 11)

Written 2026-11-24 from the human's brief: *the macOS port keeps the same design as the
Linux version, but it should feel new — updated, modern design and seamless use.* The spike
(task 11.1, [macos/README.md](../macos/README.md)) passed the human's feel check
("scrolling, pinch and sharpness feel pretty good"). This document is the plan for the full
port: what stays identical, what gets the modern treatment, the architecture decision that
closes task 11.2, and the task breakdown the ledger carries as 11.3a–11.6.

The Tk viewer ([docs/viewer.md](viewer.md)) stays the Linux shell, green and unchanged
(M11's second clause). Nothing in this plan touches the verified core: the shell remains
unverified and replaceable (Plan.md §8); what moves across the FFI is exactly the logic that
already has proofs or `#guard`s, so those keep applying.

## 1. What stays the same (the design)

The layout, the features and every behaviour rule of the Tk viewer, which are themselves
modelled on PDF.js:

* **Layout**: toolbar (left: sidebar toggle, page navigation, page field with labels,
  view-mode control; centre: zoom out/in and the zoom presets; right: the tools —
  Select text, Highlight, Add comment, Add text, Draw — then Save and the overflow menu),
  sidebar with the four panels (thumbnails, outline, attachments, layers), the page area,
  find with highlight-all and a match count.
* **Behaviour**: the zoom model (`Toolbar.ZoomChoice` presets, Automatic Zoom, quantised
  1/64 px/pt, `View.stepInZ`/`stepOutZ`, zoom anchored at the pointer or window centre —
  C2's `View.reanchor`), the view modes (single / continuous / facing / continuous-facing,
  odd/even spreads), page-at-a-time wheel rules, rotation, back/forward history, document
  open settings (9.r8: every open starts afresh), the 10 Mpx per-page cap (12.3b/c), the
  budgets and ceilings (12.3), page labels, external-link confirmation.
* **Selection and marks**: whole-text selection bands (`Select.selBands`), the selection
  bubble, the Highlight pop-over and its five colours, notes with `Marks.noteAnchor`'s
  click-vs-selection rule, Add text and Draw, delete/undo/redo, the active-tool rules
  (`Toolbar.Mode`, exactly one tool pressed, Escape closes pop-overs but keeps the tool).
* **Saving**: marks written into the PDF by incremental update (C7), the first-overwrite
  prompt, Save / Don't Save / Cancel on close, the revision-retention notice, XFDF
  import/export.
* **Keys**: the macOS column of the key table in `Menu.lean` (⌘O/⌘S/⇧⌘S/⌘W/⌘Q, ⌘F with
  ⌘G/⇧⌘G, ⌥⌘G, ⌘[/⌘], ⌘↑/⌘↓, ⌃⌘S, ⌃⌘H, ⌘+/⌘−/⌘0/⌘9, ⌘Z/⇧⌘Z, ⌘.) — already designed to
  Mac conventions in task 10.9 and proven consistent by its `#guard`s.
* **Honest UI** (12.5): the trusted file-identity line in full screen, invisible-text
  counts on copy, the `repaired` flag surfaced, open-settings notes that were not honoured.

## 2. What feels new (the modern translation)

The same design, re-expressed in current AppKit. On macOS 26 the system design is Liquid
Glass (WWDC25 session 310, "Build an AppKit app with the new design"): standard toolbars
and sidebars get the glass treatment automatically when the app is built against the
macOS 26 SDK; `NSGlassEffectView` exists for custom floating controls and is absent on
older systems, so every 26-only call is runtime-gated. Deployment minimum: macOS 14; the
app simply looks pre-glass there.

| Tk viewer surface | Native implementation |
|---|---|
| Window + title `NAME - page k/n - SafePDF` | `NSWindow`, full-size content view, unified toolbar style; `title` = document name with the **document proxy icon** (drag the file out of the title bar), `subtitle` = `page k/n · zoom` (labels as in Tk); native full screen |
| Toolbar (40 px Tk canvas buttons, hand-drawn icons) | `NSToolbar` with standard items; **SF Symbols** icons; adjacent buttons grouped onto shared glass automatically on 26 (`NSToolbarItemGroup` where the grouping should differ); same item order as the Tk bar; no user customisation (parity) |
| Zoom drop-down, view-mode drop-down | `NSMenuToolbarItem`s backed by the same pure models (`ZoomChoice.presets`, `ViewChoice`) |
| Page field | toolbar `NSTextField`, same label/`(k of N)` rules, Enter/Escape/revert semantics from `Toolbar.pageEntry` |
| Find bar | `NSSearchToolbarItem` (collapses to an icon), match count + previous/next beside it; same search semantics and highlight-all |
| Sidebar (Tk frame, 9.r9 panels) | `NSSplitViewController` with a sidebar item — glass/vibrancy material automatic; a segmented control (SF Symbols) switches thumbnails / outline / attachments / layers; `NSCollectionView` thumbnails, `NSOutlineView` outline; ⌃⌘S and the toolbar toggle animate it |
| Canvas + scroll bars, Tcl-emulated momentum | `NSScrollView`: native momentum, rubber-banding, responsive scrolling, overlay scrollers; **live magnification** during pinch (bitmap scales in the gesture, sharp re-render at gesture end); the content scrolls edge-to-edge under the toolbar with the 26 **scroll-edge effect** |
| Blurry-then-sharp swap after zoom | the sharp image **cross-fades** over the scaled one (short `CALayer` transition) — the swap stops being visible |
| Status line (bottom strip) | no status bar (modern apps have none): page/zoom live in the subtitle; render notes, open-settings notes, "zoom limited to 10 Mpx", errors appear as a **transient glass pill** overlay (bottom centre, fades out); persistent flags (`repaired`, encryption) as a small titlebar accessory; the full-screen identity line stays as its own overlay (12.5 requires it) |
| Selection fill `#3874f2` at 35 % | the user's **accent colour** at 35 % over the same `Select.selBands` geometry (falls back to the Tk blue for the default accent); I-beam/hand/crosshair via `NSCursor` from `Toolbar.cursorFor` |
| Selection bubble (Tk window) | a floating glass bar (`NSGlassEffectView`, `NSVisualEffectView` before 26) with SF Symbol buttons; same contents and rules |
| Highlight pop-over, note popup | `NSPopover` anchored to the button / the mark; ⌘Return / Escape / ⌘. as today |
| Right-click menu | `NSMenu` context menu, same items |
| Menubar built from `Menu.lean` | real `NSMenu` menubar **built from the same exported table** (labels, key equivalents, enabled rules); a proper application menu (About SafePDF, Hide, Quit); File/Edit/View/Go plus the standard Window and Help menus |
| Dialogs (Tk message boxes, file dialogs) | `NSOpenPanel`/`NSSavePanel` (UTType `pdf`), `NSAlert` as **document-modal sheets** (Save / Don't Save / Cancel, external link, first overwrite) |
| Dark mode (none in Tk) | full dark-mode support: semantic colours everywhere, dark canvas around the paper-white pages (as Preview), template-rendered symbols |
| Unbundled binary, generic Dock icon | **`SafePdf.app` bundle**: Info.plist (name *SafePDF*, viewer role for `com.adobe.pdf`), `.icns` from `docs/branding/`, ad-hoc code signing. The bundle fixes the application-menu name (viewer.md's "task 11.x") and gives Finder/Dock open-with and Dock-drop for free (part of issue #14) |

Design rules, following Apple's own restraint guidance: glass only on floating controls
(toolbar, selection bubble, status pill) — never behind content; standard controls
everywhere, no custom chrome; animation only where it explains something (sidebar slide,
re-render cross-fade, find-match pulse); first page visible fast (the spike's numbers: init
~50 ms, open ~5 ms, 70–200 ms per page at 2×).

Explicitly *not* in scope for M11 (natural unlocks later): printing via `NSPrintOperation`
(the toolbar keeps the disabled placeholder, as Tk), window tabs for multiple PDFs
(issue #13 — `NSWindow` tabbing makes this cheap later), in-window drag-and-drop
(issue #14), the inspector views.

## 3. Architecture (closes task 11.2)

**Decision: one shared Lean logic layer, exported through the C API; AppKit (Swift) owns
only widgets and events.** The spike's six open questions, answered:

1. **Where the shared logic lives** — in Lean, exported. Any rule that has a theorem or a
   `#guard` (zoom stepping and re-anchoring, selection bands, hit tests and cursors, the
   marks model with undo/redo, `noteAnchor`, the save plan (C7), the key/menu/enablement
   tables, XFDF) crosses the FFI as **pure functions: state in → state out + display
   data**. The UI event loop, views and gesture recognisers are native. Nothing proven is
   reimplemented, so the proofs keep applying to the shipped behaviour.
2. **Structured data crosses as flat C structs** (glyph cells, link rects, outline rows,
   menu/toolbar tables), caller-owned, freed by one `safepdf_free_*` per type — the
   simplest shape to import into Swift. No JSON, no opaque accessor forests.
3. **Pixels**: keep the one `memcpy` for now (measured inside the spike's 70–200 ms page
   times); a retain/release pair over the Lean `ByteArray` is a later optimisation, not a
   plan item.
4. **Rendering is asynchronous via the document worker** (12.2a–d), not in-process threads:
   the C API v2 wraps `Worker.Session` — the GUI reads the file through the capped read
   (12.1) and hands bytes to a **confined worker** (seatbelt sandbox) with priorities
   (current page, neighbours, thumbnails), cancellation, a deadline kill and respawn.
   Completion callbacks land on a caller-supplied dispatch queue. The macOS app is
   sandboxed and stall-free from day one — the spike's in-process render path and its
   known limitations (single thread, no cancellation, document leak) are retired rather
   than fixed.
5. **Packaging**: `safepdf_core.h` + `libsafepdfffi.a` stay the `safe-pdf-core` C
   deliverable under `macos/` for now; promoting them to `include/` + an SwiftPM wrapper is
   deferred until someone outside this repo consumes them. Distribution signing/notarisation
   deferred likewise (ad-hoc signing for M11).
6. **Swift, not Objective-C**, for the shell (`swiftc` ships with the command-line tools;
   the C header imports through a module map; no Xcode project — `macos/build.sh` grows a
   Swift compile step). The spike's `main.m` is replaced, not extended.

Save stays in the GUI process (as in Tk since 12.2c): the GUI holds the document bytes, the
exported `Save` logic plans the incremental update, native panels and file I/O write it.

## 4. Tasks (ledger Phase 11, 11.3a–11.6)

* **11.3a — C API v2 over the worker**: document handles with retain/release (close cancels
  and drains), open from GUI-read capped bytes; async render/text-index/links/outline/
  labels/attachments/layers through `Worker.Session` with callbacks onto a dispatch queue;
  flat C structs + `safepdf_free_*`; the exported pure-logic surface (View/Select/Marks/
  Save/Toolbar/Menu tables).
* **11.3b — App scaffold (Swift)**: bundle, window, toolbar, sidebar, scroll view, menubar
  from the exported table, panels/sheets, dark mode, build script.
* **11.3c — Viewing parity**: view modes, zoom model, pinch + cross-fade, rotation, page
  field, history, open settings, subtitle/status pill, scroll-edge effect.
* **11.3d — Text and navigation parity**: selection, copy, find, links, the four sidebar
  panels, honest-UI items.
* **11.3e — Marks and save parity**: tools, bubble, pop-overs, undo/redo, XFDF, Save/Save
  As with the C7 flow.
* **11.4 — Platform build selection + CI** (as planned): macOS builds the native shell,
  Linux keeps Tk; both non-default targets; a macOS CI job.
* **11.5 — Native smoke**: accessibility-driven scripted session mirroring
  `viewer-smoke.sh`, under the front-app watcher discipline (never activates in background
  mode, as 10.16 established for Tk); the viewer corpus session re-run natively.
* **11.6 — Feel pass with the human** (§5's checklist); fix what feels off; record the
  verdict in the ledger.

## 5. Acceptance

**M11 (unchanged)**: the macOS app passes the M8/M9 corpus and session checks natively
(Cmd keys, momentum scroll, Retina, dark mode); the Linux Tk build stays green and
unchanged.

**Feel checklist (11.6, judged by the human)**: fast flicks through a long PDF (momentum,
rubber-band, pages catch up without stalls — the worker renders, the UI never blocks);
pinch-and-hold mid-gesture, then release (live scaling, prompt sharp cross-fade); repeated
⌘+/⌘− (anchoring, no flicker); window resize (fit modes re-render smoothly, pages stay
centred); light ↔ dark switch while a document is open; dragging between Retina and
non-Retina displays; time to first page against `lake exe viewer`; the new-feel items —
glass toolbar over edge-to-edge content, sidebar material, accent-coloured selection, the
status pill, the proxy icon.

Sources for the macOS 26 design behaviour: Apple, WWDC25 session 310 —
[Build an AppKit app with the new design](https://developer.apple.com/videos/play/wwdc2025/310/)
(automatic toolbar glass grouping, sidebar material, scroll-edge effect, `NSGlassEffectView`,
restraint guidance).
