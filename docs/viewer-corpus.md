# The viewer on the corpus (M8 check)

Task 8.5 (Plan.md §6 Phase 8, milestone **M8: daily-drivable viewer on the corpus**; §8 native
app). `scripts/viewer-corpus.sh` drives the compiled `viewer` over every PDF in
`corpus/files/` and through a scripted reading session, and turns "daily-drivable" into
measured numbers. The viewer itself is not changed for this: the driver only uses what the
running viewer already offers (its Tk interpreter, its menus, key and mouse bindings).

## Running it

    lake build viewer
    scripts/viewer-corpus.sh [--no-build] [--json OUT] [--out DIR] [--timeout SEC] \
                             [--no-session] [--no-corpus] [FILE.pdf ...]

Without files it takes `corpus/files/*.pdf` (git-ignored; see `docs/corpus.md` to fetch it).
`--json OUT` writes every number below (per file, per page, per session step) as JSON;
`--out DIR` keeps the raw driver logs (otherwise a temporary directory is removed);
`--timeout` is the hard limit per file (default 900 s; the driver and then the viewer are
killed and the file counts as a crash). The exit status is 0 exactly when M8 holds under the
thresholds below. Needs `Xvfb`, `wish` (Tk 8.6 or 9.0 — the lean-tools sandbox has Debian's
`wish9.0`), `python3`; `qpdf` is optional (session check). A full run over the 81 corpus files
takes about 5 minutes on the sandbox (8 cores, one file at a time).

### How it drives the viewer

* Every file gets its **own Xvfb** (display `:140`–`:199`, the first free one; the script never
  uses `$DISPLAY`, so a stale `:99` does not matter, and never `xvfb-run`) and is killed after
  the file. The viewer runs at `SAFEPDF_VIEWER_GEOMETRY=1600x1000` in the continuous view
  (`SAFEPDF_VIEWER_VIEW=continuous`), Automatic Zoom (125 % on the corpus' Letter/A4 pages
  with the outline sidebar open), substitute fonts on (the default).
* The driver is a small Tcl script run by `wish` on the same display. It reaches the viewer's
  interpreter with Tk's **`send`** (the viewer registers as Tk application `tk`) and only
  evaluates what a user's input would cause: `.menubar.go invoke {Next page}`, `event generate`
  of keys and clicks, the find bar, the context menu, Ctrl+S / Ctrl+W.
* It **instruments** the viewer from the outside: `::safepdf::emit` — the single Tcl command
  through which every Tk event reaches the Lean code — is renamed and wrapped by a procedure
  that times each event (`clock microseconds`), and execution traces on `image` and `.c` note
  which page photos (`image create photo ::safepdf::pgN`) or render-error texts (canvas items
  tagged `perr eN`) each event created. The viewer's synchronous rendering is therefore
  measured exactly where the user waits: an event that renders a page blocks the window for
  its whole duration.
* `File > Open` is answered by the driver (`tk_getOpenFile` is replaced in the viewer's
  interpreter by a procedure returning the file), so the measured open starts with an empty
  cache, exactly like opening from the menu (the file was opened once at start-up from the
  command line, which warms the OS file cache).
* **Corpus pass.** Open; then `Go > Next page` until the last page; after each step the
  driver waits (polling with `send`) until the new current page is on screen and no deferred
  render (`after … renderMore`) is pending, i.e. the pages in view and one more each side are
  rendered (`View.wantedPages`). Recorded per file: whether it opened (status line without
  `cannot open`/`cannot read`, at least one page), the page count, for every page the
  **time-to-display** = the duration of the event that put the page on screen (render +
  photo upload + overlay; for page 1, the render time the status line reports, since the open
  event also parses the file), the **wait** after each Next page (from the click until the
  page is on screen; ≈ 0 when the page was already rendered as a neighbour), every event over
  5 s (**hang**: the window is frozen that long), render errors, the viewer's exit status and
  stderr (a crash = non-zero/signal exit, the viewer vanishing mid-run, or the hard timeout),
  and the **peak RSS** (`VmHWM` of `/proc/PID/status`, read every 10 pages and at the end).
* **Session** on three papers — `arxiv-2201.11903` (outline, 43 pages),
  `www.ntsb.gov-AIR2201` (encrypted, AES-256 / R6, 11 pages) and `arxiv-2303.08774` (long,
  100 pages), each on a copy in the work directory: open; click the outline entry at about a
  third of the list (`.ol.t`, `<ButtonRelease-1>` at its row; the page must change); Ctrl+F,
  a word (`arithmetic`, `airplane`, `benchmark`), Enter (F3 once if the page has several
  hits): the status must say `hit k/n on page p`; a double click on the current (orange)
  hit's word and Ctrl+C: the clipboard must contain the word; `h` highlights the selection
  (status `highlighted`, the photo's paper pixel under it `255 255 152`); a right click left of
  it, `Add note...` in the context menu, a note text with Tcl metacharacters and `ü`, Save in
  the popup (status `note saved`); the title starts with `* `; Ctrl+S (status `saved …` to
  `FILE-annotated.pdf`); Ctrl+W (title back to `safe-pdf`); `File > Open` the saved file: the
  status must report ≥ 2 saved marks and, on the hit's page, the paper under the highlight is
  yellow again (now drawn by the renderer from the appearance stream); Ctrl+W, Quit. The
  script then runs `qpdf --check` on the saved file and checks that the original is a
  byte-for-byte prefix of it (`cmp -n`).

### Limits of the method

* `send` must work: Tk refuses it when the X server's access control is off (`xhost +`); the
  private Xvfb started here has it on. If the viewer ever disables `send` (see *Findings*),
  this script needs an equivalent hook.
* Times are wall-clock on a shared machine (the sandbox: 8 cores, one viewer at a time); they
  are rendering times of the verified core plus Tk's photo upload, not frame timings.
* Pages are visited front to back with Next page; scrolling with the wheel inside a page
  (task 9.2, the `scroll` smoke benchmark) is not repeated here. A page rendered as a
  neighbour is not rendered again when it becomes current, so every page is measured once.
* The session uses the context menu without its grab (it is unposted before the entry is
  invoked) and generated events; a real pointer and keyboard are not involved.

## What "daily-drivable" means here (proposed thresholds)

M8 holds when, on the whole corpus at 1600×1000 in the continuous view:

1. **Every corpus file opens** (a document with pages; no `cannot open`).
2. **Every page is displayed** (as an image, or — counted separately — as a render-error
   text; neither may be missing).
3. **No crash**: the viewer exits 0 on every file, never disappears mid-run, never needs the
   hard timeout.
4. **No hang**: no single event (render, open, search, save) blocks the window for more than
   **5 s**, and no page's time-to-display exceeds 5 s.
5. **p95 time-to-display ≤ 500 ms** over all corpus pages (median reported; the M7 target of
   a median page < 100 ms compiled is the renderer's own milestone, not this one).
6. **Memory bounded**: peak RSS ≤ **1 GiB** for every file (the page cache is capped at
   256 MiB / 64 entries, Tk holds the photos in view plus two).
7. **The session passes** on the three papers (all steps above, qpdf and prefix checks).

## Results

Measured on commit **b5da79e** (wave 46e; `viewer` built from it unchanged), Linux sandbox
(aarch64, 8 cores, Tk 9.0, Xvfb), 2026-11-20, one full run of `scripts/viewer-corpus.sh`
(about 5 minutes; system load average ≈ 3–4 from other jobs during the run). An earlier run
(at a load of up to ≈ 20, before two timing fixes in the session driver) gave the same corpus
numbers within a few per cent (p95 238 ms, max 2,936 ms, peak 1,413 MiB).

### Summary

| | |
|---|---|
| files opened | **81 / 81** |
| pages displayed | **2,450 / 2,450** (0 render errors) |
| time-to-display, all pages | median **73 ms**, p95 **233 ms**, max **3,394 ms** |
| pages over 500 ms / over 1 s / over 5 s | 47 / 10 / **0** |
| wait after Next page (page usually already rendered as a neighbour) | median 1.3 ms, p95 103 ms, max 2,281 ms |
| open (parse + first page, File > Open) | median 77 ms, max 501 ms (`arxiv-2112.10752`) |
| hangs (any event > 5 s) | **0** (longest event: a 3.4 s page render) |
| crashes / non-zero exits / timeouts | **0 / 0 / 0**; nothing on stderr |
| peak RSS (VmHWM) | median 242 MiB, max **1,417 MiB** (`arxiv-2501.12948`); all others ≤ 534 MiB |
| session (3 papers) | **3 / 3 passed** (every step; qpdf --check ok; original a byte prefix) |

Thresholds: every file opens — yes; every page displayed — yes; no crash — yes; no hang —
yes; p95 ≤ 500 ms — yes (233 ms); **memory ≤ 1 GiB — no** (one file); session — yes.

**M8 does not hold yet under these thresholds, for one reason: the peak memory of
`arxiv-2501.12948`.** Everything else holds with margin. With a 2 GiB bound it would hold;
the threshold is left at 1 GiB on purpose (see *Findings*, F1).

### Findings (for follow-up tasks; nothing was changed in the viewer or the core)

* **F1 — 1.4 GiB peak on one page (memory).** `arxiv-2501.12948.pdf` page 16 holds one
  DCT image of **11881×7646** RGB (90 Mpx, 272 MB decoded). Rendering that page alone
  (`SAFEPDF_PAGE=16 inspect --view raster`) peaks at **1,203 MiB RSS** at 72, 90 and 150 dpi
  alike (every other page of the file: 53–58 MiB), so the image is decoded at full resolution
  regardless of the output size and held in several full-size copies. In the viewer the
  page takes 1.0 s and VmHWM jumps from 201 MiB to 1,413 MiB while pages 11–20 are visited.
  Reproduce: `scripts/viewer-corpus.sh --no-session corpus/files/arxiv-2501.12948.pdf`, or
  the `inspect` command above under a peak-RSS meter. Suggested follow-up: decode (or
  subsample) to the device resolution / free intermediate buffers early; the image passes
  `Limits`, so this is a footprint issue, not a limit violation.
* **F2 — slow vector pages (not hangs).** Ten pages take over 1 s, the slowest
  `arxiv-2307.09288` p25 3.39 s, `arxiv-2210.00002` p36 2.28 s / p31 1.91 s,
  `arxiv-1303.5076` p22 1.78 s / p23 1.76 s, `arxiv-2112.10752` p32 1.31 s. The core alone
  gives the same (`SAFEPDF_PAGE=25 SAFEPDF_DPI=125 inspect --view raster
  corpus/files/arxiv-2307.09288.pdf` → 2.75 s; `arxiv-2210.00002` p36 2.27 s;
  `arxiv-1303.5076` p22 1.33 s), so it is renderer cost (M7 work), not the shell. Because
  rendering is synchronous, the window is frozen for that time (docs/viewer.md, "Not done:
  rendering in a background thread"); in continuous mode this usually happens while the
  page is still a neighbour below the view, i.e. on the Next-page step before it.
* **F3 — Tk `send` is enabled in the viewer (defence in depth).** The viewer's interpreter
  registers as Tk application `tk`, and any X client of the same display that Tk's `send`
  access check admits can evaluate arbitrary Tcl in it (`exec` included) — this script relies
  on exactly that. A PDF cannot reach it, so it is outside the threat model of the core, but a
  shell meant to be safe could `rename send {}` in `Viewer.setupScript` unless a test hook asks for it; this script would then need such a
  hook (e.g. keep `send` only when `SAFEPDF_VIEWER_DRIVE=1`).
* No crash, no hang, no render error, no stderr output, no failed session step. The encrypted
  NTSB file (AES-256, R6) saves by incremental update (9.5f) and reopens with its marks.

### Session details

| paper | outline jump | search → hit | copy | save | reopen |
|---|---|---|---|---|---|
| `arxiv-2201.11903` (outline, 43 p.) | `8 Conclusions`: p1 → p9, 279 ms | `arithmetic`: hit on p9, 223 ms | `arithmetic` | 2 marks, 2,231 bytes appended | 2 saved marks, highlight drawn by the renderer |
| `www.ntsb.gov-AIR2201` (encrypted R6, 11 p.) | `Conclusion`: p1 → p8, 318 ms | `airplane`: p1 (wrapped), 255 ms | `airplanes` | 2 marks, 2,561 bytes appended | 2 saved marks, highlight drawn |
| `arxiv-2303.08774` (long, 100 p.) | `Risks & mitigations`: p1 → p11, 270 ms | `benchmark`: p14, 362 ms | `benchmarks` | 2 marks, 1,848 bytes appended | 2 saved marks, highlight drawn |

The copied word is the whole word under the double click (the search matched its prefix).
Save (Ctrl+S, including the strict re-parse of the result and reopening it) took 137, 233 and 165 ms.

### Per file

Time-to-display per page as defined above; open = File > Open (parse + first page).

| file | pages | open ms | median ms | p95 ms | max ms | peak RSS MiB |
|---|--:|--:|--:|--:|--:|--:|
| arxiv-0704.0001 | 37 | 118 | 118 | 182 | 225 | 341 |
| arxiv-0712.3572 | 14 | 81 | 98 | 103 | 163 | 226 |
| arxiv-0801.0001 | 10 | 58 | 50 | 67 | 67 | 181 |
| arxiv-0805.0004 | 21 | 86 | 119 | 359 | 426 | 258 |
| arxiv-0812.0001 | 11 | 114 | 106 | 216 | 216 | 208 |
| arxiv-0903.0001 | 20 | 27 | 48 | 57 | 59 | 232 |
| arxiv-0905.0002 | 45 | 64 | 76 | 86 | 90 | 374 |
| arxiv-1003.0001 | 14 | 111 | 121 | 214 | 294 | 202 |
| arxiv-1008.0003 | 13 | 90 | 115 | 137 | 245 | 205 |
| arxiv-1101.00001 | 12 | 105 | 115 | 216 | 313 | 206 |
| arxiv-1105.2345 | 10 | 55 | 91 | 136 | 136 | 180 |
| arxiv-1207.7214 | 38 | 56 | 95 | 112 | 117 | 347 |
| arxiv-1207.7235 | 42 | 42 | 63 | 80 | 106 | 376 |
| arxiv-1212.00001 | 11 | 60 | 48 | 66 | 66 | 184 |
| arxiv-1301.3781 | 12 | 57 | 61 | 68 | 70 | 184 |
| arxiv-1303.5076 | 69 | 160 | 129 | 1108 | 1776 | 458 |
| arxiv-1406.2661 | 9 | 66 | 70 | 148 | 148 | 175 |
| arxiv-1409.0003 | 30 | 27 | 79 | 87 | 88 | 304 |
| arxiv-1409.0473 | 15 | 70 | 68 | 86 | 150 | 202 |
| arxiv-1409.1556 | 14 | 77 | 74 | 83 | 94 | 196 |
| arxiv-1412.6980 | 15 | 85 | 83 | 145 | 189 | 216 |
| arxiv-1502.03167 | 11 | 84 | 90 | 104 | 104 | 182 |
| arxiv-1503.02531 | 9 | 69 | 72 | 82 | 82 | 173 |
| arxiv-1505.00001 | 4 | 134 | 117 | 166 | 166 | 166 |
| arxiv-1512.03385 | 12 | 87 | 95 | 106 | 135 | 193 |
| arxiv-1602.03837 | 16 | 95 | 98 | 133 | 197 | 216 |
| arxiv-1603.04467 | 19 | 89 | 84 | 128 | 156 | 248 |
| arxiv-1706.00001 | 10 | 115 | 113 | 158 | 158 | 183 |
| arxiv-1706.03762 | 15 | 59 | 64 | 375 | 417 | 235 |
| arxiv-1711.05101 | 19 | 75 | 85 | 347 | 371 | 296 |
| arxiv-1807.06209 | 73 | 146 | 133 | 421 | 825 | 500 |
| arxiv-1808.00001 | 20 | 123 | 110 | 175 | 221 | 241 |
| arxiv-1810.04805 | 16 | 75 | 79 | 150 | 192 | 231 |
| arxiv-1904.00001 | 20 | 64 | 68 | 87 | 87 | 232 |
| arxiv-1912.01703 | 12 | 50 | 67 | 77 | 98 | 189 |
| arxiv-2005.14165 | 75 | 53 | 77 | 506 | 987 | 470 |
| arxiv-2006.00001 | 11 | 85 | 116 | 310 | 310 | 194 |
| arxiv-2006.11239 | 25 | 117 | 102 | 860 | 875 | 397 |
| arxiv-2010.11929 | 22 | 71 | 79 | 240 | 596 | 270 |
| arxiv-2106.09685 | 26 | 88 | 72 | 195 | 492 | 355 |
| arxiv-2111.00001 | 13 | 113 | 135 | 238 | 290 | 239 |
| arxiv-2112.10752 | 45 | 501 | 239 | 778 | 1309 | 534 |
| arxiv-2201.11903 | 43 | 80 | 61 | 87 | 115 | 365 |
| arxiv-2203.02155 | 68 | 63 | 66 | 105 | 335 | 448 |
| arxiv-2209.00001 | 19 | 84 | 75 | 87 | 160 | 249 |
| arxiv-2210.00002 | 48 | 56 | 48 | 1293 | 2279 | 440 |
| arxiv-2302.13971 | 27 | 80 | 65 | 139 | 426 | 278 |
| arxiv-2303.08774 | 100 | 68 | 66 | 118 | 413 | 443 |
| arxiv-2304.00001 | 5 | 108 | 102 | 161 | 161 | 164 |
| arxiv-2307.09288 | 77 | 62 | 97 | 451 | 3394 | 509 |
| arxiv-2308.00001 | 17 | 49 | 58 | 68 | 69 | 214 |
| arxiv-2401.00001 | 16 | 70 | 93 | 280 | 559 | 345 |
| arxiv-2402.00003 | 5 | 110 | 132 | 196 | 196 | 156 |
| arxiv-2405.00001 | 6 | 108 | 98 | 133 | 133 | 170 |
| arxiv-2412.19437 | 53 | 139 | 65 | 543 | 569 | 408 |
| arxiv-2501.12948 | 86 | 69 | 65 | 280 | 1037 | 1417 |
| arxiv-2504.00001 | 8 | 91 | 90 | 102 | 102 | 173 |
| arxiv-2507.00001 | 25 | 82 | 80 | 87 | 89 | 263 |
| arxiv-2508.00001 | 3 | 58 | 52 | 52 | 52 | 136 |
| arxiv-2511.00001 | 52 | 28 | 59 | 72 | 85 | 386 |
| arxiv-2512.00001 | 4 | 137 | 127 | 134 | 134 | 179 |
| arxiv-2601.00001 | 44 | 57 | 74 | 248 | 399 | 390 |
| arxiv-2602.00001 | 21 | 65 | 70 | 83 | 86 | 247 |
| arxiv-2603.00001 | 29 | 63 | 53 | 68 | 69 | 286 |
| arxiv-astro-ph_0603449 | 91 | 51 | 50 | 65 | 69 | 383 |
| arxiv-astro-ph_9805201 | 72 | 70 | 55 | 81 | 85 | 417 |
| arxiv-astro-ph_9812133 | 33 | 76 | 68 | 128 | 130 | 310 |
| arxiv-cond-mat_0410550 | 5 | 90 | 102 | 234 | 234 | 172 |
| arxiv-cs_0410012 | 8 | 114 | 132 | 291 | 291 | 171 |
| arxiv-gr-qc_0507012 | 12 | 30 | 37 | 44 | 47 | 191 |
| arxiv-hep-th_9711200 | 22 | 38 | 54 | 63 | 65 | 242 |
| arxiv-math_0211159 | 39 | 47 | 55 | 65 | 68 | 338 |
| arxiv-math_0303109 | 22 | 65 | 76 | 84 | 85 | 243 |
| arxiv-quant-ph_9508027 | 28 | 39 | 68 | 75 | 84 | 276 |
| www.ntsb.gov-AAR0501 | 120 | 153 | 58 | 95 | 558 | 511 |
| www.ntsb.gov-AAR0701 | 173 | 221 | 61 | 111 | 256 | 454 |
| www.ntsb.gov-AAR1201 | 74 | 94 | 55 | 89 | 145 | 396 |
| www.ntsb.gov-AIR2201 | 11 | 197 | 86 | 171 | 171 | 182 |
| www.ntsb.gov-MIR2301 | 12 | 317 | 114 | 158 | 292 | 193 |
| www.ntsb.gov-RAR0801 | 36 | 74 | 77 | 103 | 107 | 328 |
| www.uscis.gov-g-1145 | 1 | 105 | 98 | 98 | 98 | 117 |
