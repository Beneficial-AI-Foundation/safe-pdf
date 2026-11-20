# The viewer as bib-lean's reader

Plan.md §6 Phase 10 (tasks 10.1–10.4). `viewer --biblean` speaks the reader contract of the
sibling project bib-lean (`bib-lean/docs/READER-CONTRACT.md`, which is authoritative): bib-lean
starts the viewer as a child process, the viewer fetches the PDF over loopback HTTP, shows it,
and sends annotations, the re-saved file, the full text and detected identifiers back.
Nothing here depends on bib-lean's code; the code is shell code under
`SafePdf/Shell/App/BibLean/` (`Http`, `Launch`, `Text`, `Annots`, `SelfTest`) and the entry
point `SafePdf/Shell/App/Main.lean`.

## Building

`viewer` is a **non-default** target (it needs Tcl/Tk; see `docs/viewer.md`):

    lake build viewer          # .lake/build/bin/viewer

bib-lean requires this repository as a Lake dependency pinned by commit and builds the same
target (Plan.md §8 decision of 2026-11-20); its own plain `lake build` never needs Tk.

## Configuring bib-lean

In `<LIB>/config` (or per launch with `biblean open KEY --reader '…'`):

    reader = exec /path/to/viewer --biblean --page {page}

bib-lean splits the words itself (no shell, nothing expanded) and replaces `{page}` with the
zero-based page to open at (`0` when none was asked for).

## What the viewer receives (contract §2)

| | |
|---|---|
| `BIBLEAN_SERVER` | `http://127.0.0.1:PORT` (also `localhost`); anything else, in particular a non-loopback host, is a usage error (exit 2). The client only ever connects to `127.0.0.1`. |
| `BIBLEAN_ATTACHMENT` | the attachment's 8-character item key (exit 2 if malformed) |
| `BIBLEAN_PAGE` | the zero-based page (1–6 digits, else ignored); absent when none was asked for. It wins over `--page N`, which carries the `{page}` of the `exec` template. A page beyond the page count is ignored. |
| **file descriptor 3** | the bearer token: one line, 64 lowercase hex digits. Read once at start from `/dev/fd/3`; never taken from argv or the environment, never printed. A missing or malformed token is exit 3. |

The token is held in a type without `ToString`/`Repr` and only ever written into the
`Authorization: Bearer` header of requests to the loopback origin. Error messages name the
method, the path (holding only the key) and the HTTP status, never the token or a body.
File descriptor 3 is **closed** right after a valid token was read from it (contract SHOULD;
task 10.1b): `close(3)` in the C shim (`safepdf_close_fd3`, `Shim.closeFd3`), installed by
`Main.lean` as `Launch.closeTokenFd` and called by `Launch.openFromBibLean`, so the window,
`--probe` and `--self-test` all close it. After a failed read fd 3 is left alone.

## Modes

    viewer --biblean [--page N]                     # the window
    viewer --biblean [--page N] --self-test         # headless conformance run (task 10.4)
    viewer --biblean [--page N] --probe [--annots echo|demo]   # headless diagnostics (tests)

Exit codes (contract §5, as bib-lean's stock viewer): `0` closed cleanly / the run finished,
`1` failure (server refused, the file did not open, a self-test step failed), `2` usage error,
`3` no valid token on file descriptor 3.

### The window

Fetches `GET /api/attachments/{key}/file` into the strict parser (`Api.openBytes`), the title
from `GET /api/items/{key}` and its parent; posts every page's text to `/fulltext` and the
first DOI/arXiv id of pages 1–2 to `/detected` (only for an attachment without a parent item)
on a background thread that never blocks viewing.

The window opens the fetched bytes **from memory** (`Viewer.openBytes`; no temporary file,
nothing written to disk), shows the library's title (`State.titleOverride`: the parent item's
title, else the attachment's) instead of a file name, at the requested page (`BIBLEAN_PAGE`,
else `--page`). Annotations sync live (task 10.2's `Annots.Sync`, attached to the window as a
`Viewer.Library`, task 10.1b):

* **at open** the stored set from `GET /api/items/{key}` is merged into the marks read back
  from the file (`Sync.load`); our stored marks that are not in the file yet show as unsaved
  (`* ` in the title), other viewers' elements are kept aside and posted back verbatim;
* **after every change** of the marks (highlight, note, text, recolour, delete, XFDF import,
  Save) the whole set is posted, debounced 400 ms (as bib-lean's own reader);
* **Save** is labelled *Save to library* (menu and toolbar tooltip; bib-lean's reader saves to
  the library too): `Save.build`'s bytes (the original plus an incremental update, reopened
  strictly and read back) go to `PUT /api/attachments/{key}/file` — no local file — then the
  window reopens those bytes from memory on the same page and the set is posted again. Save
  As… still writes a local copy (the window stays on the library's document, whose marks stay
  unsaved there). Close and Quit ask about marks not yet saved into the library's file (they
  are already in its annotation list);
* **on Close** (Ctrl+W) and **after the window closed** pending requests are flushed for at
  most 3 s; when something is still pending (a server that never answers) the process exits
  at once. After the flush the window run always ends through `IO.Process.exit` (task 8.9), so
  a page still rendering on a worker thread never holds the process open (Lean would
  otherwise join it when `main` returns). Opening another file (Ctrl+O) lets the library go: the new file is a local one.

### `--self-test`

The contract's sequence without a window (`BibLean/SelfTest.lean`):

1. the launch above (GET the file and the item);
2. two deterministic marks on page 1: a yellow highlight over the first word (a fixed box near
   the top-left when the page has no text) and a yellow note `safe-pdf self-test note`
   20 pt in from the CropBox's upper-left corner — added to the file's own marks merged with
   the stored set, and **not added again** when already there;
3. `POST …/annotations` with the whole set (our marks have `id` = their `/NM`
   `safepdf-mark-N`; other viewers' elements are posted back verbatim) — expects `200` and one
   key per element;
4. `POST …/detected` with the first DOI/arXiv id of pages 1–2 (always, even with a parent
   item; skipped when the PDF has none) — expects `202`; then `POST …/fulltext` — expects `200`;
5. `PUT …/file` with the re-saved file (`Save.build`: the original bytes plus an incremental
   update, reopened strictly and read back before it is sent) — expects `200`; skipped when
   every mark is already in the file.

So a second run on the file bib-lean stored creates nothing, posts the same ids (bib-lean keeps
the item keys) and sends no file. Output: one `name: value` line per step (`key`, `pages`,
`bytes`, `sha256` of the served file, `page-env`, `page-arg`, `page`, `marks`, `annotations`
with the answered keys, `detected`, `fulltext`, `put`), then `viewer self-test: ok` or
`viewer self-test: FAILED (steps)`.

Run it by hand through bib-lean:

    biblean --dir LIB open KEY --reader "exec $PWD/.lake/build/bin/viewer --biblean --self-test"

## Conformance tests

| Script | What |
|---|---|
| `scripts/biblean-contract.sh --biblean BIN` | bib-lean's contract checks **S1–S25** (its `tests/reader/contract.sh`, re-implemented with our viewer in place of its curl stub; the checks on the stub's own payload — S2–S5, S8, S9, S11, S14, S15, S21, S23, S24 — are adapted to the self-test's) against a real `biblean` binary BIN in fresh temporary libraries, plus X1–X7 (the stored file holds the marks, our exit codes, token hygiene). BIN is never built from here: copy a built one out of a bib-lean checkout. `--pdf FILE` picks the fixture (default `Tests/biblean/text-pdf.py`'s; bib-lean's `tests/fixtures/reader-sample.pdf` works too). |
| `scripts/biblean-contract.sh` (`--stub`) / `Tests/biblean/selftest-test.sh` | the viewer-side checks against our stub server `Tests/biblean/stub_server.py`; the bib-lean-side ones (launcher, config, sessions, fsck) print `skip`. No bib-lean needed. |
| `Tests/biblean/launch-test.sh`, `text-test.sh`, `annots-test.sh` | launch, text/detection and annotation sync through `--probe` and the window (Xvfb) against the stub server. |
| `Tests/biblean/window-test.sh` | the window (task 10.1b, smoke mode `biblean`): the library's title, the requested page, no temporary or local file, fd 3 closed while the window is up, the stored set loaded, a highlight posted before any save, Save to library = `PUT` then `POST`. |

Run them with `env -u DISPLAY` (they start their own Xvfb where needed; `xvfb-run` reuses
fd 3 and breaks the token pipe).

## Not implemented yet

* A scripted Tk session of the window path against a real bib-lean (the window is tested
  against the stub server only), and M10's manual
  parts: a highlight made in the viewer appearing in bib-lean's window and its search, and the
  stored file opened in pdf.js showing it.
* `SIGTERM` handling beyond the runtime's default (the contract's SHOULD "exit promptly on
  `SIGTERM`" holds since the default action terminates the process).
