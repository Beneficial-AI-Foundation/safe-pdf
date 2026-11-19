#!/usr/bin/env python3
"""Operator coverage report over the corpus (task 5.4, Plan.md §6 Phase 5, exit M5).

Stdlib only; run as `python3 -I scripts/corpus/opcoverage.py`.

Runs the already-built inspector `inspect --json --view ops FILE` (one process per file, each
wrapped in `timeout 60` when the `timeout` command exists and killed after 65 s regardless)
over every manifest entry whose PDF is present in <corpus>/files/ and whose SHA-256 matches the
manifest, and writes docs/opcoverage.md and docs/opcoverage.json.

Definitions (see SafePdf/Shell/Views/Svg.lean):
  * an operator occurrence is *unsupported* iff the interpreter reported it as unknown (it
    emitted a DisplayItem.unsupported item); every other occurrence is *covered*;
  * *covered (strict)* additionally excludes the operators that phase 5 executes only as
    placeholders or no-ops: gs, Do, sh, BI (inline image), d0, d1 (see DEFERRED);
  * coverage = covered / all operator occurrences, over all pages of all files.

Failures. The interpreter is total by construction, so any of these on a file that opens is
reported as an interpreter-run failure: the process timed out, crashed (exit code other than
0/1), or printed no parseable summary. Separately reported, and not interpreter failures:
files the parser cannot open (summary has "error"), and pages whose /Contents cannot be
decoded (page "error", e.g. a filter error or the document decode budget).

  --corpus DIR      corpus directory (manifest.json + files/), default <repo>/corpus
  --inspector PATH  default <repo>/.lake/build/bin/inspect
  --files GLOB      only entries whose id or file name matches GLOB (fnmatch)
  --out-md PATH / --out-json PATH   default docs/opcoverage.md / docs/opcoverage.json
  --no-verify       skip the SHA-256 check against the manifest
Never opens PDFs with anything but the inspector. Exit 0 unless no file could be checked.
"""
import argparse, datetime, fnmatch, hashlib, json, os, shutil, subprocess, sys, time

TIMEOUT_S = 60
DEFERRED = ["gs", "Do", "sh", "BI", "d0", "d1"]
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def git_commit():
    try:
        r = subprocess.run(["git", "-C", ROOT, "rev-parse", "--short", "HEAD"],
                           capture_output=True, text=True, timeout=10)
        return r.stdout.strip() or "unknown"
    except Exception:
        return "unknown"


def wrap(cmd):
    t = shutil.which("timeout")
    return [t, str(TIMEOUT_S)] + cmd if t else cmd


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run_one(inspector, path):
    """One inspector run; a row dict."""
    t0 = time.perf_counter()
    try:
        r = subprocess.run(wrap([inspector, "--json", "--view", "ops", path]),
                           capture_output=True, timeout=TIMEOUT_S + 5)
    except subprocess.TimeoutExpired:
        return dict(status="timeout", detail="killed after %d s" % (TIMEOUT_S + 5),
                    wall_ms=round((time.perf_counter() - t0) * 1000, 3))
    except Exception as e:
        return dict(status="crash", detail="inspector failed to run: %s" % e, wall_ms=None)
    wall = round((time.perf_counter() - t0) * 1000, 3)
    if r.returncode == 124:
        return dict(status="timeout", detail="timed out after %d s" % TIMEOUT_S, wall_ms=wall)
    if r.returncode not in (0, 1):
        err = r.stderr.decode("utf-8", "replace").strip().splitlines()
        return dict(status="crash", detail="exit code %d: %s" % (r.returncode, err[-1] if err else ""),
                    wall_ms=wall)
    lines = r.stdout.decode("utf-8", "replace").strip().splitlines()
    try:
        objs = [json.loads(l) for l in lines]
    except ValueError as e:
        return dict(status="crash", detail="unparseable output: %s" % e, wall_ms=wall)
    if not objs or "summary" not in objs[-1]:
        return dict(status="crash", detail="no summary line", wall_ms=wall)
    s = objs[-1]["summary"]
    if "error" in s:
        return dict(status="unopened", detail=s["error"], open=s.get("open"), wall_ms=wall)
    pages = objs[:-1]
    page_errors = [dict(page=p["page"], error=p["error"]) for p in pages if p.get("error")]
    return dict(status="ok", open=s.get("open"), wall_ms=wall, pages=s["pages"], ops=s["ops"],
                covered=s["covered"], unsupported=s["unsupported"], warned=s["warned"],
                interp_warnings=s["interpWarnings"], tok_warnings=s["tokWarnings"],
                truncated_pages=s["truncatedPages"], error_pages=s["errorPages"],
                page_errors=page_errors[:5], max_page_ops=s["maxPageOps"],
                ms=float(s.get("ms", 0)), max_page_ms=float(s.get("maxPageMs", 0)),
                items=s["items"], histogram=s["histogram"])


def pct(n, d, digits=3):
    return None if d == 0 else round(100.0 * n / d, digits)


def pct_text(n, d):
    return "n/a" if d == 0 else "%.3f%%" % (100.0 * n / d)


def aggregate(rows):
    hist = {}
    items = {}
    for r in rows:
        if r["status"] != "ok":
            continue
        for op, c in r["histogram"].items():
            h = hist.setdefault(op, dict(count=0, unsupported=0, warned=0, files=0))
            h["count"] += c["count"]; h["unsupported"] += c["unsupported"]
            h["warned"] += c["warned"]; h["files"] += 1
        for k, v in r["items"].items():
            items[k] = items.get(k, 0) + v
    ok = [r for r in rows if r["status"] == "ok"]
    ops = sum(r["ops"] for r in ok)
    unsup = sum(r["unsupported"] for r in ok)
    deferred = sum(hist.get(op, {}).get("count", 0) - hist.get(op, {}).get("unsupported", 0)
                   for op in DEFERRED)
    covered = ops - unsup
    return dict(
        files=len(rows), files_ok=len(ok),
        interpreter_failures=sum(1 for r in rows if r["status"] in ("timeout", "crash")),
        unopened=sum(1 for r in rows if r["status"] == "unopened"),
        pages=sum(r["pages"] for r in ok), error_pages=sum(r["error_pages"] for r in ok),
        files_with_error_pages=sum(1 for r in ok if r["error_pages"]),
        truncated_pages=sum(r["truncated_pages"] for r in ok),
        ops=ops, covered=covered, unsupported=unsup, covered_pct=pct(covered, ops),
        covered_strict=covered - deferred, covered_strict_pct=pct(covered - deferred, ops),
        warned=sum(r["warned"] for r in ok),
        interp_warnings=sum(r["interp_warnings"] for r in ok),
        tok_warnings=sum(r["tok_warnings"] for r in ok),
        files_full_coverage=sum(1 for r in ok if r["unsupported"] == 0),
        min_file_covered_pct=min((pct(r["covered"], r["ops"]) for r in ok if r["ops"]), default=None),
        max_wall_ms=max((r["wall_ms"] or 0 for r in rows), default=0),
        max_ops_ms=max((r["ms"] for r in ok), default=0),
        max_page_ms=max((r["max_page_ms"] for r in ok), default=0),
        max_page_ops=max((r["max_page_ops"] for r in ok), default=0),
        items=items,
        histogram=dict(sorted(hist.items(), key=lambda kv: (-kv[1]["count"], kv[0]))))


def render_md(data):
    s = data["summary"]
    L = ["# Operator coverage (task 5.4, M5)", "",
         "Generated by `python3 -I scripts/corpus/opcoverage.py` at commit `%s` on %s." % (
             data["commit"], data["generated"]), "",
         "Each corpus file is run through `inspect --json --view ops` (verified core: page tree, "
         "budgeted content decoding, `Core.Content.Ops.tokenize`, `Core.Content.interp` with the "
         "default config). An operator occurrence is **covered** unless the interpreter "
         "reported it as unknown (a `DisplayItem.unsupported` item). **Covered (strict)** also "
         "excludes the operators phase 5 runs only as placeholders or no-ops (%s); task 5.2b "
         "resolves ExtGState, XObjects and images." % ", ".join("`%s`" % o for o in DEFERRED), "",
         "**Scope.** Only page content streams are counted. Form XObjects are not expanded "
         "before task 5.2b (`Do` is a placeholder), so operators inside forms, Type 3 glyph "
         "procedures, patterns and annotation appearance streams are not yet in this report.", "",
         "## Summary", "", "| | |", "|---|---|",
         "| files checked | %d |" % s["files"],
         "| files interpreted | %d |" % s["files_ok"],
         "| interpreter-run failures (timeout, crash, no summary) | %d |" % s["interpreter_failures"],
         "| files the parser cannot open | %d |" % s["unopened"],
         "| pages | %d |" % s["pages"],
         "| pages with undecodable /Contents | %d (in %d files) |" % (s["error_pages"], s["files_with_error_pages"]),
         "| pages truncated at maxOpsPerPage | %d |" % s["truncated_pages"],
         "| operator occurrences | %d |" % s["ops"],
         "| **covered** | **%d (%s)** |" % (s["covered"], pct_text(s["covered"], s["ops"])),
         "| covered (strict) | %d (%s) |" % (s["covered_strict"], pct_text(s["covered_strict"], s["ops"])),
         "| unsupported | %d |" % s["unsupported"],
         "| covered but warned (malformed operands etc.) | %d |" % s["warned"],
         "| interpreter / tokenizer warnings | %d / %d |" % (s["interp_warnings"], s["tok_warnings"]),
         "| files with 100%% coverage | %d / %d |" % (s["files_full_coverage"], s["files_ok"]),
         "| lowest per-file coverage | %s |" % ("n/a" if s["min_file_covered_pct"] is None else "%.3f%%" % s["min_file_covered_pct"]),
         "| max wall time per file (process) | %.1f ms |" % s["max_wall_ms"],
         "| max ops-view time per file (decode + tokenize + interpret) | %.1f ms |" % s["max_ops_ms"],
         "| max time per page | %.1f ms |" % s["max_page_ms"],
         "| max operators on one page | %d |" % s["max_page_ops"],
         "", "Display items: " + ", ".join("%s %d" % kv for kv in sorted(s["items"].items())), ""]
    unsup = [(op, h) for op, h in s["histogram"].items() if h["unsupported"]]
    L += ["## Unsupported operators", ""]
    if unsup:
        L += ["| operator | occurrences | files |", "|---|---|---|"]
        L += ["| `%s` | %d | %d |" % (op, h["unsupported"], h["files"])
              for op, h in sorted(unsup, key=lambda kv: -kv[1]["unsupported"])]
    else:
        L += ["None."]
    L += ["", "## Operator histogram", "",
          "| operator | occurrences | % of all | unsupported | warned | files |",
          "|---|---|---|---|---|---|"]
    for op, h in s["histogram"].items():
        L.append("| `%s` | %d | %s | %d | %d | %d |" % (
            op.replace("|", "\\|"), h["count"], pct_text(h["count"], s["ops"]), h["unsupported"],
            h["warned"], h["files"]))
    bad = [r for r in data["files"] if r["status"] != "ok" or r.get("error_pages") or r.get("unsupported")]
    L += ["", "## Files with failures, decode errors or unsupported operators", ""]
    if bad:
        L += ["| file | status | ops | covered | unsupported | error pages | detail |",
              "|---|---|---|---|---|---|---|"]
        for r in bad:
            det = r.get("detail") or "; ".join("p%d: %s" % (e["page"], e["error"]) for e in r.get("page_errors", []))
            L.append("| %s | %s | %s | %s | %s | %s | %s |" % (
                r["id"], r["status"], r.get("ops", ""),
                "" if r["status"] != "ok" else pct_text(r["covered"], r["ops"]),
                r.get("unsupported", ""), r.get("error_pages", ""), det.replace("|", "\\|")))
    else:
        L += ["None."]
    L += ["", "## Per file", "",
          "| file | open | pages | ops | covered | warned | warnings (interp+tok) | ms | max page ms |",
          "|---|---|---|---|---|---|---|---|---|"]
    for r in data["files"]:
        if r["status"] != "ok":
            L.append("| %s | %s | | | | | | | |" % (r["id"], r["status"]))
            continue
        L.append("| %s | %s | %d | %d | %s | %d | %d+%d | %.1f | %.1f |" % (
            r["id"], r["open"], r["pages"], r["ops"], pct_text(r["covered"], r["ops"]), r["warned"],
            r["interp_warnings"], r["tok_warnings"], r["ms"], r["max_page_ms"]))
    return "\n".join(L) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--corpus", default=os.path.join(ROOT, "corpus"))
    ap.add_argument("--inspector", default=os.path.join(ROOT, ".lake", "build", "bin", "inspect"))
    ap.add_argument("--files")
    ap.add_argument("--out-md", default=os.path.join(ROOT, "docs", "opcoverage.md"))
    ap.add_argument("--out-json", default=os.path.join(ROOT, "docs", "opcoverage.json"))
    ap.add_argument("--no-verify", action="store_true")
    a = ap.parse_args()
    if not os.path.exists(a.inspector):
        print("opcoverage: inspector not found at %s (run `lake build`)" % a.inspector, file=sys.stderr)
        return 2
    with open(os.path.join(a.corpus, "manifest.json")) as f:
        manifest = json.load(f)
    rows, skipped = [], []
    for e in manifest["entries"]:
        p = os.path.join(a.corpus, "files", e["id"] + ".pdf")
        if a.files and not (fnmatch.fnmatch(e["id"], a.files) or fnmatch.fnmatch(os.path.basename(p), a.files)):
            continue
        if not os.path.exists(p):
            skipped.append(dict(id=e["id"], reason="missing"))
            continue
        if not a.no_verify and sha256(p) != e.get("sha256"):
            skipped.append(dict(id=e["id"], reason="sha256 mismatch"))
            continue
        r = run_one(a.inspector, p)
        r["id"] = e["id"]
        rows.append(r)
        print("%-40s %-9s %s" % (e["id"], r["status"],
              "" if r["status"] != "ok" else "%d ops, %s covered, %.1f ms" % (
                  r["ops"], pct_text(r["covered"], r["ops"]), r["ms"])), file=sys.stderr)
    if not rows:
        print("opcoverage: no corpus file to check", file=sys.stderr)
        return 1
    summary = aggregate(rows)
    data = dict(generated=datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
                commit=git_commit(), timeout_s=TIMEOUT_S, deferred=DEFERRED, skipped=skipped,
                summary=summary,
                files=[{k: v for k, v in r.items() if k not in ("histogram",)} for r in rows])
    with open(a.out_json, "w") as f:
        json.dump(data, f, indent=1, sort_keys=False)
        f.write("\n")
    with open(a.out_md, "w") as f:
        f.write(render_md(data))
    print("opcoverage: %d files, %d ops, covered %s (strict %s), %d unsupported, %d interpreter "
          "failures, %d unopened, max page %.1f ms; wrote %s, %s" % (
              summary["files"], summary["ops"], pct_text(summary["covered"], summary["ops"]),
              pct_text(summary["covered_strict"], summary["ops"]), summary["unsupported"],
              summary["interpreter_failures"], summary["unopened"], summary["max_page_ms"],
              a.out_md, a.out_json))
    return 0


if __name__ == "__main__":
    sys.exit(main())
