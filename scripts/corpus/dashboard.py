#!/usr/bin/env python3
"""Corpus dashboard (task 0.11). Stdlib only; run as `python3 -I scripts/corpus/dashboard.py`.

Runs the already-built inspector (`.lake/build/bin/inspect --json FILE`, ONE process per
file so wall time is per-file; parseMs comes from the inspector itself) over every
manifest entry whose PDF is present in corpus/files/, and writes docs/dashboard.md and
docs/dashboard.json. Since task 2.11 it also runs `inspect --json --view resolve FILE`
(a second process) to check that every in-use object resolves, and reports how files
open: strict, repaired, or failed. Every inspector process is wrapped in `timeout 20`
(when the `timeout` command exists) and killed after 20 s regardless.

  --corpus DIR      corpus directory (manifest.json + files/), default <repo>/corpus
  --inspector PATH  default <repo>/.lake/build/bin/inspect
  --files GLOB      only entries whose id or file name matches GLOB (fnmatch)
  --out-md PATH / --out-json PATH   default docs/dashboard.md / docs/dashboard.json
  --compare OLD.json  run, print regressions vs OLD (ok before, not ok now), exit 1 if any.
                      Does not write outputs unless --write is also given.
  --milestone TEXT  inspector milestone label (default M2)
  --no-resolve      skip the per-file object-resolution run
Never opens PDFs with anything but the inspector. Exit 0 unless --compare finds regressions.
"""
import argparse, datetime, fnmatch, json, os, shutil, statistics, subprocess, sys, time

TIMEOUT_S = 20

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MILESTONE_NOTE = {
    "M0": "M0: the inspector's parse is a header check only (`%PDF-x.y` found near the start), "
          "so '% opens' is trivially high and says nothing about real parsing ability. "
          "Later milestones diff against this file's JSON.",
    "M2": "M2 (task 2.11): 'opens' means the xref chain loads (strict) or the repair scan "
          "rebuilds it (repaired), and /Root resolves to a dictionary. 'Objects resolve' "
          "fetches every in-use xref entry (classic offsets and object-stream members) with "
          "getObject; it does not decode content streams, fonts or images; encrypted "
          "files are decrypted with the empty user password (task 4.3b).",
}


def git_commit():
    try:
        r = subprocess.run(["git", "-C", ROOT, "rev-parse", "--short", "HEAD"],
                           capture_output=True, text=True, timeout=10)
        return r.stdout.strip() or "unknown"
    except Exception:
        return "unknown"


def bucket(year):
    if not isinstance(year, int):
        return "unknown"
    if year < 2005: return "<2005"
    if year < 2010: return "2005-2009"
    if year < 2015: return "2010-2014"
    if year < 2020: return "2015-2019"
    return "2020+"


BUCKET_ORDER = ["<2005", "2005-2009", "2010-2014", "2015-2019", "2020+", "unknown"]


def wrap(cmd):
    t = shutil.which("timeout")
    return [t, str(TIMEOUT_S)] + cmd if t else cmd


def run_resolve(inspector, path):
    """Per-file object resolution (`--view resolve`); a dict of counts or an error."""
    t0 = time.perf_counter()
    try:
        r = subprocess.run(wrap([inspector, "--json", "--view", "resolve", path]),
                           capture_output=True, text=True, timeout=TIMEOUT_S + 5)
    except Exception as e:
        return dict(resolve_error="resolve run failed: %s" % e, resolve_wall_ms=None)
    wall = round((time.perf_counter() - t0) * 1000, 3)
    if r.returncode == 124:
        return dict(resolve_error="resolve timed out after %d s" % TIMEOUT_S, resolve_wall_ms=wall)
    line = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""
    try:
        j = json.loads(line)
    except ValueError:
        return dict(resolve_error="unparseable resolve output (rc=%d)" % r.returncode, resolve_wall_ms=wall)
    if "resolvedOk" not in j:
        return dict(resolve_wall_ms=wall)  # did not open; the summary row has the error
    return dict(resolve_wall_ms=wall, in_use=j["inUse"], compressed=j["compressed"],
                resolved_ok=j["resolvedOk"], resolve_errors=j["resolveErrors"],
                first_resolve_errors=j.get("firstErrors", []), resolve_ms=j.get("resolveMs"))


def run_one(inspector, path):
    t0 = time.perf_counter()
    try:
        r = subprocess.run(wrap([inspector, "--json", path]), capture_output=True, text=True,
                           timeout=TIMEOUT_S + 5)
    except Exception as e:
        return dict(ok=False, error="inspector failed to run: %s" % e, rc=-1, version=None,
                    parse_ms=None, wall_ms=(time.perf_counter() - t0) * 1000)
    wall = (time.perf_counter() - t0) * 1000
    base = dict(rc=r.returncode, wall_ms=round(wall, 3), version=None, parse_ms=None, open="failed")
    if r.returncode == 124:
        return dict(base, ok=False, error="timed out after %d s" % TIMEOUT_S)
    if r.returncode == 2:  # usage / IO error: an error row, not a crash
        msg = (r.stderr.strip().splitlines() or ["usage/IO error"])[0]
        return dict(base, ok=False, error=msg)
    line = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""
    try:
        j = json.loads(line)
    except ValueError:
        return dict(base, ok=False, error="unparseable inspector output (rc=%d): %r" % (r.returncode, line[:200]))
    ok = bool(j.get("ok")) and r.returncode == 0
    err = j.get("error")
    if not ok and not err:
        err = "inspector exit code %d" % r.returncode
    return dict(base, ok=ok, error=None if ok else err, version=j.get("version"),
                parse_ms=j.get("parseMs"), header_offset=j.get("headerOffset"),
                open=j.get("open", "strict" if ok else "failed"), revisions=j.get("revisions"),
                objects=j.get("objects"), encrypted=j.get("encrypted"))


def pct(n, d):
    return "n/a" if d == 0 else "%.1f%%" % (100.0 * n / d)


def p95(xs):
    if not xs: return None
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(round(0.95 * (len(xs) - 1) + 1e-9)))] if len(xs) > 1 else xs[0]


def summarize(rows):
    n = len(rows)
    nok = sum(1 for r in rows if r["ok"])
    pm = [r["parse_ms"] for r in rows if r["parse_ms"] is not None]
    wm = [r["wall_ms"] for r in rows if r["wall_ms"] is not None]
    mode = lambda m: sum(1 for r in rows if r.get("open") == m)
    rp = lambda k: round(100.0 * k / n, 2) if n else None
    resolved = [r for r in rows if r.get("resolved_ok") is not None]
    fetched = sum(r["resolved_ok"] + r["resolve_errors"] for r in resolved)
    rok = sum(r["resolved_ok"] for r in resolved)
    rw = [r["resolve_wall_ms"] for r in rows if r.get("resolve_wall_ms") is not None]
    nstrict, nrep = mode("strict"), mode("repaired")
    return dict(files=n, opened=nok, pct_opens=None if n == 0 else round(100.0 * nok / n, 2),
                strict=nstrict, repaired=nrep, failed=n - nstrict - nrep,
                pct_strict=rp(nstrict), pct_repaired=rp(nrep), pct_failed=rp(n - nstrict - nrep),
                encrypted=sum(1 for r in rows if r.get("encrypted")),
                objects_fetched=fetched, objects_resolved=rok,
                pct_objects_resolved=round(100.0 * rok / fetched, 4) if fetched else None,
                files_all_resolve=sum(1 for r in resolved if r["resolve_errors"] == 0),
                files_resolve_checked=len(resolved),
                wall_ms_max=max(wm) if wm else None, resolve_wall_ms_max=max(rw) if rw else None,
                parse_ms_median=statistics.median(pm) if pm else None, parse_ms_p95=p95(pm),
                wall_ms_median=statistics.median(wm) if wm else None, wall_ms_p95=p95(wm),
                total_bytes=sum(r["bytes"] for r in rows))


def group(rows, key):
    g = {}
    for r in rows:
        g.setdefault(key(r), []).append(r)
    return g


def f(x, nd=3):
    return "n/a" if x is None else ("%.*f" % (nd, x))


def render_md(data):
    s = data["summary"]
    L = ["# Corpus dashboard", "",
         "- Generated: %s" % data["generated"],
         "- Git commit: `%s`" % data["commit"],
         "- Inspector milestone: %s" % data["milestone"],
         "- Corpus: `%s`" % data["corpus"], "",
         "> **Honesty note.** " + data["milestone_note"], "",
         "## Headline", "",
         "| metric | value |", "|---|---|",
         "| files | %d |" % s["files"],
         "| opens (strict or repaired) | %d (%s) |" % (s["opened"], pct(s["opened"], s["files"])),
         "| open: strict | %d (%s) |" % (s["strict"], pct(s["strict"], s["files"])),
         "| open: repaired | %d (%s) |" % (s["repaired"], pct(s["repaired"], s["files"])),
         "| open: failed | %d (%s) |" % (s["failed"], pct(s["failed"], s["files"])),
         "| encrypted (opened and decrypted, empty user password; task 4.3b) | %d |" % s["encrypted"],
         "| in-use objects resolved (`--view resolve`) | %d / %d (%s) |" % (
             s["objects_resolved"], s["objects_fetched"],
             "n/a" if s["pct_objects_resolved"] is None else "%.3f%%" % s["pct_objects_resolved"]),
         "| files whose in-use objects all resolve | %d / %d |" % (s["files_all_resolve"], s["files_resolve_checked"]),
         "| parse time, median (inspector `parseMs`) | %s ms |" % f(s["parse_ms_median"]),
         "| parse time, p95 | %s ms |" % f(s["parse_ms_p95"]),
         "| wall time per process, median | %s ms |" % f(s["wall_ms_median"], 1),
         "| wall time per process, p95 | %s ms |" % f(s["wall_ms_p95"], 1),
         "| wall time per process, max (summary / resolve) | %s / %s ms |" % (
             f(s["wall_ms_max"], 1), f(s["resolve_wall_ms_max"], 1)),
         "| total size | %.1f MB |" % (s["total_bytes"] / 1e6), ""]
    rows = data["files"]

    def table(title, groups, order):
        out = ["## " + title, "",
               "| group | files | opens | % opens | strict | repaired | failed | objects resolved | median parse ms | MB |",
               "|---|---|---|---|---|---|---|---|---|---|"]
        for k in order:
            if k not in groups: continue
            gs = summarize(groups[k])
            out.append("| %s | %d | %d | %s | %d | %d | %d | %s | %s | %.1f |" % (
                k, gs["files"], gs["opened"], pct(gs["opened"], gs["files"]),
                gs["strict"], gs["repaired"], gs["failed"],
                pct(gs["objects_resolved"], gs["objects_fetched"]),
                f(gs["parse_ms_median"]), gs["total_bytes"] / 1e6))
        if len(out) == 4: out.append("| (none) | 0 | 0 | n/a | 0 | 0 | 0 | n/a | n/a | 0.0 |")
        return out + [""]

    ge = group(rows, lambda r: r["engine"])
    L += table("By engine", ge, sorted(ge, key=lambda k: (-len(ge[k]), k)))
    gy = group(rows, lambda r: bucket(r["year"]))
    L += table("By year bucket", gy, BUCKET_ORDER)
    fails = [r for r in rows if not r["ok"]]
    L += ["## Failures", ""]
    if fails:
        L += ["| file | error |", "|---|---|"]
        L += ["| %s | %s |" % (r["id"], str(r["error"]).replace("|", "\\|")) for r in fails]
    else:
        L.append("None.")
    L += ["", "## Repaired files", ""]
    rep_rows = [r for r in rows if r.get("open") == "repaired"]
    L += (["| file |", "|---|"] + ["| %s |" % r["id"] for r in rep_rows]) if rep_rows else ["None."]
    L += ["", "## Object-resolution failures", ""]
    bad = [r for r in rows if r.get("resolve_errors") or r.get("resolve_error")]
    if bad:
        L += ["| file | errors / fetched | first errors |", "|---|---|---|"]
        for r in bad:
            if r.get("resolve_error"):
                L.append("| %s | n/a | %s |" % (r["id"], r["resolve_error"].replace("|", "\\|")))
                continue
            fe = "; ".join("%d %d: %s" % (e["num"], e["gen"], e["error"]) for e in r["first_resolve_errors"])
            L.append("| %s | %d / %d | %s |" % (r["id"], r["resolve_errors"],
                     r["in_use"] + r["compressed"], fe.replace("|", "\\|")))
    else:
        L.append("None.")
    return "\n".join(L) + "\n"


def compare(old_path, rows):
    with open(old_path, encoding="utf-8") as fh:
        old = json.load(fh)
    new = {r["id"]: r for r in rows}
    regress, missing = [], []
    for o in old.get("files", []):
        if not o.get("ok"): continue
        n = new.get(o["id"])
        if n is None: missing.append(o["id"])
        elif not n["ok"]: regress.append((o["id"], n["error"]))
    for i, e in regress:
        print("REGRESSION: %s opened before, now fails: %s" % (i, e))
    for i in missing:
        print("note: %s opened before but was not run this time (file absent or filtered)" % i)
    print("compare: %d regression(s), %d not re-run, vs %s (old commit %s)" % (
        len(regress), len(missing), old_path, old.get("commit")))
    return 1 if regress else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--corpus", default=os.path.join(ROOT, "corpus"))
    ap.add_argument("--inspector", default=os.path.join(ROOT, ".lake", "build", "bin", "inspect"))
    ap.add_argument("--files")
    ap.add_argument("--out-md", default=os.path.join(ROOT, "docs", "dashboard.md"))
    ap.add_argument("--out-json", default=os.path.join(ROOT, "docs", "dashboard.json"))
    ap.add_argument("--compare")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--milestone", default="M2")
    ap.add_argument("--no-resolve", action="store_true")
    a = ap.parse_args()

    entries = []
    mpath = os.path.join(a.corpus, "manifest.json")
    if os.path.isfile(mpath):
        with open(mpath, encoding="utf-8") as fh:
            entries = json.load(fh).get("entries", [])
    todo = []
    for e in entries:
        p = os.path.join(a.corpus, "files", e["id"] + ".pdf")
        if not os.path.isfile(p): continue
        if a.files and not (fnmatch.fnmatch(e["id"], a.files) or fnmatch.fnmatch(os.path.basename(p), a.files)):
            continue
        todo.append((e, p))
    if todo and not os.access(a.inspector, os.X_OK):
        sys.exit("dashboard: inspector not found/executable: %s (build it first)" % a.inspector)

    rows = []
    for e, p in todo:
        cat = e.get("category", {})
        res = run_one(a.inspector, p)
        if res["ok"] and not a.no_resolve:
            res.update(run_resolve(a.inspector, p))
        rows.append(dict(id=e["id"], bytes=os.path.getsize(p), engine=cat.get("engine", "unknown"),
                         year=cat.get("year"), producer=cat.get("producer"), **res))
    data = dict(
        generated=datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        commit=git_commit(), milestone=a.milestone,
        milestone_note=MILESTONE_NOTE.get(a.milestone, "See Plan.md for what this milestone's parse covers."),
        corpus=os.path.relpath(a.corpus, ROOT) if a.corpus.startswith(ROOT) else a.corpus,
        summary=summarize(rows), files=rows)

    rc = 0
    if a.compare:
        rc = compare(a.compare, rows)
    if not a.compare or a.write:
        for path, text in ((a.out_md, render_md(data)),
                           (a.out_json, json.dumps(data, indent=1, ensure_ascii=False) + "\n")):
            os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(text)
        print("dashboard: %d files, %d open; wrote %s, %s" % (
            data["summary"]["files"], data["summary"]["opened"], a.out_md, a.out_json))
    return rc


if __name__ == "__main__":
    sys.exit(main())
