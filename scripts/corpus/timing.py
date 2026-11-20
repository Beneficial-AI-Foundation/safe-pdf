#!/usr/bin/env python3
"""Per-page compiled render times over the corpus (task 7.9). Stdlib only;
run as `python3 -I scripts/corpus/timing.py`.

Runs the already-built inspector once per file,
`SAFEPDF_DPI=D inspect --view raster --json FILE`, which renders every page and reports
each page's wall-clock time around the pure `renderDocPage` call (`nanos`; parsing, process
start-up and file writing excluded; docs/raster.md "Timing"). A file whose run exceeds the
per-file timeout is killed; the pages it reported are kept, its remaining pages are rendered
one process per page (`SAFEPDF_PAGE=N`) with the per-page timeout, and a page that still
times out is recorded with status "timeout" and its time as the timeout (a lower bound).

Prints the number of pages, median / p95 / max page time and the N slowest pages.

  --corpus DIR       directory of PDFs (default <repo>/corpus/files)
  --inspector PATH   default <repo>/.lake/build/bin/inspect
  --files GLOB       only files whose name matches GLOB (fnmatch; repeatable)
  --dpi D            default 72
  --top N            slowest pages to list (default 30)
  --jobs J           files rendered in parallel (default 1; >1 perturbs the times)
  --file-timeout S   per-file timeout in seconds (default 600)
  --page-timeout S   per-page timeout in seconds (default 120)
  --json OUT         write {"summary": …, "pages": [...]} to OUT
  --compare OLD.json print the per-page change against an earlier --json output
Skips cleanly (exit 0 with a message) when the inspector or the corpus is missing.
"""
import argparse, concurrent.futures, fnmatch, json, math, os, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def parse_lines(text):
    """The page objects and the summary object of `--view raster --json` output."""
    pages, summary = [], None
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            j = json.loads(line)
        except ValueError:
            continue
        if "summary" in j:
            summary = j["summary"]
        elif "page" in j:
            pages.append(j)
    return pages, summary


def run(cmd, env, timeout):
    """(stdout, timed_out) of a process killed after `timeout` seconds."""
    p = subprocess.Popen(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                         text=True)
    try:
        out, _ = p.communicate(timeout=timeout)
        return out, False
    except subprocess.TimeoutExpired:
        p.kill()
        out, _ = p.communicate()
        return out or "", True


def page_rec(name, j):
    return dict(file=name, page=j["page"], ms=j["nanos"] / 1e6,
                status=j.get("status", "ok"), error=j.get("error"))


def time_file(args, path):
    """Every page record of one file (and a file-level note)."""
    name = os.path.basename(path)
    env = dict(os.environ)
    env["SAFEPDF_DPI"] = str(args.dpi)
    env.pop("SAFEPDF_PAGE", None)
    env.pop("SAFEPDF_RASTER_DIR", None)
    cmd = [args.inspector, "--view", "raster", "--json", path]
    t0 = time.perf_counter()
    out, timed_out = run(cmd, env, args.file_timeout)
    pages, summary = parse_lines(out)
    recs = [page_rec(name, j) for j in pages]
    note = None
    if summary is not None and "error" in summary and not pages:
        return recs, "does not open: %s" % summary.get("error")
    if timed_out:
        note = "file run timed out after %d s at page %d" % (args.file_timeout, len(pages) + 1)
        done = {r["page"] for r in recs}
        # page count unknown when the summary was not printed: ask the info view cheaply by
        # rendering page by page until the inspector reports no such page.
        n = len(pages) + 1
        while True:
            env1 = dict(env)
            env1["SAFEPDF_PAGE"] = str(n)
            out1, to1 = run(cmd, env1, args.page_timeout)
            p1, s1 = parse_lines(out1)
            if to1 and not p1:
                recs.append(dict(file=name, page=n, ms=args.page_timeout * 1000.0,
                                 status="timeout", error="timed out"))
            elif p1:
                for j in p1:
                    if j["page"] not in done:
                        recs.append(page_rec(name, j))
            if s1 is not None and isinstance(s1.get("pages"), int):
                if n >= s1["pages"]:
                    break
            elif not to1:
                break
            n += 1
    sys.stderr.write("%-50s %4d pages %8.1f s%s\n" % (name[:50], len(recs),
                     time.perf_counter() - t0, (" (" + note + ")") if note else ""))
    return recs, note


def pct(xs, q):
    """Nearest-rank percentile of a sorted list."""
    if not xs:
        return 0.0
    k = max(1, math.ceil(q / 100.0 * len(xs)))
    return xs[k - 1]


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--corpus", default=os.path.join(ROOT, "corpus", "files"))
    ap.add_argument("--inspector", default=os.path.join(ROOT, ".lake", "build", "bin", "inspect"))
    ap.add_argument("--files", action="append")
    ap.add_argument("--dpi", type=int, default=72)
    ap.add_argument("--top", type=int, default=30)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--file-timeout", type=int, default=600)
    ap.add_argument("--page-timeout", type=int, default=120)
    ap.add_argument("--json")
    ap.add_argument("--compare")
    args = ap.parse_args()
    if not os.path.isfile(args.inspector):
        print("timing: inspector not built (%s); skipping" % args.inspector)
        return 0
    if not os.path.isdir(args.corpus):
        print("timing: no corpus directory %s; skipping" % args.corpus)
        return 0
    files = sorted(f for f in os.listdir(args.corpus) if f.lower().endswith(".pdf"))
    if args.files:
        files = [f for f in files if any(fnmatch.fnmatch(f, g) for g in args.files)]
    if not files:
        print("timing: no PDF files selected; skipping")
        return 0
    paths = [os.path.join(args.corpus, f) for f in files]
    recs, notes = [], {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        for path, (r, note) in zip(paths, ex.map(lambda p: time_file(args, p), paths)):
            recs.extend(r)
            if note:
                notes[os.path.basename(path)] = note
    times = sorted(r["ms"] for r in recs)
    summary = dict(files=len(files), pages=len(recs), dpi=args.dpi,
                   errors=sum(1 for r in recs if r["status"] == "error"),
                   timeouts=sum(1 for r in recs if r["status"] == "timeout"),
                   medianMs=round(pct(times, 50), 3), p95Ms=round(pct(times, 95), 3),
                   p99Ms=round(pct(times, 99), 3), maxMs=round(times[-1] if times else 0, 3),
                   totalMs=round(sum(times), 3),
                   over500=sum(1 for t in times if t > 500),
                   over5000=sum(1 for t in times if t > 5000), notes=notes)
    print("files %d, pages %d (errors %d, timeouts %d), dpi %d" % (
        summary["files"], summary["pages"], summary["errors"], summary["timeouts"], args.dpi))
    print("median %.1f ms, p95 %.1f ms, p99 %.1f ms, max %.1f ms, total %.1f s" % (
        summary["medianMs"], summary["p95Ms"], summary["p99Ms"], summary["maxMs"],
        summary["totalMs"] / 1000))
    print("pages > 500 ms: %d, > 5 s: %d" % (summary["over500"], summary["over5000"]))
    for f, n in sorted(notes.items()):
        print("note: %s: %s" % (f, n))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(dict(summary=summary, pages=recs), fh, indent=1)
    old = {}
    if args.compare:
        try:
            with open(args.compare) as fh:
                for r in json.load(fh).get("pages", []):
                    old[(r["file"], r["page"])] = r["ms"]
        except (OSError, ValueError) as e:
            print("note: --compare %s not read (%s)" % (args.compare, e))
    print("\n%d slowest pages:" % args.top)
    for r in sorted(recs, key=lambda r: -r["ms"])[:args.top]:
        extra = ""
        if (r["file"], r["page"]) in old:
            extra = "  (was %.1f ms)" % old[(r["file"], r["page"])]
        st = "" if r["status"] == "ok" else "  [%s]" % r["status"]
        print("  %10.1f ms  %s p%d%s%s" % (r["ms"], r["file"], r["page"], st, extra))
    return 0


if __name__ == "__main__":
    sys.exit(main())
