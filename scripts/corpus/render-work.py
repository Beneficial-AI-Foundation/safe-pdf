#!/usr/bin/env python3
"""Counted render work per page over the corpus (task 13.4a, calibration spike). Stdlib only;
run as `python3 -I scripts/corpus/render-work.py`.

Compiles `scripts/corpus/RenderWork.lean` (read-only on `SafePdf/`; it needs a finished
`lake build`, whose object files it links) into a scratch directory, runs the binary once per
PDF and prints, per candidate unit (counted steps, pixels written), the maximum, p99, p95 and
median over pages and the heaviest pages. Counted work is deterministic: no timing is taken.
Why the tool is compiled by hand: it must not touch `lakefile.lean`, and
`lake env lean --run scripts/corpus/RenderWork.lean FILE DPI` (interpreted) works too but is
far slower.

  --corpus DIR      directory of PDFs (default <repo>/corpus/files; a worktree passes the main checkout's)
  --dpi D           default 72
  --top N           heaviest pages to list (default 5)
  --jobs J          files in parallel (default 2)
  --file-timeout S  per-file timeout (default 1800)
  --files GLOB      only files matching GLOB (fnmatch; repeatable)
  --check           also compare the replayed image with `renderDocPage`'s (slower)
  --build-dir DIR   where the binary goes (default a fresh temp directory)
  --json OUT        write {"summary", "pages"} to OUT
  --synthetic DIR   instead of the corpus: write the synthetic inputs into DIR (outside the
                    repo) and print their counted work at --dpi (repeat with --dpi 144)
Skips cleanly (exit 0) when the build outputs or the corpus are missing.
"""
import argparse, concurrent.futures, fnmatch, json, math, os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, "scripts", "corpus", "RenderWork.lean")


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, **kw)


def build(bdir):
    """Compile RenderWork.lean to C, archive the already built objects, link. Returns the
    binary path or None."""
    objs = []
    for base in (os.path.join(ROOT, ".lake", "build", "ir"),
                 os.path.join(ROOT, ".lake", "packages", "jpeg2000", ".lake", "build", "ir")):
        for d, _, fs in os.walk(base):
            for f in fs:
                p = os.path.join(d, f)
                rel = os.path.relpath(p, base)
                if f.endswith(".c.o.export") and not rel.startswith("Tests") \
                        and not f.startswith("Extract"):
                    objs.append(p)
    if not objs:
        print("render-work: no object files under .lake/build/ir (run `lake build`); skipping")
        return None
    c = os.path.join(bdir, "RenderWork.c")
    r = run(["lake", "env", "lean", "-c", c, SRC])
    if "error" in r.stdout:
        print(r.stdout)
        raise SystemExit("render-work: RenderWork.lean does not compile")
    lib = os.path.join(bdir, "libobjs.a")
    r = run(["ar", "rcs", lib] + sorted(objs))
    if r.returncode:
        raise SystemExit("render-work: ar failed\n" + r.stdout)
    exe = os.path.join(bdir, "render-work")
    r = run(["lake", "env", "leanc", "-O1", "-o", exe, c, lib])
    if r.returncode:
        raise SystemExit("render-work: link failed\n" + r.stdout)
    return exe


COLS = ["page", "w", "h", "items", "steps", "pixels", "replay", "approx", "groups", "smasks",
        "imgok"]


def run_file(exe, path, dpi, check, timeout):
    """(rows, note) for one PDF; rows are dicts."""
    cmd = [exe, path, str(dpi)] + (["--check"] if check else [])
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        return parse(path, out), "timeout after %d s" % timeout
    note = None
    if p.returncode != 0 and not p.stdout.startswith("#open-error"):
        note = "exit %d: %s" % (p.returncode, p.stderr.strip()[:200])
    return parse(path, p.stdout), note or (p.stdout.split("\n")[0] if p.stdout.startswith("#open") else None)


def parse(path, out):
    rows = []
    for line in out.splitlines():
        if line.startswith("#"):
            continue
        f = line.split("\t")
        name = os.path.basename(path)
        if len(f) == 2:
            rows.append(dict(file=name, page=int(f[0]), error=True))
        elif len(f) == len(COLS):
            d = dict(zip(COLS, f))
            d = {k: (int(v) if v.lstrip("-").isdigit() else v) for k, v in d.items()}
            d["file"] = name
            rows.append(d)
    return rows


def pct(xs, q):
    """Nearest-rank percentile of a sorted list."""
    if not xs:
        return 0
    return xs[max(1, math.ceil(q / 100.0 * len(xs))) - 1]


def stats(rows, key):
    xs = sorted(r[key] for r in rows)
    return dict(max=xs[-1], p99=pct(xs, 99), p95=pct(xs, 95), median=pct(xs, 50),
                total=sum(xs))


# ---- synthetic inputs ------------------------------------------------------------------

def pdf(content, w=612, h=792):
    objs = ["<< /Type /Catalog /Pages 2 0 R >>",
            "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
            "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 %d %d] /Contents 4 0 R /Resources << >> >>"
            % (w, h),
            "<< /Length %d >>\nstream\n%s\nendstream" % (len(content), content)]
    out, offs = "%PDF-1.7\n", []
    for i, o in enumerate(objs):
        offs.append(len(out))
        out += "%d 0 obj\n%s\nendobj\n" % (i + 1, o)
    x = len(out)
    out += "xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    out += "".join("%010d 00000 n \n" % o for o in offs)
    out += "trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, x)
    return out.encode("latin-1")


def synthetic():
    inputs = {}
    n = 2000
    clips = "".join("%.2f %.2f %.2f %.2f re W n\n" % (i * 0.05, i * 0.05, 612 - i * 0.1,
                                                      792 - i * 0.1) for i in range(n))
    inputs["clip-stack-2000.pdf"] = pdf("0 0 1 rg\n" + clips + "0 0 612 792 re f\n")
    inputs["clip-stack-2000-fills.pdf"] = pdf("0 0 1 rg\n" + "".join(
        "%.2f %.2f %.2f %.2f re W n 0 0 612 792 re f\n" % (i * 0.05, i * 0.05, 612 - i * 0.1,
                                                           792 - i * 0.1) for i in range(n)))
    inputs["full-page-fill.pdf"] = pdf("1 0 0 rg 0 0 612 792 re f\n")
    inputs["full-page-fills-1000.pdf"] = pdf("".join(
        "%d 0 0 rg 0 0 612 792 re f\n" % (i % 2) for i in range(1000)))
    inputs["page-long-stroke.pdf"] = pdf("2 w 0 0 m 612 792 l S\n")
    zig = "1 w 0 0 m\n" + "".join("%d %d l\n" % (612 if i % 2 else 0, (i + 1) * 792 // 10000)
                                  for i in range(10000)) + "S\n"
    inputs["stroke-zigzag-10000.pdf"] = pdf(zig)
    # one fill of 5,000 vertical slivers: ~10,000 edges active on every row, tiny covered area
    inputs["sliver-fill-5000.pdf"] = pdf("0 g\n" + "".join(
        "%.2f 0 0.05 792 re\n" % (i * 0.12) for i in range(5000)) + "f\n")
    return inputs


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--corpus", default=os.path.join(ROOT, "corpus", "files"))
    ap.add_argument("--dpi", type=int, default=72)
    ap.add_argument("--top", type=int, default=5)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--file-timeout", type=int, default=1800)
    ap.add_argument("--files", action="append")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--build-dir")
    ap.add_argument("--json")
    ap.add_argument("--synthetic")
    args = ap.parse_args()
    bdir = args.build_dir or tempfile.mkdtemp(prefix="safepdf-render-work-")
    os.makedirs(bdir, exist_ok=True)
    exe = build(bdir)
    if exe is None:
        return 0
    if args.synthetic:
        os.makedirs(args.synthetic, exist_ok=True)
        print("%-30s %6s %9s %14s %14s %12s" % ("input", "dpi", "WxH", "steps", "pixels", "groups"))
        for name, data in synthetic().items():
            path = os.path.join(args.synthetic, name)
            with open(path, "wb") as fh:
                fh.write(data)
            rows, note = run_file(exe, path, args.dpi, False, args.file_timeout)
            for r in rows:
                print("%-30s %6d %9s %14d %14d %12d" % (name, args.dpi, "%dx%d" % (r["w"], r["h"]),
                                                       r["steps"], r["pixels"], r["groups"]))
            if note or not rows:
                print("  note:", note or "no rows")
        return 0
    if not os.path.isdir(args.corpus):
        print("render-work: no corpus directory %s; skipping" % args.corpus)
        return 0
    files = sorted(f for f in os.listdir(args.corpus) if f.lower().endswith(".pdf"))
    if args.files:
        files = [f for f in files if any(fnmatch.fnmatch(f, g) for g in args.files)]
    paths = [os.path.join(args.corpus, f) for f in files]
    rows, notes = [], {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        futs = {ex.submit(run_file, exe, p, args.dpi, args.check, args.file_timeout): p
                for p in paths}
        for fu in concurrent.futures.as_completed(futs):
            r, note = fu.result()
            rows.extend(r)
            name = os.path.basename(futs[fu])
            if note:
                notes[name] = note
            sys.stderr.write("%-50s %4d pages%s\n" % (name[:50], len(r),
                                                       "  (%s)" % note if note else ""))
    rows.sort(key=lambda r: (r["file"], r["page"]))
    good = [r for r in rows if not r.get("error")]
    opened = len({r["file"] for r in rows})
    print("files %d (%d with pages), pages %d (render errors %d, files with a note %d), dpi %d" % (
        len(files), opened, len(rows), len(rows) - len(good), len(notes), args.dpi))
    for f, n in sorted(notes.items()):
        print("note: %s: %s" % (f, n))
    if not good:
        return 0
    summary = {k: stats(good, k) for k in ("steps", "pixels")}
    mism = sum(1 for r in good if r["replay"] != r["steps"])
    print("replay steps != real steps on %d pages; pages with groups/soft masks: %d/%d; "
          "pages with Type 3 / pattern items charged by delta: %d"
          % (mism, sum(1 for r in good if r["groups"] or r["smasks"]),
             sum(1 for r in good if r["smasks"]), sum(1 for r in good if r["approx"])))
    if args.check:
        print("--check: image equal on %d of %d pages" % (
            sum(1 for r in good if r["imgok"] == 1), len(good)))
    for k in ("steps", "pixels"):
        s = summary[k]
        print("%-7s max %d  p99 %d  p95 %d  median %d  total %d" % (
            k, s["max"], s["p99"], s["p95"], s["median"], s["total"]))
    for k in ("steps", "pixels"):
        print("\nheaviest %d pages by %s:" % (args.top, k))
        for r in sorted(good, key=lambda r: -r[k])[:args.top]:
            print("  %12d %s p%d  (%dx%d, %d items, steps %d, pixels %d)" % (
                r[k], r["file"], r["page"], r["w"], r["h"], r["items"], r["steps"], r["pixels"]))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(dict(summary=summary, pages=good, notes=notes), fh)
    return 0


if __name__ == "__main__":
    sys.exit(main())
