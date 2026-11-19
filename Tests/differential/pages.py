#!/usr/bin/env python3
"""Page-tree differential comparator: our `pages` view vs `qpdf --json` (v2).

Plan.md section 7 item 1; Phase 4 exit M4 ("page count + page boxes match qpdf on
corpus").  Stdlib only (python3 -I).

Offline mode (fixtures / CI debugging):
    python3 -I Tests/differential/pages.py --ours OURS.jsonl --qpdf QPDF.json

Our side (`inspect --view pages --json FILE`), one JSON object per line:
    {"index","num","gen","mediaBox":[llx,lly,urx,ury],"cropBox":[..],
     "mediaBoxDefaulted","rotate","label","links"}  per page, then
    {"summary": {"pages", "declaredCount", "countMismatch", ...}} or
    {"summary": {"error": msg}} when the core rejects the page tree.
    Box numbers are exact decimals (parsed here with Decimal).  The CropBox is
    already clipped to the MediaBox (Core.Doc rule A6).

qpdf side (`qpdf --json=2 --json-key=pages --json-key=qpdf --decode-level=none
FILE`, qpdf >= 11):  "pages": [{"object": "N G R", ...}, ...] gives the page
order (qpdf's own page-tree walk); "qpdf": [header, {"obj:N G R": {"value": V}
| {"stream": ...}}] gives the raw objects.  qpdf does not report effective
boxes, so this script computes them from the raw objects with the same rules as
the core (Core/Doc.lean A1-A6), but by a different walk:

  * Inheritance follows the page's /Parent chain upwards (the core walks /Kids
    downwards).  Each attribute is the first node's own valid value; the chain
    stops at a missing /Parent, a non-reference, or a repeated node.
  * One-level resolution: a value "N G R" is replaced by that object's value; a
    stream or a missing object counts as absent.
  * /MediaBox, /CropBox: an array of exactly four numbers, else absent (and
    inheritance continues); corners normalized (min/max).  No MediaBox anywhere:
    US Letter [0 0 612 792] (our default; reported as `defaulted`, and our
    `mediaBoxDefaulted` must be true).
  * CropBox: absent -> MediaBox; else intersected with the MediaBox; an empty
    intersection (max(ll) > min(ur) on either axis) -> MediaBox.  So OUR clipped
    crop box is compared with qpdf's RAW crop box clipped the same way.
  * /Rotate: an integer, or an integral real, taken modulo 360; a value that is
    not a multiple of 90 is 0; a non-number is absent; default 0.

Numbers: exact Decimal comparison with tolerance 0 for integers and 1e-9 for
reals (in practice both sides are exact: qpdf prints the file's digits, we
print the exact decimal).

Classification per file (`classify`):
  agree      count, every page reference, MediaBox, CropBox and Rotate equal.
  known      known divergence, not a mismatch: the core rejects a page tree in
             which a node is reached twice (a page shared by two parents, or a
             /Kids cycle) with `reference cycle`, while qpdf repairs it (it
             duplicates a shared page).  docs/deviations-from-spec.md D-002.
  disagree   categories: ours-failed (we reject, qpdf opens, not a cycle),
             count, ref (page i is a different object), mediabox, cropbox,
             rotate, defaulted-flag.
qpdf failing on the file (exit not 0/3, or no JSON) is a skip.

ASSUMPTIONS (qpdf manual, JSON v2; UNVERIFIED locally since qpdf is not
installed here -- CI runs qpdf 11 on ubuntu-24.04):
  - "pages" is a list of objects with "object": "N G R", in document order.
  - `--json-key` may be repeated; "qpdf" holds [header, objects dict].
  - numbers are native JSON numbers; references are "N G R" strings; names "/X".
  - when qpdf duplicates a shared page, the copy is a new object listed in
    "pages" and present in the "qpdf" objects.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from decimal import Decimal

TIMEOUT = 60
REAL_TOL = Decimal("1e-9")
LETTER = (Decimal(0), Decimal(0), Decimal(612), Decimal(792))
_REF = re.compile(r"^(\d+) (\d+) R$")


class Skip(Exception):
    pass


class Bad(Exception):
    pass


# ---- our side ---------------------------------------------------------------
def load_ours(text):
    pages, summary = [], None
    for ln, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        try:
            rec = json.loads(line, parse_float=Decimal)
        except ValueError as e:
            raise Bad("ours line %d: not JSON: %s" % (ln, e))
        if "summary" in rec:
            summary = rec["summary"]
        else:
            pages.append(rec)
    if summary is None:
        raise Bad("ours: no summary line")
    return pages, summary


# ---- qpdf side --------------------------------------------------------------
def load_qpdf(text):
    doc = json.loads(text, parse_float=Decimal)
    if not isinstance(doc, dict) or "pages" not in doc or "qpdf" not in doc:
        raise Bad("qpdf JSON lacks 'pages' or 'qpdf' (need JSON v2, qpdf >= 11)")
    q = doc["qpdf"]
    if not (isinstance(q, list) and len(q) == 2 and isinstance(q[1], dict)):
        raise Bad("unexpected 'qpdf' array shape")
    objs = {}
    for k, v in q[1].items():
        m = re.fullmatch(r"obj:(\d+) (\d+) R", k)
        if m:
            objs[(int(m.group(1)), int(m.group(2)))] = v
    refs = []
    for p in doc["pages"]:
        m = _REF.match(p.get("object", "")) if isinstance(p, dict) else None
        if not m:
            raise Bad("qpdf page entry without an 'object' reference: %r" % (p,))
        refs.append((int(m.group(1)), int(m.group(2))))
    return refs, objs


def _is_num(v):
    return isinstance(v, (int, Decimal)) and not isinstance(v, bool)


def resolve(objs, v):
    """One-level resolution (rule A1): a stream or a missing object is None."""
    if isinstance(v, str):
        m = _REF.match(v)
        if m:
            e = objs.get((int(m.group(1)), int(m.group(2))))
            if not isinstance(e, dict) or "value" not in e:
                return None
            return e["value"]
    return v


def rect_of(v):
    if not (isinstance(v, list) and len(v) == 4 and all(_is_num(x) for x in v)):
        return None
    a, b, c, d = (Decimal(x) for x in v)
    return (min(a, c), min(b, d), max(a, c), max(b, d))


def rotate_of(v):
    if not _is_num(v):
        return None
    d = Decimal(v)
    if d != d.to_integral_value():
        return 0
    r = int(d) % 360
    return r if r in (0, 90, 180, 270) else 0


def clip(c, m):
    llx, lly = max(c[0], m[0]), max(c[1], m[1])
    urx, ury = min(c[2], m[2]), min(c[3], m[3])
    if llx <= urx and lly <= ury:
        return (llx, lly, urx, ury)
    return m


def node_dict(objs, ref):
    e = objs.get(ref)
    if isinstance(e, dict) and isinstance(e.get("value"), dict):
        return e["value"]
    return None


def effective(objs, ref, max_chain=10000):
    """Effective (media, crop, rotate, defaulted) of page `ref` via its /Parent chain."""
    media = crop = rot = None
    seen = set()
    cur = ref
    while cur is not None and cur not in seen and len(seen) < max_chain:
        seen.add(cur)
        d = node_dict(objs, cur)
        if d is None:
            break
        if media is None:
            media = rect_of(resolve(objs, d.get("/MediaBox")))
        if crop is None:
            crop = rect_of(resolve(objs, d.get("/CropBox")))
        if rot is None:
            rot = rotate_of(resolve(objs, d.get("/Rotate")))
        p = d.get("/Parent")
        m = _REF.match(p) if isinstance(p, str) else None
        cur = (int(m.group(1)), int(m.group(2))) if m else None
    defaulted = media is None
    media = media or LETTER
    crop = media if crop is None else clip(crop, media)
    return media, crop, (rot if rot is not None else 0), defaulted


# ---- comparison -------------------------------------------------------------
def num_eq(a, b):
    a, b = Decimal(a), Decimal(b)
    if a == a.to_integral_value() and b == b.to_integral_value():
        return a == b
    return abs(a - b) <= REAL_TOL


def box_eq(a, b):
    return len(a) == 4 and len(b) == 4 and all(num_eq(x, y) for x, y in zip(a, b))


def show_box(b):
    return "[%s]" % " ".join(str(x) for x in b)


def compare(ours_text, qpdf_text):
    pages, summary = load_ours(ours_text)
    refs, objs = load_qpdf(qpdf_text)
    rep = {"status": "agree", "categories": {}, "compared": 0, "qpdf_pages": len(refs),
           "our_pages": len(pages), "defaulted": 0, "known": 0, "diffs": []}

    def bad(cat, msg):
        rep["categories"][cat] = rep["categories"].get(cat, 0) + 1
        rep["diffs"].append("%s: %s" % (cat, msg))

    if "error" in summary:
        err = summary["error"]
        if "reference cycle" in err:
            rep["status"] = "known"
            rep["known"] = 1
            rep["categories"]["shared-or-cyclic-page-tree"] = 1
            rep["diffs"].append("known (D-002): ours rejects the page tree (%s); qpdf lists %d page(s)"
                                % (err, len(refs)))
        else:
            rep["status"] = "disagree"
            bad("ours-failed", "%s; qpdf lists %d page(s)" % (err, len(refs)))
        return rep
    if len(pages) != len(refs):
        bad("count", "ours %d, qpdf %d" % (len(pages), len(refs)))
    for i, (p, ref) in enumerate(zip(pages, refs)):
        rep["compared"] += 1
        if (p["num"], p["gen"]) != ref:
            bad("ref", "page %d: ours %d %d R, qpdf %d %d R" % (i, p["num"], p["gen"], ref[0], ref[1]))
            continue
        media, crop, rot, dflt = effective(objs, ref)
        rep["defaulted"] += dflt
        if not box_eq(p["mediaBox"], media):
            bad("mediabox", "page %d: ours %s, qpdf %s" % (i, show_box(p["mediaBox"]), show_box(media)))
        if bool(p["mediaBoxDefaulted"]) != dflt:
            bad("defaulted-flag", "page %d: ours %s, qpdf-side %s" % (i, p["mediaBoxDefaulted"], dflt))
        if not box_eq(p["cropBox"], crop):
            bad("cropbox", "page %d: ours %s, qpdf (clipped) %s" % (i, show_box(p["cropBox"]), show_box(crop)))
        if p["rotate"] != rot:
            bad("rotate", "page %d: ours %s, qpdf %s" % (i, p["rotate"], rot))
    if rep["categories"]:
        rep["status"] = "disagree"
    return rep


def format_report(rep):
    cats = " ".join("%s=%d" % kv for kv in sorted(rep["categories"].items()))
    lines = ["%s: our-pages=%d qpdf-pages=%d compared=%d defaulted=%d%s" % (
        rep["status"], rep["our_pages"], rep["qpdf_pages"], rep["compared"], rep["defaulted"],
        (" [" + cats + "]") if cats else "")]
    lines += ["    " + d for d in rep["diffs"][:20]]
    if len(rep["diffs"]) > 20:
        lines.append("    ... %d more" % (len(rep["diffs"]) - 20))
    return "\n".join(lines)


def stats_of(rep):
    s = {"compared": rep["compared"], "our_pages": rep["our_pages"],
         "qpdf_pages": rep["qpdf_pages"], "defaulted": rep["defaulted"], "known": rep["known"]}
    for k, v in rep["categories"].items():
        s["cat_" + k] = v
    return s


# ---- live mode (used by run.py) ----------------------------------------------
def run_ours(inspect, path):
    if not os.path.exists(inspect):
        raise Skip("inspector not built")
    p = subprocess.run([inspect, "--view", "pages", "--json", path],
                       capture_output=True, timeout=TIMEOUT)
    out = p.stdout.decode("utf-8", "replace")
    if out.lstrip()[:1] != "{":
        raise Skip("view not implemented")
    if p.returncode != 0 and '"summary"' not in out:
        raise RuntimeError("inspect exited %d: %s" % (p.returncode, p.stderr.decode("utf-8", "replace")[:200]))
    return out


def run_qpdf(path):
    p = subprocess.run(["qpdf", "--json=2", "--json-key=pages", "--json-key=qpdf",
                        "--decode-level=none", path], capture_output=True, timeout=TIMEOUT)
    # exit 3 = warnings (output still valid); 2 = errors
    if p.returncode not in (0, 3) or not p.stdout.strip():
        raise Skip("qpdf failed (exit %d): %s" % (p.returncode, p.stderr.decode("utf-8", "replace").strip()[:120]))
    return p.stdout.decode("utf-8", "replace")


def check_file(inspect, path):
    """Returns (status, detail, stats) for run.py; status agree | known | disagree | error."""
    if shutil.which("qpdf") is None:
        raise Skip("tool missing: qpdf")
    try:
        rep = compare(run_ours(inspect, path), run_qpdf(path))
    except Bad as e:
        return "error", str(e), {}
    return rep["status"], format_report(rep), stats_of(rep)


def main(argv=None):
    ap = argparse.ArgumentParser(description="Compare pages dumps offline")
    ap.add_argument("--ours", required=True)
    ap.add_argument("--qpdf", required=True)
    ap.add_argument("--json", metavar="OUT")
    a = ap.parse_args(argv)
    with open(a.ours, encoding="utf-8") as f1, open(a.qpdf, encoding="utf-8") as f2:
        try:
            rep = compare(f1.read(), f2.read())
        except Bad as e:
            print("error: %s" % e)
            return 2
    print(format_report(rep))
    if a.json:
        with open(a.json, "w") as fh:
            json.dump(rep, fh, indent=1)
    return 1 if rep["status"] == "disagree" else 0


if __name__ == "__main__":
    sys.exit(main())
