#!/usr/bin/env python3
"""Text-extraction differential comparator: our `text` view vs poppler's `pdftotext`
(comparator `text`) or MuPDF's `mutool draw -F txt` (comparator `text-mupdf`).

Plan.md section 7 item 1; Phase 6 exit M6 ("text extraction >= 98% similarity vs
pdfium/MuPDF on corpus (normalized edit distance)"), task 6.6.  Stdlib only
(python3 -I).  This script REPORTS the similarity; the M6 threshold is evaluated
by a human / the orchestrator (`--min-similarity` exists for when CI should gate).

Offline mode (fixtures / debugging):
    python3 -I Tests/differential/text.py --ours OURS.jsonl --ref REF.txt
                                          [--min-similarity X] [--json OUT]
    python3 -I Tests/differential/text.py --selftest

Our side: `inspect --view text --json FILE`, one JSON object per page
    {"page","chars","glyphs","replacement","warnings","error","text"}
then {"summary": {...}} (or {"summary": {"error": msg}} when the document does
not open).  A page with an "error" counts as empty text.

Reference side: `pdftotext -enc UTF-8 FILE -` (poppler; default "reading order"
mode, NOT -layout, which pads with spaces to mimic the physical layout).  Its
output ends every page with a form feed (U+000C); the text is split on form
feeds and the final empty piece dropped.  When the page counts differ, pages
are paired by index and a page present on one side only is compared with the
empty string (distance = its length); the file gets the note `page-count`.

Normalization (applied to both sides, in this order; `normalize`):
  1. Unicode NFKC (`unicodedata`): compatibility forms, e.g. the ligatures
     U+FB00-FB06 -> "ff", "fi", ...; NBSP -> space; full-width forms; super-
     scripts.  (Our extraction already decomposes U+FB00-FB06.)
  2. Dropped: soft hyphen U+00AD, zero-width space/non-joiner/joiner
     U+200B-U+200D, word joiner U+2060, BOM / ZWNBSP U+FEFF, and every other
     control character (category Cc) that is not whitespace.
  3. Folded (disable with --no-fold): dashes U+2010-U+2015 and minus U+2212 ->
     "-"; single quotes U+2018-U+201B and U+2032 -> "'"; double quotes
     U+201C-U+201F and U+2033 -> '"'.  Nothing else is folded (bullets,
     accents, case all count).
  4. Whitespace: every run of whitespace (str.isspace: space, tab, newlines,
     form feed, U+2028/2029, ...) becomes ONE space; leading and trailing
     whitespace is removed.  So line breaks and paragraph gaps do not count,
     but a missing or extra word space counts as one edit.
U+FFFD (our "unmapped" glyph) is kept: it is an edit against the reference.

Similarity of a page pair (a, b) after normalization:
    sim = 1 - lev(a, b) / max(len(a), len(b))      (1.0 when both are empty)
with lev the Levenshtein distance over Unicode code points (insert, delete,
substitute, all cost 1).  `lev` strips the common prefix and suffix, then runs
Myers' / Hyyro's bit-parallel algorithm with Python big integers (exact, O(n *
m / wordsize)); it is checked against the textbook O(n*m) DP by --selftest.
Size guard: when, after stripping, the longer remainder exceeds EXACT_MAX
(100 000 code points), the page is compared at TOKEN level instead (split on
the single spaces; Levenshtein over word tokens, same bit-parallel algorithm),
its similarity is the token similarity, and the page's character distance is
estimated as round((1 - sim_tok) * max(len(a), len(b))).  Such pages are
counted in the stat `fallback_pages`.  Beyond TOKEN_MAX (200 000 tokens) a
page is scored by bag-of-words overlap (multiset F1) and counted the same way.

Aggregates:
  per file    mean / median / min page similarity, and the character-weighted
              file similarity 1 - sum(lev) / sum(max len);
  corpus      (run.py) the character-weighted similarity over all pages of all
              compared files, plus the worst pages with a short excerpt around
              the first difference.
Stats per file (ints, summed by run.py): pages, pages_exact, page_count_mismatch,
chars_ours, chars_ref, dist, maxlen, fallback_pages, ours_replacement (U+FFFD in
our normalized text), ours_failed.

Status per file: agree (compared; any similarity, unless below
--min-similarity), disagree (file similarity below --min-similarity when one
is given), known (the core rejects the document: reported here with its error,
counted as similarity 0; open failures are the objects / pages comparators'
business), error (inspector crash, timeout, output that is not our JSON),
skipped (pdftotext missing or failing on the file).
"""
import argparse
import json
import os
import random
import shutil
import statistics
import subprocess
import sys
import unicodedata

TIMEOUT = 600
EXACT_MAX = 100_000
TOKEN_MAX = 200_000
EXCERPT = 60

# Filled by check_file (live mode): every compared page, for run.py's report.
PAGES = []   # (sim, file, page, dist, maxlen, excerpt)


class Skip(Exception):
    pass


class Bad(Exception):
    pass


# ---- normalization ------------------------------------------------------------
_DROP = {0x00AD, 0x200B, 0x200C, 0x200D, 0x2060, 0xFEFF}
_FOLD = {}
for _c in list(range(0x2010, 0x2016)) + [0x2212]:
    _FOLD[_c] = "-"
for _c in (0x2018, 0x2019, 0x201A, 0x201B, 0x2032):
    _FOLD[_c] = "'"
for _c in (0x201C, 0x201D, 0x201E, 0x201F, 0x2033):
    _FOLD[_c] = '"'


def normalize(s, fold=True):
    s = unicodedata.normalize("NFKC", s)
    out = []
    space = False
    for ch in s:
        o = ord(ch)
        if ch.isspace():
            space = True
            continue
        if o in _DROP or (unicodedata.category(ch) == "Cc"):
            continue
        if fold and o in _FOLD:
            ch = _FOLD[o]
        if space and out:
            out.append(" ")
        space = False
        out.append(ch)
    return "".join(out)


# ---- edit distance ------------------------------------------------------------
def lev_dp(a, b):
    """Textbook O(len(a) * len(b)) Levenshtein (reference for --selftest)."""
    prev = list(range(len(b) + 1))
    for i, x in enumerate(a, 1):
        cur = [i] + [0] * len(b)
        for j, y in enumerate(b, 1):
            cur[j] = min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (x != y))
        prev = cur
    return prev[-1]


def lev_bits(a, b):
    """Levenshtein distance by Myers' bit-vector algorithm (Hyyro 2003, global
    variant) on Python ints; `a` and `b` are sequences of hashable symbols."""
    if len(a) > len(b):
        a, b = b, a
    m = len(a)
    if m == 0:
        return len(b)
    peq = {}
    for i, c in enumerate(a):
        peq[c] = peq.get(c, 0) | (1 << i)
    mask = (1 << m) - 1
    high = 1 << (m - 1)
    pv, mv, score = mask, 0, m
    for c in b:
        eq = peq.get(c, 0)
        xv = eq | mv
        xh = ((((eq & pv) + pv) & mask) ^ pv) | eq
        ph = (mv | ~(xh | pv)) & mask
        mh = pv & xh
        if ph & high:
            score += 1
        elif mh & high:
            score -= 1
        ph = ((ph << 1) | 1) & mask
        mh = (mh << 1) & mask
        pv = (mh | ~(xv | ph)) & mask
        mv = ph & xv
    return score


def strip_common(a, b):
    i = 0
    n = min(len(a), len(b))
    while i < n and a[i] == b[i]:
        i += 1
    j = 0
    while j < n - i and a[len(a) - 1 - j] == b[len(b) - 1 - j]:
        j += 1
    return a[i:len(a) - j], b[i:len(b) - j], i


def bag_f1(ta, tb):
    from collections import Counter
    ca, cb = Counter(ta), Counter(tb)
    inter = sum((ca & cb).values())
    if not ta and not tb:
        return 1.0
    if inter == 0:
        return 0.0
    p, r = inter / len(ta), inter / len(tb)
    return 2 * p * r / (p + r)


def page_distance(a, b):
    """(distance, maxlen, fallback) for normalized strings a, b."""
    ml = max(len(a), len(b))
    ra, rb, _ = strip_common(a, b)
    if max(len(ra), len(rb)) <= EXACT_MAX:
        return lev_bits(ra, rb), ml, False
    ta, tb = a.split(" "), b.split(" ")
    if max(len(ta), len(tb)) <= TOKEN_MAX:
        sim = 1 - lev_bits(ta, tb) / max(len(ta), len(tb), 1)
    else:
        sim = bag_f1(ta, tb)
    return round((1 - sim) * ml), ml, True


def first_diff_excerpt(a, b):
    _, _, i = strip_common(a, b)
    lo = max(0, i - 15)
    return "at %d: ref=%r ours=%r" % (i, b[lo:i + EXCERPT], a[lo:i + EXCERPT])


# ---- inputs -------------------------------------------------------------------
def load_ours(text):
    """-> (list of page texts, summary dict).  Page n is index n-1."""
    pages, summary = {}, None
    # Split on "\n" only: str.splitlines() also breaks at U+2028/U+2029/U+0085/0x1C-0x1E,
    # which may occur inside a JSON string value.
    for ln, line in enumerate(text.split("\n"), 1):
        if not line.strip():
            continue
        try:
            rec = json.loads(line)
        except ValueError as e:
            raise Bad("ours line %d: not JSON: %s" % (ln, e))
        if not isinstance(rec, dict):
            raise Bad("ours line %d: not an object" % ln)
        if "summary" in rec:
            summary = rec["summary"]
        elif "page" in rec and "text" in rec:
            pages[int(rec["page"])] = rec["text"] if rec.get("error") is None else ""
        else:
            raise Bad("ours line %d: neither a page nor the summary" % ln)
    if summary is None:
        raise Bad("ours: no summary line")
    n = max(pages) if pages else 0
    return [pages.get(k, "") for k in range(1, n + 1)], summary


def load_ref(text):
    parts = text.split("\f")
    if parts and parts[-1].strip() == "":
        parts = parts[:-1]
    return parts


# ---- comparison ---------------------------------------------------------------
def compare(ours_text, ref_text, name="input", fold=True, min_sim=None):
    ours, summary = load_ours(ours_text)
    ref = load_ref(ref_text)
    failed = "error" in summary and "pages" not in summary
    rows = []
    n = max(len(ours), len(ref))
    for k in range(n):
        a = normalize(ours[k] if k < len(ours) else "", fold)
        b = normalize(ref[k] if k < len(ref) else "", fold)
        d, ml, fb = page_distance(a, b)
        sim = 1.0 if ml == 0 else 1 - d / ml
        rows.append({"page": k + 1, "sim": sim, "dist": d, "maxlen": ml, "fallback": fb,
                     "ours_chars": len(a), "ref_chars": len(b),
                     "replacement": a.count("�"),
                     "excerpt": "" if d == 0 else first_diff_excerpt(a, b)})
    sims = [r["sim"] for r in rows]
    dist = sum(r["dist"] for r in rows)
    maxlen = sum(r["maxlen"] for r in rows)
    fsim = 1.0 if maxlen == 0 else 1 - dist / maxlen
    rep = {
        "file": name, "pages_ours": len(ours), "pages_ref": len(ref),
        "ours_failed": summary.get("error") if failed else None,
        "similarity": fsim,
        "mean": statistics.fmean(sims) if sims else 1.0,
        "median": statistics.median(sims) if sims else 1.0,
        "min": min(sims) if sims else 1.0,
        "rows": rows,
    }
    if failed:
        rep["status"] = "known"
    elif min_sim is not None and fsim < min_sim:
        rep["status"] = "disagree"
    else:
        rep["status"] = "agree"
    return rep


def format_report(rep):
    s = "similarity %.4f (pages ours %d ref %d; page mean %.4f median %.4f min %.4f)" % (
        rep["similarity"], rep["pages_ours"], rep["pages_ref"], rep["mean"], rep["median"],
        rep["min"])
    if rep["pages_ours"] != rep["pages_ref"]:
        s += " page-count"
    if rep["ours_failed"]:
        s += " ours-failed: %s" % rep["ours_failed"]
    return s


def stats_of(rep):
    rows = rep["rows"]
    return {
        "compared": len(rows),
        "pages": len(rows),
        "pages_exact": sum(1 for r in rows if r["dist"] == 0),
        "page_count_mismatch": int(rep["pages_ours"] != rep["pages_ref"]),
        "chars_ours": sum(r["ours_chars"] for r in rows),
        "chars_ref": sum(r["ref_chars"] for r in rows),
        "dist": sum(r["dist"] for r in rows),
        "maxlen": sum(r["maxlen"] for r in rows),
        "fallback_pages": sum(1 for r in rows if r["fallback"]),
        "ours_replacement": sum(r["replacement"] for r in rows),
        "ours_failed": int(bool(rep["ours_failed"])),
    }


def worst_lines(pages, n=10):
    """Report lines for the n worst pages: (sim, file, page, dist, maxlen, excerpt)."""
    out = []
    for sim, f, pg, d, ml, ex in sorted(pages, key=lambda t: (t[0], -t[4]))[:n]:
        if d == 0:
            break
        out.append("  %.4f %s p%d (lev %d / %d) %s" % (sim, f, pg, d, ml, ex))
    return out


# ---- live mode (used by run.py) -----------------------------------------------
def run_ours(inspect, path):
    if not os.path.exists(inspect):
        raise Skip("inspector not built")
    p = subprocess.run([inspect, "--view", "text", "--json", path],
                       capture_output=True, timeout=TIMEOUT)
    out = p.stdout.decode("utf-8", "replace")
    if out.lstrip()[:1] != "{":
        if "unknown view" in (out + p.stderr.decode("utf-8", "replace")).lower():
            raise Skip("view not implemented")
        raise Bad("inspect exited %d without JSON: %s" % (
            p.returncode, p.stderr.decode("utf-8", "replace").strip()[:200]))
    if p.returncode != 0 and '"summary"' not in out:
        raise Bad("inspect exited %d: %s" % (p.returncode, p.stderr.decode("utf-8", "replace")[:200]))
    return out


# Reference extractors: name -> (executable, argv builder). Both write UTF-8 text with
# a form feed after every page, so `load_ref` splits them the same way.
#   pdftotext: poppler's default "reading order" text (`pdftotext -enc UTF-8 FILE -`).
#   mupdf:     MuPDF's structured-text output (`mutool draw -q -F txt -o - FILE`).
REFERENCES = {
    "pdftotext": ("pdftotext", lambda p: ["pdftotext", "-enc", "UTF-8", p, "-"]),
    "mupdf": ("mutool", lambda p: ["mutool", "draw", "-q", "-F", "txt", "-o", "-", p]),
}


def run_ref(path, ref="pdftotext"):
    tool, argv = REFERENCES[ref]
    p = subprocess.run(argv(path), capture_output=True, timeout=TIMEOUT)
    if p.returncode != 0:
        raise Skip("%s failed (exit %d): %s" % (
            tool, p.returncode, p.stderr.decode("utf-8", "replace").strip()[:120]))
    return p.stdout.decode("utf-8", "replace")


def check_file(inspect, path, fold=True, min_sim=None, ref="pdftotext"):
    """Returns (status, detail, stats) for run.py; records pages in PAGES.
    `ref` selects the reference extractor (`REFERENCES`: pdftotext or mupdf)."""
    tool = REFERENCES[ref][0]
    if shutil.which(tool) is None:
        raise Skip("tool missing: %s" % tool)
    try:
        rep = compare(run_ours(inspect, path), run_ref(path, ref), path, fold, min_sim)
    except Bad as e:
        return "error", str(e), {}
    except subprocess.TimeoutExpired as e:
        return "error", "timeout: %s" % e, {}
    for r in rep["rows"]:
        PAGES.append((r["sim"], path, r["page"], r["dist"], r["maxlen"], r["excerpt"]))
    return rep["status"], format_report(rep), stats_of(rep)


# ---- self test ----------------------------------------------------------------
def selftest():
    rng = random.Random(6)
    bad = 0
    for trial in range(400):
        alpha = "ab c" if trial % 2 else "abcdefgh é�"
        a = "".join(rng.choice(alpha) for _ in range(rng.randrange(0, 90)))
        b = "".join(rng.choice(alpha) for _ in range(rng.randrange(0, 90)))
        if lev_bits(a, b) != lev_dp(a, b):
            bad += 1
            print("MISMATCH %r %r: bits %d dp %d" % (a, b, lev_bits(a, b), lev_dp(a, b)))
    cases = [("kitten", "sitting", 3), ("", "abc", 3), ("abc", "", 3), ("flaw", "lawn", 2),
             ("x" * 70, "x" * 69 + "y", 1)]
    for a, b, d in cases:
        if lev_bits(a, b) != d:
            bad += 1
            print("MISMATCH %r %r: want %d got %d" % (a, b, d, lev_bits(a, b)))
    norm = [("a­b", "ab"), ("ﬁne", "fine"), ("x \n\n\t y\f", "x y"),
            ("“q” – ’", "\"q\" - '"), ("a b", "a b"), ("​z", "z")]
    for s, want in norm:
        if normalize(s) != want:
            bad += 1
            print("NORMALIZE %r: want %r got %r" % (s, want, normalize(s)))
    print("selftest: %s" % ("ok" if bad == 0 else "%d failure(s)" % bad))
    return 1 if bad else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description="Compare text dumps offline")
    ap.add_argument("--ours", help="our `inspect --view text --json` output")
    ap.add_argument("--ref", help="pdftotext -enc UTF-8 output (pages end with form feeds)")
    ap.add_argument("--json", metavar="OUT")
    ap.add_argument("--min-similarity", type=float, default=None, metavar="X",
                    help="exit 1 when the file similarity is below X")
    ap.add_argument("--no-fold", action="store_true", help="do not fold dashes and quotes")
    ap.add_argument("--selftest", action="store_true", help="check lev_bits and normalize")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    if not (a.ours and a.ref):
        ap.error("--ours and --ref are required (or --selftest)")
    with open(a.ours, encoding="utf-8") as f1, open(a.ref, encoding="utf-8") as f2:
        try:
            rep = compare(f1.read(), f2.read(), a.ours, not a.no_fold, a.min_similarity)
        except Bad as e:
            print("error: %s" % e)
            return 2
    print("%s: %s" % (rep["status"], format_report(rep)))
    for r in rep["rows"]:
        print("  page %d: %.4f (lev %d / %d)%s" % (r["page"], r["sim"], r["dist"], r["maxlen"],
              (" " + r["excerpt"]) if r["excerpt"] else ""))
    if a.json:
        with open(a.json, "w") as fh:
            json.dump(rep, fh, indent=1)
    return 1 if rep["status"] == "disagree" else 0


if __name__ == "__main__":
    sys.exit(main())
