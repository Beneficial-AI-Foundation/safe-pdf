#!/usr/bin/env python3
"""FlateDecode differential comparator: our decoder vs Python `zlib` (task 3.6b).

Plan.md section 6 Phase 3.  Stdlib only (python3 -I); skips cleanly when the
inspector is not built.

Offline mode (fixtures / debugging; no inspector needed):
    python3 -I Tests/differential/streams.py --ours OURS.bin --raw RAW.bin

Live mode (used by run.py, or directly):
    python3 -I Tests/differential/streams.py [--per-file N] FILE.pdf...

Method, per PDF:
  1. `inspect --view streams --json FILE` (20 s timeout) lists every stream with
     its filter chain, `raw` length, our `decoded` length and any `error`.
  2. Only streams whose chain is exactly [FlateDecode], with no /DecodeParms
     (`decodeParms` false), are compared; everything else is counted as skipped.
  3. RAW BYTES are located by the script itself (the view exposes no offset):
     scan the file for `N G obj` (all matches, last first, so incremental
     updates resolve to the newest definition), find the first `>> stream`
     EOL within 64 KiB after it, take exactly `raw` bytes (the length OUR
     decoder used, so a wrong /Length is not re-parsed here) and accept the
     candidate only if the bytes after it are `\\s*endstream`.  Otherwise the
     stream is skipped ("raw bytes not located").
  4. Every located stream gets a cheap SIZE check: zlib's decoded length against
     the view's `decoded` (one inspector call per file).  A sample of up to
     `--per-file` streams (evenly spread; 0 = all) also gets a BYTE comparison:
     `SAFEPDF_STREAM=N SAFEPDF_STREAM_OUT=tmp inspect --view streams FILE`
     writes our full decoded bytes, compared with zlib's.
  zlib side: `zlib.decompressobj()`; outcome `ok` (stream end, nothing after),
  `trailing` (stream end, bytes after), `truncated` (no stream end) or `error`
  (zlib.error, e.g. bad Adler-32).  Our decoder is strict about Adler-32.

Per-stream categories:
  agree       both decode, same bytes (sub-count `trailing`: zlib saw trailing bytes)
  disagree    both decode, different bytes / length
  ours-error  we reject, zlib decodes (ok/trailing/truncated)
  zlib-error  zlib rejects (error) or hits truncation, we decode
  both-error  both reject
  skipped     not plain Flate / not located / sample cap / zlib size limit
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile
import time
import zlib
import json

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
INSPECT = os.path.join(ROOT, ".lake", "build", "bin", "inspect")
LIST_TIMEOUT = 20
ONE_TIMEOUT = 20
ZLIB_MAX = 256 * 1024 * 1024   # stop inflating beyond this many bytes
DICT_WINDOW = 65536


class Skip(Exception):
    pass


# ---- zlib side --------------------------------------------------------------
def zlib_decode(raw):
    """Returns (status, output); status in ok|trailing|truncated|error|limit."""
    d = zlib.decompressobj()
    try:
        out = d.decompress(raw, ZLIB_MAX)
    except zlib.error as e:
        return "error", str(e)
    if len(out) >= ZLIB_MAX and d.unconsumed_tail:
        return "limit", out
    if not d.eof:
        return "truncated", out
    return ("trailing" if d.unused_data else "ok"), out


def classify(ours, ours_err, zstatus, zout):
    """One stream.  ours: bytes|None, ours_err: str|None.  Returns (category, detail)."""
    if zstatus == "limit":
        return "skipped", "zlib output over %d bytes" % ZLIB_MAX
    if ours_err is not None:
        if zstatus == "error":
            return "both-error", "ours: %s; zlib: %s" % (ours_err, zout)
        return "ours-error", "ours: %s; zlib: %s (%d bytes)" % (ours_err, zstatus, len(zout))
    if zstatus in ("error", "truncated"):
        det = zout if zstatus == "error" else "truncated (%d bytes)" % len(zout)
        return "zlib-error", "zlib: %s; ours decoded %d bytes" % (det, len(ours))
    if ours == zout:
        return ("agree", "trailing") if zstatus == "trailing" else ("agree", "")
    i = next((k for k, (a, b) in enumerate(zip(ours, zout)) if a != b), min(len(ours), len(zout)))
    return "disagree", "ours %d bytes, zlib %d bytes, first difference at offset %d" % (
        len(ours), len(zout), i)


# ---- raw byte location ------------------------------------------------------
def locate_raw(data, num, gen, rawlen):
    """Raw stream bytes of `num gen obj` with exactly `rawlen` bytes, or None."""
    obj_re = re.compile(rb"(?<![0-9])%d[ \t\r\n\x00\x0c]+%d[ \t\r\n\x00\x0c]+obj\b" % (num, gen))
    stream_re = re.compile(rb">>[ \t\r\n\x00\x0c]*stream(\r\n|\n|\r)")
    matches = list(obj_re.finditer(data))
    for m in reversed(matches):
        s = stream_re.search(data, m.end(), m.end() + DICT_WINDOW)
        if not s:
            continue
        start = s.end()
        end = start + rawlen
        if end > len(data):
            continue
        if re.match(rb"[ \t\r\n\x00\x0c]*endstream", data[end:end + 64]):
            return data[start:end]
    return None


# ---- inspector side ---------------------------------------------------------
def list_streams(inspect, path):
    if not os.path.exists(inspect):
        raise Skip("inspector not built")
    try:
        p = subprocess.run([inspect, "--view", "streams", "--json", path],
                           capture_output=True, timeout=LIST_TIMEOUT)
    except subprocess.TimeoutExpired:
        raise Skip("inspect --view streams timed out (%d s)" % LIST_TIMEOUT)
    recs = []
    for line in p.stdout.decode("utf-8", "replace").splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if "num" in r:
            recs.append(r)
    if not recs and p.returncode != 0:
        raise Skip("inspect exited %d" % p.returncode)
    return recs


def our_bytes(inspect, path, num):
    """Our full decoded bytes of object `num` (or raises RuntimeError)."""
    with tempfile.TemporaryDirectory() as td:
        out = os.path.join(td, "out.bin")
        env = dict(os.environ, SAFEPDF_STREAM=str(num), SAFEPDF_STREAM_OUT=out)
        p = subprocess.run([inspect, "--view", "streams", path], capture_output=True,
                           timeout=ONE_TIMEOUT, env=env)
        if not os.path.exists(out):
            raise RuntimeError("no output written (exit %d): %s" % (
                p.returncode, p.stderr.decode("utf-8", "replace").strip()[:120]))
        with open(out, "rb") as fh:
            return fh.read()


def sample(idx, n):
    """n evenly spread elements of idx (all when n <= 0 or n >= len)."""
    if n <= 0 or n >= len(idx):
        return list(idx)
    if n == 1:
        return [idx[0]]
    return [idx[(i * (len(idx) - 1)) // (n - 1)] for i in range(n)]


def is_plain_flate(r):
    return r.get("filters") == ["FlateDecode"] and not r.get("decodeParms") and not r.get("resolved")


# ---- per-file check ---------------------------------------------------------
NEW_STATS = ("flate_plain", "byte_compared", "agree", "agree_trailing", "disagree", "ours_error",
             "zlib_error", "both_error", "skipped_nonflate", "skipped_unlocated",
             "skipped_unsampled", "skipped_other", "size_checked", "size_disagree",
             "bytes_compared", "ours_ms", "zlib_ms", "compared")


def check_file(inspect, path, per_file=20, verbose=False):
    """Returns (status, detail, stats) for run.py."""
    recs = list_streams(inspect, path)
    st = {k: 0 for k in NEW_STATS}
    problems = []
    with open(path, "rb") as fh:
        data = fh.read()
    seen = {}
    for r in recs:
        seen[r["num"]] = seen.get(r["num"], 0) + 1
    cand = []
    for r in recs:
        if not is_plain_flate(r) or "raw" not in r:
            st["skipped_nonflate"] += 1
        elif seen[r["num"]] > 1:
            st["skipped_other"] += 1      # several generations of one entry: ambiguous
        else:
            cand.append(r)
    st["flate_plain"] = len(cand)
    located = []
    for r in cand:
        raw = locate_raw(data, r["num"], r["gen"], r["raw"])
        if raw is None:
            st["skipped_unlocated"] += 1
            problems.append("%d %d: raw bytes not located (skipped)" % (r["num"], r["gen"]))
        else:
            located.append((r, raw))
    chosen = {id(located[i][0]) for i in sample(range(len(located)), per_file)}
    for r, raw in located:
        t0 = time.perf_counter()
        zs, zo = zlib_decode(raw)
        st["zlib_ms"] += int((time.perf_counter() - t0) * 1000)
        tag = "%d %d" % (r["num"], r["gen"])
        ours_err = r.get("error")
        if isinstance(ours_err, bool):
            ours_err = "error"
        try:
            st["ours_ms"] += int(float(r.get("ms", 0)))
        except (TypeError, ValueError):
            pass
        if id(r) not in chosen:
            # size-only check against the view's decoded length
            if zs == "limit":
                st["skipped_other"] += 1
                continue
            st["size_checked"] += 1
            if ours_err is None and zs in ("ok", "trailing") and len(zo) != r.get("decoded"):
                st["size_disagree"] += 1
                problems.append("obj %s SIZE: ours %s bytes, zlib %d bytes" % (tag, r.get("decoded"), len(zo)))
            elif (ours_err is None) != (zs in ("ok", "trailing")):
                # accept/reject mismatch surfaces in the byte check only for sampled
                # streams; here it is reported as a size-level problem too.
                if ours_err is not None or zs in ("error", "truncated"):
                    cat, det = classify(None if ours_err else b"", ours_err, zs, zo)
                    if cat in ("ours-error", "zlib-error"):
                        st["size_disagree"] += 1
                        problems.append("obj %s %s (size pass): %s" % (tag, cat.upper(), det))
            st["skipped_unsampled"] += 1
            continue
        ours = None
        if ours_err is None:
            try:
                ours = our_bytes(inspect, path, r["num"])
            except (RuntimeError, subprocess.TimeoutExpired) as e:
                ours_err = "could not fetch our bytes: %s" % e
        cat, det = classify(ours, ours_err, zs, zo)
        st["byte_compared"] += 1
        if cat == "agree":
            st["agree"] += 1
            st["bytes_compared"] += len(zo)
            if det == "trailing":
                st["agree_trailing"] += 1
        elif cat == "skipped":
            st["skipped_other"] += 1
        else:
            key = cat.replace("-", "_")
            st[key] += 1
            if cat != "both-error":
                problems.append("obj %s %s: %s" % (tag, cat.upper(), det))
    st["compared"] = st["byte_compared"]
    bad = st["disagree"] + st["ours_error"] + st["zlib_error"] + st["size_disagree"]
    summary = "flate=%d bytes-compared=%d agree=%d disagree=%d ours-error=%d zlib-error=%d both-error=%d size-checked=%d size-disagree=%d" % (
        st["flate_plain"], st["byte_compared"], st["agree"], st["disagree"], st["ours_error"],
        st["zlib_error"], st["both_error"], st["size_checked"], st["size_disagree"])
    detail = "\n".join([summary] + ["  " + p for p in problems]) if (bad or problems) else summary
    return ("disagree" if bad else "agree"), detail, st


# ---- offline mode -----------------------------------------------------------
def compare_offline(ours_path, raw_path):
    with open(raw_path, "rb") as fh:
        raw = fh.read()
    with open(ours_path, "rb") as fh:
        ours = fh.read()
    zs, zo = zlib_decode(raw)
    cat, det = classify(ours, None, zs, zo)
    return cat, det


def main(argv=None):
    ap = argparse.ArgumentParser(description="Flate differential: our decoder vs zlib")
    ap.add_argument("--ours", help="offline: file holding our decoded bytes")
    ap.add_argument("--raw", help="offline: file holding the raw (compressed) stream bytes")
    ap.add_argument("--per-file", type=int, default=20,
                    help="byte-compare at most N streams per file (0 = all; default 20)")
    ap.add_argument("--inspect", default=INSPECT)
    ap.add_argument("--json", metavar="OUT")
    ap.add_argument("files", nargs="*")
    a = ap.parse_args(argv)
    if a.ours or a.raw:
        if not (a.ours and a.raw):
            ap.error("--ours and --raw go together")
        cat, det = compare_offline(a.ours, a.raw)
        print("%s%s" % (cat, (": " + det) if det else ""))
        return 0 if cat == "agree" else 1
    if not a.files:
        ap.error("give PDF files, or --ours/--raw")
    total = {}
    bad = False
    results = []
    for f in a.files:
        try:
            status, detail, st = check_file(a.inspect, f, a.per_file)
        except Skip as e:
            print("%s: skipped (%s)" % (f, e))
            continue
        print("%s: %s %s" % (f, status, detail))
        results.append({"file": f, "status": status, "detail": detail, "stats": st})
        for k, v in st.items():
            total[k] = total.get(k, 0) + v
        bad = bad or status != "agree"
    print("totals: " + " ".join("%s=%d" % kv for kv in sorted(total.items())))
    if a.json:
        with open(a.json, "w") as fh:
            json.dump({"totals": total, "results": results}, fh, indent=1)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
