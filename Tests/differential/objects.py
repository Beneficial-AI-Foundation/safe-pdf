#!/usr/bin/env python3
"""Object-level differential comparator: our inspector vs `qpdf --json` (v2).

Plan.md section 7 item 1; Phase 1 exit M1 clause 3.  Stdlib only (python3 -I).

Offline mode (used by fixtures / CI debugging):
    python3 -I Tests/differential/objects.py --ours OURS.jsonl --qpdf QPDF.json

Our side  (`inspect --view objects --json FILE`), one JSON per line:
    {"num","gen","offset","value":V} | {"num","gen","offset","error":msg}
    then {"summary": {...}}.  V: null/true/false/int/real(has '.')/
    "b:<hex>" string/"/Name" (#xx escapes)/"N G R"/array/dict("/Key")/
    {"stream": {"dict": {...}, "length": L}}.
qpdf side (JSON v2, qpdf >= 11): {"qpdf": [header, {"obj:N G R":
    {"value": V} | {"stream": {"dict": {...}}}, "trailer": {...}}]}.

ASSUMPTIONS (qpdf manual verified except where marked UNVERIFIED):
  - top level "qpdf" = 2-element array, element 1 = objects dict.   [verified]
  - strings "u:<utf8>" or "b:<hex>"; names "/Name" decoded (no #xx), and
    "n:/..." form with #xx escapes (qpdf >= 11.7).                  [verified]
  - /Length omitted from stream dicts.                               [verified]
  - numbers are native JSON numbers, int/real spelling preserved.   [verified
    only that precision is kept; spelling of reals such as ".5" UNVERIFIED]
  - "u:" text may stem from PDFDocEncoding / UTF-16BE(BOM) / UTF-8(BOM) source
    bytes (qpdf converts to Unicode when lossless).                 [UNVERIFIED]
  - qpdf drops null-valued dictionary entries on parse.             [UNVERIFIED]
  - plain (non "n:") names never carry '#' escapes.                 [UNVERIFIED]
  - `--json-key=qpdf` is accepted by qpdf 11.x.                     [UNVERIFIED]
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


class Skip(Exception):
    pass


# ---- PDFDocEncoding (for qpdf "u:" strings) --------------------------------
def _pdfdoc_map():
    m = {}
    for b in range(0x20, 0x7F):
        m[b] = chr(b)
    for b in (0x09, 0x0A, 0x0D):
        m[b] = chr(b)
    for b, c in zip(range(0x18, 0x20), [0x2D8, 0x2C7, 0x2C6, 0x2D9, 0x2DD, 0x2DB, 0x2DA, 0x2DC]):
        m[b] = chr(c)
    hi = [0x2022, 0x2020, 0x2021, 0x2026, 0x2014, 0x2013, 0x192, 0x2044, 0x2039,
          0x203A, 0x2212, 0x2030, 0x201E, 0x201C, 0x201D, 0x2018, 0x2019, 0x201A,
          0x2122, 0xFB01, 0xFB02, 0x141, 0x152, 0x160, 0x178, 0x17D, 0x131, 0x142,
          0x153, 0x161, 0x17E]
    for b, c in zip(range(0x80, 0x9F), hi):
        m[b] = chr(c)
    m[0xA0] = chr(0x20AC)
    for b in range(0xA1, 0x100):
        if b != 0xAD:
            m[b] = chr(b)
    return m


_PDFDOC_REV = {c: b for b, c in _pdfdoc_map().items()}


def string_candidates(text):
    """Byte strings that qpdf could have rendered as "u:<text>"."""
    c = {text.encode("utf-8")}                       # lenient: raw UTF-8
    c.add(b"\xef\xbb\xbf" + text.encode("utf-8"))    # explicit UTF-8 marker
    try:
        c.add(b"\xfe\xff" + text.encode("utf-16-be", "strict"))
    except UnicodeEncodeError:
        pass
    if all(ch in _PDFDOC_REV for ch in text):
        c.add(bytes(_PDFDOC_REV[ch] for ch in text))
    return frozenset(c)


# ---- normalization ----------------------------------------------------------
# Canonical forms: None/bool, ("int",int), ("real",Decimal), ("str",bytes),
# ("qstr",frozenset[bytes]) (qpdf side only), ("name",bytes), ("ref",n,g),
# ("arr",[..]), ("dict",{bytes:..}), ("stream",dict_canon).
_REF = re.compile(r"^(\d+) (\d+) R$")
_HEX = re.compile(r"^(?:[0-9a-fA-F]{2})*$")


def _unescape_name(s):
    out = bytearray()
    i, b = 0, s.encode("utf-8")
    while i < len(b):
        if b[i] == 0x23 and i + 2 < len(b) + 0 and re.fullmatch(rb"[0-9a-fA-F]{2}", b[i+1:i+3]):
            out.append(int(b[i+1:i+3], 16))
            i += 3
        else:
            out.append(b[i])
            i += 1
    return bytes(out)


class Bad(Exception):
    pass


def norm_name(s, qpdf):
    if qpdf and s.startswith("n:"):
        return _unescape_name(s[2:])
    if not s.startswith("/"):
        raise Bad("bad name %r" % s)
    return _unescape_name(s) if not qpdf else s.encode("utf-8")


def _num(v):
    if isinstance(v, bool):
        return v
    if isinstance(v, int):
        return ("int", v)
    return ("real", v)


def norm(v, qpdf):
    if v is None or isinstance(v, bool):
        return v
    if isinstance(v, (int, Decimal)):
        return _num(v)
    if isinstance(v, str):
        if v.startswith("b:"):
            if not _HEX.match(v[2:]):
                raise Bad("bad hex string %r" % v[:40])
            return ("str", bytes.fromhex(v[2:]))
        if v.startswith("u:"):
            if not qpdf:
                raise Bad("unexpected u: string on our side")
            return ("qstr", string_candidates(v[2:]))
        m = _REF.match(v)
        if m:
            return ("ref", int(m.group(1)), int(m.group(2)))
        if v.startswith("/") or (qpdf and v.startswith("n:")):
            return ("name", norm_name(v, qpdf))
        raise Bad("unrecognised string value %r" % v[:40])
    if isinstance(v, list):
        return ("arr", [norm(x, qpdf) for x in v])
    if isinstance(v, dict):
        if set(v) == {"stream"}:
            s = v["stream"]
            return ("stream", norm_dict(s.get("dict", {}), qpdf))
        return norm_dict(v, qpdf)
    raise Bad("unexpected JSON %r" % type(v))


def norm_dict(d, qpdf):
    out = {}
    for k, x in d.items():
        key = norm_name(k, qpdf)
        if key == b"/Length":   # qpdf omits /Length; we exclude it on both sides
            continue
        nx = norm(x, qpdf)
        if nx is None:         # null entry == absent (qpdf drops them)
            continue
        out[key] = nx
    return ("dict", out)


# ---- diff -------------------------------------------------------------------
def show(c):
    if c is None or isinstance(c, bool):
        return json.dumps(c)
    t = c[0]
    if t in ("int", "real"):
        return str(c[1])
    if t == "str":
        return "b:" + c[1].hex()
    if t == "qstr":
        return "u:" + sorted(c[1])[0].decode("utf-8", "replace")
    if t == "name":
        return c[1].decode("latin-1")
    if t == "ref":
        return "%d %d R" % (c[1], c[2])
    if t == "arr":
        return "[%d items]" % len(c[1])
    if t == "dict":
        return "<<%d keys>>" % len(c[1])
    return "stream"


def diff(a, b, path, out, warn):
    """a = ours, b = qpdf.  Appends human-readable diffs to out."""
    ta = a if (a is None or isinstance(a, bool)) else a[0]
    tb = b if (b is None or isinstance(b, bool)) else b[0]
    if ta in ("int", "real") and tb in ("int", "real"):
        if a[1] != b[1]:
            out.append("%s: ours %s, qpdf %s" % (path or "/", show(a), show(b)))
        elif ta != tb:
            warn.append("%s: int/real mismatch: ours %s, qpdf %s" % (path or "/", show(a), show(b)))
        return
    if ta in ("str", "qstr") and tb in ("str", "qstr"):
        if ta == tb == "str":
            ok = a[1] == b[1]
        else:
            ours, q = (a, b) if ta == "str" else (b, a)
            ok = ours[1] in q[1]
        if not ok:
            out.append("%s: ours %s, qpdf %s" % (path or "/", show(a), show(b)))
        return
    if ta != tb or (ta not in ("arr", "dict", "stream") and a != b):
        out.append("%s: ours %s, qpdf %s" % (path or "/", show(a), show(b)))
        return
    if ta == "arr":
        if len(a[1]) != len(b[1]):
            out.append("%s: array length ours %d, qpdf %d" % (path or "/", len(a[1]), len(b[1])))
        for i, (x, y) in enumerate(zip(a[1], b[1])):
            diff(x, y, "%s[%d]" % (path, i), out, warn)
    elif ta == "stream":
        diff(a[1], b[1], path, out, warn)
    elif ta == "dict":
        for k in sorted(set(a[1]) | set(b[1])):
            p = path + k.decode("latin-1")
            if k not in b[1]:
                out.append("%s: ours %s, qpdf <absent>" % (p, show(a[1][k])))
            elif k not in a[1]:
                out.append("%s: ours <absent>, qpdf %s" % (p, show(b[1][k])))
            else:
                diff(a[1][k], b[1][k], p, out, warn)


# ---- loaders ----------------------------------------------------------------
def load_ours(text):
    objs, errors, summary = {}, {}, None
    for ln, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        try:
            rec = json.loads(line, parse_float=Decimal)
        except ValueError as e:
            raise Bad("ours line %d: not JSON: %s" % (ln, e))
        if "summary" in rec:
            summary = rec["summary"]
            continue
        key = (rec["num"], rec["gen"])
        if "error" in rec:
            errors[key] = rec["error"]
            objs.pop(key, None)
        else:
            objs[key] = rec["value"]
            errors.pop(key, None)
    return objs, errors, summary


def load_qpdf(text):
    doc = json.loads(text, parse_float=Decimal)
    if not isinstance(doc, dict) or "qpdf" not in doc:
        raise Bad("qpdf JSON has no top-level 'qpdf' key (need JSON v2, qpdf >= 11)")
    q = doc["qpdf"]
    if not (isinstance(q, list) and len(q) == 2 and isinstance(q[1], dict)):
        raise Bad("unexpected 'qpdf' array shape")
    objs = {}
    for k, v in q[1].items():
        m = re.fullmatch(r"obj:(\d+) (\d+) R", k)
        if not m:
            continue  # "trailer"
        objs[(int(m.group(1)), int(m.group(2)))] = v
    return objs


def qpdf_entry_value(e):
    if "stream" in e:
        return {"stream": e["stream"]}
    if "value" in e:
        return e["value"]
    raise Bad("qpdf object with neither value nor stream")


# ---- comparison -------------------------------------------------------------
def compare(ours_text, qpdf_text):
    ours, errors, _ = load_ours(ours_text)
    qobjs = load_qpdf(qpdf_text)
    rep = {"compared": 0, "agree": 0, "disagree": 0, "ours_only": 0,
           "qpdf_only": 0, "our_errors": len(errors), "warnings": [],
           "disagreements": [], "ours_only_ids": [], "bad_inputs": []}
    for key in sorted(ours):
        tag = "%d %d" % key
        if key not in qobjs:
            rep["ours_only"] += 1
            rep["ours_only_ids"].append(tag)
            continue
        rep["compared"] += 1
        out, warn = [], []
        try:
            a = norm(ours[key], False)
            b = norm(qpdf_entry_value(qobjs[key]), True)
            diff(a, b, "", out, warn)
        except Bad as e:
            out = ["unparseable: %s" % e]
        rep["warnings"] += ["obj %s %s" % (tag, w) for w in warn]
        if out:
            rep["disagree"] += 1
            rep["disagreements"].append({"obj": tag, "diffs": out, "class": triage(out)})
        else:
            rep["agree"] += 1
    rep["qpdf_only"] = len([k for k in qobjs if k not in ours and k not in errors])
    return rep


def triage(diffs):
    """Plan.md 7.1 classes; only the obvious ones, else untriaged."""
    if any("unparseable" in d for d in diffs):
        return "our bug? (output outside the view contract)"
    if all("ours <absent>" in d for d in diffs):
        return "untriaged (qpdf has extra keys: repair/synthesis?)"
    return "untriaged"


def format_report(rep, name=""):
    lines = ["%scompared=%d agree=%d disagree=%d ours-only=%d qpdf-only=%d our-errors=%d warnings=%d" % (
        name, rep["compared"], rep["agree"], rep["disagree"], rep["ours_only"],
        rep["qpdf_only"], rep["our_errors"], len(rep["warnings"]))]
    for d in rep["disagreements"]:
        lines.append("DISAGREE obj %s [%s]" % (d["obj"], d["class"]))
        lines += ["    " + x for x in d["diffs"][:10]]
        if len(d["diffs"]) > 10:
            lines.append("    ... %d more" % (len(d["diffs"]) - 10))
    for w in rep["warnings"][:20]:
        lines.append("warning: " + w)
    if rep["ours_only"]:
        lines.append("ours-only (qpdf lacks; xref-unreachable or repaired away?): " +
                     ", ".join(rep["ours_only_ids"][:20]))
    if rep["qpdf_only"]:
        lines.append("qpdf-only: %d (expected: objects in compressed object streams until Phase 2/3)" % rep["qpdf_only"])
    return "\n".join(lines)


# ---- live mode (used by run.py) ----------------------------------------------
def run_ours(inspect, path):
    if not os.path.exists(inspect):
        raise Skip("inspector not built")
    p = subprocess.run([inspect, "--view", "objects", "--json", path],
                       capture_output=True, timeout=TIMEOUT)
    out = p.stdout.decode("utf-8", "replace")
    first = out.lstrip()[:1]
    if first != "{":
        raise Skip("view not implemented")
    if p.returncode != 0:
        raise RuntimeError("inspect exited %d: %s" % (p.returncode, p.stderr.decode("utf-8", "replace")[:200]))
    return out


def run_qpdf(path):
    p = subprocess.run(["qpdf", "--json=2", "--json-key=qpdf", "--decode-level=none", path],
                       capture_output=True, timeout=TIMEOUT)
    # exit 3 = warnings (output still valid); 2 = errors
    if p.returncode not in (0, 3) or not p.stdout.strip():
        raise Skip("qpdf failed (exit %d): %s" % (p.returncode, p.stderr.decode("utf-8", "replace").strip()[:120]))
    return p.stdout.decode("utf-8", "replace")


def check_file(inspect, path):
    """Returns (status, detail, stats) for run.py; stats = the integer counts."""
    if shutil.which("qpdf") is None:
        raise Skip("tool missing: qpdf")
    try:
        rep = compare(run_ours(inspect, path), run_qpdf(path))
    except Bad as e:
        return "error", str(e)
    text = format_report(rep)
    stats = {k: v for k, v in rep.items() if isinstance(v, int) and not isinstance(v, bool)}
    return ("disagree" if rep["disagree"] else "agree"), text, stats


def main(argv=None):
    ap = argparse.ArgumentParser(description="Compare objects dumps offline")
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
    return 1 if rep["disagree"] else 0


if __name__ == "__main__":
    sys.exit(main())
