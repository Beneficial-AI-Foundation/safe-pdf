#!/usr/bin/env python3
"""Corpus acquisition for safe-pdf.  Run as:  python3 -I scripts/corpus/fetch.py

  (no args)            download every manifest entry missing from corpus/files/,
                       verify SHA-256 + size of all present files, report.
  --add URL [URL...]   download, hash and append new entries to the manifest.
      --category K=V   (repeatable) override/add category fields, e.g. engine=pdfTeX
      --source S       source label (default: derived from host)
      --license L      license note (default: derived from host)
  --reindex            recompute producer/engine metadata of present files (offline).
  --summary            print counts per engine / year / producer from the manifest.

Stdlib only.  Downloaded bytes are only ever read, never executed or parsed by
anything but the regexes below.  Files are written to a temp name, verified,
then renamed; mismatches are reported and deleted.
"""
import hashlib, json, os, re, sys, time, zlib, urllib.request, urllib.error
from collections import Counter
from urllib.parse import urlparse

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MANIFEST = os.path.join(ROOT, "corpus", "manifest.json")
FILES = os.path.join(ROOT, "corpus", "files")
UA = "safe-pdf-corpus-fetch/0.1 (research corpus; polite rate limit)"
MIN_INTERVAL = {"arxiv.org": 3.5}   # seconds between requests per host
DEFAULT_INTERVAL = 1.0
MAX_BYTES = 64 * 1024 * 1024
_last = {}


def throttle(host):
    wait = MIN_INTERVAL.get(host, DEFAULT_INTERVAL) - (time.monotonic() - _last.get(host, -1e9))
    if wait > 0:
        time.sleep(wait)
    _last[host] = time.monotonic()


def download(url, dest):
    host = urlparse(url).hostname or ""
    for attempt in range(3):
        throttle(host)
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        try:
            with urllib.request.urlopen(req, timeout=60) as r, open(dest, "wb") as f:
                n = 0
                while True:
                    b = r.read(1 << 16)
                    if not b:
                        break
                    n += len(b)
                    if n > MAX_BYTES:
                        raise IOError("larger than %d bytes" % MAX_BYTES)
                    f.write(b)
            return
        except (urllib.error.URLError, IOError, TimeoutError) as e:
            if os.path.exists(dest):
                os.unlink(dest)
            code = getattr(e, "code", None)
            if code in (404, 403, 410) or attempt == 2:
                raise
            time.sleep(10 * (attempt + 1))


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


_PROD = re.compile(rb"/Producer\s*(\((?:\\.|[^\\()])*\)|<[0-9A-Fa-f\s]*>)")
_CREA = re.compile(rb"/Creator\s*(\((?:\\.|[^\\()])*\)|<[0-9A-Fa-f\s]*>)")
_XMP = re.compile(rb"<pdf:Producer>([^<]*)</pdf:Producer>")


def _decode(tok):
    if tok.startswith(b"<"):
        hx = re.sub(rb"\s", b"", tok[1:-1])
        if len(hx) % 2:
            hx += b"0"
        raw = bytes.fromhex(hx.decode())
    else:
        raw = re.sub(rb"\\(.)", lambda m: m.group(1), tok[1:-1])
    if raw.startswith(b"\xfe\xff"):
        return raw[2:].decode("utf-16-be", "replace")
    return raw.decode("latin-1")


def _find(data, rx):
    m = None
    for m in rx.finditer(data):  # last occurrence = newest Info dict
        pass
    return _decode(m.group(1)) if m else None


def _info_dict(data):
    """Bytes of the document Info dict (trailer /Info N 0 R, last definition), or None."""
    refs = re.findall(rb"/Info\s+(\d+)\s+(\d+)\s+R", data)
    if not refs:
        return None
    n, g = refs[-1]
    best = None
    for m in re.finditer(rb"(?<![0-9])" + n + rb"\s+" + g + rb"\s+obj\b", data):
        best = m.end()
    if best is None:
        return None
    end = data.find(b"endobj", best)
    return data[best:end if end >= 0 else best + 4096]


def pdf_meta(path):
    """Return (producer, creator, embedded_producers) read from raw bytes.
    Producer/Creator come from the trailer's Info dict when it is a plain object
    (embedded figures carry their own /Producer, reported separately).  If the Info
    dict lives in an object stream, fall back to the first match in inflated streams."""
    with open(path, "rb") as f:
        data = f.read()
    info = _info_dict(data)
    prod = crea = None
    if info is not None:
        prod, crea = _find(info, _PROD), _find(info, _CREA)
    allp = {_decode(m.group(1)) for m in _PROD.finditer(data)}
    if prod is None:
        chunks = []
        for i, m in enumerate(re.finditer(rb"stream\r?\n", data)):
            if i >= 3000:
                break
            try:
                chunks.append(zlib.decompressobj().decompress(data[m.end():m.end() + (1 << 20)], 1 << 20))
            except zlib.error:
                pass
        blob = b"\n".join(chunks)
        m = _PROD.search(blob)
        prod = _decode(m.group(1)) if m else None
        m = _CREA.search(blob)
        crea = crea or (_decode(m.group(1)) if m else None)
        if prod is None:
            x = _XMP.findall(data) or _XMP.findall(blob)
            prod = x[0].decode("utf-8", "replace") if x else None
    emb = sorted({engine_of(p, None) for p in allp if p != prod} - {engine_of(prod, crea)})
    return prod, crea, emb


def engine_of(producer, creator):
    # Producer wins; Creator only when Producer names nothing recognisable.
    r = _engine_of(producer)
    return r if r not in ("other", "unknown") else _engine_of(creator) if creator else r


def _engine_of(s):
    s = (s or "").lower()
    if not s:
        return "unknown"
    for key, name in (("luatex", "LuaTeX"), ("xetex", "XeTeX"), ("xdvipdfmx", "XeTeX"),
                      ("pdftex", "pdfTeX"), ("dvipdfm", "dvipdfm"), ("dvips", "dvips+ghostscript"),
                      ("microsoft", "Word"), ("word", "Word"), ("libreoffice", "LibreOffice"),
                      ("openoffice", "LibreOffice"), ("matplotlib", "matplotlib"),
                      ("ghostscript", "Ghostscript"), ("acrobat", "Acrobat"), ("quartz", "Quartz"),
                      ("skia", "Chrome/Skia"), ("cairo", "cairo"), ("latex", "LaTeX-other")):
        if key in s:
            return name
    return "other"


def arxiv_year(aid):
    m = re.match(r"(?:[a-z\-]+(?:\.[A-Z]{2})?/)?(\d\d)(\d\d)", aid)
    if not m:
        return None
    yy = int(m.group(1))
    return (1900 + yy) if yy >= 91 and yy <= 99 else 2000 + yy


def load():
    with open(MANIFEST) as f:
        return json.load(f)


def save(m):
    m["entries"].sort(key=lambda e: e["id"])
    tmp = MANIFEST + ".tmp"
    with open(tmp, "w") as f:
        json.dump(m, f, indent=1, ensure_ascii=False)
        f.write("\n")
    os.replace(tmp, MANIFEST)


def safe_name(eid):
    return re.sub(r"[^A-Za-z0-9._-]", "_", eid) + ".pdf"


def fetch_one(url, final):
    """Download to temp, return (path_tmp). Caller verifies."""
    os.makedirs(FILES, exist_ok=True)
    tmp = final + ".part"
    download(url, tmp)
    return tmp


def do_fetch():
    m = load()
    ok = bad = new = 0
    problems = []
    for e in m["entries"]:
        final = os.path.join(FILES, safe_name(e["id"]))
        if not os.path.exists(final):
            print("fetch  %s" % e["url"], flush=True)
            try:
                tmp = fetch_one(e["url"], final)
            except Exception as ex:
                problems.append((e["id"], "download failed: %s" % ex))
                continue
            new += 1
        else:
            tmp = None
        path = tmp or final
        size, digest = os.path.getsize(path), sha256_of(path)
        if size != e["size"] or digest != e["sha256"]:
            os.unlink(path)
            problems.append((e["id"], "MISMATCH size %d/%d sha %s.. (deleted)" % (size, e["size"], digest[:12])))
            bad += 1
            continue
        if tmp:
            os.replace(tmp, final)
        ok += 1
    total = sum(e["size"] for e in m["entries"])
    print("entries: %d  verified: %d  newly downloaded: %d  mismatched: %d  failed/missing: %d  total %.1f MB"
          % (len(m["entries"]), ok, new, bad, len(problems) - bad, total / 1e6))
    for i, p in problems:
        print("PROBLEM %s: %s" % (i, p))
    return 1 if problems else 0


def parse_cats(items):
    d = {}
    for it in items:
        k, _, v = it.partition("=")
        if not _:
            sys.exit("--category expects key=value, got %r" % it)
        d[k] = int(v) if k == "year" and v.isdigit() else v
    return d


def do_add(urls, cats, source, lic):
    m = load()
    have = {e["url"] for e in m["entries"]}
    for url in urls:
        if url in have:
            print("skip (already in manifest): " + url)
            continue
        u = urlparse(url)
        if u.hostname == "arxiv.org" and u.path.startswith("/pdf/"):
            aid = re.sub(r"v\d+$", "", u.path[len("/pdf/"):].removesuffix(".pdf"))
            eid, src = "arxiv-" + aid.replace("/", "_"), "arxiv"
            lic_ = "arXiv submission; copyright remains with authors; fetched by URL, never redistributed"
            year = arxiv_year(aid)
        else:
            eid = (u.hostname or "x") + "-" + os.path.basename(u.path).removesuffix(".pdf")
            src, lic_, year = u.hostname or "web", "unverified", None
        if any(e["id"] == eid for e in m["entries"]):
            print("skip (id exists): " + eid)
            continue
        final = os.path.join(FILES, safe_name(eid))
        print("fetch  " + url, flush=True)
        try:
            tmp = fetch_one(url, final)
        except Exception as ex:
            print("FAILED %s: %s" % (url, ex))
            continue
        with open(tmp, "rb") as f:
            head = f.read(1024)
        if b"%PDF-" not in head:
            os.unlink(tmp)
            print("FAILED %s: not a PDF" % url)
            continue
        prod, crea, emb = pdf_meta(tmp)
        cat = {"engine": engine_of(prod, crea), "year": year, "producer": prod or "unknown", "embedded": emb}
        cat.update(cats)
        entry = {"id": eid, "url": url, "sha256": sha256_of(tmp), "size": os.path.getsize(tmp),
                 "source": source or src, "category": cat, "license": lic or lic_}
        if crea:
            entry["creator"] = crea
        os.replace(tmp, final)
        m["entries"].append(entry)
        save(m)
        print("  added %s  %s  %s" % (eid, cat["engine"], cat["producer"]))
    return 0


def do_summary():
    m = load()
    es = m["entries"]
    for key in ("engine", "year"):
        c = Counter(str(e["category"].get(key)) for e in es)
        print(key + ": " + ", ".join("%s=%d" % kv for kv in sorted(c.items())))
    c = Counter(e["category"].get("producer", "?") for e in es)
    print("producers:")
    for k, v in c.most_common():
        print("  %3d  %s" % (v, k))
    print("total: %d entries, %.1f MB" % (len(es), sum(e["size"] for e in es) / 1e6))
    return 0


def do_reindex():
    m = load()
    for e in m["entries"]:
        path = os.path.join(FILES, safe_name(e["id"]))
        if not os.path.exists(path):
            continue
        prod, crea, emb = pdf_meta(path)
        c = e["category"]
        c["engine"], c["producer"], c["embedded"] = engine_of(prod, crea), prod or "unknown", emb
        if crea:
            e["creator"] = crea
    save(m)
    return do_summary()


def main(argv):
    if "--reindex" in argv:
        return do_reindex()
    if "--summary" in argv:
        return do_summary()
    if "--add" in argv:
        urls, cats, source, lic, i = [], [], None, None, 0
        mode = None
        while i < len(argv):
            a = argv[i]
            if a == "--add":
                mode = "add"
            elif a == "--category":
                i += 1; cats.append(argv[i]); mode = "add"
            elif a == "--source":
                i += 1; source = argv[i]
            elif a == "--license":
                i += 1; lic = argv[i]
            elif mode == "add":
                urls.append(a)
            else:
                sys.exit("unknown argument " + a)
            i += 1
        if not urls:
            sys.exit("--add needs at least one URL")
        return do_add(urls, parse_cats(cats), source, lic)
    if argv:
        sys.exit(__doc__)
    return do_fetch()


if __name__ == "__main__":
    if not os.path.exists(MANIFEST):
        os.makedirs(os.path.dirname(MANIFEST), exist_ok=True)
        save({"version": 1, "entries": []})
    sys.exit(main(sys.argv[1:]))
