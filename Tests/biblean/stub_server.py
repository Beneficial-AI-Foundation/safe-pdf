"""A stub of bib-lean's server for the reader contract (tasks 10.1, 10.2, 10.3; Plan.md §6 Phase 10).

    python3 -I Tests/biblean/stub_server.py --token-file F --pdf P --att KEY --parent KEY \
        --title T --att-title T --port-file F --log F [--chunked] \
        [--fulltext-out F] [--detected-out F] [--fail-text 500|close|hang] \
        [--annots-in F] [--annots-out F] [--put-out F] [--fail-annots 500|close|hang]

Implements the routes `viewer --biblean` calls (bib-lean docs/READER-CONTRACT.md §3):

* GET /api/attachments/{att}/file  -> 200 the PDF bytes (Content-Length, Cache-Control: no-store)
* GET /api/items/{att}             -> 200 {"version", "item": {attachment, parentItem}, "children"}
* GET /api/items/{parent}          -> 200 {"version", "item": {regular item, fields.title}, ...}
  (`--parent ""`: the attachment has no parent, `parentItem` is null)
* POST /api/attachments/{att}/fulltext -> 200 {"bytes": n}; the body (UTF-8 text, at most
  32 MiB, else 413) is written to --fulltext-out
* POST /api/attachments/{att}/detected -> 202 {"pending": true, "identifiers": {...}} when the
  JSON body is an object with a string "doi" or "arxiv" (one JSON line appended to
  --detected-out), 422 {"error": "rejected"} otherwise, 400 for a body that is not JSON
* POST /api/attachments/{att}/annotations -> the whole neutral set (contract §4): validated as
  bib-lean does (a JSON array; each element an object with a known `kind`, an integer
  `pageIndex` >= 0, `rects` of four numbers each, a string `sortIndex`, optional string/null
  `id` (unique), `text`, `comment`, `color` `#rrggbb`), 400 otherwise; the set replaces the
  stored one, 200 {"version": n, "keys": [...]} with an element whose `id` was stored before
  keeping its key; {"body", "keys", "before" (id -> key before)} is appended to --annots-out
  as one JSON line
* PUT /api/attachments/{att}/file -> the re-saved PDF (at most 64 MiB, else 413; must start
  with `%PDF-`, else 400), written to --put-out (an earlier one moves to --put-out.N),
  200 {"version", "file", "previous"}
* --annots-in F: the initial stored set, a JSON array of neutral elements; GET
  /api/items/{att} lists the stored set as children in bib-lean's stored form
  ({"itemType": "annotation", "annotation": {kind, pageIndex, position, text, comment, color,
  sortIndex}}, `position` the compact JSON {"extra","id","kind","rects"} with sorted keys,
  `strikeout` stored as `underline`, a missing colour as #ffd400)
* --fail-annots 500|close|hang does to the annotation POST and the file PUT what --fail-text
  does to the text routes
* --fail-text 500 answers both POST routes with 500; --fail-text close drops the connection
  without an answer, --fail-text hang answers only after 40 s (the viewer must keep working,
  and exit promptly, either way)

Every /api request must carry `Authorization: Bearer <token>` (the token is read from
--token-file, never from argv); without it, or with a wrong one, the answer is 401
`{"error": "unauthorized", ...}` as in bib-lean. Unknown keys get 404. Listens on 127.0.0.1 with
a port chosen by the OS, written to --port-file once listening. --chunked sends the items
answers with `Transfer-Encoding: chunked` (exercises the client's chunked decoding).
Each request is appended to --log as one JSON line: method, path, auth ("ok", "missing",
"wrong"), whether an Origin header came, the Content-Type, the status. The token itself is never logged.
Standard library only.
"""

import argparse
import hmac
import json
import os
import sys
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--token-file", required=True)
    ap.add_argument("--pdf", required=True)
    ap.add_argument("--att", required=True)
    ap.add_argument("--parent", required=True)
    ap.add_argument("--title", required=True)
    ap.add_argument("--att-title", default="Full Text PDF")
    ap.add_argument("--port-file", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--chunked", action="store_true")
    ap.add_argument("--fulltext-out")
    ap.add_argument("--detected-out")
    ap.add_argument("--fail-text", choices=["500", "close", "hang"])
    ap.add_argument("--annots-in")
    ap.add_argument("--annots-out")
    ap.add_argument("--put-out")
    ap.add_argument("--fail-annots", choices=["500", "close", "hang"])
    a = ap.parse_args()

    # The stored set: (key, neutral element) pairs, as bib-lean keeps them.
    store = {"version": 3, "set": [], "next": 0, "puts": 0}

    def fresh_key():
        store["next"] += 1
        alphabet = "23456789ABCDEFGHIJKLMNPQRSTUVWXYZ"
        n, out = store["next"] + 33 ** 7, ""
        for _ in range(8):
            out = alphabet[n % 33] + out
            n //= 33
        return out

    def assign(elements):
        by_id = {e.get("id"): k for k, e in store["set"] if e.get("id") is not None}
        out = []
        for e in elements:
            k = by_id.get(e.get("id")) if e.get("id") is not None else None
            out.append((k or fresh_key(), e))
        store["set"] = out
        store["version"] += 1
        return [k for k, _ in out]

    def stored_child(key, e):
        kind = e["kind"]
        position = json.dumps({"extra": e.get("extra"), "id": e.get("id"), "kind": kind,
                               "rects": e["rects"]}, sort_keys=True, separators=(",", ":"))
        return {"key": key, "itemType": "annotation",
                "annotation": {"kind": "underline" if kind == "strikeout" else kind,
                               "pageIndex": e["pageIndex"], "position": position,
                               "text": e.get("text"), "comment": e.get("comment"),
                               "color": e.get("color") or "#ffd400",
                               "sortIndex": e["sortIndex"]}}

    kinds = {"highlight", "underline", "strikeout", "note", "text", "ink", "image"}

    def number(x):
        return isinstance(x, (int, float)) and not isinstance(x, bool)

    def valid(body):
        if not isinstance(body, list):
            return False
        ids = set()
        for e in body:
            if not isinstance(e, dict) or e.get("kind") not in kinds:
                return False
            p = e.get("pageIndex")
            if not isinstance(p, int) or isinstance(p, bool) or p < 0:
                return False
            rs = e.get("rects")
            if not isinstance(rs, list) or not all(
                    isinstance(r, list) and len(r) == 4 and all(number(x) for x in r) for r in rs):
                return False
            if not isinstance(e.get("sortIndex"), str):
                return False
            for k in ("id", "text", "comment"):
                if e.get(k) is not None and not isinstance(e[k], str):
                    return False
            c = e.get("color")
            if c is not None and not (isinstance(c, str) and len(c) == 7 and c[0] == "#"
                                      and all(ch in "0123456789abcdefABCDEF" for ch in c[1:])):
                return False
            if e.get("id") is not None:
                if e["id"] in ids:
                    return False
                ids.add(e["id"])
        return True

    if a.annots_in:
        with open(a.annots_in, "r", encoding="utf-8") as f:
            initial = json.load(f)
        if not valid(initial):
            raise SystemExit("--annots-in is not a valid neutral set")
        assign(initial)
        store["version"] = 3

    with open(a.token_file, "r", encoding="ascii") as f:
        token = f.read().strip()
    with open(a.pdf, "rb") as f:
        pdf = f.read()

    def common(key):
        return {"key": key, "tags": [], "relations": [], "citationKey": None,
                "citationKeyPinned": False, "replaces": [], "deleted": False,
                "dateAdded": "2026-11-20T00:00:00Z", "dateModified": "2026-11-20T00:00:00Z",
                "version": 3}

    att_item = dict(common(a.att), itemType="attachment", linkMode="imported_file",
                    contentType="application/pdf", file="paper.pdf", title=a.att_title,
                    pageCount=None, parentItem=a.parent or None)
    parent_item = dict(common(a.parent), itemType="journalArticle",
                       fields={"title": a.title, "date": "2026"},
                       creators=[{"creatorType": "author", "lastName": "Doe", "firstName": "J."}],
                       parentItem=None)
    items = {a.att: att_item}
    if a.parent:
        items[a.parent] = parent_item

    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, fmt, *args):  # no stderr noise
            pass

        def record(self, auth, status):
            with open(a.log, "a", encoding="utf-8") as f:
                f.write(json.dumps({"method": self.command, "path": self.path, "auth": auth,
                                    "origin": self.headers.get("Origin") is not None,
                                    "ctype": self.headers.get("Content-Type"),
                                    "status": status}) + "\n")

        def send(self, status, body, ctype, chunked=False):
            self.send_response(status)
            self.send_header("Content-Type", ctype)
            self.send_header("Cache-Control", "no-store")
            if chunked:
                self.send_header("Transfer-Encoding", "chunked")
                self.end_headers()
                for i in range(0, len(body), 7):
                    part = body[i:i + 7]
                    self.wfile.write(b"%x\r\n" % len(part) + part + b"\r\n")
                self.wfile.write(b"0\r\nX-Trailer: 1\r\n\r\n")
            else:
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

        def error(self, status, code, auth):
            self.record(auth, status)
            self.send(status, json.dumps({"error": code, "message": code}).encode(),
                      "application/json")

        def do_GET(self):
            h = self.headers.get("Authorization")
            if h is None:
                return self.error(401, "unauthorized", "missing")
            if not hmac.compare_digest(h.encode(), ("Bearer " + token).encode()):
                return self.error(401, "unauthorized", "wrong")
            parts = self.path.split("/")
            if len(parts) == 5 and parts[1:3] == ["api", "attachments"] and parts[4] == "file":
                if parts[3] != a.att:
                    return self.error(404, "not_found", "ok")
                self.record("ok", 200)
                return self.send(200, pdf, "application/pdf")
            if len(parts) == 4 and parts[1:3] == ["api", "items"] and parts[3] in items:
                children = ([stored_child(k, e) for k, e in store["set"]]
                            if parts[3] == a.att else [])
                body = json.dumps({"version": store["version"], "item": items[parts[3]],
                                   "children": children, "collections": []}).encode()
                self.record("ok", 200)
                return self.send(200, body, "application/json", chunked=a.chunked)
            return self.error(404, "not_found", "ok")

        def do_POST(self):
            h = self.headers.get("Authorization")
            if h is None:
                return self.error(401, "unauthorized", "missing")
            if not hmac.compare_digest(h.encode(), ("Bearer " + token).encode()):
                return self.error(401, "unauthorized", "wrong")
            parts = self.path.split("/")
            if (len(parts) == 5 and parts[1:3] == ["api", "attachments"]
                    and parts[4] == "annotations"):
                return self.annotations(parts[3])
            if not (len(parts) == 5 and parts[1:3] == ["api", "attachments"]
                    and parts[4] in ("fulltext", "detected")):
                return self.error(405, "method_not_allowed", "ok")
            n = int(self.headers.get("Content-Length", "0"))
            if n > 32 * 1024 * 1024:
                return self.error(413, "too_large", "ok")
            body = self.rfile.read(n)
            if a.fail_text == "close":
                self.record("ok", 0)
                self.close_connection = True
                self.connection.shutdown(2)
                return
            if a.fail_text == "hang":
                time.sleep(40)
            if a.fail_text == "500":
                return self.error(500, "ioError", "ok")
            if parts[3] != a.att:
                return self.error(404, "not_found", "ok")
            if parts[4] == "fulltext":
                try:
                    body.decode("utf-8")
                except UnicodeDecodeError:
                    return self.error(400, "badRequest", "ok")
                if a.fulltext_out:
                    with open(a.fulltext_out, "wb") as f:
                        f.write(body)
                self.record("ok", 200)
                return self.send(200, json.dumps({"bytes": len(body)}).encode(), "application/json")
            try:
                ids = json.loads(body.decode("utf-8"))
            except (UnicodeDecodeError, ValueError):
                return self.error(400, "badRequest", "ok")
            if not isinstance(ids, dict):
                return self.error(400, "badRequest", "ok")
            found = {k: ids[k] for k in ("doi", "arxiv", "isbn") if isinstance(ids.get(k), str)}
            if not found:
                return self.error(422, "rejected", "ok")
            if a.detected_out:
                with open(a.detected_out, "a", encoding="utf-8") as f:
                    f.write(json.dumps(ids) + "\n")
            self.record("ok", 202)
            return self.send(202, json.dumps({"pending": True, "identifiers": found}).encode(),
                             "application/json")

        def failing(self):
            """Applies --fail-annots; True when the request was answered (or dropped)."""
            if a.fail_annots == "close":
                self.record("ok", 0)
                self.close_connection = True
                self.connection.shutdown(2)
                return True
            if a.fail_annots == "hang":
                time.sleep(40)
            if a.fail_annots == "500":
                self.error(500, "ioError", "ok")
                return True
            return False

        def annotations(self, key):
            n = int(self.headers.get("Content-Length", "0"))
            body = self.rfile.read(n)
            if self.failing():
                return None
            if key != a.att:
                return self.error(404, "not_found", "ok")
            try:
                elements = json.loads(body.decode("utf-8"))
            except (UnicodeDecodeError, ValueError):
                return self.error(400, "badRequest", "ok")
            if not valid(elements):
                return self.error(400, "badRequest", "ok")
            before = {e["id"]: k for k, e in store["set"] if e.get("id") is not None}
            keys = assign(elements)
            if a.annots_out:
                with open(a.annots_out, "a", encoding="utf-8") as f:
                    f.write(json.dumps({"body": elements, "keys": keys, "before": before}) + "\n")
            self.record("ok", 200)
            return self.send(200, json.dumps({"version": store["version"], "keys": keys}).encode(),
                             "application/json")

        def do_PUT(self):
            h = self.headers.get("Authorization")
            if h is None:
                return self.error(401, "unauthorized", "missing")
            if not hmac.compare_digest(h.encode(), ("Bearer " + token).encode()):
                return self.error(401, "unauthorized", "wrong")
            parts = self.path.split("/")
            if not (len(parts) == 5 and parts[1:3] == ["api", "attachments"] and parts[4] == "file"):
                return self.error(405, "method_not_allowed", "ok")
            n = int(self.headers.get("Content-Length", "0"))
            if n > 64 * 1024 * 1024:
                return self.error(413, "too_large", "ok")
            body = self.rfile.read(n)
            if self.failing():
                return None
            if parts[3] != a.att:
                return self.error(404, "not_found", "ok")
            if not body.startswith(b"%PDF-"):
                return self.error(400, "badRequest", "ok")
            store["puts"] += 1
            if a.put_out:
                if os.path.exists(a.put_out):
                    os.replace(a.put_out, f"{a.put_out}.{store['puts'] - 1}")
                with open(a.put_out, "wb") as f:
                    f.write(body)
            store["version"] += 1
            self.record("ok", 200)
            return self.send(200, json.dumps({"version": store["version"], "file": "paper.pdf",
                                              "previous": "paper.pdf.1"}).encode(),
                             "application/json")

    srv = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    tmp = a.port_file + ".tmp"
    with open(tmp, "w", encoding="ascii") as f:
        f.write(str(srv.server_address[1]))
    os.replace(tmp, a.port_file)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
