"""A stub of bib-lean's server for the reader contract (tasks 10.1, 10.3; Plan.md §6 Phase 10).

    python3 -I Tests/biblean/stub_server.py --token-file F --pdf P --att KEY --parent KEY \
        --title T --att-title T --port-file F --log F [--chunked] \
        [--fulltext-out F] [--detected-out F] [--fail-text 500|close|hang]

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
    a = ap.parse_args()

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
                body = json.dumps({"version": 3, "item": items[parts[3]], "children": [],
                                   "collections": []}).encode()
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

        def do_PUT(self):
            self.error(405, "method_not_allowed", "n/a")

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
