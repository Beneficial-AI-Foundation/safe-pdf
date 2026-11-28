"""The bug_jpx p1 /Im0 page oracle, using only its recorded DeviceGray plane."""
import base64
import hashlib
import json
import subprocess


SOURCE_PATH = "pdf-sources/pdf.js/bug_jpx.pdf"
SOURCE_SHA = "4010d808557a72278368c05518367735ed186cbdd04974b8506275f9ac40f999"
STREAM_SHA = "90629e28a6820f2e6106562e85dcfdea5eef59e79476c68bfea163c70b85008a"
PLANE_SHA = "9f1dcbc35c350d6027f98be0f5c8b43b42ca52b7604459c0c42be3aa88913d47"
PAGE_RGB_SHA = {
    "reference": "10a5de99375ce1f421e6eca13f4e24efa3233998002202ec8a0aaaee6a562939",
    "control": "f073fa22c0b4ce4eb194ffdd67276e4ebf96bb4cd32b0a1bba8c9144e799650f",
}
PAGE_BOX = [0, 0, 612, 792]
REGION = (269, 200, 398, 265)
CONTENT = b"q\n128 0 0 64 269.6739197 527.7081909 cm\n/Im0 Do\nQ\n"
IMAGE_DICT = {"/Type": "/XObject", "/Subtype": "/Image", "/Name": "/X",
              "/Width": 128, "/Height": 64, "/ColorSpace": "/DeviceGray",
              "/BitsPerComponent": 8}
PLANE = bytes(128 * 64)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(f"bug_jpx recorded plane: {message}")


def qpdf(*args):
    proc = subprocess.run(["qpdf", *args], capture_output=True, timeout=30)
    require(proc.returncode == 0, proc.stderr.decode(errors="replace")[:500])
    return proc.stdout


def objects(path, ids=()):
    # Inline encoded bytes. qpdf resolves the xref and parses names and dictionaries.
    options = [f"--json-object={n}" for n in ids]
    return json.loads(qpdf("--json=2", "--json-key=qpdf", "--decode-level=none",
                           "--json-stream-data=inline", *options, path))["qpdf"][1]


def graph(ids, samples):
    """All page-affecting dictionaries, operators and streams in this one-page PDF."""
    catalog, tree, page, content, image = [f"{n} 0 R" for n in ids]

    def stream(attrs, data):
        return {"stream": {"dict": attrs, "data": base64.b64encode(data).decode("ascii")}}

    return {
        "obj:" + catalog: {"value": {"/Type": "/Catalog", "/Pages": tree}},
        "obj:" + tree: {"value": {"/Type": "/Pages", "/Count": 1, "/Kids": [page]}},
        "obj:" + page: {"value": {"/Type": "/Page", "/Parent": tree, "/Contents": content,
                                  "/MediaBox": PAGE_BOX, "/CropBox": PAGE_BOX, "/Rotate": 0,
                                  "/Resources": {"/ProcSet": ["/PDF", "/ImageB"],
                                                 "/XObject": {"/Im0": image}}}},
        "obj:" + content: stream({}, CONTENT),
        "obj:" + image: stream(IMAGE_DICT, samples),
    }


def source_contract(pdf, manifest):
    sources = [s for s in manifest["files"] if s["path"] == SOURCE_PATH]
    entries = [e for e in manifest["pdf_jpx"] if e["source_pdf"] == SOURCE_PATH]
    require(len(sources) == len(entries) == 1, "missing or ambiguous manifest entry")
    entry = entries[0]
    require(sha(pdf.read_bytes()) == sources[0]["sha256"] == SOURCE_SHA
            and pdf.stat().st_size == sources[0]["size"] == 5451, "source PDF size/hash")
    require(entry["object"] == [15, 0] and entry["filters"] == ["/JPXDecode"]
            and entry["sha256"] == STREAM_SHA and entry["size"] == 202,
            "image object/filter/size/hash")
    plane = entry.get("recorded_plane", {})
    expected = dict(width=128, height=64, depth=8, signed=False, constant=0,
                    source="Recorded OpenJPEG 2.5.3 decode with the two empty tile-parts omitted. "
                           "Compare the original identified by this entry's sha256 to this single plane.")
    require(plane == expected,
            "missing or changed recorded_plane contract")
    facts = entry["codestream"]
    require((facts["width"], facts["height"], facts["components"], facts["bit_depths"],
             facts["signed"], facts["subsampling"]) == (128, 64, 1, [8], [False], ["1x1"])
            and entry["pdf_image"] == {k: IMAGE_DICT["/" + k] for k in
                                       ("Width", "Height", "ColorSpace", "BitsPerComponent")}
            and sha(PLANE) == PLANE_SHA, "sample format or plane digest")

    ids = (12, 9, 13, 14, 15)
    source = objects(pdf, (*ids, "trailer"))
    require(source.pop("trailer")["value"]["/Root"] == "12 0 R", "source catalog")
    image = source["obj:15 0 R"]["stream"]
    payload = base64.b64decode(image["data"], validate=True)
    require(len(payload) == 202 and sha(payload) == STREAM_SHA, "encoded object 15 digest")
    # Remove only the audited non-paint catalog links and replace the single image encoding.
    root = source["obj:12 0 R"]["value"]
    require(root.pop("/Metadata") == "2 0 R" and root.pop("/Outlines") == "6 0 R"
            and image["dict"].pop("/Filter") == "/JPXDecode", "source catalog or image encoding")
    image["data"] = base64.b64encode(PLANE).decode("ascii")
    require(source == graph(ids, PLANE), "page tree, paint, mask or image changed")
    return plane, payload


def verified_pdf(path, samples, payload):
    """Serialize only the five audited objects; reparse the resulting file before use."""
    expected = graph(range(1, 6), samples)
    trailer = {"/Root": "1 0 R", "/Size": 6}
    document = {"qpdf": [{"jsonversion": 2, "pdfversion": "1.6"},
                         {**expected, "trailer": {"value": trailer}}]}
    recipe = path.with_suffix(".json")
    recipe.write_text(json.dumps(document))
    qpdf("--json-input", "--stream-data=preserve", "--object-streams=disable",
         "--static-id", recipe, path)
    return verify_pdf(path, samples, payload)


def verify_pdf(path, samples, payload):
    parsed = objects(path)
    actual_trailer = parsed.pop("trailer")["value"]
    static_id = "b:31415926535897932384626433832795"  # qpdf --static-id
    require(actual_trailer == {"/Root": "1 0 R", "/Size": 6, "/ID": [static_id, static_id]}
            and parsed == graph(range(1, 6), samples),
            "serialized PDF differs from the five audited JPX-free objects")
    raw = path.read_bytes()
    require(payload not in raw, "encoded source payload in serialized PDF")
    return sha(raw)


def reference(pdf, manifest, tmp, region, render):
    """Return (reference Image, log, provenance); render(path) returns (Image, log)."""
    require(tuple(region) == REGION, "audited placement changed")
    try:
        plane, payload = source_contract(pdf, manifest)
    except (KeyError, TypeError, IndexError) as exc:
        raise ValueError(f"incomplete bug_jpx contract: {exc}") from exc
    provenance = dict(kind="recorded-plane-jpx-free", source_sha256=SOURCE_SHA,
                      stream_sha256=STREAM_SHA, plane_sha256=PLANE_SHA, recorded_plane=plane,
                      source_object=[15, 0], reference_object=[5, 0], page=1,
                      content_sha256=sha(CONTENT), region=list(REGION))
    logs = []
    for label, sample in (("control", 192), ("reference", 0)):
        samples = bytes([sample]) * len(PLANE)
        path = tmp / f"bug-jpx-{label}.pdf"
        pdf_sha = verified_pdf(path, samples, payload)
        image, log = render(path)
        require((image.w, image.h) == (612, 792), "reference page dimensions")
        digest = sha(image.rgb)
        require(digest == PAGE_RGB_SHA[label], f"{label} RGB digest {digest}")
        provenance[label] = dict(pdf_sha256=pdf_sha, rgb_sha256=digest, gray_sample=sample)
        logs.append(log)
    return image, "\n".join(dict.fromkeys(logs)), provenance


def worker_result(ours, ref, result):
    """Keep the normal crop score, with exact geometry and samples for this flat page."""
    exact = (ours.w, ours.h, ours.rgb) == (ref.w, ref.h, ref.rgb)
    status = result["status"]
    if status == "within" and not exact:
        status = "recorded-plane page mismatch"
    return dict(result, status=status, exact_recorded_page=exact)
