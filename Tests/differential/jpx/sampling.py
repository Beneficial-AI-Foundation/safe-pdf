"""M10 §9 page references for the reviewed fractional clips and odd SIZ origin.

Every entry requires the original MuPDF paint and its direct 72 dpi crop.
See sampling.md for sample sources, PDF geometry and independent controls.
"""
import base64
import hashlib
import json
import math
import subprocess
from typing import NamedTuple
import xml.etree.ElementTree as ET
import zlib


class Case(NamedTuple):
    source: str
    obj: int
    owner: int
    mask: int | None
    native: tuple
    rect: tuple
    matrix: tuple
    clip: tuple | None  # top-left device coordinates
    direct_sha: str
    samples_sha: str
    reference_sha: str
    control_sha: str | None = None
    mask_probe: tuple | None = None


PDFBOX = (91, 80, 422, 188)
COLOR_MATRIX = (330.48, 0, 0, 106.32001, 91.02539, 80.68933)
COLOR_CLIP = (91.025, 80.689, 421.505, 187.01)
CASES = {
    "JPXTestCMYK": Case(
        "b37f0229370f5ac04ebfd98b3c678d33f4fa3c87ee914a5a5f1c54bf7ca7994d", 12, 12, 16,
        (1377, 443, "CMYK"), PDFBOX, COLOR_MATRIX, COLOR_CLIP,
        "98fba049ab81b6e61a961d8636dbcb781a50d21f77f8005b9fd9d39e23b5ade1",
        "aa2e1ef0d090113cb14ea4194e81a977833c8e4cf7e585155d55d0017fa0f49f",
        "a32516a64839cc132c86d4e10bdf456195abe928922e22639cb1e5f15373c4bb", mask_probe=(418, 159)),
    "JPXTestGrey": Case(
        "b1a1791f6292b792344700ee30dd7987084bf9338c28afccede3454df0fd9080", 84, 84, None,
        (690, 223, "Gray"), PDFBOX, (330.96, 0, 0, 106.80002, 90.78539, 80.44931),
        (91.025, 80.690, 421.505, 187.01),
        "5c31c8906c05743813ace7c003def5b18f1a28d235667ad3c1e15ade0508a894",
        "36daf4eb8785d8715981a344e47ee72c8ecf431e799d1825ce2b9d0fb993d48f",
        "41d99512dcd1d75a322ed9995dd0a72f35de42974150c1989ecb11fbabbece97",
        "fd0651fc59560417c63efafe558f131ca80142db62782ed5210738bb0d0d97ff"),
    "JPXTestRGB": Case(
        "bb605c1ce58f85ac1cce9cd2b2293bebb066d6c8e0de1488b63b13116a4fd4db", 12, 12, 16,
        (1377, 443, "RGB"), PDFBOX, COLOR_MATRIX, COLOR_CLIP,
        "a92015ca2316a5f971eb8fbdb89e2c585344fe473d65a230a0ee92772b73bf0c",
        "5edc9957c59662f2a9c9097bbbe5c86063099a3c7a07615735f6431da3fd1c70",
        "26ff9f7a9973f105b7fbbef88168080aae1b7ca37db36e26959495e1172d05e0", mask_probe=(420, 159)),
    "S2": Case(
        "57d874f2760ded2b70eb58b7b5e31df407d5641b7225576b77458b5dc5009543", 35, 24, 35,
        (18, 166, "Gray"), (307, 606, 312, 653), (4.554245, 0, 0, -46.08011, 307.12599, 652.70608),
        (307.126, 606.626, 311.680, 652.706),
        "81159e0e63126ea90094299ea6985c8de9ae08744ebbb5985f5bf81f26d6c749",
        "514b2c004ece5e24e857be1c05815dc0d517043cc77f56f30ea9978c74b1c3b2",
        "9fadfadddd03cd8ff9c55414171ff1d7cc2e300a8e442e34c9a8840107c4157e"),
    "jpx_subsampling": Case(
        "01f92ae453f8f6d2e8c61574054c1ca3160e3481a3f9c8cc365aa1ff7cd3e1f3", 11, 11, None,
        (32, 32, "RGB"), (110, 10, 210, 110), (100, 0, 0, 100, 110, 10), None,
        "73f613a084a7d5d64ff3b62cab4266ea27f6ddf4776577d26bec8bd3d72b2aa7",
        "d4869a6d99cc6373383821244c089bbb52210cbae77605af8712f6a7da5d590b",
        "9b5d73e18c09cee65213cb65d2617d758fb6ece6f745d7f33dcb6a1b25acdcb8"),
}


def require(ok, message):
    if not ok:
        raise ValueError("sampling reference: " + message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def select(pdf, digest, page, denominator, reference, rows, obj):
    case = CASES.get(pdf.stem)
    if case is None:
        require(obj is None, "unexpected sampling row")
        return None
    require((digest, page, denominator, reference, obj) == (case.source, 1, 1, "mupdf", case.obj),
            "wrong source, view, primary renderer or sampling row")
    matches = [r for r in rows if r["object"] == obj]
    require(len(matches) == 1, "missing or ambiguous occurrence")
    r, = matches
    require(tuple(r["region"]) == case.rect and r["owner"] == case.owner
            and r["role"] == ("soft mask" if case.owner != obj else "image")
            and r["mask"] == (f"{case.mask} 0 R" if case.mask else None)
            and (r["dictionary"]["Width"], r["dictionary"]["Height"]) == case.native[:2],
            "wrong placement, role, mask or native dimensions")
    return case


def trace_site(path, case):
    root = ET.parse(path)
    w, h, space = case.native
    for parent in root.iter():
        nodes = list(parent)
        for i, node in enumerate(nodes):
            if node.tag != "fill_image":
                continue
            matrix = tuple(map(float, node.get("transform", "").split()))
            if matrix != case.matrix or (node.get("width"), node.get("height")) != (str(w), str(h)):
                continue
            paint = dict(matrix=matrix, size=[w, h], colorspace=node.get("colorspace"))
            if case.mask:
                require(i >= 1 and nodes[i-1].tag == "clip_image_mask" and
                        all(nodes[i-1].get(k) == node.get(k) for k in ("transform", "width", "height")),
                        "missing corresponding mask paint")
                paint["mask_object"] = case.mask
                i -= 1
            if case.clip:
                require(i >= 1 and nodes[i-1].tag == "clip_path", "missing fractional clip")
                clip = nodes[i-1]
                m = tuple(map(float, clip.get("transform", "").split()))
                require(len(m) == 6 and m[:5] == (1, 0, 0, -1, 0) and
                        [p.tag for p in clip] == ["moveto", "lineto", "lineto", "lineto", "closepath"],
                        "expected rectangular clip")
                vertices = [(float(p.get("x")), m[5] - float(p.get("y"))) for p in list(clip)[:4]]
                l, t, r, b = case.clip
                require(all(abs(x-X) < .0001 and abs(y-Y) < .0001 for (x,y),(X,Y) in
                            zip(vertices, [(l,b), (r,b), (r,t), (l,t)])), "clip vertices changed")
                paint["clip"] = case.clip
            color = "Indexed(71,DeviceRGB)" if case.obj != case.owner else "Device" + space
            require(node.get("alpha") == "1" and node.get("colorspace") == color,
                    "reviewed paint colour space or opacity changed")
            return paint
    raise ValueError("sampling reference: reviewed source paint missing")


# At 576 dpi the largest reviewed source page is 4763 × 6736 × 3 bytes.
# Bound both the native-sheet/control subprocesses and the oversampled source.
PROCESS = dict(address_space_mib=768, cpu_seconds=45, output_mib=100, timeout_seconds=60)


def run(*args):
    import resource

    def limits():
        for key, value in [(resource.RLIMIT_AS, PROCESS["address_space_mib"] << 20),
                           (resource.RLIMIT_CPU, PROCESS["cpu_seconds"]),
                           (resource.RLIMIT_FSIZE, PROCESS["output_mib"] << 20)]:
            _, hard = resource.getrlimit(key)
            resource.setrlimit(key, (value if hard < 0 else min(hard, value), hard))

    result = subprocess.run(args, capture_output=True, timeout=PROCESS["timeout_seconds"], preexec_fn=limits)
    log = result.stderr.decode(errors="replace").splitlines()
    require(result.returncode == 0 and all(line in
            {"warning: ICC support is not available", "warning: invalid marked content and clip nesting"}
            for line in log), f"{args[0]} exit {result.returncode}: {log[:3]}")
    return result.stdout


def stream(attrs, data):
    return {"stream": {"dict": attrs, "data": base64.b64encode(data).decode("ascii")}}


def write_json(path, objects):
    path.write_text(json.dumps({"qpdf": [{"jsonversion": 2, "pdfversion": "1.7"}, objects]}))


def image_stream(pdf, num):
    key = f"obj:{num} 0 R"
    obj = json.loads(run("qpdf", "--json=2", "--json-key=qpdf", f"--json-object={num}",
                         "--json-stream-data=inline", "--decode-level=none", pdf))["qpdf"][1][key]["stream"]
    return obj["dict"], base64.b64decode(obj["data"], validate=True)


def native_sheet(tmp, attrs, encoded, native):
    """Paint the unmasked image at 1:1 into its original device colour space."""
    w, h, space = native
    require((attrs.get("/Width"), attrs.get("/Height"), attrs.get("/ColorSpace"),
             attrs.get("/BitsPerComponent"), attrs.get("/Filter")) ==
            (w, h, "/Device" + space, 8, "/JPXDecode"), "unexpected source image")
    attrs = attrs.copy()
    attrs.pop("/SMask", None)
    recipe, pdf, pam = (tmp / ("native." + ext) for ext in ("json", "pdf", "pam"))
    write_json(recipe, {
        "trailer": {"value": {"/Root": "1 0 R", "/Size": 6}},
        "obj:1 0 R": {"value": {"/Type": "/Catalog", "/Pages": "2 0 R"}},
        "obj:2 0 R": {"value": {"/Type": "/Pages", "/Count": 1, "/Kids": ["3 0 R"]}},
        "obj:3 0 R": {"value": {"/Type": "/Page", "/Parent": "2 0 R", "/MediaBox": [0, 0, w, h],
                                "/Resources": {"/XObject": {"/I": "5 0 R"}}, "/Contents": "4 0 R"}},
        "obj:4 0 R": stream({}, f"q {w} 0 0 {h} 0 0 cm /I Do Q".encode()),
        "obj:5 0 R": stream(attrs, encoded),
    })
    run("qpdf", "--json-input", recipe, pdf)
    run("mutool", "draw", "-q", "-r", "72", "-c", space.lower(), "-F", "pam", "-o", pam, pdf, "1")
    header, raw = pam.read_bytes().split(b"ENDHDR\n", 1)
    nc = {"RGB": 3, "CMYK": 4, "Gray": 1}[space]
    require(header.splitlines()[:5] == [b"P7", f"WIDTH {w}".encode(), f"HEIGHT {h}".encode(),
            f"DEPTH {nc}".encode(), b"MAXVAL 255"] and len(raw) == w*h*nc, "native PAM format")
    return raw


def ramp(origin):
    """Explicit DeviceRGB planes, with the first stored 2:1 sample extended to the edge."""
    def chroma(i):
        return max(i - origin, 0) // 2
    return bytes(v for y in range(32) for x in range(32) for v in
                 (x*255//31, 17*chroma(y), 255*((chroma(x)//4 + chroma(y)//4) % 2)))


def flate_control(pdf, tmp, case):
    attrs, encoded = image_stream(pdf, case.obj)
    if case.clip is None:
        even, data = image_stream(pdf, 10)
        # The entire even/odd payload is identical except six low bytes in SIZ:
        # X/Ysiz, XO/YOsiz and XT/YTsiz. Sampling is 1x1, 2x2, 2x2.
        require(len(encoded) == len(data) == 1075 and encoded[40:51] == bytes.fromhex("0003070101070202070202")
                and [(i, a, b) for i, (a, b) in enumerate(zip(data, encoded)) if a != b] ==
                [(11,32,33), (15,32,33), (19,0,1), (23,0,1), (27,32,33), (31,32,33)],
                "even/odd image grid changed")
        require(native_sheet(tmp, even, data, case.native) == ramp(0), "even-origin native samples")
        raw = ramp(1)
    else:
        raw = native_sheet(tmp, attrs, encoded, case.native)
    require(sha(raw) == case.samples_sha, "native component values changed")
    patch, result = tmp / "replacement.json", tmp / "target-flate.pdf"
    write_json(patch, {f"obj:{case.obj} 0 R": stream({**attrs, "/Filter": "/FlateDecode"}, zlib.compress(raw))})
    run("qpdf", f"--update-from-json={patch}", "--object-streams=disable", pdf, result)
    return result


def integrate(pnm, rect, factor, view):
    """Average all subpixels of each 72 dpi pixel, with integer rounding, same grid origin."""
    with pnm.open("rb") as f:
        require(f.readline() == b"P6\n", "expected RGB PNM")
        w, h = map(int, f.readline().split())
        require((w, h) == view and f.readline() == b"255\n", "wrong sampled view")
        start = f.tell()
        require(pnm.stat().st_size == start + 3*w*h, "incomplete reference raster")
        l, t, r, b = rect
        require(0 <= l < r <= w/factor and 0 <= t < b <= h/factor, "crop outside view")
        rgb = bytearray()
        for y in range(t, b):
            band = []
            for j in range(factor):
                f.seek(start + 3*((factor*y+j)*w + factor*l))
                band.append(f.read(3*factor*(r-l)))
            for x in range(r-l):
                for k in range(3):
                    i = 3*factor*x + k
                    total = sum(sum(row[i:i+3*factor:3]) for row in band)
                    rgb.append((total + factor*factor//2)//(factor*factor))
        return bytes(rgb)


def render_crop(pdf, tmp, case, factor):
    target = tmp / "sampling.ppm"
    page = (595.28, 841.89) if case.rect == PDFBOX else (540, 720) if case.clip else (220, 220)
    run("mutool", "draw", "-q", "-b", "CropBox", "-r", str(72*factor), "-c", "rgb", "-F", "pnm",
        "-o", target, pdf, "1")
    return integrate(target, case.rect, factor, tuple(math.ceil(x*factor) for x in page))


def reference(pdf, tmp, case, direct_rgb):
    """Produce the independent RGB crop and a separately rendered equivalent control."""
    require(sha(direct_rgb) == case.direct_sha, "direct 72 dpi source raster changed")
    paint = trace_site(tmp / "trace.xml", case)
    control = flate_control(pdf, tmp, case)
    factor = 8 if case.clip else 1
    control_rgb = render_crop(control, tmp, case, factor)
    rgb = render_crop(pdf, tmp, case, factor) if case.clip else control_rgb
    require(sha(rgb) == case.reference_sha, "reviewed reference crop changed")
    require(sha(control_rgb) == (case.control_sha or case.reference_sha), "reviewed Flate control crop changed")
    evidence = dict(kind="fractional clip area" if case.clip else "odd-origin DeviceRGB Flate",
                    source_sha256=case.source, trace=paint, native_samples_sha256=case.samples_sha,
                    direct_rgb_sha256=case.direct_sha, reference_crop_sha256=case.reference_sha,
                    control_rgb_sha256=sha(control_rgb), samples_per_axis=factor, process=PROCESS)
    if case.mask_probe:
        w, h, _ = case.native
        mask = run("qpdf", f"--show-object={case.mask}", "--filtered-stream-data", pdf)
        require(len(mask) == w*h and sha(mask) == "ccce0898f32697255a64d6d1e24e305f221999db034fe577d687c951e958240b",
                "external mask samples changed")
        x, y = case.mask_probe
        a, _, _, d, e, f = case.matrix
        xs = range(math.floor((x-e)*w/a), math.ceil((x+1-e)*w/a))
        ys = range(math.floor((y-f)*h/d), math.ceil((y+1-f)*h/d))
        require(all(mask[j*w+i] == 0 for j in ys for i in xs), "expected transparent sample footprint")
        evidence["mask_probe"] = dict(device=[x,y], native=[xs.start,ys.start,xs.stop,ys.stop],
                                      alpha=0, paper_rgb=[255,255,255])
    return rgb, control_rgb, evidence
