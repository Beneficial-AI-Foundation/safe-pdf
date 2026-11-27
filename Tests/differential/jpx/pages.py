#!/usr/bin/env python3
"""M10.2c: compare source-PDF placements in the confined worker. See docs/jpx-pages.md."""
import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


pixels = load_module("pixels", HERE.parent / "pixels.py")
recorded = load_module("bug_jpx_recorded_plane", HERE / "bug_jpx_recorded_plane.py")
sampling = load_module("sampling", HERE / "sampling.py")


def check(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(args, cwd=REPO, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True, timeout=210)
    log = (result.stdout + result.stderr).strip()
    check(result.returncode == 0, f"{Path(args[0]).name} exit {result.returncode}: {log[:1500]}")
    return result.stdout.strip(), log


def box(region, w, h):
    rect = (0, 0, w, h) if region == "page" else tuple(region)
    x0, y0, x1, y1 = rect
    check(0 <= x0 < x1 <= w and 0 <= y0 < y1 <= h, f"invalid placement {rect} in {w}x{h}")
    return rect


def crop(image, rect):
    x0, y0, x1, y1 = rect
    return pixels.Image(x1 - x0, y1 - y0, b"".join(
        image.row(y)[3*x0:3*x1] for y in range(y0, y1)))


def colors(rgb):
    """Exact palette size below the cap (including the pikepdf controls)."""
    seen = set()
    for i in range(0, len(rgb), 3):
        seen.add(rgb[i:i+3])
        if len(seen) == 4096:
            return ">=4096"
    return len(seen)


def compare_region(ours, ref, rect):
    a, b = crop(ours, rect), crop(ref, rect)
    result = pixels.compare_images(a, b)
    ac, bc = colors(a.rgb), colors(b.rgb)
    flat = (b"\x80" * 3, b"\xff" * 3)
    if bc == 1 and b.rgb[:3] in flat:
        status = "reference indistinguishable from blank/placeholder"
    elif ac == 1 and a.rgb[:3] in flat:
        status = "blank/placeholder in placement"
    elif result["pct"] > pixels.TAU:
        status = "placement mismatch"
    else:
        status = "within"
    return dict(status=status, differing=result["diff"], percent=result["pct"],
                identical=result["identical"], worker_colors=ac, reference_colors=bc,
                worker_flat_rgb=list(a.rgb[:3]) if ac == 1 else None,
                reference_flat_rgb=list(b.rgb[:3]) if bc == 1 else None)


def compare_reviewed_crop(ours, ref, rect, expected_digest, paints, native_size):
    """Require the approved raster and, for the PDF.js grid, its live paint at this site."""
    digest = sha(crop(ref, rect).rgb)
    evidence = dict(reference_crop_sha256=digest)
    if digest != expected_digest:
        return dict(evidence, status="reference gap", detail="reference crop differs from reviewed RGB")
    if paints is not None and paints.count(dict(rect=list(rect), size=native_size)) != 1:
        return dict(evidence, status="reference gap", detail="expected one image paint at this placement")
    evidence.update(compare_region(ours, ref, rect))
    if evidence["worker_colors"] == 1 and evidence["reference_colors"] != 1 and evidence["status"] == "within":
        evidence["status"] = "flat worker in nonuniform placement"
    return evidence


def outside_changed(ours, ref, rects):
    """Exact RGB diagnostic for everything outside the union of the measured rectangles."""
    other = bytearray(ref.rgb)
    for x0, y0, x1, y1 in rects:
        for y in range(y0, y1):
            a, b = 3 * (ours.w*y+x0), 3 * (ours.w*y+x1)
            other[a:b] = ours.rgb[a:b]
    return other != ours.rgb


def sampling_result(pdf, tmp, case, ours, ref, direct):
    """Keep the direct measurement even if a required placement control fails."""
    rect = case.rect
    result = dict(direct_mupdf=direct)
    try:
        rgb, control, evidence = sampling.reference(pdf, tmp, case, crop(ref, rect).rgb)
        w, h = rect[2] - rect[0], rect[3] - rect[1]
        local = (0, 0, w, h)
        target = pixels.Image(w, h, rgb)
        result.update(sampling_evidence=evidence)
        equiv = compare_region(pixels.Image(w, h, control), target, local)
        result["flate_control_vs_reference"] = equiv
        check(equiv["status"] == "within", "equivalent Flate control disagrees with reference")
        result.update(compare_region(crop(ours, rect), target, local))
        if case.mask_probe:
            x, y = case.mask_probe
            observed = ours.row(y)[3*x:3*x+3]
            i = 3*((y-rect[1])*w + x-rect[0])
            check(rgb[i:i+3] == b"\xff"*3, "reference painted a fully transparent footprint")
            result["masked_worker_rgb"] = list(observed)
            if min(observed) < 255 - pixels.TOL:
                result["status"] = "external mask sample mismatch"
        if case.clip:
            x, y, r, b = rect
            interior = compare_region(ours, ref, (x+1, y+1, r-1, b-1))
            result["direct_interior"] = interior
            if interior["status"] != "within":
                result["status"] = "placement interior mismatch"
        if rect == sampling.PDFBOX:
            white = pixels.Image(ours.w, ours.h, b"\xff" * (3*ours.w*ours.h))
            check(not outside_changed(ref, white, [rect]), "paint outside reviewed reference clip")
            result["worker_outside_clip_white"] = not outside_changed(ours, white, [rect])
            if not result["worker_outside_clip_white"]:
                result["status"] = "paint outside placement"
    except (OSError, ValueError, KeyError, ET.ParseError, subprocess.TimeoutExpired) as exc:
        result.update(status="sampling reference gap", detail=str(exc))
    return result


def catalog(manifest, plans):
    sources = {f["path"]: f for f in manifest["files"] if "pdf-source" in f["roles"]}
    expected = defaultdict(dict)
    for stream in manifest["pdf_jpx"]:
        for occurrence in [stream, *stream.get("also_in", [])]:
            objects = expected[occurrence["source_pdf"]]
            num, gen = occurrence["object"]
            check(gen == 0 and num not in objects, f"unaudited object {num} {gen}")
            objects[num] = stream
    check(set(expected) == set(sources), "source files disagree with expanded JPX manifest")
    check(len(sources) == len(plans) and {Path(p).stem for p in sources} == plans.keys(),
          "update placement audit for this decoder corpus")
    return sources, expected


def object_ref(number):
    return f"{number} 0 R"


def inventory(pdf, source, expected, plan, upstream):
    check(pdf.stat().st_size == source["size"] and sha(pdf.read_bytes()) == source["sha256"],
          f"source size/SHA-256 mismatch: {pdf}")
    output, _ = run(["qpdf", "--json=2", "--json-key=qpdf", "--json-key=pages", pdf])
    doc = json.loads(output)
    objs = doc["qpdf"][1]
    images = {}
    for num, gen, d, filters in upstream.jpx_streams(objs):
        check(num in expected and gen == 0, f"unexpected JPX object {num} {gen}")
        entry = expected[num]
        data = upstream.extract_one(str(pdf), num, gen, filters, upstream.resolve(objs, d.get("/DecodeParms")))
        check(len(data) == entry["size"] and sha(data) == entry["sha256"], f"JPX hash mismatch at {num}")
        facts = upstream.image_facts(objs, d)
        if entry["source_pdf"] == source["path"] and entry["object"] == [num, gen]:
            check(filters == entry["filters"] and facts == entry["pdf_image"],
                  f"filter chain or dictionary disagrees with manifest at {num}")
        images[num] = dict(filters=filters, dictionary=facts, stream_sha256=entry["sha256"])
    check(images.keys() == expected.keys(), "source JPX objects disagree with manifest")
    check(len(doc["pages"]) == len(plan["pages"]), "source page count disagrees with placement audit")
    rows = []
    for page, (recipe, info) in enumerate(zip(plan["pages"], doc["pages"]), 1):
        page_dict = objs["obj:" + info["object"]]["value"]
        direct = {i["object"] for i in info["images"]}
        for owner, rect in recipe:
            ref = object_ref(owner)
            path = plan.get("annotation_path")
            if path:
                annot, form, nested, image = map(object_ref, path)
                annots = page_dict["/Annots"]
                if isinstance(annots, str):
                    annots = objs["obj:" + annots]["value"]
                check(annot in annots and objs["obj:" + annot]["value"]["/AP"]["/N"] == form
                      and image == ref, "stamp appearance changed")
                for parent, child in [(form, nested), (nested, image)]:
                    form_dict = objs["obj:" + parent]["stream"]["dict"]
                    check(child in form_dict["/Resources"]["/XObject"].values(), "stamp form changed")
            else:
                check(ref in direct, f"{ref} absent from page {page} resources")
            image_dict = objs["obj:" + ref]["stream"]["dict"]
            mask = image_dict.get("/SMask")
            components = []
            if owner in images:
                components.append((owner, "annotation appearance" if path else "image"))
            if mask:
                num = int(mask.split()[0])
                if num in images:
                    components.append((num, "soft mask"))
            check(components, f"no JPX in placement of {owner}")
            for num, role in components:
                rows.append(dict(page=page, object=num, role=role, owner=owner, mask=mask,
                                 region=rect, **images[num]))
                if path:
                    rows[-1]["annotation_path"] = path
        for n, num in plan.get("thumbnails", []):
            if n == page:
                check(page_dict.get("/Thumb") == object_ref(num), f"unverified thumbnail {num}")
                rows.append(dict(page=page, object=num, role="thumbnail", status="unpainted /Thumb",
                                 **images[num]))
    check({r["object"] for r in rows} == images.keys(), "placement audit leaves unaccounted objects")
    return rows


def worker_page(pdf, page, denominator, worker, tmp, pages, build_root):
    rgba = tmp / "worker.rgba"
    out, _ = run(["lake", "env", "lean", "--run", REPO / "scripts/corpus/JpxWorkerPage.lean",
                  worker, pdf, str(page), str(denominator), rgba], cwd=build_root)
    count, w, h = map(int, out.split())
    check(count == pages, f"worker page count {count}, reference count {pages}")
    data = rgba.read_bytes()
    check(w > 0 and h > 0 and len(data) == w*h*4, "invalid worker RGBA")
    check(data[3::4] == b"\xff" * (w*h), "worker page has nonopaque pixels")
    rgb = bytearray(3*w*h)
    for c in range(3):
        rgb[c::3] = data[c::4]
    return pixels.Image(w, h, rgb)


def audit_trace(trace, rows, image, expected_fills):
    """Match the reviewed Do sites to the actual display transforms in device pixels."""
    nodes = defaultdict(list)
    for node in ET.parse(trace).iter():
        if node.tag not in ("fill_image", "clip_image_mask"):
            continue
        a, b, c, d, e, f = map(float, node.attrib["transform"].split())
        xs, ys = (e, e+a, e+c, e+a+c), (f, f+b, f+d, f+b+d)
        rect = (max(0, math.floor(min(xs))), max(0, math.floor(min(ys))),
                min(image.w, math.ceil(max(xs))), min(image.h, math.ceil(max(ys))))
        nodes[node.tag].append((int(node.attrib["width"]), int(node.attrib["height"]), rect))
    check(len(nodes["fill_image"]) == expected_fills, "reference image paint count changed")
    for row in rows:
        rect = box(row["region"], image.w, image.h)
        size = row["dictionary"]["Width"], row["dictionary"]["Height"]
        for tag in (["fill_image", "clip_image_mask"] if row["mask"] else ["fill_image"]):
            # The audit uses visible (clipped) bounds. A fractional clip can move the
            # outer edge by one pixel relative to the un-clipped image transform.
            matches = [r for w, h, r in nodes[tag] if (w, h) == size
                       and all(abs(x-y) <= 1 for x, y in zip(r, rect))]
            check(len(matches) == 1, f"obj {row['object']} expected one {tag} at {rect}, got {matches}")


def map_reference(pdf, args, tmp, page_report):
    import resource
    target = tmp / "map.ppm"
    budget = args.map_reference_mib * 1024**2

    def limit():
        for key, cap in [(resource.RLIMIT_AS, budget), (resource.RLIMIT_CPU, 45),
                         (resource.RLIMIT_FSIZE, 8 * 1024**2)]:
            _, hard = resource.getrlimit(key)
            cap = cap if hard == resource.RLIM_INFINITY else min(cap, hard)
            resource.setrlimit(key, (cap, cap))

    evidence = dict(address_space_mib=args.map_reference_mib, cpu_seconds=45,
                    timeout_seconds=60, output_limit_mib=8)
    page_report["reference_process"] = evidence
    started = time.monotonic()
    try:
        result = subprocess.run([sys.executable, "-I", HERE / "pdfium-map.py", pdf, target],
                                capture_output=True, text=True, timeout=60, preexec_fn=limit)
    except subprocess.TimeoutExpired:
        evidence["timed_out"] = True
        raise
    finally:
        evidence["elapsed_seconds"] = round(time.monotonic() - started, 3)
    evidence.update(returncode=result.returncode, stdout=result.stdout.strip(), stderr=result.stderr.strip())
    check(result.returncode == 0 and not result.stderr and len(result.stdout.splitlines()) == 1
          and result.stdout.startswith("pypdfium2 "),
          f"PDFium map exit {result.returncode}: {result.stderr.strip()}")
    return pixels.read_image(target), result.stdout.strip()


def reference_page(pdf, page, denominator, reference, args, tmp, rows, expected_fills, page_report):
    if reference == "pdfium":
        return map_reference(pdf, args, tmp, page_report)
    if reference == "pdfjs":
        check(args.pdfjs_dir, "supply --pdfjs-dir for this PDF.js reference")
        image = tmp / "reference.png"
        audit = tmp / "grid.json"
        _, log = run(["node", HERE / "pdfjs-page.mjs", args.pdfjs_dir.resolve(), pdf,
                      str(page), str(denominator), image, str(expected_fills), audit],
                     env={**os.environ, "NODE_USE_ENV_PROXY": "0"})
        check(len(log.splitlines()) == 1 and log.startswith("PDF.js "),
              f"PDF.js reference diagnostic: {log[:1500]}")
        page_report["reference_paints"] = json.loads(audit.read_text())
    else:
        image = tmp / "reference.ppm"
        cmd = ["mutool", "draw", "-q", "-b", "CropBox", "-r", str(72 / denominator), "-c", "rgb"]
        trace = tmp / "trace.xml"
        logs = []
        # Some builds report decoder errors and still write a partial/white page.
        allowed = {"warning: ICC support is not available", "warning: invalid marked content and clip nesting"}
        for fmt, target in [("pnm", image), ("trace", trace)]:
            _, log = run(cmd + ["-F", fmt, "-o", target, pdf, str(page)])
            check(all(s in allowed for s in log.splitlines()), f"MuPDF reference diagnostic: {log}")
            logs.extend(log.splitlines())
        ref = pixels.read_image(image)
        audit_trace(trace, rows, ref, expected_fills)
        return ref, "\n".join(dict.fromkeys(logs))
    return pixels.read_image(image), log


def subsampled_tint_result(pdf, page, denominator, plan, rows, args, tmp, ours, ref, rect, direct):
    """Verify the two-tint DeviceN ramp, preserving the original MuPDF placement score."""
    result = dict(direct_mupdf=direct)
    try:
        recipe = plan["pdfjs_tint"]
        check(recipe["object"] == 13 and page == denominator == 1 and rect == (110, 110, 210, 210),
              "unexpected subsampled DeviceN placement")
        evidence = {}
        other, log = reference_page(pdf, page, denominator, "pdfjs", args, tmp, rows, 4, evidence)
        check((other.w, other.h) == (ref.w, ref.h) == (220, 220), "subsampling reference view changed")
        paints = evidence["reference_paints"]
        check(len(paints) == 4, "expected four subsampling image paints")
        target = crop(other, rect)
        for y in range(32):
            row = target.row((2*y + 1)*100//64)
            for x in range(32):
                i = 3*((2*x + 1)*100//64)
                check(row[i:i+3] == bytes((x*255//31, y*255//31, 0)), "DeviceN tint sample changed")
        result.update(pdfjs_log=log, pdfjs_paints=paints, tint_sample_centres=1024)
        result.update(compare_reviewed_crop(ours, other, rect, recipe["crop"], paints, [32, 32]))
    except (OSError, ValueError, KeyError, pixels.Bad, subprocess.TimeoutExpired) as exc:
        result.update(status="reference gap", detail=str(exc))
    return result


def measure_page(pdf, source, manifest, page, plan, rows, args, page_report):
    denominator = plan.get("scale_denominator", 1)
    page_report.update(dpi=72 / denominator, reference=plan.get("reference", "mupdf"))
    if plan.get("gap"):
        page_report["stage"] = "reference"
        raise ValueError(plan["gap"])
    with tempfile.TemporaryDirectory(prefix="safe-pdf-jpx-") as work:
        tmp = Path(work)
        page_report["stage"] = "worker"
        ours = worker_page(pdf, page, denominator, args.worker.resolve(), tmp, len(plan["pages"]), args.build_root)
        page_report.update(worker_size=[ours.w, ours.h], worker_rgb_sha256=sha(ours.rgb))
        page_report["stage"] = "reference"
        fills = len(plan["pages"][page-1]) + plan.get("other_fills", 0)
        recorded_page = source["sha256"] == recorded.SOURCE_SHA
        if recorded_page:
            check(page == denominator == fills == len(rows) == 1 and
                  rows[0]["owner"] == rows[0]["object"] == 15 and rows[0]["role"] == "image" and
                  page_report["reference"] == "recorded-plane-jpx-free", "recorded page contract changed")
            ref, log, page_report["reference_provenance"] = recorded.reference(
                pdf, manifest, tmp, rows[0]["region"],
                lambda vetted: reference_page(vetted, page, denominator, "mupdf", args, tmp, rows, fills, page_report))
        else:
            check(page_report["reference"] in ("pdfium", "pdfjs", "mupdf"), "unknown page reference")
            ref, log = reference_page(pdf, page, denominator, page_report["reference"], args, tmp, rows, fills, page_report)
        page_report.update(reference_log=log, reference_size=[ref.w, ref.h], reference_rgb_sha256=sha(ref.rgb))
        page_report["stage"] = "view"
        check((ref.w, ref.h) == (ours.w, ours.h), f"view dimensions differ: {ref.w}x{ref.h} vs {ours.w}x{ours.h}")
        if "view_size" in plan:
            check([ref.w, ref.h] == plan["view_size"], "reference dimensions disagree with audited view")
        measured = {}
        sampling_case = sampling.CASES.get(pdf.stem)
        if sampling_case is None:
            check("sampling_object" not in plan, "unexpected sampling recipe")
        else:
            check(any(row["object"] == sampling_case.obj for row in rows), "missing reviewed sampling occurrence")
        for row in rows:
            rect = box(row["region"], ours.w, ours.h)
            if "reference_crops" in plan:
                native_size = [row["dictionary"][k] for k in ("Width", "Height")]
                measured[rect] = compare_reviewed_crop(
                    ours, ref, rect, plan["reference_crops"][str(row["owner"])],
                    page_report.get("reference_paints"), native_size)
            elif rect not in measured:
                measured[rect] = compare_region(ours, ref, rect)
            if recorded_page:
                measured[rect] = recorded.worker_result(ours, ref, measured[rect])
            if sampling_case and row["object"] == sampling_case.obj:
                direct = measured[rect]
                try:
                    sampling.select(pdf, source["sha256"], page, denominator, page_report["reference"],
                                    rows, plan.get("sampling_object"))
                    measured[rect] = sampling_result(pdf, tmp, sampling_case, ours, ref, direct)
                except ValueError as exc:
                    measured[rect] = dict(status="sampling reference gap", detail=str(exc), direct_mupdf=direct)
            if pdf.stem == "jpx_subsampling" and row["object"] == 13:
                measured[rect] = subsampled_tint_result(
                    pdf, page, denominator, plan, rows, args, tmp, ours, ref, rect, measured[rect])
            row.update(rect=rect, **measured[rect])
        page_report["outside_rgb_changed"] = outside_changed(ours, ref, measured)
        del page_report["stage"]


def selftest():
    w = h = 100
    rect = (11, 22, 17, 28)
    base = bytearray(b"\xff" * (3*w*h))
    wrong = bytearray(base)
    for y in range(rect[1], rect[3]):
        for x in range(rect[0], rect[2]):
            off = 3 * (w*y+x)
            base[off:off+3] = bytes((220, 12*x, 5*y))
            wrong[off:off+3] = b"\x80" * 3
    ref = pixels.Image(w, h, base)
    holder = pixels.Image(w, h, wrong)
    check(pixels.compare_images(holder, ref)["pct"] <= pixels.TAU, "control should pass whole-page metric")
    check(compare_region(holder, ref, rect)["status"] == "blank/placeholder in placement", "missed placeholder")
    base[0:3] = b"\x00" * 3
    other = pixels.Image(w, h, base)
    check(compare_region(other, ref, rect)["status"] == "within" and outside_changed(other, ref, [rect]),
          "misclassified unrelated change")
    native_size = [6, 6]
    digest = sha(crop(ref, rect).rgb)
    paints = [dict(rect=list(rect), size=native_size)]
    check(compare_reviewed_crop(other, ref, rect, digest, paints, native_size)["status"] == "within",
          "complete site rejected")
    check(compare_reviewed_crop(other, ref, rect, digest, [], native_size)["status"] == "reference gap",
          "accepted missing paint")
    check(compare_reviewed_crop(other, holder, rect, digest, paints, native_size)["status"] == "reference gap",
          "accepted placeholder reference")
    print("PASS: placeholder rejected, matching placement accepted, missing paint and incomplete reference rejected.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-root", type=Path, default=REPO, help="existing safe-pdf Lean build at the same decoder pin")
    parser.add_argument("--cache", type=Path)
    parser.add_argument("--worker", type=Path)
    parser.add_argument("--pdfjs-dir", type=Path, help="installed pdfjs-dist directory for jpx_numcomps")
    parser.add_argument("--map-reference-mib", type=int, default=1024,
                        help="address space for PDFium on the 212 MP map (default 1024 MiB)")
    parser.add_argument("--only", action="append", help="exact PDF stem; repeatable focused comparison")
    parser.add_argument("--json", type=Path, help="write full page and occurrence evidence")
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        selftest()
        return 0
    check(args.map_reference_mib > 0, "--map-reference-mib must be positive")
    check((args.build_root / "lake-manifest.json").read_bytes() == (REPO / "lake-manifest.json").read_bytes(),
          "Lean build uses a different package manifest")
    package = args.build_root / ".lake/packages/jpeg2000"
    args.cache = args.cache or package / "corpus/files"
    args.worker = args.worker or args.build_root / ".lake/build/bin/worker"
    plans = json.loads((HERE / "placements.json").read_text())
    manifest = json.loads((package / "corpus/manifest.json").read_text())
    sources, expected = catalog(manifest, plans)
    selected = set(args.only or plans)
    check(selected <= plans.keys(), f"unknown --only: {selected - plans.keys()}")
    upstream = load_module("pdf_extract", package / "scripts/extract-pdf-jpx.py")
    _, version = run(["mutool", "-v"])
    report = dict(scope="focused" if args.only else "full", mupdf=version,
                  map_reference_mib=args.map_reference_mib,
                  worker_sha256=sha(args.worker.read_bytes()),
                  corpus_manifest_sha256=sha((package / "corpus/manifest.json").read_bytes()),
                  channel_tolerance=pixels.TOL, max_percent=pixels.TAU, documents=[])
    counts = Counter()
    for path, source in sources.items():
        name = Path(path).stem
        if name not in selected:
            continue
        plan = plans[name]
        pdf = (args.cache / path).resolve()
        doc = dict(source=path, sha256=source["sha256"], pages=[])
        report["documents"].append(doc)
        try:
            rows = inventory(pdf, source, expected[path], plan, upstream)
        except (OSError, ValueError, KeyError, RuntimeError, subprocess.TimeoutExpired) as e:
            rows = [dict(object=n, status="inventory gap", detail=str(e)) for n in expected[path]]
        doc["occurrences"] = rows
        for page in range(1, len(plan["pages"])+1):
            active = [r for r in rows if r.get("page") == page and r["role"] != "thumbnail"]
            if not active:
                continue
            evidence = dict(page=page)
            doc["pages"].append(evidence)
            try:
                measure_page(pdf, source, manifest, page, plan, active, args, evidence)
                if evidence["outside_rgb_changed"]:
                    print(f"{name} p{page}: additional RGB differences outside the measured placements")
            except (OSError, ValueError, pixels.Bad, ET.ParseError, subprocess.TimeoutExpired) as e:
                evidence["gap"] = str(e)
                print(f"{name} p{page}: {e}", flush=True)
                for row in active:
                    row.update(status=evidence["stage"] + " gap")
        for row in rows:
            counts[row["status"]] += 1
            primary = f"direct MuPDF {row['direct_mupdf']['percent']:.3f}%" if "direct_mupdf" in row else ""
            print(f"{name} p{row.get('page', '?')} obj {row['object']} {row.get('role','')}: {row['status']}",
                  f"{row['percent']:.3f}% ({row['worker_colors']} vs {row['reference_colors']} colors)"
                  if "percent" in row else row.get("detail", ""), primary, flush=True)
    paths = [p for p in sources if Path(p).stem in selected]
    report["coverage"] = dict(pdfs=len(paths), pages=sum(len(plans[n]["pages"]) for n in selected),
                              objects=sum(len(expected[p]) for p in paths),
                              streams=len({s["sha256"] for p in paths for s in expected[p].values()}))
    report["counts"] = dict(counts)
    if args.json:
        args.json.write_text(json.dumps(report, indent=2) + "\n")
    print(report["scope"], version, report["coverage"], dict(counts))
    return int(not counts["within"] or any(k not in ("within", "unpainted /Thumb") for k in counts))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.TimeoutExpired) as exc:
        sys.exit(f"JPX corpus gate unavailable: {exc}")
