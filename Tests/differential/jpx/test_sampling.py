"""M10 §9 placement-control tests. Set JPX_CACHE to exercise the five actual PDFs."""
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("pages", HERE / "pages.py")
pages = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pages)
sampling = pages.sampling


class SamplingTests(unittest.TestCase):
    def test_grid_average_keeps_origin_and_fractional_coverage(self):
        # The right half of a pixel is black, with white neighbours on either side.
        with tempfile.TemporaryDirectory() as work:
            pnm = Path(work) / "sample.ppm"
            row = b"\xff"*9 + b"\0"*3 + b"\xff"*6
            pnm.write_bytes(b"P6\n6 2\n255\n" + row*2)
            self.assertEqual(sampling.integrate(pnm, (1, 0, 2, 1), 2, (6, 2)), b"\x80"*3)
            with self.assertRaisesRegex(ValueError, "sampled view"):
                sampling.integrate(pnm, (1, 0, 2, 1), 2, (8, 2))
            pnm.write_bytes(pnm.read_bytes()[:-1])
            with self.assertRaisesRegex(ValueError, "incomplete"):
                sampling.integrate(pnm, (1, 0, 2, 1), 2, (6, 2))

    def test_missing_site_altered_digest_or_missing_trace(self):
        case = sampling.CASES["S2"]
        path = Path("S2.pdf")
        row = dict(object=35, owner=24, mask="35 0 R", role="soft mask", region=case.rect,
                   dictionary={"Width": 18, "Height": 166})
        for obj, rows, digest in ((None, [row], case.source), (35, [], case.source),
                                  (35, [{**row, "owner": 35}], case.source), (35, [row], "wrong")):
            with self.subTest(obj=obj, rows=rows, digest=digest), self.assertRaises(ValueError):
                sampling.select(path, digest, 1, 1, "mupdf", rows, obj)
        with tempfile.TemporaryDirectory() as work:
            tmp = Path(work)
            with self.assertRaisesRegex(ValueError, "direct 72 dpi"):
                sampling.reference(path, tmp, case, b"wrong")
            trace = tmp / "trace.xml"
            trace.write_text("<document/>")
            with self.assertRaisesRegex(ValueError, "source paint missing"):
                sampling.trace_site(trace, case)
            matrix = " ".join(map(str, case.matrix))
            trace.write_text(f'<page><fill_image transform="{matrix}" width="18" height="166"/></page>')
            with self.assertRaisesRegex(ValueError, "mask paint"):
                sampling.trace_site(trace, case)

    def test_reviewed_reference_and_control_fail_closed(self):
        case = sampling.CASES["JPXTestGrey"]
        w, h = 596, 842
        page = bytearray(b"\xff" * (w*h*3))
        l, t, r, b = case.rect
        for y in range(t, b):
            i = 3*(w*y+l)
            page[i:i+3*(r-l)] = b"\x20\x40\x80"*(r-l)
        image = pages.pixels.Image(w, h, page)
        rgb = pages.crop(image, case.rect).rgb

        def measure(worker, control=rgb):
            with patch.object(sampling, "reference", return_value=(rgb, control, {})):
                return pages.sampling_result(None, None, case, pages.pixels.Image(w, h, worker),
                                             image, {"status": "retained direct score"})
        self.assertEqual(measure(page)["status"], "within")
        outside = bytearray(page)
        outside[0:3] = b"\x00"*3
        self.assertEqual(measure(outside)["status"], "paint outside placement")
        inside = bytearray(page)
        for y in range(t+8, b-8):
            i = 3*(w*y+l+8)
            inside[i:i+90] = b"\xff"*90
        self.assertEqual(measure(inside)["status"], "placement interior mismatch")
        altered = measure(page, b"\xff"*len(rgb))
        self.assertEqual(altered["status"], "sampling reference gap")
        self.assertEqual(altered["direct_mupdf"]["status"], "retained direct score")

    def test_altered_reviewed_rasters(self):
        good = b"reviewed RGB"
        case = sampling.CASES["JPXTestGrey"]._replace(direct_sha=sampling.sha(good),
                    reference_sha=sampling.sha(good), control_sha=sampling.sha(good))
        with patch.object(sampling, "trace_site"), patch.object(sampling, "flate_control"):
            for outputs, message in (((good, b"changed"), "reference crop changed"),
                                     ((b"changed", good), "Flate control crop changed")):
                with self.subTest(message=message), patch.object(sampling, "render_crop", side_effect=outputs):
                    with self.assertRaisesRegex(ValueError, message):
                        sampling.reference(Path("source"), Path("tmp"), case, good)


@unittest.skipUnless(os.environ.get("JPX_CACHE"), "set JPX_CACHE for source-PDF controls")
class CorpusTests(unittest.TestCase):
    def test_worker_reencoding_and_external_mask_controls(self):
        root = Path(os.environ["JPX_CACHE"]) / "pdf-sources"
        worker = pages.REPO / ".lake/build/bin/worker"
        for name, case in sampling.CASES.items():
            with self.subTest(source=name), tempfile.TemporaryDirectory() as work:
                tmp = Path(work)
                pdf, = root.glob(f"*/{name}.pdf")
                self.assertEqual(sampling.sha(pdf.read_bytes()), case.source)
                def render(path):
                    return pages.worker_page(path, 1, 1, worker, tmp, 1, pages.REPO)
                source = render(pdf)
                full = render(sampling.flate_control(pdf, tmp, case))
                score = pages.compare_region(source, full, case.rect)
                self.assertEqual(score["differing"], 0)
                if case.owner != case.obj or not case.clip:
                    self.assertTrue(score["identical"])
                if case.mask:
                    attrs, _ = sampling.image_stream(pdf, case.mask)
                    w, h, _ = case.native
                    # A fully transparent external mask must remove colour from the placement.
                    attrs.pop("/DecodeParms", None)
                    attrs.pop("/Filter")
                    recipe = tmp / "zero.json"
                    sampling.write_json(recipe, {f"obj:{case.mask} 0 R": sampling.stream(attrs, bytes(w*h))})
                    blank = tmp / "zero-mask.pdf"
                    sampling.run("qpdf", f"--update-from-json={recipe}", pdf, blank)
                    zero = render(blank)
                    self.assertFalse(pages.outside_changed(source, zero, [case.rect]))
                    score = pages.compare_region(source, zero, case.rect)["percent"]
                    self.assertGreater(score, pages.pixels.TAU)
                    print(f"{name} transparent mask: {score:.3f}% changed", flush=True)
                    if case.mask != case.obj:  # The colour PDFBox pages have a nonconstant mask.
                        sampling.write_json(recipe, {f"obj:{case.mask} 0 R":
                                            sampling.stream(attrs, b"\xff"*(w*h))})
                        opaque = tmp / "opaque-mask.pdf"
                        sampling.run("qpdf", f"--update-from-json={recipe}", pdf, opaque)
                        solid = render(opaque)
                        self.assertFalse(pages.outside_changed(source, solid, [case.rect]))
                        score = pages.compare_region(source, solid, case.rect)["percent"]
                        x, y = case.mask_probe
                        self.assertEqual(source.row(y)[3*x:3*x+3], b"\xff"*3)
                        self.assertLess(min(solid.row(y)[3*x:3*x+3]), 255-pages.pixels.TOL)
                        print(f"{name} opaque mask: {score:.3f}% changed", flush=True)
                        # The page cache uses the largest extent of every use. A second,
                        # native-size use outside the page requests level zero for the
                        # same XObject while the original on-page Do and clip stay intact.
                        ops = sampling.run("qpdf", "--show-object=8", "--filtered-stream-data", pdf)
                        ops += b"\nq 1377 0 0 443 2000 2000 cm /Im0 Do Q\n"
                        sampling.write_json(recipe, {"obj:8 0 R": sampling.stream({}, ops)})
                        native = tmp / "full-resolution.pdf"
                        sampling.run("qpdf", f"--update-from-json={recipe}", pdf, native)
                        full = render(native)
                        self.assertFalse(pages.outside_changed(source, full, [case.rect]))
                        self.assertEqual(pages.compare_region(source, full, case.rect)["differing"], 0)


if __name__ == "__main__":
    unittest.main()
