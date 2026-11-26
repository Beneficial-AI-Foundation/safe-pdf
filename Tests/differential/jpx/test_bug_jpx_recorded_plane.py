"""Focused tests for the recorded-plane oracle. Set JPX_CACHE for the live corpus case."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import Mock


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("pages", HERE / "pages.py")
pages = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pages)
oracle = pages.load_module("bug_jpx_recorded_plane", HERE / "bug_jpx_recorded_plane.py")


def flat_page(sample, offset=0):
    left, top, right, bottom = oracle.REGION
    paper = b"\xff" * (3 * 612)
    line = (paper[:3*(left+offset)] + bytes([sample]) * (3*(right-left))
            + paper[3*(right+offset):])
    return pages.pixels.Image(612, 792, paper * top + line * (bottom-top) + paper * (792-bottom))


class PageTests(unittest.TestCase):
    def test_both_pinned_rasters_are_the_expected_rectangle(self):
        for label, value in (("reference", 0), ("control", 192)):
            self.assertEqual(oracle.sha(flat_page(value).rgb), oracle.PAGE_RGB_SHA[label])

    def test_worker_gate(self):
        ref = flat_page(0)
        cases = [(ref, "within"), (flat_page(255), "blank/placeholder in placement"),
                 (flat_page(128), "blank/placeholder in placement"),
                 (flat_page(0, offset=1), "recorded-plane page mismatch")]
        for worker, expected in cases:
            with self.subTest(expected=expected):
                crop = pages.compare_region(worker, ref, oracle.REGION)
                result = oracle.worker_result(worker, ref, crop)
                self.assertEqual(result["status"], expected)
                self.assertEqual(result["exact_recorded_page"], expected == "within")

    def test_invalid_case_never_renders(self):
        with tempfile.TemporaryDirectory() as work:
            tmp = Path(work)
            render = Mock(side_effect=AssertionError("renderer reached"))
            with self.assertRaisesRegex(ValueError, "placement changed"):
                oracle.reference(tmp / "missing", {}, tmp, (0, 0, 128, 64), render)
            with self.assertRaisesRegex(ValueError, "incomplete"):
                oracle.reference(tmp / "missing", {}, tmp, oracle.REGION, render)
            render.assert_not_called()

    @unittest.skipUnless(shutil.which("qpdf"), "qpdf required")
    def test_mutations_of_serialized_bytes(self):
        with tempfile.TemporaryDirectory() as work:
            pdf = Path(work) / "reference.pdf"
            sentinel = b"benign test sentinel"
            oracle.verified_pdf(pdf, oracle.PLANE, sentinel)
            raw = pdf.read_bytes()
            for old, new in ((b"269.6739197", b"268.6739197"), (b"/ImageB", b"/ImageC"),
                             (oracle.PLANE, b"X" + oracle.PLANE[1:])):
                with self.subTest(changed=old[:12]):
                    self.assertIn(old, raw)
                    pdf.write_bytes(raw.replace(old, new, 1))
                    with self.assertRaisesRegex(ValueError, "audited JPX-free objects"):
                        oracle.verify_pdf(pdf, oracle.PLANE, sentinel)
            pdf.write_bytes(raw)
            encoded = Path(work) / "encoded.pdf"
            oracle.qpdf("--static-id", "--compress-streams=y", pdf, encoded)
            attrs = oracle.objects(encoded)["obj:5 0 R"]["stream"]["dict"]
            self.assertEqual(attrs["/Filter"], "/FlateDecode")
            with self.assertRaisesRegex(ValueError, "audited JPX-free objects"):
                oracle.verify_pdf(encoded, oracle.PLANE, sentinel)
            pdf.write_bytes(raw + sentinel)
            with self.assertRaisesRegex(ValueError, "encoded source payload"):
                oracle.verify_pdf(pdf, oracle.PLANE, sentinel)


@unittest.skipUnless(os.environ.get("JPX_CACHE"), "set JPX_CACHE for the pinned corpus")
class CorpusTests(unittest.TestCase):
    def setUp(self):
        self.pdf = Path(os.environ["JPX_CACHE"]) / oracle.SOURCE_PATH
        manifest = Path(os.environ.get("JPX_MANIFEST", pages.PACKAGE / "corpus/manifest.json"))
        self.manifest = json.loads(manifest.read_bytes())
        self.work = tempfile.TemporaryDirectory()
        self.addCleanup(self.work.cleanup)
        self.tmp = Path(self.work.name)

    def test_reject_missing_files_wrong_hash_and_sample_format_before_render(self):
        render = Mock(side_effect=AssertionError("renderer reached"))
        bad = self.tmp / "wrong.pdf"
        with self.assertRaises(FileNotFoundError):
            oracle.reference(bad, self.manifest, self.tmp, oracle.REGION, render)
        bad.write_bytes(b"wrong source")
        with self.assertRaisesRegex(ValueError, "source PDF size/hash"):
            oracle.reference(bad, self.manifest, self.tmp, oracle.REGION, render)
        for field, value in (("signed", True), ("constant", 1), ("width", 127), ("depth", 16)):
            with self.subTest(field=field):
                manifest = copy.deepcopy(self.manifest)
                entry = next(e for e in manifest["pdf_jpx"] if e["source_pdf"] == oracle.SOURCE_PATH)
                entry["recorded_plane"][field] = value
                with self.assertRaisesRegex(ValueError, "recorded_plane contract"):
                    oracle.reference(self.pdf, manifest, self.tmp, oracle.REGION, render)
        render.assert_not_called()

    def test_reference_and_contrast_control(self):
        def render(path):
            rows = [dict(object=15, region=oracle.REGION, mask=None,
                         dictionary=dict(Width=128, Height=64))]
            return pages.reference_page(path, 1, 1, "mupdf", None, self.tmp, rows, 1)

        image, _, provenance = oracle.reference(self.pdf, self.manifest, self.tmp, oracle.REGION, render)
        self.assertEqual(image.rgb, flat_page(0).rgb)
        self.assertEqual(provenance["control"]["rgb_sha256"], oracle.sha(flat_page(192).rgb))
        with self.assertRaisesRegex(ValueError, "control RGB digest"):
            oracle.reference(self.pdf, self.manifest, self.tmp, oracle.REGION,
                             lambda path: (flat_page(255), ""))


if __name__ == "__main__":
    unittest.main()
