"""Generator for the golden inputs of the `pages` and `outline` inspector views (task 4.4).

Usage: python3 -I Tests/golden/generate_pages.py Tests/golden/pages
Stdlib only, deterministic (no compression). The generated PDFs are the test inputs:

* tree.pdf    nested page tree with inheritance (MediaBox and Rotate -90 on an
              intermediate node, a real-valued box, a CropBox partly outside the
              MediaBox, a disjoint CropBox, a page without any MediaBox), a dangling
              /Kids reference, a wrong /Count, page labels (roman, prefixed decimal
              with /St), link and non-link annotations.
* outline.pdf outline with nesting, a /Next cycle back to an earlier item, non-ASCII and
              UTF-16BE titles, a named destination through the /Names /Dests tree and
              the /Dests dictionary, an unresolved name, a URI action, an out-of-range
              page index.
* shared.pdf  one page object listed under two parents (rejected as a cycle by the core;
              qpdf duplicates the page instead: Tests/differential/pages.py).
"""

import os
import sys


def pdf(objs):
    """objs: list of bodies (bytes) for objects 1..n; trailer /Root 1 0 R."""
    out = b"%PDF-1.7\n"
    offs = []
    for i, body in enumerate(objs, 1):
        offs.append(len(out))
        out += b"%d 0 obj\n" % i + body + b"\nendobj\n"
    x = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    for o in offs:
        out += b"%010d 00000 n \n" % o
    out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, x)
    return out


def tree():
    return pdf([
        # 1 catalog
        b"<< /Type /Catalog /Pages 2 0 R /PageLabels << /Nums [0 << /S /r >> "
        b"2 << /S /D /P (A-) /St 5 >>] >> >>",
        # 2 root: no MediaBox; /Count wrong (says 6, has 5); dangling kid 99
        b"<< /Type /Pages /Kids [3 0 R 99 0 R 7 0 R] /Count 6 >>",
        # 3 intermediate: inherited MediaBox (corners swapped, real) and Rotate -90
        b"<< /Type /Pages /Parent 2 0 R /Kids [4 0 R 5 0 R 6 0 R] /Count 3 "
        b"/MediaBox [595.2760 841.89 0 0] /Rotate -90 >>",
        # 4 page: inherits everything; two links and one text annotation
        b"<< /Type /Page /Parent 3 0 R /Annots [8 0 R 9 0 R 10 0 R] >>",
        # 5 page: own CropBox partly outside the MediaBox, own Rotate 180
        b"<< /Type /Page /Parent 3 0 R /CropBox [-10 -10 300.5 400] /Rotate 180 >>",
        # 6 page: disjoint CropBox (MediaBox used), Rotate 45 (not a multiple of 90 -> 0)
        b"<< /Type /Page /Parent 3 0 R /CropBox [1000 1000 2000 2000] /Rotate 45 >>",
        # 7 page directly under the root: no MediaBox anywhere (Letter, defaulted)
        b"<< /Type /Page /Parent 2 0 R /Rotate 450 >>",
        # 8 link to page index 3 (object 7) with /Fit
        b"<< /Type /Annot /Subtype /Link /Rect [10 10 50 50] /Dest [7 0 R /Fit] >>",
        # 9 URI link
        b"<< /Type /Annot /Subtype /Link /Rect [60 60 10 10] /A << /S /URI /URI (http://x) >> >>",
        # 10 text annotation (not a link)
        b"<< /Type /Annot /Subtype /Text /Rect [0 0 1 1] /Contents (note) >>",
    ])


def outline():
    return pdf([
        # 1 catalog
        b"<< /Type /Catalog /Pages 2 0 R /Outlines 5 0 R /Dests 13 0 R "
        b"/Names << /Dests 14 0 R >> >>",
        # 2 root
        b"<< /Type /Pages /Kids [3 0 R 4 0 R] /Count 2 /MediaBox [0 0 200 100] >>",
        b"<< /Type /Page /Parent 2 0 R >>",
        b"<< /Type /Page /Parent 2 0 R >>",
        # 5 outline root
        b"<< /Type /Outlines /First 6 0 R /Last 9 0 R /Count 4 >>",
        # 6 top item with two children; explicit dest to page 1 (object 4)
        b"<< /Title (Chapter 1) /Parent 5 0 R /Next 9 0 R /First 7 0 R /Last 8 0 R /Count 2 "
        b"/Dest [4 0 R /XYZ 0 100 null] >>",
        # 7 child: non-ASCII PDFDocEncoding title, named destination (string -> name tree)
        b"<< /Title (Caf\\351 \\\\ s) /Parent 6 0 R /Next 8 0 R /Dest (intro) >>",
        # 8 child: UTF-16BE title, named destination (name -> /Dests dict)
        b"<< /Title <FEFF00480069> /Parent 6 0 R /Prev 7 0 R /Dest /legacy >>",
        # 9 top item: URI action; /First points back to item 6 (cycle, cut)
        b"<< /Title (Web) /Parent 5 0 R /Prev 6 0 R /Next 10 0 R /First 6 0 R "
        b"/A << /S /URI /URI (http://example.com) >> >>",
        # 10 top item: unresolved name
        b"<< /Title (Missing) /Parent 5 0 R /Next 11 0 R /Dest (nowhere) >>",
        # 11 top item: GoTo with an out-of-range integer page index
        b"<< /Title (Far) /Parent 5 0 R /Next 12 0 R /A << /S /GoTo /D [7 /Fit] >> >>",
        # 12 top item: no destination; /Next back to 10 (repeated node, cut)
        b"<< /Title () /Parent 5 0 R /Next 10 0 R >>",
        # 13 /Dests dictionary (PDF 1.1)
        b"<< /legacy [3 0 R /FitH 50] >>",
        # 14 name tree root with one leaf kid
        b"<< /Kids [15 0 R] >>",
        b"<< /Limits [(a) (z)] /Names [(intro) << /D [3 0 R /Fit] >>] >>",
    ])


def shared():
    return pdf([
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R 4 0 R] /Count 2 /MediaBox [0 0 612 792] >>",
        b"<< /Type /Pages /Parent 2 0 R /Kids [5 0 R] /Count 1 >>",
        b"<< /Type /Pages /Parent 2 0 R /Kids [5 0 R] /Count 1 >>",
        b"<< /Type /Page /Parent 3 0 R >>",
    ])


def main():
    d = sys.argv[1]
    for name, data in (("tree.pdf", tree()), ("outline.pdf", outline()),
                       ("shared.pdf", shared())):
        with open(os.path.join(d, name), "wb") as f:
            f.write(data)


if __name__ == "__main__":
    main()
