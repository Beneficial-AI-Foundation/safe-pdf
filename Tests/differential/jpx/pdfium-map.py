"""Render the audited issue19517 map with the test-only PDFium wheel."""
import hashlib
from pathlib import Path
import sys

import pypdfium2 as pdfium


def main(source, target):
    version = f"pypdfium2 {pdfium.PYPDFIUM_INFO}, PDFium {pdfium.PDFIUM_INFO}"
    if pdfium.PYPDFIUM_INFO.tag != "5.15.2" or pdfium.PDFIUM_INFO.tag != "159.0.8149.0":
        raise ValueError(f"unreviewed map renderer: {version}")
    with source.open("rb") as f:
        if hashlib.file_digest(f, "sha256").hexdigest() != "908c133880c7148864102eab517224d524cdd32769d2ae0f1e6d69e75a0471d6":
            raise ValueError("expected pinned issue19517 source")
    with pdfium.PdfDocument(source) as doc:
        page = doc[0]
        image, = page.get_objects()
        if (len(doc) != 1 or page.get_size() != (12608, 16806)
                or not isinstance(image, pdfium.PdfImage) or image.get_px_size() != (12608, 16806)
                or image.get_bounds() != (0, 0, 12608, 16806)):
            raise ValueError("map page or image geometry changed")
        bitmap = page.render(scale=1/16, rev_byteorder=True, force_bitmap_format=pdfium.raw.FPDFBitmap_BGR)
        if (bitmap.width, bitmap.height) != (788, 1051):
            raise ValueError("expected a 788 x 1051 RGB map")
        rgb = memoryview(bitmap.buffer).cast("B")
        with target.open("wb") as f:
            f.write(b"P6\n788 1051\n255\n")
            for y in range(bitmap.height):
                offset = y * bitmap.stride
                f.write(rgb[offset:offset + 3 * bitmap.width])
    print(version)


if __name__ == "__main__":
    main(*map(Path, sys.argv[1:]))
