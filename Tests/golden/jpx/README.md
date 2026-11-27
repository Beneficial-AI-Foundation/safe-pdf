# One-bit JPX render fixtures

The three polarity PDFs are original single-page fixtures. Each draws three 16 × 8 images at
one point per pixel on a 48 × 8 white page. Every input row consists of eight
zero samples and eight one samples.

| Placement | Image dictionary | Expected left and right halves |
| --- | --- | --- |
| Left | DeviceGray, reversed `/Decode` in the JPX fixture | Black, white |
| Middle | Red stencil, `/ImageMask true /Decode [0 1]` | Red, white |
| Right | Red stencil, `/ImageMask true /Decode [1 0]` | White, red |

`polarity.pdf` wraps the reversible output from the pinned decoder package's
`JPEG2000.Encode.encode` in a greyscale JP2 container. The encoder input has one
unsigned one-bit component, zero decomposition levels and no component transform.
`plain-polarity.pdf` stores the same rows directly as `00 ff` pairs and uses the
default DeviceGray mapping. The worker test checks every output byte against the
six expected bands. MuPDF 1.25.1 agrees on every pixel of the unfiltered control.

`inline-polarity.pdf` places the same JP2 bytes inside three inline images using
`BI`, `ID` and `EI` in the page content. It uses terminal `/JPXDecode` for the
grayscale image, a Flate prefix for the first stencil, and an ASCIIHex prefix
for the second. The page has an empty resource dictionary. It exercises the
content parser and the page's inline image cache through the worker.

`named-tints.pdf` draws that one-bit JP2 twice on a 32 × 8 page. The XObject
references the DeviceN colour-space array. The inline image names the same array
through its page resources. The type 4 tint function maps x to (1, 1−x, 1−x),
so each image paints eight white pixels followed by eight red pixels on every
row. An uncompressed version of the same page matched these 256 pixels in MuPDF.
