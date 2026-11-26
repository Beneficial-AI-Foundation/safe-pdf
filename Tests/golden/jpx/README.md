# One-bit JPX render fixtures

Both PDFs are original single-page fixtures. Each draws three 16 × 8 images at
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
