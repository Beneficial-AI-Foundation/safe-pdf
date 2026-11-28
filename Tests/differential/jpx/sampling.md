# M10.2v placement controls

The comparison uses the original source PDFs and the existing 72 dpi placement rectangles. MuPDF 1.25.1 must render each page and trace its actual image. The five rows below also require an independent placement control. The gate records both measurements in each row. A missing source paint, changed source, mask, geometry, decoded sample digest or reviewed crop fails the reference.

| Source and object | Direct MuPDF | Direct PDF.js | Reviewed reference | Worker vs equivalent Flate in the worker |
| --- | ---: | ---: | ---: | ---: |
| JPXTestCMYK 12 | 599/35,748 (1.676%) | 36.956% | 0/35,748 | 0/35,748 |
| JPXTestGrey 84 | 596/35,748 (1.667%) | 0.000% | 0/35,748 | 0/35,748 |
| JPXTestRGB 12 | 606/35,748 (1.695%) | 0.428% | 0/35,748 | 0/35,748 |
| S2 35, soft mask of 24 | 55/235 (23.404%) | 2.553% | 1/235 (0.426%) | byte-identical |
| jpx_subsampling 11 | 503/10,000 (5.030%) | 0.000% | 0/10,000 | byte-identical |

All percentages count differing pixels with the usual symmetric 3 × 3 neighbourhood, 32/255 per-channel tolerance and 1% placement limit. PDF.js observations used 6.5.438 on Node 22.23.5 with canvas 1.2.1. The live gate renders equivalent Flate controls in MuPDF and pins their crop digests. The focused suite also renders those PDFs in the confined worker.

## Image samples and masks

For the four clipped placements the control paints the target image on an unmasked sheet at one native sample per pixel. MuPDF writes a PAM in the source device colour space, including all four CMYK channels. Only the target stream encoding changes in the equivalent source page. The original clip, image space, soft mask relationship, graphics state, paint order and other page data are retained. The table gives samples at (0,0), (width/2,height/4) rounded down, and the last pixel.

| Native sheet | Three measured sample tuples |
| --- | --- |
| CMYK, 1377 × 443 | (0,0,0,0), (8,12,0,0), (0,0,0,253) |
| Gray, 690 × 223 | 254, 255, 28 |
| RGB, 1377 × 443 | (252,252,252), (255,255,255), (21,21,21) |
| S2 soft mask, 18 × 166 | All 2,988 values are 255 |

On the RGB and CMYK pages the external Flate DeviceGray image 16 is 1377 × 443. Its 610,011 bytes include 469,216 opaque and 132,192 transparent samples, plus partially covered samples. The remaining values are 16, 32, 48, 64, 128 and 191. Rendering with a transparent mask changes 65.495% of RGB and 65.413% of CMYK. Rendering with the mask fully opaque changes 0.380% of RGB and 1.270% of CMYK. Both controls leave the exterior byte-identical. In particular, the RGB opaque-mask error alone can pass the aggregate tolerance. The gate checks the transparent footprint at device (420,159) on RGB and (418,159) on CMYK. Every contributing mask sample is zero, and both reviewed source crops show white paper. The worker paints white there. With the opaque mask the samples become (255,235,150) and (248,244,138) respectively.

S2 paints a vertically flipped Indexed/DeviceRGB colour strip with 72 palette entries through mask 35. The source, its full-resolution Flate mask control and the original MuPDF trace agree on the owner, dimensions and transform. Zeroing the mask changes all 235 measured pixels in the worker and leaves the exterior byte-identical. The other eight image paints on the page remain present.

At 72 dpi the worker's preferred wavelet reduction is one level for RGB and CMYK (689 × 222), and zero for Gray, S2 mask 35 and object 11. A separate control adds a second native-size use of the RGB/CMYK image entirely outside the page. The shared image cache then requests level zero (1377 × 443) for the original on-page use. Full-resolution and ordinary reduced JPX yield zero pixels outside tolerance on both placements. The direct MuPDF discrepancies also persist with Flate colour samples in the two readers, at 1.673% CMYK, 1.581% Gray, 1.709% RGB and 23.404% S2.

## Fractional rectangle coverage

The device-space PDFBox RGB/CMYK clip is [91.025, 80.689, 421.505, 187.010]. Gray starts at y = 80.690. At 72 dpi an interior column in the top pixel row covers 0.311 of a pixel for RGB/CMYK, the bottom row covers 0.010 and the right column covers 0.505. The RGB page paints just one masked image. All pixels outside the audited rectangle are white in the worker and direct reference. Gray has a larger image transform extending beyond the same clip. S2's clip is [307.126, 606.626, 311.680, 652.706]. The right column covers 0.680 of a pixel and the top row covers 0.374. Its narrow five-pixel-wide rectangle makes a single edge column significant.

Every direct MuPDF failure on these four placements falls on the one-pixel rim. The unmodified worker and direct reference measure 0% on all four interiors. For example at device (415,80) on RGB the worker gives (192,225,244), direct MuPDF (5,136,214) and PDF.js white. At (411,187) on Gray the worker and PDF.js give white and direct MuPDF gives (32,32,32). The direct MuPDF pixel paints near-full image colour over the bottom edge even though the geometric clip covers only 0.010 of that pixel row.

The area reference renders the original page at 576 dpi. For each original 72 dpi pixel it averages the 64 RGB subpixels at the same top-left grid origin with nearest-integer rounding. Each subpixel contributes exactly 1/64 of the device pixel. A straight boundary can move by less than 1/8 of a device pixel due to grid fitting at that resolution. The original fractional clip, alpha and background are present in every subsample. A 4 × 4 convergence check gives 0.571% CMYK, 0.476% Gray, 0.495% RGB and 0.851% S2. At 8 × 8 the source and Flate controls are byte-identical for CMYK, RGB and S2 and within 0% for Gray. The direct 72 dpi interior is still checked for each row, and all three PDFBox pages must have an entirely white exterior. The production renderer needs no sampling or compositing change for these observations.

## Odd-origin RGB component grid

Objects 10 and 11 declare DeviceRGB, with a 32 × 32 red plane and 16 × 16 green and blue planes sampled 2:1 along each axis. Their codestreams differ in exactly six SIZ bytes. The image origin moves from (0,0) to (1,1) and both end coordinates and tile dimensions increase from 32 to 33. The sample payload is identical. The 1:1 even-origin sheet independently verifies every red horizontal ramp value, green vertical ramp value and blue checker cell in MuPDF.

For local sample (x,y), red is floor(255x/31). For the odd origin the first stored chroma coordinate is ceil(1/2) = 1. The horizontal index is max(0, floor((x+1)/2) − 1), and likewise for y. Green is 17 times the vertical index. Blue alternates between 0 and 255 in four-chroma-sample squares. This gives the first blue transition at local x = 9 and y = 9. The 3,072 derived RGB bytes match an independently rendered native PDF.js page (SHA-256 d4869a6d99cc6373383821244c089bbb52210cbae77605af8712f6a7da5d590b). The live gate uses these RGB bytes to replace only object 11 in its source PDF, and requires MuPDF to paint the resulting 100 × 100 crop at [110,10,210,110]. PDF.js painting the original produces the same crop byte for byte. All four original source paints are also required in the direct MuPDF comparison.

## Reproduce

Run these commands from the safe-pdf root with the worker built.

~~~sh
JPX_CACHE=/path/to/jpeg2000/corpus/files python3 -IB Tests/differential/jpx/test_sampling.py
python3 -IB Tests/differential/jpx/pages.py --cache /path/to/jpeg2000/corpus/files \
  --only JPXTestCMYK --only JPXTestGrey --only JPXTestRGB --only S2 --only jpx_subsampling \
  --json /tmp/jpx-sampling.json
~~~

The focused page command includes the other occurrences in S2 and jpx_subsampling. Their own gates determine their status.
