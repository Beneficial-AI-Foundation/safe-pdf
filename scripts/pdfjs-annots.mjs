// pdf.js check of an annotated file (task 9.10, docs/viewer.md "M9 evidence"): getDocument +
// page.getAnnotations() on every page; prints each annotation's subtype, id, colour (a
// FreeText's /DA font colour and size), rect, appearance flag, contents; optionally renders
// page 1 to a PNG through pdf.js's Node canvas factory (@napi-rs/canvas).
//   node scripts/pdfjs-annots.mjs PDFJS_DIST_DIR FILE [OUT.png]
// PDFJS_DIST_DIR is an installed pdfjs-dist (e.g. `npm install pdfjs-dist@4.10.38` in a scratch
// directory outside the repository); nothing here is a project dependency.
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

const [pdfjsDir, file, outPng] = process.argv.slice(2);
const pdfjs = await import(pathToFileURL(path.join(pdfjsDir, "legacy/build/pdf.mjs")).href);
const data = new Uint8Array(fs.readFileSync(file));
const doc = await pdfjs.getDocument({ data, verbosity: 0, isEvalSupported: false,
  standardFontDataUrl: path.join(pdfjsDir, "standard_fonts") + "/" }).promise;
console.log(`pdfjs ${pdfjs.version}: ${doc.numPages} pages`);
for (let p = 1; p <= doc.numPages; p++) {
  const page = await doc.getPage(p);
  for (const a of await page.getAnnotations()) {
    const color = a.color ? Array.from(a.color).join(",") : (a.defaultAppearanceData ? "font:" + Array.from(a.defaultAppearanceData.fontColor).join(",") + " size:" + a.defaultAppearanceData.fontSize : "-");
    const contents = a.contentsObj ? a.contentsObj.str : "";
    const extra = a.subtype === "Ink" ? ` inkLists=${a.inkLists.length}` :
      a.subtype === "Highlight" ? ` quads=${(a.quadPoints || []).length / 8}` :
      a.subtype === "FreeText" ? ` textContent=${JSON.stringify(a.textContent || [])}` : "";
    console.log(`page ${p}: ${a.subtype} id=${a.id} color=${color} ` +
      `rect=${a.rect.map((x) => x.toFixed(1)).join(",")} hasAppearance=${a.hasAppearance} ` +
      `contents=${JSON.stringify(contents)}${extra}`);
  }
}
if (outPng) {
  const page = await doc.getPage(1);
  const vp = page.getViewport({ scale: 1 });
  const factory = doc.canvasFactory;
  const { canvas, context } = factory.create(vp.width, vp.height);
  await page.render({ canvasContext: context, viewport: vp, annotationMode: pdfjs.AnnotationMode.ENABLE }).promise;
  fs.writeFileSync(outPng, canvas.toBuffer("image/png"));
  console.log(`rendered page 1 to ${outPng} (${vp.width}x${vp.height})`);
}
