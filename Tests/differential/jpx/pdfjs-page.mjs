// jpeg2000 Plan §9. Use an existing PDF.js Node distribution for the DeviceN page.
import { readFile, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

const [dist, pdf, pageNumber, denominator, out, expectedFills] = process.argv.slice(2);
const pdfjs = await import(pathToFileURL(resolve(dist, "legacy/build/pdf.mjs")));
console.log(`PDF.js ${pdfjs.version}, Node ${process.version}`);
const task = pdfjs.getDocument({
  data: new Uint8Array(await readFile(pdf)),
  stopAtErrors: true,
  isEvalSupported: false,
  useSystemFonts: false,
  wasmUrl: resolve(dist, "wasm") + "/",
  iccUrl: resolve(dist, "iccs") + "/",
});
try {
  const doc = await task.promise;
  const page = await doc.getPage(Number(pageNumber));
  const list = await page.getOperatorList();
  const fills = list.fnArray.filter(op => op === pdfjs.OPS.paintImageXObject).length;
  if (fills !== Number(expectedFills)) {
    throw new Error(`expected ${expectedFills} image paints on page ${pageNumber}, got ${fills}`);
  }
  const viewport = page.getViewport({ scale: 1 / Number(denominator) });
  const { canvas, context } = doc.canvasFactory.create(
    Math.ceil(viewport.width), Math.ceil(viewport.height)
  );
  await page.render({ canvasContext: context, viewport, background: "white" }).promise;
  await writeFile(out, canvas.toBuffer("image/png"));
} finally {
  await task.destroy();
}
