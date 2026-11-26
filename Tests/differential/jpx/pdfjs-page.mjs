// jpeg2000 Plan §9. Use an existing PDF.js Node distribution for the DeviceN page.
import { readFile, writeFile } from "node:fs/promises";
import { createRequire } from "node:module";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

const [dist, pdf, pageNumber, denominator, out, expectedFills, gridAudit] = process.argv.slice(2);
const pdfjs = await import(pathToFileURL(resolve(dist, "legacy/build/pdf.mjs")));
let version = `PDF.js ${pdfjs.version}, Node ${process.version}`;
if (gridAudit) {
  const require = createRequire(resolve(dist, "package.json"));
  const canvas = require("@napi-rs/canvas/package.json").version;
  version += `, canvas ${canvas}`;
  if (pdfjs.version !== "6.5.438" || canvas !== "1.2.1") {
    throw new Error(`unreviewed grid renderer: ${version}`);
  }
}
console.log(version);
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
  if (!gridAudit && fills !== Number(expectedFills)) {
    throw new Error(`expected ${expectedFills} image paints on page ${pageNumber}, got ${fills}`);
  }
  const viewport = page.getViewport({ scale: 1 / Number(denominator) });
  if (gridAudit) {
    // Each grid Do is in its own q / cm / Do / Q. Report actual paints by
    // device rectangle so a missing site leaves just its own mandatory gap.
    const paints = [];
    let matrix = viewport.transform;
    const stack = [];
    for (const [i, op] of list.fnArray.entries()) {
      const args = list.argsArray[i];
      if (op === pdfjs.OPS.save) stack.push(matrix);
      if (op === pdfjs.OPS.restore) matrix = stack.pop();
      if (op === pdfjs.OPS.transform) matrix = pdfjs.Util.transform(matrix, args);
      if (op === pdfjs.OPS.paintImageXObject) {
        const [a, b, c, d, e, f] = matrix;
        if (b !== 0 || c !== 0 || a <= 0 || d >= 0) throw new Error("unexpected grid transform");
        paints.push({ rect: [e, f + d, e + a, f], size: args.slice(1, 3) });
      }
    }
    await writeFile(gridAudit, JSON.stringify(paints));
  }
  const { canvas, context } = doc.canvasFactory.create(
    Math.ceil(viewport.width), Math.ceil(viewport.height)
  );
  await page.render({ canvasContext: context, viewport, background: "white" }).promise;
  await writeFile(out, canvas.toBuffer("image/png"));
} finally {
  await task.destroy();
}
