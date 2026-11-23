"""Generate pdfTeX test pages for the pixel differential (task 7.4, docs/raster.md).

    python3 -I Tests/differential/fixtures/gen_tex_pages.py OUTDIR
    cd OUTDIR && for n in text type3 times math vector image mixed; do
        pdflatex -interaction=batchmode $n.tex; done
    python3 -I Tests/differential/run.py --comparator pixels --files 'OUTDIR/*.pdf'

Pages: text (CM Type 1, 8 pages), type3 (T1 fontenc without cm-super: bitmap Type 3
fonts), times (mathptmx, Nimbus Type 1), math (CM math), vector (400 random fills,
strokes, Bezier circles, even-odd fills via pdfliteral), image (a generated 320x240
PNG, Flate + predictors, one copy rotated), mixed (colour, table, rules, picture).
Deterministic (seeded); stdlib only.
"""
import math
import os
import random
import struct
import sys
import zlib

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
random.seed(7)
WORDS = ("lorem ipsum dolor sit amet consectetur adipiscing elit sed do eiusmod tempor "
         "incididunt ut labore et dolore magna aliqua enim ad minim veniam quis nostrud "
         "exercitation ullamco laboris nisi aliquip ex ea commodo consequat duis aute irure "
         "reprehenderit voluptate velit esse cillum fugiat nulla pariatur excepteur sint "
         "occaecat cupidatat non proident sunt in culpa qui officia deserunt mollit anim "
         "id est laborum office affine fluffy waffle").split()


def para(n):
    ws = [random.choice(WORDS) for _ in range(n)]
    ws[0] = ws[0].capitalize()
    return " ".join(ws) + "."


def png(path, w, h):
    raw = bytearray()
    for y in range(h):
        raw.append(0)
        for x in range(w):
            r = int(127 + 127 * math.sin(x / 9.0))
            g = int(127 + 127 * math.cos(y / 13.0))
            b = (x * y) % 256
            raw += bytes((r, g, b))

    def chunk(t, b):
        return struct.pack(">I", len(b)) + t + b + struct.pack(">I", zlib.crc32(t + b) & 0xFFFFFFFF)
    with open(path, "wb") as fh:
        fh.write(b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0))
                 + chunk(b"IDAT", zlib.compress(bytes(raw), 9)) + chunk(b"IEND", b""))


png(os.path.join(out, "img.png"), 320, 240)

head = r"""\documentclass[11pt]{article}
%s
\usepackage{graphicx,color,amsmath}
\pagestyle{plain}
\begin{document}
"""
docs = {}
docs["text"] = head % "" + "\n\n".join(para(random.randint(60, 140)) for _ in range(30)) + "\n\\end{document}\n"
docs["type3"] = head % r"\usepackage[T1]{fontenc}" + "\n\n".join(para(random.randint(60, 140)) for _ in range(8)) + "\n\\end{document}\n"
docs["times"] = head % r"\usepackage{mathptmx}" + "\\section{Times}\n" + "\n\n".join(
    para(random.randint(60, 140)) for _ in range(25)) + "\n\\end{document}\n"
docs["math"] = head % "" + "\n".join(
    r"\begin{equation} \int_0^{%d} \frac{x^{%d} + \sqrt{y_%d}}{\sum_{k=1}^{n} \alpha_k \beta^k} \,dx = \prod_{j} \left( \frac{a_j}{b_j} \right)^{\gamma} \end{equation} %s" % (i, i, i, para(30))
    for i in range(12)) + "\n\\end{document}\n"
lit = []
for i in range(400):
    x, y = random.uniform(0, 450), random.uniform(0, 650)
    r, g, b = (random.random() for _ in range(3))
    k = random.choice("fSBb")
    if k == "f":
        lit.append("%.3f %.3f %.3f rg %.1f %.1f %.1f %.1f re f" % (r, g, b, x, y, random.uniform(2, 40), random.uniform(2, 40)))
    elif k == "S":
        lit.append("%.3f %.3f %.3f RG %.2f w %.1f %.1f m %.1f %.1f l %.1f %.1f %.1f %.1f %.1f %.1f c S" % (
            r, g, b, random.uniform(0.2, 3), x, y, x + 30, y + 10, x + 40, y - 20, x + 60, y + 30, x + 80, y))
    elif k == "B":
        c = 0.5523
        rad = random.uniform(3, 25)
        lit.append("%.3f %.3f %.3f rg 0 0 0 RG 0.5 w %.1f %.1f m %.2f %.2f %.2f %.2f %.2f %.2f c %.2f %.2f %.2f %.2f %.2f %.2f c %.2f %.2f %.2f %.2f %.2f %.2f c %.2f %.2f %.2f %.2f %.2f %.2f c B" % (
            r, g, b, x + rad, y,
            x + rad, y + c * rad, x + c * rad, y + rad, x, y + rad,
            x - c * rad, y + rad, x - rad, y + c * rad, x - rad, y,
            x - rad, y - c * rad, x - c * rad, y - rad, x, y - rad,
            x + c * rad, y - rad, x + rad, y - c * rad, x + rad, y))
    else:
        lit.append("%.3f %.3f %.3f rg %.1f %.1f m %.1f %.1f l %.1f %.1f l h f*" % (
            r, g, b, x, y, x + 50, y + 5, x + 20, y + 40))
docs["vector"] = head % "" + "\\noindent\\pdfliteral{q " + "\n".join(lit) + " Q}\n\\end{document}\n"
docs["image"] = head % "" + "\\noindent\\includegraphics[width=\\textwidth]{img.png}\n\n" + para(80) + \
    "\n\n\\includegraphics[width=0.4\\textwidth,angle=30]{img.png}\n\\end{document}\n"
docs["mixed"] = head % "" + "\\section{Mixed}\n" + para(100) + "\n\n{\\color{red}" + para(40) + "}\n\n" + \
    "\\begin{tabular}{|l|c|r|}\\hline a & b & c\\\\\\hline 1 & 2 & 3\\\\\\hline\\end{tabular}\n\n" + \
    "\\fbox{" + para(8) + "} \\rule{5cm}{2mm}\n\n\\includegraphics[width=4cm]{img.png}\n\n" + \
    "\\begin{picture}(200,100)\\put(0,0){\\line(1,1){80}}\\put(100,0){\\framebox(60,40){box}}\\end{picture}\n" + \
    "\\newpage\n\\begin{center}\\Huge Big \\textbf{Bold} \\textit{Italic} \\texttt{Mono}\\end{center}\n" + para(120) + \
    "\n\\end{document}\n"
for name, src in docs.items():
    with open(os.path.join(out, name + ".tex"), "w") as fh:
        fh.write(src)
print(" ".join(docs))
