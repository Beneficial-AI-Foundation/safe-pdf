#!/usr/bin/env python3
"""Proof-hygiene scanner (Plan.md section 3 rule 3).  Standard library only; run with `python3 -I`.

  hygiene.py scan [--root DIR]      grep sources for forbidden constructs, ignoring comments/strings
  hygiene.py axioms                 read `#print axioms` output on stdin, fail on non-standard axioms
  hygiene.py modules [--root DIR]   print the strict modules (dotted names) for scripts/envscan.lean

Strict files (SafePdf/Core/, SafePdf/Spec/, SafePdf/Repair.lean) forbid: partial, unsafe, panic!,
any `ident!` call (get!, head!, back!, getElem!, ...), `xs[i]!` indexing, and sorry.
Everything under SafePdf/ and Tests/ forbids sorry.
Task 13.9 adds source rules for strict files: `extern`, `implemented_by`, `axiom` declarations,
`native_decide`, `decide +native` and `ofReduceBool`, `skipKernelTC` (also forbidden anywhere
under SafePdf/ and Tests/).  The strict set also contains SafePdf/Shell/Worker/Protocol.lean
(pure; the GUI decodes untrusted worker output with it).  The built environment is checked by
scripts/envscan.lean.
"""
import os
import re
import sys

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

STRICT_RULES = [
    ("partial", re.compile(r"\bpartial\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("panic!", re.compile(r"\bpanic!")),
    # `s!`/`m!`/`f!` are string-interpolation macros (`s!"…"`), not partial calls.
    ("`!` call (get!/head!/...)",
     re.compile(r"(?<![\w'.])(?![smf]!)[\w.']*[A-Za-z_][\w']*!(?!=)")),
    ("`[i]!` indexing", re.compile(r"[\]\)]!(?!=)")),
    ("sorry", re.compile(r"\bsorry\b")),
    ("@[extern]", re.compile(r"\bextern\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("axiom declaration", re.compile(r"(?<![\w.'#])axiom\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("decide +native", re.compile(r"\bdecide\s*\+\s*native\b")),
    ("ofReduceBool", re.compile(r"\bofReduceBool\b")),
]
ANY_RULES = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("debug.skipKernelTC", re.compile(r"\bskipKernelTC\b")),
]
STRICT_RULES.append(("debug.skipKernelTC", re.compile(r"\bskipKernelTC\b")))

# Strict directories and files, relative to the root (shared with scripts/envscan.lean via `modules`).
STRICT_TARGETS = ("SafePdf/Core", "SafePdf/Spec", "SafePdf/Repair.lean", "SafePdf/Api.lean",
                  "SafePdf/Quarantine", "SafePdf/Shell/Worker/Protocol.lean")


def blank(ch):
    return "\n" if ch == "\n" else " "


def strip_code(src):
    """Replace comments and string/char literals by spaces, preserving newlines."""
    out = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        two = src[i:i + 2]
        if two == "--":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif two == "/-":
            depth = 0
            while i < n:
                if src[i:i + 2] == "/-":
                    depth += 1
                    out.append("  ")
                    i += 2
                elif src[i:i + 2] == "-/":
                    depth -= 1
                    out.append("  ")
                    i += 2
                    if depth == 0:
                        break
                else:
                    out.append(blank(src[i]))
                    i += 1
        elif c == "r" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'")) \
                and re.match(r'r#*"', src[i:]):
            m = re.match(r'r(#*)"', src[i:])
            close = '"' + m.group(1)
            j = src.find(close, i + m.end())
            j = n if j < 0 else j + len(close)
            out.extend(blank(ch) for ch in src[i:j])
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.extend(blank(ch) for ch in src[i:j])
            i = j
        elif c == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'")):
            m = re.match(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'", src[i:])
            if m:
                out.append(" " * m.end())
                i += m.end()
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def lean_files(path):
    if os.path.isfile(path):
        return [path] if path.endswith(".lean") else []
    found = []
    for d, dirs, files in os.walk(path):
        dirs[:] = sorted(x for x in dirs if x not in (".lake", ".git"))
        found += [os.path.join(d, f) for f in sorted(files) if f.endswith(".lean")]
    return found


def strict_files(root):
    strict = set()
    for p in STRICT_TARGETS:
        t = os.path.join(root, p)
        if os.path.exists(t):
            strict.update(lean_files(t))
    return strict


def strict_modules(root):
    """Dotted module names of the strict files under `root`."""
    mods = []
    for f in sorted(strict_files(root)):
        rel = os.path.relpath(f, root)
        mods.append(rel[:-len(".lean")].replace(os.sep, "."))
    return mods


def scan(root):
    strict = strict_files(root)
    anyfiles = set()
    for t in ("SafePdf", "Tests"):
        p = os.path.join(root, t)
        if os.path.exists(p):
            anyfiles.update(lean_files(p))
    violations = []
    for f in sorted(strict | anyfiles):
        rules = STRICT_RULES if f in strict else ANY_RULES
        with open(f, encoding="utf-8", errors="replace") as fh:
            code = strip_code(fh.read())
        for ln, line in enumerate(code.split("\n"), 1):
            for name, rx in rules:
                if rx.search(line):
                    violations.append("%s:%d: forbidden %s" % (os.path.relpath(f, root), ln, name))
    return violations


def check_axioms(text):
    bad = []
    seen = 0
    # Each message: 'Name' depends on axioms: [a, b]  |  'Name' does not depend on any axioms
    for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", text):
        seen += 1
        if m.group(3) is not None:
            axs = [a.strip() for a in m.group(3).replace("\n", " ").split(",") if a.strip()]
            extra = [a for a in axs if a not in ALLOWED_AXIOMS]
            if extra:
                bad.append("%s depends on disallowed axiom(s): %s" % (m.group(1), ", ".join(extra)))
    return seen, bad


def main(argv):
    if len(argv) >= 2 and argv[1] == "scan":
        root = "."
        if "--root" in argv:
            root = argv[argv.index("--root") + 1]
        v = scan(root)
        for line in v:
            print(line)
        if v:
            print("hygiene: %d violation(s)" % len(v), file=sys.stderr)
            return 1
        print("hygiene: source scan OK")
        return 0
    if len(argv) >= 2 and argv[1] == "modules":
        root = argv[argv.index("--root") + 1] if "--root" in argv else "."
        for m in strict_modules(root):
            print(m)
        return 0
    if len(argv) >= 2 and argv[1] == "axioms":
        seen, bad = check_axioms(sys.stdin.read())
        for b in bad:
            print("axioms: " + b)
        if bad:
            return 1
        if seen == 0:
            print("axioms: no `#print axioms` results found in Lean output", file=sys.stderr)
            return 1
        print("hygiene: axioms OK (%d checked)" % seen)
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
