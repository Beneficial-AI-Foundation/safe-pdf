#!/usr/bin/env python3
"""Encrypted fixtures for annotating encrypted files (task 9.5f, Tests/WriteAnnots.lean).

Each file is Tests/fixtures-write/annots/text.pdf (two pages of Helvetica text, page 2 with
an existing /Square) encrypted by qpdf with an EMPTY user password and owner password
"owner" (ISO 32000-2 §7.6):

  rc4-40.pdf          V1 R2, RC4 40-bit
  rc4-128.pdf         V2 R3, RC4 128-bit
  aes-128.pdf         V4 R4, /CF /StdCF /CFM /AESV2
  aes-256.pdf         V5 R6, /CF /StdCF /CFM /AESV3
  aes-256-objstm.pdf  as aes-256.pdf, but with object streams and an xref stream (the
                      writer's update is then an xref stream that must carry /Encrypt)

RC4 and AES-128 files are deterministic (qpdf --static-id --static-aes-iv, test-only
options); qpdf draws the R6 salts of the AES-256 files at random even then, so --check
verifies those only with `qpdf --check` (they decrypt with the empty password). The files are
committed; this script regenerates them (needs qpdf) or verifies them.

Usage:
    python3 -I Tests/fixtures-write/encrypted/generate.py           # write the PDFs
    python3 -I Tests/fixtures-write/encrypted/generate.py --check   # verify the files on disk
"""
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SOURCE = os.path.join(HERE, "..", "annots", "text.pdf")

SETUPS = [
    ("rc4-40.pdf", ["40"], "disable"),
    ("rc4-128.pdf", ["128", "--use-aes=n"], "disable"),
    ("aes-128.pdf", ["128", "--use-aes=y"], "disable"),
    ("aes-256.pdf", ["256"], "disable"),
    ("aes-256-objstm.pdf", ["256"], "generate"),
]


def build(name, enc, objstm):
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, name)
        cmd = (["qpdf", "--static-id", "--static-aes-iv", "--allow-weak-crypto",
                "--object-streams=" + objstm, "--stream-data=preserve",
                "--encrypt", "", "owner"] + enc + ["--", SOURCE, out])
        subprocess.run(cmd, check=True)
        with open(out, "rb") as f:
            return f.read()


def main():
    check = "--check" in sys.argv[1:]
    if shutil.which("qpdf") is None:
        print("qpdf not found: skipped")
        return 0
    bad = 0
    for name, enc, objstm in SETUPS:
        data = build(name, enc, objstm)
        path = os.path.join(HERE, name)
        if check and enc[0] == "256":
            r = subprocess.run(["qpdf", "--check", path], capture_output=True)
            if r.returncode != 0:
                print(f"{name}: qpdf --check failed")
                bad += 1
        elif check:
            with open(path, "rb") as f:
                if f.read() != data:
                    print(f"{name}: differs from a fresh build")
                    bad += 1
        else:
            with open(path, "wb") as f:
                f.write(data)
            print(f"wrote {name} ({len(data)} bytes)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
