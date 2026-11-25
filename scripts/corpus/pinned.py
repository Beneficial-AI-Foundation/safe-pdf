#!/usr/bin/env python3
"""Pinned corpus subset (task 12.6).  Run as:  python3 -I scripts/corpus/pinned.py [...]

The subset is scripts/corpus/pinned.txt: manifest ids, one per line.  Every id must exist in
corpus/manifest.json, which pins the file by URL, size and SHA-256.

  (no args)       verify every pinned file present in corpus/files/ (size + SHA-256);
                  exit 1 when one is missing or mismatched.
  --fetch         first download the missing pinned files (fetch.py's downloader: temp
                  name, verified, then renamed; mismatches deleted), then verify.
  --stage DIR     after verifying, create DIR and symlink each pinned file into it, so a
                  single glob selects the subset (run.py --files 'DIR/*.pdf').
  --paths         after verifying, print the pinned files' paths, one per line (for
                  scripts taking FILE arguments, e.g. scripts/viewer-corpus.sh).

Stdlib only.  Downloaded bytes are only hashed, never parsed or executed.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)  # our own fetch.py (python3 -I leaves the script dir off sys.path)
import fetch  # noqa: E402

PINNED = os.path.join(HERE, "pinned.txt")


def pinned_ids(path=PINNED):
    """Ids listed in pinned.txt, comments and blank lines dropped, order kept."""
    ids = []
    with open(path) as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if line:
                ids.append(line)
    return ids


def main(argv):
    do_fetch = "--fetch" in argv
    show_paths = "--paths" in argv
    stage = None
    if "--stage" in argv:
        i = argv.index("--stage")
        if i + 1 >= len(argv):
            print("pinned: --stage needs a directory", file=sys.stderr)
            return 2
        stage = argv[i + 1]
    known = {"--fetch", "--paths", "--stage"}
    for a in argv:
        if a.startswith("-") and a not in known:
            print("pinned: unknown option %s" % a, file=sys.stderr)
            return 2

    entries = {e["id"]: e for e in fetch.load()["entries"]}
    ids = pinned_ids()
    unknown = [i for i in ids if i not in entries]
    if unknown:
        print("pinned: ids not in corpus/manifest.json: %s" % ", ".join(unknown), file=sys.stderr)
        return 1
    log = sys.stderr if show_paths else sys.stdout
    problems, paths = [], []
    for i in ids:
        e = entries[i]
        final = os.path.join(fetch.FILES, fetch.safe_name(i))
        tmp = None
        if not os.path.exists(final):
            if not do_fetch:
                problems.append((i, "missing (run with --fetch)"))
                continue
            print("fetch  %s" % e["url"], file=log, flush=True)
            try:
                tmp = fetch.fetch_one(e["url"], final)
            except Exception as ex:  # report every failure, keep going
                problems.append((i, "download failed: %s" % ex))
                continue
        path = tmp or final
        size, digest = os.path.getsize(path), fetch.sha256_of(path)
        if size != e["size"] or digest != e["sha256"]:
            os.unlink(path)
            problems.append((i, "MISMATCH size %d/%d sha %s.. (deleted)" % (size, e["size"], digest[:12])))
            continue
        if tmp:
            os.replace(tmp, final)
        paths.append(final)
    print("pinned: %d ids, %d verified, %d problems" % (len(ids), len(paths), len(problems)), file=log)
    for i, p in problems:
        print("PROBLEM %s: %s" % (i, p), file=log)
    if problems:
        return 1
    if stage:
        os.makedirs(stage, exist_ok=True)
        for p in paths:
            link = os.path.join(stage, os.path.basename(p))
            if os.path.lexists(link):
                os.unlink(link)
            os.symlink(os.path.abspath(p), link)
        print("pinned: staged %d files in %s" % (len(paths), stage), file=log)
    if show_paths:
        for p in paths:
            print(os.path.relpath(p, fetch.ROOT))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
