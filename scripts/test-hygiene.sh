#!/usr/bin/env bash
# Self-test of the hygiene guard (task 13.9). Run from anywhere; needs `lake` and the pinned toolchain
# (the environment fixtures are compiled with `lake env lean`; it does not need the project built).
#   scripts/test-hygiene.sh [CASE...]
# Each directory scripts/hygiene-fixtures/<case>/ is a tree with one planted violation (or, for
# `clean`, none) and a file EXPECT of two lines: the kind, then the expected output text.
#   source  scripts/check-hygiene.sh --root TREE --no-axioms --no-envscan must fail, printing the text
#   env     the tree's modules are compiled, then `--no-axioms --no-source --lib` (the environment
#           scan alone, so it is the environment scan that must catch it) must fail, printing the text
#   pass    the full guard on the tree (source and environment scan) must succeed, printing the text
# The fixtures live outside SafePdf/ and Tests/, which the guard scans, so the real run never sees them.
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
fx="$here/hygiene-fixtures"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

cases=("$@")
if [ ${#cases[@]} -eq 0 ]; then
  for d in "$fx"/*/; do cases+=("$(basename "$d")"); done
fi

pass=0
fail=0
report() { # name ok? detail
  if [ "$2" = 1 ]; then pass=$((pass + 1)); echo "ok    $1"
  else fail=$((fail + 1)); echo "FAIL  $1: $3"; fi
}

# Compile every module of the tree `$1` into `$2` (a lib directory), in file order.
compile_tree() {
  local root="$1" lib="$2" f rel
  while IFS= read -r f; do
    rel="${f#"$root"/}"
    mkdir -p "$lib/$(dirname "$rel")"
    (cd "$repo" && lake env lean -R "$root" -o "$lib/${rel%.lean}.olean" "$f") >"$tmp/compile.log" 2>&1 \
      || { cat "$tmp/compile.log"; return 1; }
  done < <(find "$root/SafePdf" -name '*.lean' | sort)
}

for c in "${cases[@]}"; do
  d="$fx/$c"
  if [ ! -f "$d/EXPECT" ]; then report "$c" 0 "no EXPECT file"; continue; fi
  kind="$(sed -n 1p "$d/EXPECT")"
  want="$(sed -n 2p "$d/EXPECT")"
  case "$kind" in
    source)
      out="$("$here/check-hygiene.sh" --root "$d" --no-axioms --no-envscan 2>&1)"; rc=$?
      ;;
    env)
      rm -rf "$tmp/tree" "$tmp/lib"; cp -r "$d" "$tmp/tree"; mkdir -p "$tmp/lib"
      if ! compile_tree "$tmp/tree" "$tmp/lib"; then report "$c" 0 "fixture does not compile"; continue; fi
      out="$("$here/check-hygiene.sh" --root "$tmp/tree" --lib "$tmp/lib" --no-axioms --no-source 2>&1)"; rc=$?
      ;;
    pass)
      rm -rf "$tmp/tree" "$tmp/lib"; cp -r "$d" "$tmp/tree"; mkdir -p "$tmp/lib"
      if ! compile_tree "$tmp/tree" "$tmp/lib"; then report "$c" 0 "fixture does not compile"; continue; fi
      out="$("$here/check-hygiene.sh" --root "$tmp/tree" --lib "$tmp/lib" --no-axioms 2>&1)"; rc=$?
      ;;
    *) report "$c" 0 "unknown kind '$kind'"; continue ;;
  esac
  if [ "$kind" = pass ]; then
    if [ $rc -eq 0 ] && grep -qF -- "$want" <<<"$out"; then report "$c" 1 ""
    else report "$c" 0 "expected success with '$want', got exit $rc: $(tail -3 <<<"$out" | tr '\n' '|')"; fi
  else
    if [ $rc -ne 0 ] && grep -qF -- "$want" <<<"$out"; then report "$c" 1 ""
    else report "$c" 0 "expected failure with '$want', got exit $rc: $(tail -3 <<<"$out" | tr '\n' '|')"; fi
  fi
done

echo "test-hygiene: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
