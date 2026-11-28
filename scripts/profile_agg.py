#!/usr/bin/env python3
"""Aggregate scripts/profile.sh output (task 13.17). Stdlib only:
`python3 -I scripts/profile_agg.py OUT`.

A sample is one `=== SAMPLE` block holding every thread's backtrace. Threads whose innermost
frame is a wait (poll/futex/cond-wait/read/...) are idle and ignored; per sample the active
thread that has a project frame (else the first active thread) is the sample's stack. Samples
with no active thread are counted but not in the percentages. Reports, as shares of samples
with a stack:
  * bignum frame on the stack (lean_int_big_*, lean_nat_pow, __gmpz_*, lean_cstr_to_nat, ...);
  * allocator frame on the stack, and allocator as the leaf (malloc/free/realloc, lean_alloc*);
  * leaf functions; inclusive project functions (once per sample); the innermost project
    function above a bignum frame.
Lean symbols `lp_safe_x2dpdf_SafePdf_Core_Foo_bar...` are shown as `SafePdf.Core.Foo.bar`
(underscores in names are ambiguous, so this is approximate).
  --top N   rows per table (default 15)   --project PREFIX   (default SafePdf)
"""
import argparse, re, sys
from collections import Counter

IDLE = re.compile(r"^(poll|ppoll|epoll_wait|__?futex.*|futex.*|pthread_cond_.*wait.*|pthread_join|"
                  r"__pthread_.*|nanosleep|clock_nanosleep|select|__?libc_read|read|syscall|"
                  r"sem_wait|do_futex_wait.*|__GI_.*wait.*|__syscall_cancel.*|__futex_abstimed_wait.*)$")
BIG = re.compile(r"^(lean_int_big_|lean_nat_big_|lean_big_|lean_nat_pow|lean_int_pow|__gmpz_|"
                 r"__gmpn_|lean_cstr_to_nat|lean_nat_gcd|lean_int_gcd|lean_nat_log2|lean_mpz)")
ALLOC = re.compile(r"^(malloc|free|realloc|calloc|cfree|_int_malloc|_int_free|_int_realloc|"
                   r"malloc_consolidate|malloc_trim|sysmalloc|__libc_malloc|__libc_free|"
                   r"__libc_realloc|__libc_calloc|lean_alloc|lean_free|lean_dealloc|"
                   r"lean_del_core|lean_dec_ref_cold|lean_small_alloc|lean_small_free|"
                   r"lean_free_object|lean_realloc|tcache_)")
FRAME = re.compile(r"^#(\d+)\s+(?:0x[0-9a-f]+ in )?([A-Za-z_][\w.$@]*)")


def demangle(sym):
    """`lp_safe_x2dpdf_SafePdf_Core_Foo_bar_x3f` -> `SafePdf.Core.Foo.bar?` (also `l_` prefix)."""
    m = re.match(r"^lp_safe_x2dpdf_(.*)$", sym) or re.match(r"^l_(.*)$", sym)
    if not m:
        return sym
    s = re.sub(r"(___?(lambda|spec|boxed|closed|rarg|elambda|redArg)).*$", "", m.group(1))
    s = re.sub(r"(_\d+)+$", "", s)
    s = re.sub(r"_x([0-9a-f]{2})", lambda g: chr(int(g.group(1), 16)), s)
    return s.replace("_", ".")


def parse(path):
    samples, cur, thread = [], None, None
    with open(path, errors="replace") as f:
        for line in f:
            if line.startswith("=== SAMPLE"):
                cur = []; samples.append(cur); thread = None
            elif cur is None:
                continue
            elif line.startswith("Thread "):
                thread = []; cur.append(thread)
            else:
                m = FRAME.match(line)
                if m and thread is not None:
                    thread.append(m.group(2))
    return samples


def pick(sample, project):
    act = [t for t in sample if t and not IDLE.match(t[0])]
    if not act:
        return None
    proj = [t for t in act if any(demangle(fr).startswith(project) for fr in t)]
    return (proj or act)[0]


def pct(k, n):
    return f"{100.0 * k / n:5.1f}%"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file"); ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--project", default="SafePdf")
    a = ap.parse_args()
    samples = parse(a.file)
    chosen = [t for t in (pick(s, a.project) for s in samples) if t]
    n = len(chosen)
    print(f"{a.file}: {len(samples)} samples, {n} with an active thread stack")
    if not n:
        return 1
    leaf, incl, innerbig = Counter(), Counter(), Counter()
    big = alloc = leaf_alloc = 0
    for raw in chosen:
        syms = [demangle(r) for r in raw]
        leaf[syms[0]] += 1
        for fn in {x for x in syms if x.startswith(a.project)}:
            incl[fn] += 1
        bi = next((i for i, r in enumerate(raw) if BIG.match(r)), None)
        big += bi is not None
        alloc += any(ALLOC.match(r) for r in raw)
        leaf_alloc += bool(ALLOC.match(raw[0]))
        if bi is not None:
            inner = next((x for x in syms[bi:] if x.startswith(a.project)), None)
            innerbig[inner or "(no project frame within depth)"] += 1
    print(f"\nbignum frame on stack   : {big:5d} / {n} = {pct(big, n)}")
    print(f"allocator frame on stack: {alloc:5d} / {n} = {pct(alloc, n)}")
    print(f"leaf in allocator       : {leaf_alloc:5d} / {n} = {pct(leaf_alloc, n)}")
    for title, c in (("Leaf functions", leaf), (f"Inclusive {a.project} functions", incl),
                     ("Innermost project caller of a bignum frame", innerbig)):
        print(f"\n{title}")
        for k, v in c.most_common(a.top):
            print(f"  {pct(v, n)} {v:5d}  {k}")
    return 0


sys.exit(main())
