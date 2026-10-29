#!/usr/bin/env python3
"""E8 > D7 x U(1) = Spin(14) x U(1): the frame-Higgs 40, the 10, the 64 and the families.

Root-level model of Lisi's embedding.  E8 > SO(10) x SU(4); the centralizer SU(4) = A3 of
SO(10) holds both the horizontal SU(3)_M of the chirality theorem (an A2) and the complexified
Lorentz algebra spin(1,3)_C = su(2) x su(2) (an orthogonal root pair D2).  Then

    248 = 91 + 1 + 64 + 64bar + 14 + 14,   so(14) = so(4) + so(10) + (4, 10),

with 14 = (4,1) + (1,10) and 64 = (2,1; 16) + (1,2; 16bar).  We verify these root counts, match
them with the Clifford model, and compute how SU(3)_M sits against spin(1,3).

All arithmetic is exact (Fractions).  The root data is a complex-algebra statement and does not
see the real form (Lorentz signature).

Requires sympy and numpy.
"""

from __future__ import annotations

import contextlib
import io
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product

import sympy as sp

import check_frame_higgs as cfh
import match_e8_spin113 as m5
from check_e6_su3_bridge import ALPHA, BETA
from e8 import e8_roots, require

Vec = tuple


def fr(x) -> F:
    x = sp.nsimplify(x)
    return F(int(x.p), int(x.q))


def vec_f(m) -> Vec:
    return tuple(fr(x) for x in m)


def dp(u: Vec, v: Vec) -> F:
    return sum((a * b for a, b in zip(u, v)), F(0))


def neg(u: Vec) -> Vec:
    return tuple(-x for x in u)


def add(u: Vec, v: Vec) -> Vec:
    return tuple(a + b for a, b in zip(u, v))


def scale(c, u: Vec) -> Vec:
    return tuple(F(c) * a for a in u)


def main() -> None:
    with contextlib.redirect_stdout(io.StringIO()):
        data = m5.main()
    m, frame = data["m"], data["frame"]
    fs = [vec_f(f) for f in next(iter(data["solutions"].values()))[2]]  # frame f_1..f_5 of the SO(10) span
    so10_part = data["so10_part"]

    roots = [tuple(F(x, 2) for x in r) for r in e8_roots()]
    zero = tuple(F(0) for _ in range(8))
    a0 = tuple(F(x, 2) for x in ALPHA)
    b0 = tuple(F(x, 2) for x in BETA)
    a2m = {a0, b0, add(a0, b0), neg(a0), neg(b0), neg(add(a0, b0))}  # SU(3)_M roots

    # --- E8 > SO(10) x SU(4) ----------------------------------------------------------------
    def v5(r: Vec) -> tuple:
        return tuple(dp(r, f) for f in fs)

    d5 = [r for r in roots if sum(c * c for c in v5(r)) == 2]
    a3 = [r for r in roots if all(c == 0 for c in v5(r))]
    ten_six = [r for r in roots if sum(c * c for c in v5(r)) == 1]
    spinors = [r for r in roots if sum(c * c for c in v5(r)) == F(5, 4)]
    require((len(d5), len(a3), len(ten_six), len(spinors)) == (40, 12, 60, 128), (len(d5), len(a3), len(ten_six), len(spinors)))
    require(set(a2m) <= set(a3), "SU(3)_M lies in the centralizer SU(4) of SO(10)")
    print("PASS  E8 > SO(10) x SU(4): 240 = 40 (45) + 12 (15) + 60 (10,6) + 128 (16,4)+(16bar,4bar); "
          "SU(3)_M (6 roots) lies in the SU(4) = A3 (12 roots)")

    # --- the 27: 1 + 16 + 10 and the E6 U(1) charge ---------------------------------------------------
    w0 = vec_f(data["w0"])
    sets = {}
    for name in ("1", "16", "10"):
        sets[name] = {tuple(vec_f(so10_part(r["w"]))) for r in m.families[name]}
    require(sets["1"] == {zero}, "the singlet has no SO(10) weight")
    fvecs = set(fs) | {neg(f) for f in fs}
    require(sets["10"] == fvecs, "the 10 of the 27 has weights +-f_i")
    charges = {name: {dp(vec_f(r["w"]), w0) / dp(w0, w0) for r in m.families[name]} for name in ("1", "16", "10")}
    require(charges == {"1": {F(1)}, "16": {F(1, 4)}, "10": {F(-1, 2)}}, charges)
    print("PASS  the 10 of the 27 has SO(10) weights exactly +-f_i, i = 1..5 (the vector 10, the same isometry that "
          "carries the 16); E6 U(1) charges 4 : 1 : -2 for 1 : 16 : 10")

    # --- D2 candidates inside A3 --------------------------------------------------------------------
    classes = []
    seen = set()
    for r in a3:
        key = frozenset({r, neg(r)})
        if key not in seen:
            seen.add(key)
            classes.append(sorted(key))
    pairs = [(c1, c2) for i, c1 in enumerate(classes) for c2 in classes[i + 1:] if dp(c1[0], c2[0]) == 0]
    require(len(classes) == 6 and len(pairs) == 3, (len(classes), len(pairs)))
    shared = [sum(1 for c in pair if c[0] in a2m) for pair in pairs]
    require(shared == [1, 1, 1], shared)
    print("PASS  A3 has 3 orthogonal root pairs (candidates for spin(1,3)_C = su(2) x su(2)); every one shares "
          "exactly one su(2) with SU(3)_M and has the other su(2) outside it")

    # Clifford side weights of the complex 64 over the seven planes.
    w7 = {tuple(F(int(round(2 * x)), 2) for x in w) for w in cfh.d7_weights(frame)}
    require(len(w7) == 64, len(w7))
    s16 = {tuple(vec_f(so10_part(r["w"]))) for r in m.families["16"]}

    successes = []
    reported = False
    for pidx, (c1, c2) in enumerate(pairs):
        ra, rb = c1[0], c2[0]
        ga, gb = scale(F(1, 2), add(ra, rb)), scale(F(1, 2), add(ra, neg(rb)))
        require(dp(ga, ga) == 1 and dp(gb, gb) == 1 and dp(ga, gb) == 0, "D2 frame g_a, g_b")
        rows = [list(map(lambda x: sp.Rational(x.numerator, x.denominator), v)) for v in (*fs, ra, rb)]
        ns = sp.Matrix(rows).nullspace()
        require(len(ns) == 1, len(ns))
        t = vec_f(ns[0])
        vals = [dp(r, t) for r in roots]
        cmax = max(abs(v) for v in vals)
        grade = {r: dp(r, t) / cmax for r in roots}
        cnt = Counter(grade.values())
        require(cnt == {F(0): 84, F(1): 14, F(-1): 14, F(1, 2): 64, F(-1, 2): 64}, cnt)

        d7 = [r for r in roots if grade[r] == 0]
        d2_part = lambda r: (dp(r, ga), dp(r, gb))
        frame_higgs = [r for r in d7 if any(v5(r)) and any(d2_part(r))]
        require(len(frame_higgs) == 40, len(frame_higgs))
        require(all(sorted(map(abs, v5(r))) == [0, 0, 0, 0, 1] and sorted(map(abs, d2_part(r))) == [0, 1]
                    for r in frame_higgs), "frame-Higgs roots are +-f_i +-g_a")
        combos = {v5(r) + d2_part(r) for r in frame_higgs}
        require(len(combos) == 40, "all 10 x 4 combinations +-f_i +-g_a occur exactly once")
        d5_in = [r for r in d7 if not any(d2_part(r))]
        d2_in = [r for r in d7 if not any(v5(r))]
        require((len(d5_in), len(d2_in)) == (40, 4), (len(d5_in), len(d2_in)))
        fourteen = [r for r in roots if grade[r] == 1]
        ten_part = [r for r in fourteen if any(v5(r))]
        four_part = [r for r in fourteen if not any(v5(r))]
        require((len(ten_part), len(four_part)) == (10, 4), (len(ten_part), len(four_part)))
        require(all(sorted(map(abs, v5(r))) == [0, 0, 0, 0, 1] and not any(d2_part(r)) for r in ten_part),
                "14 contains the 10: weights +-f_i")
        require(all(not any(v5(r)) and sorted(map(abs, d2_part(r))) == [0, 1] for r in four_part),
                "14 contains the 4: weights +-g_a")
        if not reported:
            print("PASS  E8 > D7 x U(1) from the A3 root pair: roots graded by the commuting U(1) as "
                  "84 (so(14)) + 2 x 64 (spinors) + 2 x 14 (vectors) = 240")
            print("PASS  so(14) = D5 (40) + D2 (4) + 40 frame-Higgs roots +-f_i +-g_a = (10, (2,2)); "
                  "each 14 = (1,10) + (4,1): the Higgs 10 and the frame 4")
            reported = True

        # --- match the Clifford 64 against the two E8 64's -------------------------------------
        for (x, y), s6, s7 in product(((ga, gb), (gb, ga)), (1, -1), (1, -1)):
            x6, x7 = scale(s6, x), scale(s7, y)
            for c in (F(1, 2), F(-1, 2)):
                e8w = {v5(r) + (dp(r, x6), dp(r, x7)) for r in roots if grade[r] == c}
                if e8w == w7:
                    lorentz_a = add(x6, x7)  # image of e6 + e7, the su(2)_a acting on W
                    in_a2m = lorentz_a in a2m
                    successes.append((pidx, (s6, s7, x is ga), c, in_a2m, grade, x6, x7))
    require(successes, "the Clifford 64 does not match an E8 64 for any root-pair choice")
    print(f"PASS  the Clifford complex 64 (64 weights (+-1/2)^7) equals the weight set of an E8 64 in "
          f"{len(successes)} of 48 choices of (D2 pair, e6/e7 assignment, 64 vs 64bar)")

    # --- families: where do the three 16's of (27, 3) sit? ---------------------------------------
    labels_of = lambda r: (int(dp(r, a0)), int(dp(r, b0)))
    sixteen_roots = [r for r in roots if tuple(sum((c * f[k] for c, f in zip(v5(r), fs)), F(0)) for k in range(8)) in s16]
    require(len(sixteen_roots) == 64, len(sixteen_roots))
    lab_count = Counter(labels_of(r) for r in sixteen_roots)
    families = [(1, 0), (-1, 1), (0, -1)]
    require(lab_count == {(1, 0): 16, (-1, 1): 16, (0, -1): 16, (0, 0): 16}, lab_count)
    print("PASS  the 64 roots whose SO(10) part is in the 16: 16 each over the three weights of the 3 of SU(3)_M "
          "(the three families of 27 x 3) and 16 over the SU(3)_M singlet (the 16 inside the E6 adjoint)")

    by_case = defaultdict(list)
    for pidx, _, c, in_a2m, grade, x6, x7 in successes:
        by_case[in_a2m].append((grade, c))
    summary = {}
    for in_a2m, items in by_case.items():
        tables = set()
        for grade, c in items:
            row = []
            for lab in families + [(0, 0)]:
                phys = sum(1 for r in sixteen_roots if labels_of(r) == lab and grade[r] == c)
                mirror = sum(1 for r in sixteen_roots if labels_of(r) == lab and grade[r] == -c)
                require(phys + mirror == 16, (lab, phys, mirror))
                row.append((phys, mirror))
            tables.add(tuple(row))
        # The three root-pair choices are permuted by the Weyl group S3 of SU(3)_M, which permutes the
        # three family rows: compare the tables up to that permutation.
        canon = {tuple(sorted(t[:3])) + (t[3],) for t in tables}
        require(len(canon) == 1, tables)
        summary[in_a2m] = next(iter(canon))
    print("INFO  rows = SU(3)_M weight of the 16 (families 1,2,3 and the singlet); entries = "
          "(# in the physical Weyl 64, # in the 64bar), 16 roots each")
    for in_a2m in sorted(summary):
        row = summary[in_a2m]
        fam_in = sum(1 for (p, _) in row[:3] if p == 16)
        require(all(p in (0, 16) for p, _ in row), row)
        which = "su(2)_a (acting on the physical Weyl spinor) is the one inside SU(3)_M" if in_a2m else \
                "su(2)_b (the other factor) is the one inside SU(3)_M"
        print(f"INFO  {which}: families {row[:3]}, singlet {row[3]}  ->  {fam_in} of the three families in the physical 64")
    require(all(sum(1 for (p, _) in r[:3] if p == 16) <= 2 for r in summary.values()), summary)
    print("PASS  in every consistent embedding at most 2 of the 3 families (16 in (27,3)) lie in the "
          "physical Majorana-Weyl 64 of Spin(11,3); the rest lie in the 64bar")


if __name__ == "__main__":
    main()
