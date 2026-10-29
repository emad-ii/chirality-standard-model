#!/usr/bin/env python3
"""Match the Clifford 64 of Spin(11,3) to the E8 weights of the 27.

Two independent constructions of one Standard Model generation:

* E8 side (sm_charges.py): the 16 weights of the 27 under SO(10) x U(1), with
  SU(3) (roots a, b), SU(2)_L (root g) and hypercharge vector Y read off roots.
* Clifford side (spin113.py): the 16 Cartan weights (+-1/2)^5 of the
  left-handed space W of the 64, with SU(3) roots e_i - e_j (i,j = 1..3), the
  su(2) roots e4 +- e5 and Y = kappa (e1+e2+e3) + sigma (e4 - e5)/2.

We look for an orthonormal frame f_1..f_5 of the span of the SO(10) roots in
E8 (an exact isometry e_i -> f_i) such that

  1. the 40 roots +-f_i +-f_j are exactly the 40 SO(10) roots,
  2. the 16 Clifford weights map onto the 16 E8 weights of the 27,
  3. e_i - e_j (i,j <= 3) map to the SU(3) roots of E8 and the weak su(2) root
     maps to +-g,
  4. the Clifford hypercharge vector maps to the E8 hypercharge vector.

Requires sympy and numpy.
"""

from __future__ import annotations

import contextlib
import io
from collections import Counter

import sympy as sp

import sm_charges
import spin113
from check_e6_su3_bridge import ALPHA, BETA
from e8 import require

Rat = sp.Rational


def dp(u: sp.Matrix, v: sp.Matrix):
    return sp.nsimplify((u.T * v)[0])


def tup(v: sp.Matrix) -> tuple:
    return tuple(sp.nsimplify(x) for x in v)


def main() -> dict:
    with contextlib.redirect_stdout(io.StringIO()):
        frame = spin113.main()
    m = sm_charges.build()
    a, b, g, w0, ys = m.a, m.b, m.g, m.w0, m.Y
    a0 = sp.Matrix([Rat(x, 2) for x in ALPHA])
    b0 = sp.Matrix([Rat(x, 2) for x in BETA])

    d5 = [sp.Matrix([Rat(x.numerator, x.denominator) for x in r]) for r in m.d5_roots]
    d5_set = {tup(r) for r in d5}
    require(len(d5_set) == 40, len(d5_set))
    # The 16 weights of the 27 have <w, w0> = 1/3; their SO(10) weight is the projection
    # onto the span of the SO(10) roots (orthogonal to w0), which is what the Cartan
    # weights of the Clifford spinor correspond to.
    def so10_part(w: sp.Matrix) -> sp.Matrix:
        return w - w0 * (dp(w, w0) / dp(w0, w0))

    e8_16 = {tup(so10_part(r["w"])): r for r in m.families["16"]}
    require(len(e8_16) == 16, len(e8_16))

    a2 = [a, b, a + b, -a, -b, -(a + b)]
    h_roots = [r for r in d5 if dp(r, a) == 0 and dp(r, b) == 0 and dp(r, g) == 0]
    require(len(h_roots) == 2, len(h_roots))  # the roots +-h of the second su(2)
    print("INFO  E8 side: SU(3) = {a, b}, SU(2) root g, and the commuting root pair +-h:", len(h_roots), "roots")

    # --- Clifford side data ----------------------------------------------------
    cw = [tuple(Rat(int(round(2 * x)), 2) for x in w) for w in frame.weights]
    require(len(set(cw)) == 16, "16 Clifford weights")
    if frame.weak == "L":
        u_weak, u_r = (0, 0, 0, 1, 1), (0, 0, 0, 1, -1)
    else:
        u_weak, u_r = (0, 0, 0, 1, -1), (0, 0, 0, 1, 1)
    kappa, sigma = Rat(frame.kappa).limit_denominator(3), frame.sigma
    require(kappa == Rat(1, 3), kappa)
    y_c = [kappa, kappa, kappa, sigma * Rat(u_r[3], 2), sigma * Rat(u_r[4], 2)]

    # --- search for the frame --------------------------------------------------
    solutions = {}
    for h in h_roots:
        cons = sp.Matrix.vstack(w0.T, a0.T, b0.T, a.T, b.T, g.T, h.T)
        ns = cons.nullspace()
        require(len(ns) == 1, len(ns))
        t = ns[0]
        s0 = sp.nsimplify(sp.sqrt(Rat(3) / dp(t, t))) * t
        s0 = s0.applyfunc(sp.nsimplify)
        if not all(x.is_rational for x in s0):
            continue
        for s_sign in (1, -1):
            s_vec = s_sign * s0
            for r1 in a2:
                for r2 in a2:
                    if dp(r1, r2) != -1:
                        continue
                    for eps in (1, -1):
                        p, q = eps * g, h
                        if frame.weak == "L":
                            f4, f5 = (p + q) / 2, (p - q) / 2
                        else:
                            f4, f5 = (q + p) / 2, (q - p) / 2
                        f1 = (s_vec + 2 * r1 + r2) / 3
                        f2 = (s_vec - r1 + r2) / 3
                        f3 = (s_vec - r1 - 2 * r2) / 3
                        fs = [f1, f2, f3, f4, f5]
                        if any(dp(fs[i], fs[j]) != (1 if i == j else 0) for i in range(5) for j in range(5)):
                            continue
                        roots = {tup(si * fs[i] + sj * fs[j]) for i in range(5) for j in range(i + 1, 5)
                                 for si in (1, -1) for sj in (1, -1)}
                        if roots != d5_set:
                            continue
                        image = {}
                        for w in cw:
                            v = sum((w[i] * fs[i] for i in range(5)), sp.zeros(8, 1))
                            image[w] = tup(v)
                        if set(image.values()) != set(e8_16):
                            continue
                        y_image = sum((y_c[i] * fs[i] for i in range(5)), sp.zeros(8, 1))
                        if tup(y_image) != tup(ys):
                            continue
                        key = tuple(tup(f) for f in fs)
                        solutions[key] = (eps, image, fs)
    require(solutions, "no isometry matches the Clifford weights, SU(3), SU(2) and Y to the E8 data")
    print(f"PASS  found {len(solutions)} exact isometries e_i -> f_i of the SO(10) weight space that send the "
          "40 SO(10) roots to the 40 E8 roots, the 16 Clifford weights to the 16 E8 weights of the 27, "
          "SU(3) to a, b, SU(2)_L to g, and Y to the E8 hypercharge vector")

    # The solutions must differ only by Weyl-group symmetries of the data: the six permutations
    # of the three color planes (Weyl group S3 of SU(3)) times (f4, f5) -> (-f5, -f4), the Weyl
    # reflection of su(2)_L in its root e4 + e5.
    ref = next(iter(solutions))
    relations = set()
    for key in solutions:
        row = []
        for i in range(5):
            matches = [j for j in range(5) if key[i] == ref[j]]
            if matches:
                row.append(("+", matches[0]))
            else:
                negs = [j for j in range(5) if key[i] == tuple(-x for x in ref[j])]
                require(len(negs) == 1, "frame vector not related to the reference by a signed permutation")
                row.append(("-", negs[0]))
        relations.add(tuple(row))
    expected_relations = set()
    from itertools import permutations as _perms
    for perm in _perms(range(3)):
        expected_relations.add(tuple(("+", perm[i]) for i in range(3)) + (("+", 3), ("+", 4)))
        # reflection in the su(2)_L root e4 + e5: (e4, e5) -> (-e5, -e4)
        expected_relations.add(tuple(("+", perm[i]) for i in range(3)) + (("-", 4), ("-", 3)))
    require(relations == expected_relations and len(solutions) == 12, (len(solutions), relations))
    print("PASS  the 12 solutions are exactly S3 (permuting the three color planes) x Z2 "
          "(Weyl reflection of su(2)_L): the identification is canonical up to Weyl symmetries")

    # --- per-weight comparison for the first solution -----------------------------
    eps, image, fs = next(iter(solutions.values()))
    colored_doublet_sign = None
    for w in cw:
        if (w[0] == w[1] == w[2]):
            continue
        if sum(w[i] * u_weak[i] for i in range(5)) != 0:
            colored_doublet_sign = sp.sign(w[0] + w[1] + w[2])
            break
    mism = 0
    for w in cw:
        rec = e8_16[image[w]]
        t3_c = sum(w[i] * u_weak[i] for i in range(5)) / 2
        y_cw = sum(w[i] * y_c[i] for i in range(5))
        colorless = (w[0] == w[1] == w[2])
        if colorless:
            color = "1"
        else:
            color = "3" if sp.sign(w[0] + w[1] + w[2]) == colored_doublet_sign else "3b"
        ok = (
            rec["color"] == color
            and (rec["su2"] == 2) == (t3_c != 0)
            and rec["T3"] == eps * t3_c
            and rec["Y"] == y_cw
        )
        mism += 0 if ok else 1
    require(mism == 0, mism)
    print("PASS  all 16 weights agree term by term: color class, weak doublet, T3 (up to the SU(2) Weyl sign) "
          "and hypercharge of each Clifford weight equal those of the E8 weight it maps to")

    classes = Counter((r["color"], r["su2"], r["Y"]) for r in (e8_16[v] for v in image.values()))
    require(dict(classes) == sm_charges.SM_16, classes)
    print("PASS  the image is the Standard Model content of the 16 (see sm_charges.py): "
          "Q_L, u^c, d^c, L, e^c, nu^c")

    # Multiplicity bookkeeping.
    print("INFO  Clifford side: each of the 16 weights appears twice (the two spin states of spin(1,3)); "
          "the E8 16 has no spin label, so E8 weight x spin doublet = the 32 complex dims of W")
    return {"m": m, "frame": frame, "solutions": solutions, "e8_16": e8_16, "so10_part": so10_part,
            "d5": d5, "cw": cw, "w0": w0}


if __name__ == "__main__":
    main()
