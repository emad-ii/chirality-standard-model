#!/usr/bin/env python3
"""Lisi's triality eigenspaces (arXiv:2609.12112, Section 6, eq. (6.1), (6.2), (9.2)) against the family Z3.

Lisi decomposes a Lie algebra under an order-3 automorphism Theta into eigenspaces g_0 + g_{+1} + g_{-1}
and calls g_0 + g_{+1} the Vinberg Theta-algebra.  For the compact forms the relevant statements are

  e6(-78)_Theta = [so(8) + u(1) + u(1)]_0 + [8v + 8s+ + 8s-]_{+1}                (dimensions 30 + 24 + 24)
  e8(-248)_Theta = [so(14) + u(1)_w]_0 + [14v_{+1} + 64s-_{-1/2}]_{+1}            (dimensions 92 + 78 + 78)
  e8 five-grading (6.2): 14_{-1} + 64_{+1/2} + [so(7,7) + so(1,1)] + 64_{-1/2} + 14_{+1}

Here the root-level content is reproduced: the eigenvalue of Theta on a root vector is a cube root of unity
determined by the U(1) charge w, namely omega^k with k = -2 w mod 3.  (The phases of individual root vectors
and the real forms are not seen by a root-level computation.)  We then ask something the paper does not: how
Lisi's Theta (fixed algebra D7 x U(1), eigenspaces 92/78/78) sits against the Z3 grading of the chirality
theorem (fixed algebra E6 x SU(3), eigenspaces 86/81/81).  Both are exp(2 pi i h) for h in the Cartan
subalgebra, so they commute and define a Z3 x Z3 grading of E8.

Requires sympy and numpy (through match_e8_spin113).
"""

from __future__ import annotations

import contextlib
import io
from collections import Counter, defaultdict
from fractions import Fraction as F

import sympy as sp

import match_e8_spin113 as m5
from check_distler_garibaldi import SIMPLE, ip
from check_e6_su3_bridge import ALPHA, BETA
from check_triality_d4d4 import triality_on_d4
from e8 import e8_roots, require
from match_e8_d7 import add, dp, neg, scale, vec_f


def bourbaki_coefficients(roots):
    s_inv = sp.Matrix(SIMPLE).inv()
    out = {}
    for r in roots:
        c = sp.Matrix([list(r)]) * s_inv
        require(all(x.is_integer for x in c), r)
        out[r] = tuple(int(x) for x in c)
    return out


def main() -> None:
    roots = e8_roots()
    rootset = set(roots)
    coef = bourbaki_coefficients(roots)

    # --- e8: the Z3 grading of the five-grading by omega_1 ---------------------------------------------
    grade2 = {r: coef[r][0] for r in roots}  # 2 w, w in {0, +-1/2, +-1}
    require(Counter(grade2.values()) == {0: 84, 1: 64, -1: 64, 2: 14, -2: 14}, Counter(grade2.values()))
    d7 = [r for r in roots if grade2[r] == 0]
    require(len(d7) == 2 * 7 * 6, len(d7))  # |D_n| = 2 n (n - 1)
    require(sp.Matrix([list(r) for r in d7]).rank() == 7, "the grade 0 roots span a 7-dimensional space")
    sub = sp.Matrix(7, 7, lambda i, j: ip(SIMPLE[i + 1], SIMPLE[j + 1]))  # alpha_2 .. alpha_8
    require(sub.det() == 4 and all(grade2[SIMPLE[i]] == 0 for i in range(1, 8)), "Cartan matrix of D7 has determinant 4")
    print("PASS  (6.2): the five-grading of e8 by w = omega_1/2 has root counts 14 + 64 + 84 + 64 + 14 "
          "(plus 8 Cartan in grade 0: so(14) + u(1)_w has dimension 92)")

    def k_of(g2: int) -> int:
        return (-g2) % 3  # Theta = exp(-4 pi i w / 3): eigenvalue omega^(-2 w) = omega^(-g2)

    dims = Counter({0: 8, 1: 0, 2: 0})
    for r in roots:
        dims[k_of(grade2[r])] += 1
    require(dims == {0: 92, 1: 78, 2: 78}, dims)
    plus = Counter(grade2[r] for r in roots if k_of(grade2[r]) == 1)
    require(plus == {2: 14, -1: 64}, plus)
    for r in roots:
        for s in roots:
            t = tuple(a + b for a, b in zip(r, s))
            if t in rootset:
                require(k_of(grade2[t]) == (k_of(grade2[r]) + k_of(grade2[s])) % 3, "Z3 grading")
    print("PASS  (6.1): Theta = exp(-4 pi i w / 3) is a Z3 grading of e8 with eigenspaces 92 + 78 + 78; "
          "g_{+1} = 14_{+1} + 64_{-1/2} (the vector and one spinor), g_{-1} is its conjugate; the fixed algebra is "
          "D7 + U(1) (the Cartan matrix of alpha_2 .. alpha_8 is that of D7)")

    # --- e6: the 8v + 8s + 8c eigenspace ---------------------------------------------------------------
    e6 = [r for r in roots if all(c == 0 for c in coef[r][6:]) ]  # nodes alpha_1 .. alpha_6
    require(len(e6) == 72, len(e6))
    d4 = [r for r in e6 if coef[r][0] == 0 and coef[r][5] == 0]
    require(len(d4) == 24, len(d4))
    cls = Counter((coef[r][0], coef[r][5]) for r in e6 if r not in set(d4))
    require(cls == {(1, 0): 8, (0, 1): 8, (1, 1): 8, (-1, 0): 8, (0, -1): 8, (-1, -1): 8}, cls)
    x_, y_ = F(1, 3), F(1, 3)

    def k6(r):
        e = (x_ * coef[r][0] + y_ * coef[r][5]) % 1
        return {F(0): 0, F(1, 3): 1, F(2, 3): 2}[e]

    d6 = Counter({0: 6, 1: 0, 2: 0})
    for r in e6:
        d6[k6(r)] += 1
    require(d6 == {0: 30, 1: 24, 2: 24}, d6)
    require({k6(r) for r in d4} == {0}, "D4 is fixed pointwise")
    require(Counter((coef[r][0], coef[r][5]) for r in e6 if k6(r) == 1) == {(1, 0): 8, (0, 1): 8, (-1, -1): 8}, "8 + 8 + 8")
    print("PASS  (6.1) for e6: Theta = exp(2 pi i (omega_1 + omega_6)/3) in e6 fixes D4 = so(8) pointwise and the two "
          "U(1)'s, and g_{+1} = 8 + 8 + 8 (the three 8-dimensional blocks); dimensions 30 + 24 + 24")

    # --- joint Z3 x Z3 grading with the family grading --------------------------------------------------
    with contextlib.redirect_stdout(io.StringIO()):
        data = m5.main()
    fs = [vec_f(f) for f in next(iter(data["solutions"].values()))[2]]
    rts = [tuple(F(x, 2) for x in r) for r in roots]
    a0 = tuple(F(x, 2) for x in ALPHA)
    b0 = tuple(F(x, 2) for x in BETA)
    a2m = {a0, b0, add(a0, b0), neg(a0), neg(b0), neg(add(a0, b0))}

    def chi(r) -> int:
        l1, l2 = dp(r, a0), dp(r, b0)
        require(l1.denominator == 1 and l2.denominator == 1, (l1, l2))
        return (int(l1) + 2 * int(l2)) % 3

    def v5(r):
        return tuple(dp(r, f) for f in fs)

    a3 = [r for r in rts if not any(v5(r))]
    cl, seen = [], set()
    for r in sorted(a3):
        key = frozenset({r, neg(r)})
        if key not in seen:
            seen.add(key)
            cl.append(sorted(key))
    pairs = [(c1, c2) for k, c1 in enumerate(cl) for c2 in cl[k + 1:] if dp(c1[0], c2[0]) == 0]
    require(len(pairs) == 3, len(pairs))

    tables, a2_actions = [], []
    for c1, c2 in pairs:
        ra, rb = c1[0], c2[0]
        rows = [[sp.Rational(x.numerator, x.denominator) for x in v] for v in (*fs, ra, rb)]
        ns = sp.Matrix(rows).nullspace()
        require(len(ns) == 1, len(ns))
        t = tuple(F(int(sp.nsimplify(x).p), int(sp.nsimplify(x).q)) for x in ns[0])
        cmax = max(abs(dp(r, t)) for r in rts)
        g2 = {r: int(2 * dp(r, t) / cmax) for r in rts}  # 2w in {0, +-1, +-2}
        require(Counter(g2.values()) == {0: 84, 1: 64, -1: 64, 2: 14, -2: 14}, Counter(g2.values()))
        table = Counter({(0, 0): 8})
        for r in rts:
            table[(chi(r), k_of(g2[r]))] += 1
        tables.append(table)
        a2_actions.append(Counter(k_of(g2[r]) for r in a2m))
    # the sign of Theta is a convention (t -> -t): compare up to k -> -k
    canon = []
    for tb in tables:
        flip = Counter({(c, (-k) % 3): v for (c, k), v in tb.items()})
        canon.append(min(tuple(sorted(tb.items())), tuple(sorted(flip.items()))))
    require(len(set(canon)) == 1, "the three Lorentz root pairs give the same joint table")
    table = tables[0]
    marg_chi = Counter()
    marg_k = Counter()
    for (c, k), v in table.items():
        marg_chi[c] += v
        marg_k[k] += v
    require(marg_chi == {0: 86, 1: 81, 2: 81} and marg_k == {0: 92, 1: 78, 2: 78}, (marg_chi, marg_k))
    print("PASS  Z3 x Z3: Theta (Lisi, D7 x U(1)) and the family grading chi (E6 x SU(3)) commute; joint dimensions "
          "(rows chi = 0,1,2; columns k = 0,1,2), the same for the three Lorentz root pairs up to k -> -k:")
    for c in range(3):
        print("      chi=%d: %s" % (c, "  ".join(f"{table[(c, k)]:3d}" for k in range(3))))
    for act in a2_actions:
        require(act == {0: 2, 1: 2, 2: 2}, act)
    chi0_k = {k: table[(0, k)] for k in range(3)}
    print("PASS  Theta does not fix SU(3)_M: its six roots have k = 0 (two roots, the su(2) shared with spin(1,3)_C) "
          "and k = +1, -1 (two each), so Theta acts on SU(3)_M as an inner element of order 3 with fixed algebra "
          "su(2) + u(1); on the chi = 0 part (E6 + SU(3)) the k-dimensions are %s" % chi0_k)

    # --- the Weyl-type triality T and its fixed roots ------------------------------------------------------
    def t_std(r):
        lo = triality_on_d4(tuple(F(v, 2) for v in r[:4]))
        hi = triality_on_d4(tuple(F(v, 2) for v in r[4:]))
        return tuple(int(2 * v) for v in lo + hi)

    fixed = [r for r in roots if t_std(r) == r]
    require(len(fixed) == 12 and (len(roots) - 12) % 3 == 0, len(fixed))
    orbits3 = (len(roots) - len(fixed)) // 3
    fixed_dim_t = 4 + orbits3 + len(fixed)
    omega_dim = 2 + orbits3
    require((fixed_dim_t, omega_dim) == (92, 78), (fixed_dim_t, omega_dim))
    print("INFO  the Weyl-type triality T of check_triality_d4d4.py permutes the 240 roots in 12 fixed roots and "
          f"{orbits3} three-cycles and fixes a 4-dimensional part of the Cartan subalgebra.  If a lift of T to the Lie "
          f"algebra acts with trivial phase on the 12 fixed root vectors (not checked: that needs structure "
          f"constants), its eigenspaces have dimensions {fixed_dim_t}, {omega_dim}, {omega_dim} = those of Theta; "
          "this is consistent with T and Theta being conjugate, but it is a dimension count, not a proof")


if __name__ == "__main__":
    main()
