#!/usr/bin/env python3
"""Reproduce the explicit E8 computations of Distler and Garibaldi, arXiv:0905.2658.

"There is no 'Theory of Everything' inside E8" (Commun. Math. Phys. 298, 419).  The arguments there are
representation-theoretic; the parts that are finite computations in the complex root system of E8 are
reproduced here with exact arithmetic, using the paper's own Bourbaki numbering of the simple roots and its
defining vectors h.  What is NOT reproduced: the real-form arguments (signature of the Killing form,
transfers R(E8,C), Galois descent), which this root-level code cannot see.

Reproduced (section numbers are the paper's):

  4.4 / (5.5)  Dynkin index of sl2 with defining vector omega_i: 2 4 7 15 10 6 3 1
  Prop. 5.4    index 1 <-> h = omega_8, index 2 <-> h = omega_1 are the only sl2's with weights in {0,+-1,+-2}
  footnote 3   the -1 eigenspace of an order-2 element of E8 has dimension 128 or 112 (dimension no-go: 180 > 128)
  Ex. 5.3, Lemma 6.1, (6.4)  index 2 sl2: e8 = 1 x so13 + 2 x 64 + 3 x 1 + 3 x 13
  (6.3)        index 1 x index 1:  e8 = 3x1 + 1x3 + 1x1 x 66 + 2x1 x 32 + 1x2 x 32 + 2x2 x 12  (centralizer so12)
  (6.7)        index 2 x index 2, case (b): multiplicity table, centralizer sp4 x sp4 (dimension 20)
  (9.4)        index 1 x index 2: multiplicity table, centralizer A1 x B4 (dimension 39)

and, as a link to this directory's frame, the same decomposition (6.3) for each of the three orthogonal
root pairs of the SU(4) centralizing SO(10) (the candidates for spin(1,3)_C of match_e8_d7.py), together with
the SO(10) content of V_{2,1} = 32.

Requires sympy and numpy (through match_e8_spin113).
"""

from __future__ import annotations

import contextlib
import io
from collections import Counter
from fractions import Fraction as F

import sympy as sp

import match_e8_spin113 as m5
from e8 import dot, e8_roots, require
from match_e8_d7 import dp, neg, vec_f

# Bourbaki simple roots alpha_1 .. alpha_8 of E8, doubled coordinates (true = /2).
SIMPLE = [
    (1, -1, -1, -1, -1, -1, -1, 1),
    (2, 2, 0, 0, 0, 0, 0, 0),
    (-2, 2, 0, 0, 0, 0, 0, 0),
    (0, -2, 2, 0, 0, 0, 0, 0),
    (0, 0, -2, 2, 0, 0, 0, 0),
    (0, 0, 0, -2, 2, 0, 0, 0),
    (0, 0, 0, 0, -2, 2, 0, 0),
    (0, 0, 0, 0, 0, -2, 2, 0),
]


def ip(u, v) -> int:
    """True inner product of two doubled E8 vectors that pair integrally."""
    x = F(dot(u, v), 4)
    require(x.denominator == 1, (u, v, x))
    return int(x)


def decompose(weight_fns, roots):
    """Multiplicities of irreps (dims m, n, ...) of sl2^k from the weights of e8 = roots + 8 Cartan zeros."""
    k = len(weight_fns)
    n = Counter(tuple(f(r) for f in weight_fns) for r in roots)
    n[(0,) * k] += 8
    out = Counter()
    if k == 1:
        for (lam,), c in n.items():
            if lam >= 0:
                mult = c - n.get((lam + 2,), 0)
                if mult:
                    out[(lam + 1,)] = mult
        return out
    require(k == 2, k)
    for (lam, mu), c in n.items():
        if lam >= 0 and mu >= 0:
            mult = c - n.get((lam + 2, mu), 0) - n.get((lam, mu + 2), 0) + n.get((lam + 2, mu + 2), 0)
            if mult:
                out[(lam + 1, mu + 1)] = mult
    total = sum(m * a * b for (a, b), m in out.items())
    require(total == 248 and all(v > 0 for v in out.values()), (total, out))
    return out


def main() -> None:
    roots = e8_roots()
    s_mat = sp.Matrix(SIMPLE)
    s_inv = s_mat.inv()
    coef = {}
    for r in roots:
        c = sp.Matrix([list(r)]) * s_inv
        require(all(x.is_integer for x in c), r)
        coef[r] = tuple(int(x) for x in c)
    require(all(all(x >= 0 for x in c) or all(x <= 0 for x in c) for c in coef.values()), "Bourbaki simple system")
    positive = [r for r in roots if all(x >= 0 for x in coef[r])]
    require(len(positive) == 120, len(positive))
    cartan = sp.Matrix(8, 8, lambda i, j: ip(SIMPLE[i], SIMPLE[j]))
    require(cartan.det() == 1, cartan.det())  # E8 is unimodular
    ci = cartan.inv()

    def vec(x):
        """Doubled-coordinate vector of sum_i x_i alpha_i."""
        return tuple(sum(int(x[i]) * SIMPLE[i][j] for i in range(8)) for j in range(8))

    omega = [vec([int(ci[i, j]) for j in range(8)]) for i in range(8)]  # omega_i = sum_j (A^-1)_ij alpha_j
    require(all(ip(omega[i], SIMPLE[j]) == (1 if i == j else 0) for i in range(8) for j in range(8)), "fundamental weights")
    theta = next(r for r in roots if coef[r] == (2, 3, 4, 6, 5, 4, 3, 2))
    require(theta == omega[7], "the highest root is omega_8")

    def index(h):
        return F(ip(h, h), 2)

    # --- (5.5): index of sl2 with defining vector omega_i, two ways --------------------------------
    expected55 = {1: 2, 2: 4, 3: 7, 4: 15, 5: 10, 6: 6, 7: 3, 8: 1}
    by_formula = {i + 1: index(omega[i]) for i in range(8)}
    by_roots = {i + 1: F(sum(coef[r][i] ** 2 for r in positive), 60) for i in range(8)}  # (4.4): 1/(2 m^v) sum alpha(h)^2
    require(by_formula == by_roots == {k: F(v) for k, v in expected55.items()}, (by_formula, by_roots))
    print("PASS  (5.5) the Dynkin index of the sl2 with defining vector omega_i is 2 4 7 15 10 6 3 1 "
          "(i = 1..8, Bourbaki), by (h,h)/2 and by the root-sum formula (4.4)")

    # --- Prop. 5.4: index 1 and 2, weights in {0, +-1, +-2} ---------------------------------------------
    for i in range(8):
        wts = {coef[r][i] for r in roots}
        ok = wts <= {0, 1, -1, 2, -2}
        require(ok == (i in (0, 7)), (i + 1, sorted(wts)))
    for i in (0, 7):
        wts = {coef[r][i] for r in roots}
        require({1, -1} <= wts and not any(abs(w) not in (0, 1, 2) for w in wts), wts)
    print("PASS  Prop. 5.4: among the omega_i only omega_1 (index 2) and omega_8 (index 1) give weights in "
          "{0,+-1,+-2} on e8 (the highest root has coefficients 2 on alpha_1, alpha_8 and >= 3 elsewhere)")

    # --- dimension no-go (footnote 3 and section 3) -------------------------------------------------------
    odd = {i + 1: sum(1 for r in roots if coef[r][i] % 2) for i in (0, 7)}
    require(odd == {1: 128, 8: 112}, odd)
    need = 2 * 2 * 3 * 15
    require(need == 180 and need > max(odd.values()), need)
    print("PASS  the two order-2 inner automorphisms of E8 (omega_1 mod 2 with fixed D8, omega_8 mod 2 with fixed "
          "E7 + A1) have -1 eigenspaces of dimension 128 and 112; three generations of 15 left- and right-handed "
          "fermions need 2 x 2 x 45 = 180 > 128 linearly independent weight vectors")

    # --- the index 1 sl2 and E7 ---------------------------------------------------------------------------
    e7 = [r for r in roots if dot(r, theta) == 0]
    require(len(e7) == 126, len(e7))
    theta2 = max((r for r in e7 if all(x >= 0 for x in coef[r])), key=lambda r: sum(coef[r]))
    require(sum(1 for r in e7 if sum(coef[r]) == sum(coef[theta2]) and all(x >= 0 for x in coef[r])) == 1, "unique highest root")
    require(ip(theta, theta2) == 0, "orthogonal")
    require(tuple(a + b for a, b in zip(theta, theta2)) == omega[0], "Example 5.3: the diagonal h is omega_1")
    print("PASS  Ex. 5.2/5.3: E7 = roots orthogonal to the highest root (126 roots); the diagonal of the sl2's of the "
          "highest roots of E8 and of E7 has defining vector theta + theta' = omega_1, index 2")

    # --- single sl2 of index 2 (Lemma 6.1, (6.4)) ----------------------------------------------------------
    h_0 = vec([0, 1, 1, 2, 2, 2, 2, 0])  # alpha_2 + alpha_3 + 2 alpha_4 + 2 alpha_5 + 2 alpha_6 + 2 alpha_7
    require(index(h_0) == 2, index(h_0))
    one = decompose([lambda r: ip(r, h_0)], roots)
    require(one == Counter({(1,): 78, (2,): 64, (3,): 14}), one)
    require(decompose([lambda r: coef[r][0]], roots) == one, "h_0 and omega_1 give the same decomposition")
    print("PASS  Lemma 6.1 / (6.4): the index 2 sl2 (h = alpha_2+alpha_3+2alpha_4+2alpha_5+2alpha_6+2alpha_7, "
          "conjugate to omega_1) has centralizer of dimension 78 (so13); e8 = 1x78 + 2x64 + 3x(1+13)")

    # --- (6.3): index 1 x index 1 --------------------------------------------------------------------------
    pair = decompose([lambda r: ip(r, theta), lambda r: ip(r, theta2)], roots)
    require(pair == Counter({(3, 1): 1, (1, 3): 1, (1, 1): 66, (2, 1): 32, (1, 2): 32, (2, 2): 12}), pair)
    d6 = [r for r in roots if ip(r, theta) == 0 and ip(r, theta2) == 0]
    require(len(d6) == 60, len(d6))
    print("PASS  (6.3) / Prop. 7.1: the pair of index 1 sl2's (theta, theta') has centralizer so12 (66 = 60 roots + 6 "
          "Cartan) and e8 = (3,1)+(1,3)+(1,1)x66+(2,1)x32+(1,2)x32+(2,2)x12")

    # --- (6.6), (6.7): index 2 x index 2 --------------------------------------------------------------------
    # The sl2 of Lemma 6.1 is spanned by X_{-alpha_8} + X_{theta_D7}, with theta_D7 the highest root of the D7
    # on alpha_2..alpha_8; h_0 = -alpha_8 + theta_D7.  A Cartan element commutes with it iff it is orthogonal
    # to alpha_8 and to theta_D7.  (6.6) gives the defining vectors of the two index 2 sl2's inside so13 as
    # explicit combinations of simple roots; we test that they commute with this sl2 and have index 2.
    # (The coroot table (6.2) was not used: our reading of it from the PDF image did not commute.)
    theta_d7 = vec([0, 1, 1, 2, 2, 2, 2, 1])
    require(theta_d7 in roots and tuple(a - b for a, b in zip(theta_d7, SIMPLE[7])) == h_0, "h_0 = -alpha_8 + theta_D7")
    require(ip(theta_d7, SIMPLE[7]) == 0, "alpha_8 and theta_D7 are orthogonal roots")
    h_a = vec([0, -1, 1, 0, 0, 0, 0, 0])  # (6.6)(a)
    h_b = vec([0, -2, -1, -2, -1, 0, 0, 0])  # (6.6)(b)
    for h in (h_a, h_b):
        require(index(h) == 2 and ip(h, h_0) == 0, "index 2 and orthogonal to h_0")
        require(ip(h, SIMPLE[7]) == 0 and ip(h, theta_d7) == 0, "commutes with the sl2 of Lemma 6.1")
    case_a = decompose([lambda r: ip(r, h_0), lambda r: ip(r, h_a)], roots)
    require(all((m + n) % 2 == 0 for (m, n) in case_a), case_a)
    case_b = decompose([lambda r: ip(r, h_0), lambda r: ip(r, h_b)], roots)
    table67 = {(1, 1): 20, (2, 1): 20, (3, 1): 6, (1, 2): 20, (2, 2): 16, (3, 2): 4, (1, 3): 6, (2, 3): 4, (3, 3): 0}
    require({k: case_b.get(k, 0) for k in table67} == table67 and set(case_b) <= set(table67), case_b)
    print("PASS  (6.6)/(6.7): both index 2 pairs of Lemma 6.5; case (a) has every m x n with m + n even; case (b) "
          "reproduces the table 20 20 6 / 20 16 4 / 6 4 0 (centralizer sp4 x sp4 of dimension 20; V_{2,3} = 4 "
          "!= 0 so (ToE2) fails)")

    # --- (9.4): index 1 x index 2 ---------------------------------------------------------------------------
    alpha2 = SIMPLE[1]
    require(ip(alpha2, h_0) == 0, "alpha_2 commutes with h_0")
    mixed = decompose([lambda r: ip(r, alpha2), lambda r: ip(r, h_0)], roots)
    table94 = {(1, 1): 39, (2, 1): 18, (3, 1): 1, (1, 2): 32, (2, 2): 16, (3, 2): 0, (1, 3): 10, (2, 3): 2, (3, 3): 0}
    require({k: mixed.get(k, 0) for k in table94} == table94 and set(mixed) <= set(table94), mixed)
    print("PASS  (9.4) the index 1 sl2 (the highest root of so13 = -alpha_2) with the index 2 sl2: multiplicities "
          "39 18 1 / 32 16 0 / 10 2 0; centralizer A1 x B4 of dimension 39")

    # --- the self-conjugacy criterion behind (ToE3) --------------------------------------------------------
    from itertools import product

    spinor = {t for t in product((F(1, 2), F(-1, 2)), repeat=5)}
    even = {t for t in spinor if sum(1 for x in t if x < 0) % 2 == 0}
    require(len(spinor) == 32 and {neg(t) for t in spinor} == spinor, "32 of Spin(11) is closed under w -> -w")
    require({neg(t) for t in even} == spinor - even, "the 16 of Spin(10) is mapped to the 16bar by w -> -w")
    print("PASS  the weights of the 32 of Spin(11) are closed under negation (-1 lies in the Weyl group of B5), while "
          "negation exchanges the 16 and 16bar of Spin(10): a generation inside S+ always comes with an anti-generation")

    # --- link to this directory's frame ----------------------------------------------------------------------
    with contextlib.redirect_stdout(io.StringIO()):
        data = m5.main()
    m = data["m"]
    fs = [vec_f(f) for f in next(iter(data["solutions"].values()))[2]]
    so10_part = data["so10_part"]
    rts = [tuple(F(x, 2) for x in r) for r in roots]

    def v5(r):
        return tuple(dp(r, f) for f in fs)

    a3 = [r for r in rts if not any(v5(r))]
    d5 = [r for r in rts if sum(c * c for c in v5(r)) == 2]
    cl, seen = [], set()
    for r in sorted(a3):
        key = frozenset({r, neg(r)})
        if key not in seen:
            seen.add(key)
            cl.append(sorted(key))
    pairs = [(c1, c2) for k, c1 in enumerate(cl) for c2 in cl[k + 1:] if dp(c1[0], c2[0]) == 0]
    require(len(pairs) == 3, len(pairs))
    s16 = {tuple(dp(vec_f(so10_part(r["w"])), f) for f in fs) for r in m.families["16"]}
    require(len(s16) == 16 and all(all(abs(x) == F(1, 2) for x in t) for t in s16), "the 16 in f-coordinates")
    overlaps = []
    for c1, c2 in pairs:
        ra, rb = c1[0], c2[0]
        dec = decompose([lambda r: int(dp(r, ra)), lambda r: int(dp(r, rb))], rts)
        require(dec == pair, dec)
        cen = [r for r in rts if dp(r, ra) == 0 and dp(r, rb) == 0]
        require(len(cen) == 60 and set(d5) <= set(cen), "D5 inside the D6 centralizer")
        v21 = [r for r in rts if (dp(r, ra), dp(r, rb)) == (1, 0)]
        require(len(v21) == 32, len(v21))
        spin = {v5(r) for r in v21}
        require(spin == spinor, "V_{2,1} restricted to SO(10) has the weights of all of 16 + 16bar")
        sub = {t for t in spin if sum(1 for x in t if x < 0) % 2 == 0}
        require(len(sub) == 16 and (s16 == sub or s16 == spin - sub), "the Standard Model 16 is one chirality class")
        overlaps.append(len(s16 & spin))
    require(set(overlaps) == {16}, overlaps)
    print("PASS  for each of the three orthogonal root pairs of the SU(4) centralizing SO(10): the decomposition (6.3) "
          "holds, the centralizer D6 = so12 contains SO(10), and V_{2,1} = 32 restricts to 16 + 16bar with the "
          "Standard Model 16 of match_e8_spin113.py as one half")


if __name__ == "__main__":
    main()
