#!/usr/bin/env python3
"""Exact (sympy) checks of the Section-2 building blocks of Lisi's arXiv:1006.4908.

Covers: the Pauli identity, the su(2) bracket, Dirac matrices in the Weyl
representation with the (1,3) metric, chirality projectors P_L and P_R,
spin(1,3) = sl(2,C) acting on a Weyl spinor, and the hypercharge generator of
one generation.

Provenance: the su(2) bracket and Pauli identity were read from the paper text;
the form of the hypercharge generator, Y = (1/2) sigma_3 P_R + (1/2) diag(-1,1/3,1/3,1/3),
was relayed by a tool summary of the paper and not read verbatim.  That it yields
exactly the Standard Model hypercharges is a consistency check on that transcription.
The matrices below are the standard Weyl representation; the paper's overall
signs and phases may differ, which does not affect any statement checked here.

Requires sympy.
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations

import sympy as sp
from sympy import I, Matrix, Rational, eye, kronecker_product as kron, sqrt, zeros

from e8 import require

sig = [Matrix([[0, 1], [1, 0]]), Matrix([[0, -I], [I, 0]]), Matrix([[1, 0], [0, -1]])]
ETA = sp.diag(1, -1, -1, -1)


def eps(i: int, j: int, k: int) -> int:
    return sp.LeviCivita(i, j, k)


def comm(a: Matrix, b: Matrix) -> Matrix:
    return a * b - b * a


def main() -> None:
    # --- Pauli identity (2.1) and su(2) bracket ----------------------------
    for i in range(3):
        for j in range(3):
            rhs = (1 if i == j else 0) * eye(2) + I * sum((eps(i + 1, j + 1, k + 1) * sig[k] for k in range(3)), zeros(2))
            require(sp.simplify(sig[i] * sig[j] - rhs) == zeros(2), (i, j))
            lhs = comm(I * sig[i] / 2, I * sig[j] / 2)
            rhs2 = -sum((eps(i + 1, j + 1, k + 1) * I * sig[k] / 2 for k in range(3)), zeros(2))
            require(sp.simplify(lhs - rhs2) == zeros(2), (i, j))
    print("PASS  sigma_I sigma_J = delta + i eps sigma_K;  [(i/2)sigma_I, (i/2)sigma_J] = -eps_IJ^K (i/2)sigma_K")

    # --- Dirac matrices, Weyl representation --------------------------------
    z2, i2 = zeros(2), eye(2)
    g0 = Matrix.vstack(Matrix.hstack(z2, i2), Matrix.hstack(i2, z2))
    gk = [Matrix.vstack(Matrix.hstack(z2, s), Matrix.hstack(-s, z2)) for s in sig]
    gam = [g0] + gk
    for m in range(4):
        for n in range(4):
            ac = gam[m] * gam[n] + gam[n] * gam[m]
            require(ac == 2 * ETA[m, n] * eye(4), (m, n))
    print("PASS  Weyl-representation gamma matrices: {g^m, g^n} = 2 eta^mn, eta = diag(+,-,-,-)")

    # --- chirality ---------------------------------------------------------------
    ps = gam[0] * gam[1] * gam[2] * gam[3]
    require(ps * ps == -eye(4), "pseudoscalar squares to -1")
    g5 = I * ps
    require(g5 == sp.diag(-1, -1, 1, 1) and g5 * g5 == eye(4), "gamma5 = diag(-1,-1,1,1)")
    PL, PR = (eye(4) - g5) / 2, (eye(4) + g5) / 2
    require(PL + PR == eye(4) and PL * PR == zeros(4) and PL * PL == PL and PR * PR == PR, "projectors")
    for g in gam:
        require(g5 * g == -g * g5, "gamma5 anticommutes with g^m")
    print("PASS  chirality: pseudoscalar^2 = -1, g5 = i g0 g1 g2 g3, P_L, P_R complementary projectors")

    # --- spin(1,3) = sl(2,C) on a Weyl spinor ----------------------------------
    gens = [Rational(1, 4) * comm(gam[a], gam[b]) for a, b in combinations(range(4), 2)]
    require(len(gens) == 6, "six generators")
    for g in gens:
        require(g * g5 == g5 * g, "generators preserve chirality")
    # closure: every commutator is a real combination of the six
    reals = lambda m: [sp.re(x) for x in m] + [sp.im(x) for x in m]
    basis = Matrix([reals(g) for g in gens])
    require(basis.rank() == 6, "six real-independent generators")
    for x, y in combinations(gens, 2):
        c = Matrix([reals(comm(x, y))])
        require(Matrix.vstack(basis, c).rank() == 6, "closure of spin(1,3)")
    block_L = [g[:2, :2] for g in gens]  # upper block: P_L half (g5 = -1)
    block_R = [g[2:, 2:] for g in gens]  # lower block: P_R half (g5 = +1)
    require(all(sp.simplify(b.trace()) == 0 for b in block_L + block_R), "traceless blocks: sl(2,C)")
    require(Matrix([reals(b) for b in block_L]).rank() == 6, "the 2x2 block of a Weyl spinor carries all 6 generators")
    require(Matrix([reals(b) for b in block_R]).rank() == 6, "so does the other chirality")
    print("PASS  spin(1,3): 6 generators close, preserve chirality, act as sl(2,C) on each Weyl spinor")

    # --- hypercharge of one generation ---------------------------------------
    lam15 = sqrt(Rational(3, 2)) * sp.diag(-1, Rational(1, 3), Rational(1, 3), Rational(1, 3))
    require(lam15.trace() == 0 and sp.simplify((lam15 * lam15).trace()) == 2, "Lambda_15 normalization")
    # states: (lepton, 3 colors) x (isospin up/down) x (chirality L, R)
    P_R = sp.diag(0, 1)
    ty = (kron(eye(4), sig[2], P_R) / 2 + sqrt(Rational(2, 3)) * kron(lam15, eye(2), eye(2)) / 2)
    y = [sp.nsimplify(sp.simplify(ty[i, i])) for i in range(16)]
    require(all(ty[i, j] == 0 for i in range(16) for j in range(16) if i != j), "Y diagonal")
    sm = Counter({Rational(1, 6): 6, Rational(-1, 2): 2, Rational(2, 3): 3, Rational(-1, 3): 3, Rational(-1): 1, Rational(0): 1})
    require(Counter(y) == sm, Counter(y))
    print("PASS  Y = (1/2) sigma_3 P_R + (1/2) diag(-1,1/3,1/3,1/3): quarks 1/6 (L), 2/3, -1/3 (R); "
          "leptons -1/2 (L), -1, 0 (R)")


if __name__ == "__main__":
    main()
