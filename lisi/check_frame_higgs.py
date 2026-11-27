#!/usr/bin/env python3
"""The 40 frame-Higgs generators and the 10, on the Clifford side.

In spin(11,3) the 40 generators Gamma_aP (a = 1..4 spacetime, P = 5..14 spin(10))
form the complement of spin(1,3) + spin(10).  Checked here, from the matrices:

* F = span{Gamma_a Gamma_P} is *exactly* the tensor product 4 x 10 of the vector of
  spin(1,3) and the vector of spin(10), for all 6 + 45 generators of spin(1,3) + spin(10);
* the 10 has the Standard Model content (3,1)_{-1/3} + (3bar,1)_{1/3} + (1,2)_{1/2}
  + (1,2)_{-1/2}, with the colored triplets along directions 5..10 and the two Higgs
  doublets along directions 11..14;
* on the left-handed space W the boost is -I times the rotation (T_12 = -I T_34), so W is
  a Weyl spinor of sl(2,C);
* the complex 64 has 64 distinct weights (+-1/2)^7 over the seven-plane Cartan of so(14).

Requires numpy.
"""

from __future__ import annotations

import contextlib
import io
from collections import Counter

import numpy as np

import spin113
from spin113 import PLANES, commutator, joint_values, restrict
from e8 import require


def adjoint_matrix(x: np.ndarray, basis_mats: list[np.ndarray], n: int) -> np.ndarray:
    """Matrix of ad(x) on span(basis_mats), whose members are mutually orthogonal with tr(B^T B) = n."""
    stack = np.array([m.reshape(-1) for m in basis_mats])
    out = np.zeros((len(basis_mats), len(basis_mats)))
    for j, b in enumerate(basis_mats):
        c = commutator(x, b).reshape(-1)
        coef = stack @ c / n
        require(np.allclose(stack.T @ coef, c), "subspace is invariant")
        out[:, j] = coef
    return out


def d7_weights(frame: spin113.SMFrame) -> list[tuple[float, ...]]:
    """Weights (q1..q5; q6; q7) of the complexified 64 over the Cartan of so(14).

    q1..q5 are the five spin(10) planes; q6 = eigenvalue of T_12 (boost, real) and
    q7 from T_34 (rotation), so that (q6, q7) are the weights of the complexified Cartan
    (i T_12, T_34) of sl(2,C) in the e6, e7 coordinates of D2.
    """
    s, basis = frame.s, frame.basis
    R = lambda m: restrict(basis, m)
    ops = [-1j * R(s.T(*p)) for p in PLANES] + [R(s.T(1, 2)).astype(complex), -1j * R(s.T(3, 4))]
    out = []
    for w in joint_values(ops):
        r = tuple(round(2 * x) / 2 for x in w)
        require(all(abs(x - y) < 1e-8 and abs(abs(y) - 0.5) < 1e-8 for x, y in zip(w, r)), w)
        out.append(r)
    return out


def main(frame: spin113.SMFrame | None = None) -> None:
    if frame is None:
        with contextlib.redirect_stdout(io.StringIO()):
            frame = spin113.main()
    s, n = frame.s, frame.s.n

    # --- F = 4 x 10 exactly --------------------------------------------------------------
    idx_a, idx_p = range(1, 5), range(5, 15)
    fbasis = [s.biv[(a, p)] for a in idx_a for p in idx_p]  # ordering (a, P) -> 10 (a-1) + (P-5)
    v4 = [s.gam[a - 1] for a in idx_a]
    v10 = [s.gam[p - 1] for p in idx_p]
    for b in fbasis:
        require(np.array_equal(b @ b.T, np.eye(n)), "Gamma_aP are signed permutation matrices")
    gram = np.array([x.reshape(-1) for x in fbasis]) @ np.array([x.reshape(-1) for x in fbasis]).T
    require(np.array_equal(gram, n * np.eye(40)), "40 orthogonal generators")

    rho4, rho10 = {}, {}
    for key, m in s.biv.items():
        cls = s.klass(key)
        x = 0.5 * m
        if cls == "S":
            rho4[key] = adjoint_matrix(x, v4, n)
            f = adjoint_matrix(x, fbasis, n)
            require(np.allclose(f, np.kron(rho4[key], np.eye(10))), ("S", key))
        elif cls == "K":
            rho10[key] = adjoint_matrix(x, v10, n)
            f = adjoint_matrix(x, fbasis, n)
            require(np.allclose(f, np.kron(np.eye(4), rho10[key])), ("K", key))
    require(len(rho4) == 6 and len(rho10) == 45, (len(rho4), len(rho10)))
    require(np.linalg.matrix_rank(np.array([r.reshape(-1) for r in rho4.values()])) == 6, "4 is faithful")
    require(np.linalg.matrix_rank(np.array([r.reshape(-1) for r in rho10.values()])) == 45, "10 is faithful")
    print("PASS  the 40 frame-Higgs generators Gamma_aP = 4 x 10 exactly: ad(spin(1,3)) = rho_4 (x) 1 and "
          "ad(spin(10)) = 1 (x) rho_10, all 6 + 45 generators")

    # --- weights of the 4 and the 10 -------------------------------------------------------
    w4 = [np.linalg.eigvals(rho4[(1, 2)]), np.linalg.eigvals(rho4[(3, 4)])]
    require(sorted(np.round(w4[0].real, 6)) == [-1, 0, 0, 1] and np.allclose(w4[0].imag, 0), "boost eigenvalues")
    require(sorted(np.round(w4[1].imag, 6)) == [-1, 0, 0, 1] and np.allclose(w4[1].real, 0), "rotation eigenvalues")
    print("PASS  vector of spin(1,3): boost T_12 has eigenvalues +-1, 0, 0 and rotation T_34 has +-i, 0, 0: "
          "weights +-e6, +-e7 of so(4), i.e. (2,2) of su(2) x su(2)")

    def vec_rep(x: np.ndarray) -> np.ndarray:
        return adjoint_matrix(x, v10, n)

    ops_cart = [-1j * rho10[p] for p in PLANES]
    wv = Counter(tuple(round(x, 6) for x in w) for w in joint_values(ops_cart))
    expected_w = Counter()
    for i in range(5):
        for sgn in (1.0, -1.0):
            v = [0.0] * 5
            v[i] = sgn
            expected_w[tuple(v)] += 1
    clean = Counter({tuple(0.0 if abs(x) < 1e-9 else x for x in k): c for k, c in wv.items()})
    require(clean == expected_w, clean)
    print("PASS  vector of spin(10): the 10 weights are +-e_i, i = 1..5 (the Cartan of the five planes 56, 78, 9-10, 11-12, 13-14)")

    # --- Standard Model content of the 10 -----------------------------------------------------
    su3_v = [vec_rep(x) for x in frame.su3]
    weak_v = [vec_rep(x) for x in frame.weak_gens]
    y_v = vec_rep(frame.gy)
    cc = -sum(x @ x for x in su3_v)
    cw = -sum(x @ x for x in weak_v)
    require(np.allclose(np.diag(np.diag(cc)), cc) and np.allclose(np.diag(np.diag(cw)), cw),
            "color and weak Casimirs are diagonal in the Gamma_P basis")
    dc, dw = np.diag(cc), np.diag(cw)
    require(np.all(dc[:6] > 1e-6) and np.allclose(dc[6:], 0) and np.allclose(dc[:6], dc[0]), dc)
    require(np.allclose(dw[:6], 0) and np.allclose(dw[6:], 0.75), dw)
    print("PASS  the 10 = 6 colored directions (Gamma_5..Gamma_10: 3 + 3bar) + 4 weak-doublet directions "
          "(Gamma_11..Gamma_14: two complex doublets, the Higgs)")
    got = Counter(
        (int(v[0] > 1e-6), int(v[1] > 1e-6), int(round(6 * v[2])))
        for v in joint_values([cc.astype(complex), cw.astype(complex), -1j * y_v])
    )
    expected = Counter({(1, 0, -2): 3, (1, 0, 2): 3, (0, 1, 3): 2, (0, 1, -3): 2})
    require(got == expected, got)
    print("PASS  complexified 10 = (3,1)_{-1/3} + (3bar,1)_{1/3} + (1,2)_{1/2} + (1,2)_{-1/2}, "
          "the Higgs doublets H_u, H_d among them")

    # --- boost = -I rotation --------------------------------------------------------------------
    ipsi = s.gam[0] @ s.gam[1] @ s.gam[2] @ s.gam[3]
    for (a, b), (c, d) in (((1, 2), (3, 4)), ((1, 3), (4, 2)), ((1, 4), (2, 3))):
        require(np.array_equal(s.T(a, b), -ipsi @ s.T(c, d)), (a, b, c, d))
    print("PASS  boost = -I x rotation for all three pairs (T_12 = -I T_34, ...): on W, where I = +i, "
          "the boosts are -i times the rotations, so W is a Weyl spinor of sl(2,C)")

    # --- D7 Cartan weights of the complex 64 -------------------------------------------------------
    w7 = d7_weights(frame)
    cnt = Counter(w7)
    require(len(cnt) == 64 and set(cnt.values()) == {1}, len(cnt))
    parity7 = {sum(1 for x in w if x < 0) % 2 for w in cnt}
    require(len(parity7) == 1, parity7)
    left = [w for w in cnt if w[5] == w[6]]
    right = [w for w in cnt if w[5] == -w[6]]
    require(len(left) == 32 and len(right) == 32, (len(left), len(right)))
    require({w[:5] for w in left} == set(frame.weights), "q6 = q7 half is the left-handed 16")
    require({w[:5] for w in right} == {tuple(-x for x in w) for w in frame.weights}, "q6 = -q7 half is the 16bar")
    print("PASS  complex 64 over the seven planes: 64 distinct weights (+-1/2)^7, all of one parity; "
          "(2,1) x 16 (q6 = q7) + (1,2) x 16bar (q6 = -q7), 32 + 32, the Weyl spinor of so(14)")


if __name__ == "__main__":
    main()
