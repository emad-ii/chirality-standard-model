#!/usr/bin/env python3
"""Real Clifford algebra Cl(11,3), spin(11,3) and the Pati-Salam / Standard Model
subalgebras acting on the 64-dimensional Majorana-Weyl spinor.

This follows the *structure* of Lisi, "An Explicit Embedding of Gravity and the
Standard Model in E8" (arXiv:1006.4908): 14 real 128x128 gamma matrices,
spin(11,3) with 91 generators = spin(1,3) (6) + spin(10) (45) + frame-Higgs (40),
a positive-chirality Majorana-Weyl spinor of dimension 64, Pati-Salam
su(4)+su(2)+su(2) (21 generators) and the Standard Model (12 generators).

The matrices are built independently, not copied from the paper.  Cl(11,3) is
isomorphic to the simple algebra M(128, R), whose irreducible representation is
unique up to similarity, so any real 128x128 matrices satisfying the Clifford
relations are conjugate to those of the paper.  Individual matrix entries and
index orderings can differ; the verified statements are convention independent.

Chirality.  I = G_1 G_2 G_3 G_4 squares to -1 and commutes with spin(1,3) and
spin(10), so it is a complex structure on the real 64.  Its +i eigenspace W
(32 complex dimensions) is the space where gamma5 = i G_1 G_2 G_3 G_4 = -1, the
left-handed Weyl fields in the convention of check_dirac_weyl.py.  Hypercharge is
signed on W, which fixes which su(2) is su(2)_L.

Requires numpy.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from itertools import combinations
import math

import numpy as np

from e8 import require

# --------------------------------------------------------------------------- #
# Cl(11,3): 14 real 128x128 gamma matrices
# --------------------------------------------------------------------------- #

I2 = np.eye(2)
X = np.array([[0.0, 1.0], [1.0, 0.0]])
Z = np.diag([1.0, -1.0])
J = np.array([[0.0, 1.0], [-1.0, 0.0]])  # J @ J = -1


def kron(*ms: np.ndarray) -> np.ndarray:
    out = ms[0]
    for m in ms[1:]:
        out = np.kron(out, m)
    return out


def jordan_wigner(n: int = 7) -> tuple[list[np.ndarray], list[np.ndarray]]:
    """Real signature-(n,n) Clifford set on R^(2^n): n squares +1, n squares -1."""
    pos, neg = [], []
    for k in range(n):
        pre, post = [Z] * k, [I2] * (n - k - 1)
        pos.append(kron(*pre, X, *post))
        neg.append(kron(*pre, J, *post))
    return pos, neg


def build_gammas() -> tuple[list[np.ndarray], list[int]]:
    """Return gammas G[0..13] (labels 1..14) and the metric diagonal eta.

    Labels 1..4 are the spacetime directions with signature (+,-,-,-) and
    labels 5..14 are the ten spin(10) directions, all positive: total (11,3).
    """
    pos, neg = jordan_wigner(7)
    eps = neg[0] @ neg[1] @ neg[2] @ neg[3]
    n = pos[0].shape[0]
    require(np.array_equal(eps @ eps, np.eye(n)), "eps^2 = +1")
    for g in pos + neg[4:]:
        require(np.array_equal(eps @ g, g @ eps), "eps commutes with the other gammas")
    for g in neg[:4]:
        require(np.array_equal(eps @ g, -g @ eps), "eps anticommutes with e_1..e_4")
    flipped = [g @ eps for g in neg[:4]]  # square to +1, still anticommuting
    gam = [pos[0], neg[4], neg[5], neg[6]] + pos[1:] + flipped
    eta = [1, -1, -1, -1] + [1] * 10
    return gam, eta


# --------------------------------------------------------------------------- #
# spin(11,3) bivectors and their structure
# --------------------------------------------------------------------------- #

class Spin113:
    def __init__(self) -> None:
        self.gam, self.eta = build_gammas()
        self.n = self.gam[0].shape[0]
        self.labels = list(range(1, 15))
        self.biv = {(i, j): self.gam[i - 1] @ self.gam[j - 1] for i, j in combinations(self.labels, 2)}

    def B(self, a: int, b: int) -> np.ndarray:
        """Gamma_ab with the antisymmetry convention (zero if a == b)."""
        if a == b:
            return np.zeros((self.n, self.n))
        return self.biv[(a, b)] if a < b else -self.biv[(b, a)]

    def e(self, a: int) -> int:
        return self.eta[a - 1]

    def T(self, a: int, b: int) -> np.ndarray:
        """Spin generator (1/2) Gamma_ab."""
        return 0.5 * self.B(a, b)

    def klass(self, ij: tuple[int, int]) -> str:
        i, j = ij
        lo = (i <= 4) + (j <= 4)
        return {2: "S", 0: "K", 1: "F"}[lo]  # spin(1,3), spin(10), frame-Higgs


def commutator(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return a @ b - b @ a


def vec(m: np.ndarray) -> np.ndarray:
    return m.reshape(-1)


# Result handed to other scripts.
PLANES = [(5, 6), (7, 8), (9, 10), (11, 12), (13, 14)]  # Cartan of spin(10)


@dataclass
class SMFrame:
    weights: list = field(default_factory=list)  # 16 distinct Cartan weights (halves) on W
    parity: int = 0                              # number of minus signs mod 2
    weak: str = ""                               # "L" or "R": which triple is su(2)_L
    strong_r: str = ""                           # the other triple (acts on the conjugate 4bar)
    kappa: float = 0.0                           # Y = kappa (B-L plane sum) + sigma T3_R
    sigma: int = 1
    # Matrices for downstream scripts.
    s: object = None                             # the Spin113 instance
    basis: object = None                         # 128 x 64 basis of the Majorana-Weyl subspace
    su3: list = field(default_factory=list)      # 8 su(3)_c generators (128 x 128)
    weak_gens: list = field(default_factory=list)  # su(2)_L triple (128 x 128)
    gy: object = None                            # hypercharge generator (128 x 128)
    xbl: object = None                           # B-L plane generator T56 + T78 + T9,10


# --------------------------------------------------------------------------- #
# Checks
# --------------------------------------------------------------------------- #

def check_clifford(s: Spin113) -> None:
    n = s.n
    require(n == 128, n)
    for i in s.labels:
        for j in s.labels:
            gi, gj = s.gam[i - 1], s.gam[j - 1]
            expected = 2 * s.eta[i - 1] * np.eye(n) if i == j else np.zeros((n, n))
            require(np.array_equal(gi @ gj + gj @ gi, expected), (i, j))
    require(sum(1 for e in s.eta if e > 0) == 11 and sum(1 for e in s.eta if e < 0) == 3, "signature (11,3)")
    print("PASS  14 real 128x128 gamma matrices with {G_i, G_j} = 2 eta_ij, signature (11,3)")


def coefficient_matrix(s: Spin113) -> np.ndarray:
    return np.array([vec(s.biv[k]) for k in sorted(s.biv)])


def check_spin_algebra(s: Spin113) -> None:
    keys = sorted(s.biv)
    require(len(keys) == 91, len(keys))
    V = coefficient_matrix(s)
    gram = V @ V.T
    require(np.array_equal(gram, s.n * np.eye(91)), "bivectors are orthogonal with norm^2 = 128")
    print("PASS  91 bivectors Gamma_ij, linearly independent (spin(11,3) has dimension 91)")

    # structure relation [G_ab, G_cd] = 2(eta_bc G_ad - eta_ac G_bd - eta_bd G_ac + eta_ad G_bc)
    counts = Counter()
    for (a, b), (c, d) in combinations(keys, 2):
        lhs = commutator(s.B(a, b), s.B(c, d))
        terms = {}
        for coef, (p, q) in (
            (s.e(b) if b == c else 0, (a, d)),
            (-s.e(a) if a == c else 0, (b, d)),
            (-s.e(b) if b == d else 0, (a, c)),
            (s.e(a) if a == d else 0, (b, c)),
        ):
            if coef and p != q:
                terms[(p, q)] = terms.get((p, q), 0) + 2 * coef
        rhs = sum((coef * s.B(*pq) for pq, coef in terms.items()), np.zeros((s.n, s.n)))
        require(np.array_equal(lhs, rhs), ((a, b), (c, d)))
        # Z2 grading of spin(11,3) = (spin(1,3) + spin(10)) + frame-Higgs
        ka, kc = s.klass((a, b)), s.klass((c, d))
        out = {s.klass(tuple(sorted(pq))) for pq, coef in terms.items() if coef}
        rule = {
            ("S", "S"): {"S"}, ("K", "K"): {"K"}, ("S", "K"): set(), ("K", "S"): set(),
            ("S", "F"): {"F"}, ("F", "S"): {"F"}, ("K", "F"): {"F"}, ("F", "K"): {"F"},
            ("F", "F"): {"S", "K"},
        }[(ka, kc)]
        require(out <= rule, ((a, b), (c, d), out, rule))
        counts[(ka, kc)] += 1
    sizes = Counter(s.klass(k) for k in keys)
    require(dict(sizes) == {"S": 6, "K": 45, "F": 40}, sizes)
    print("PASS  [G_ab, G_cd] closes with the so(p,q) structure constants over all 4095 pairs")
    print("PASS  91 = 6 spin(1,3) + 45 spin(10) + 40 frame-Higgs; [spin(1,3), spin(10)] = 0; "
          "[F,F] in spin(1,3)+spin(10)")


def chirality(s: Spin113) -> np.ndarray:
    om = np.eye(s.n)
    for g in s.gam:
        om = om @ g
    require(np.array_equal(om @ om, np.eye(s.n)), "Omega^2 = +1 (real Weyl structure)")
    for g in s.gam:
        require(np.array_equal(om @ g, -g @ om), "Omega anticommutes with gammas")
    for m in s.biv.values():
        require(np.array_equal(om @ m, m @ om), "Omega commutes with bivectors")
    p = 0.5 * (np.eye(s.n) + om)
    rank = int(np.linalg.matrix_rank(p))
    require(rank == 64, rank)
    u, sv, _ = np.linalg.svd(p)
    basis = u[:, :64]
    require(np.allclose(p @ basis, basis), "basis lies in the +1 eigenspace")
    print("PASS  Omega = G_1...G_14 squares to +1, commutes with spin(11,3): 128 = 64 + 64 (Majorana-Weyl 64)")
    return basis


def restrict(basis: np.ndarray, m: np.ndarray) -> np.ndarray:
    return basis.T @ m @ basis


def span_residual(gens: list[np.ndarray], target: np.ndarray) -> float:
    a = np.array([vec(g) for g in gens]).T
    coef, *_ = np.linalg.lstsq(a, vec(target), rcond=None)
    return float(np.linalg.norm(a @ coef - vec(target)))


def closes(gens: list[np.ndarray]) -> bool:
    for x, y in combinations(gens, 2):
        if span_residual(gens, commutator(x, y)) > 1e-9:
            return False
    return True


def left_handed_space(s: Spin113, basis: np.ndarray) -> np.ndarray:
    """Orthonormal basis (64 x 32, complex) of the +i eigenspace of I = G1 G2 G3 G4."""
    ipsi = s.gam[0] @ s.gam[1] @ s.gam[2] @ s.gam[3]
    require(np.array_equal(ipsi @ ipsi, -np.eye(s.n)), "I^2 = -1")
    for k, m in s.biv.items():
        if s.klass(k) in ("S", "K"):
            require(np.array_equal(ipsi @ m, m @ ipsi), "I commutes with spin(1,3) + spin(10)")
    ir = restrict(basis, ipsi)
    require(np.allclose(ir @ ir, -np.eye(64)) and np.allclose(ir, -ir.T), "I is a complex structure on the 64")
    proj = 0.5 * (np.eye(64) - 1j * ir)
    vals, vecs = np.linalg.eigh(proj)
    keep = vals > 0.5
    require(int(keep.sum()) == 32, int(keep.sum()))
    return vecs[:, keep]


def joint_values(ops: list[np.ndarray]) -> list[tuple[float, ...]]:
    """Joint eigenvalues of commuting Hermitian operators (one tuple per common eigenvector)."""
    coef = [1.0, math.pi, math.e, math.sqrt(2.0), math.sqrt(5.0), math.sqrt(7.0),
            math.sqrt(11.0), math.sqrt(13.0)][: len(ops)]
    require(len(coef) == len(ops), "at most 8 operators")
    m = sum(c * o for c, o in zip(coef, ops))
    _, vecs = np.linalg.eigh((m + m.conj().T) / 2)
    out = []
    for k in range(vecs.shape[1]):
        v = vecs[:, k]
        vals = tuple(float(np.real(v.conj() @ (o @ v))) for o in ops)
        for o, val in zip(ops, vals):
            require(np.linalg.norm(o @ v - val * v) < 1e-8, "joint eigenvector")
        out.append(vals)
    return out


def check_pati_salam_and_sm(s: Spin113, basis: np.ndarray) -> SMFrame:
    six = [(p, q) for p, q in combinations(range(5, 11), 2)]
    four = [(p, q) for p, q in combinations(range(11, 15), 2)]
    su4 = [s.T(*k) for k in six]
    so4 = [s.T(*k) for k in four]
    require(len(su4) == 15 and len(so4) == 6, "spin(6) + spin(4)")
    require(closes(su4) and closes(so4), "spin(6) and spin(4) close")
    for x in su4:
        for y in so4:
            require(np.array_equal(commutator(x, y), np.zeros_like(x)), "spin(6) commutes with spin(4)")

    a, b, c, d = 11, 12, 13, 14
    T = s.T
    Lg = [0.5 * (T(a, b) + T(c, d)), 0.5 * (T(a, c) + T(d, b)), 0.5 * (T(a, d) + T(b, c))]
    Rg = [0.5 * (T(a, b) - T(c, d)), 0.5 * (T(a, c) - T(d, b)), 0.5 * (T(a, d) - T(b, c))]
    for triple in (Lg, Rg):
        signs = set()
        for i, j, k in ((0, 1, 2), (1, 2, 0), (2, 0, 1)):
            comm = commutator(triple[i], triple[j])
            for sg in (1, -1):
                if np.allclose(comm, sg * triple[k]):
                    signs.add(sg)
        require(len(signs) == 1, "su(2) relations [X_i, X_j] = +-eps_ijk X_k")
    for x in Lg:
        for y in Rg:
            require(np.array_equal(commutator(x, y), np.zeros_like(x)), "su(2)_L commutes with su(2)_R")
    print("PASS  Pati-Salam: spin(10) > spin(6) + spin(4) = su(4) + su(2) + su(2): 15 + 3 + 3 = 21 generators close")

    # --- su(3)_c and B-L inside su(4) ---------------------------------------
    xbl = T(5, 6) + T(7, 8) + T(9, 10)
    cols = np.array([vec(commutator(xbl, s.biv[k])) for k in six]).T  # (n^2, 15)
    _, sv, vt = np.linalg.svd(cols)
    null = vt[np.sum(sv > 1e-9):]
    require(null.shape[0] == 9, null.shape)  # u(3)
    cj = np.array([0.5 if k in ((5, 6), (7, 8), (9, 10)) else 0.0 for k in six])  # coefficients of xbl
    proj = null - np.outer(null @ cj, cj) / (cj @ cj)
    _, sv2, vt2 = np.linalg.svd(proj)
    su3_coef = vt2[: np.sum(sv2 > 1e-9)]
    require(su3_coef.shape[0] == 8, su3_coef.shape)
    su3 = [sum((cf * s.biv[k] for cf, k in zip(row, six)), np.zeros((s.n, s.n))) for row in su3_coef]
    require(closes(su3), "su(3) closes")
    for x in su3:
        require(np.allclose(commutator(x, xbl), 0), "su(3) commutes with B-L")
    print("PASS  u(3) = centralizer of the complex structure in spin(6); su(3) (8) + u(1) B-L close")

    R = lambda m: restrict(basis, m)
    su3_r = [R(x) for x in su3]
    casimir = -sum(x @ x for x in su3_r)
    ev = np.round(np.linalg.eigvalsh((casimir + casimir.T) / 2), 6)
    hist = Counter(ev)
    require(sorted(hist.values()) == [16, 48] and 0.0 in hist, hist)
    print("PASS  color Casimir on the 64: 48 colored dimensions (3 + 3bar) and 16 colorless")

    # --- left-handed Weyl subspace W and the su(2)_L correlation ---------------
    wm = left_handed_space(s, basis)
    print("PASS  I = G1 G2 G3 G4 is a complex structure commuting with spin(1,3) + spin(10); "
          "its +i eigenspace W (32 complex dims) has gamma5 = i G1G2G3G4 = -1: left-handed fields")

    def on_w(m64: np.ndarray) -> np.ndarray:
        """Restriction of a real generator (already on the 64) to W."""
        block = wm.conj().T @ m64 @ wm
        require(np.linalg.norm(m64 @ wm - wm @ block) < 1e-8, "generator preserves W")
        return block

    def cas(gens: list[np.ndarray]) -> np.ndarray:
        return on_w(-sum(R(x) @ R(x) for x in gens))

    def qop(m: np.ndarray) -> np.ndarray:
        return -1j * on_w(R(m))  # Hermitian; eigenvalue q means G v = i q v

    # Expected left-handed Weyl content of one generation, as
    # (colored, weak doublet, 6*Y): each entry x2 for the two spin states.
    expected = Counter({(1, 1, 1): 12, (1, 0, -4): 6, (1, 0, 2): 6, (0, 1, -3): 4, (0, 0, 6): 2, (0, 0, 0): 2})
    cc = cas(su3)
    sols = []
    for r_name, r_tri, w_name, w_tri in (("L", Lg, "R", Rg), ("R", Rg, "L", Lg)):
        cw = cas(w_tri)
        for kappa in (-1 / 3, 1 / 3):
            for sigma in (1, -1):
                y = qop(kappa * xbl + sigma * r_tri[0])
                got = Counter(
                    (int(v[0] > 1e-6), int(v[1] > 1e-6), int(round(6 * v[2])))
                    for v in joint_values([cc, cw, y])
                )
                if got == expected:
                    sols.append((r_name, w_name, kappa, sigma))
    require(sols, "no signed hypercharge reproduces the left-handed Standard Model on W")
    # The signed spectrum correlates the sign of the B-L coefficient with the choice of su(2):
    classes = {(r, w, round(3 * k)) for r, w, k, _ in sols}
    require(classes == {("L", "R", -1), ("R", "L", 1)}, classes)
    print("PASS  on W the signed (color, weak, Y) content is the left-handed Standard Model generation "
          "x 2 spin states ONLY for (kappa = -1/3, T3_R from the L triple) or (kappa = +1/3, T3_R from the R triple)")

    # These two solutions are conjugate under an inner automorphism of spin(10):
    # U = G6 G8 G10 G11 reverses the orientation of the colour complex structure (B-L -> -B-L)
    # and swaps the two su(2) triples, while commuting with spin(1,3), I and Omega.
    u = s.gam[5] @ s.gam[7] @ s.gam[9] @ s.gam[10]
    require(np.array_equal(u @ u.T, np.eye(s.n)), "U orthogonal")
    conj = lambda m: u @ m @ u.T
    require(np.allclose(conj(xbl), -xbl), "U reverses B-L")
    for k, m in s.biv.items():
        if s.klass(k) == "S":
            require(np.array_equal(conj(m), m), "U commutes with spin(1,3)")
    ipsi = s.gam[0] @ s.gam[1] @ s.gam[2] @ s.gam[3]
    require(np.array_equal(conj(ipsi), ipsi), "U commutes with I")
    require(all(span_residual(su3, conj(x)) < 1e-9 for x in su3), "U maps su(3) to itself")
    for sg in (1, -1):
        y_a = (-1 / 3) * xbl + sg * Lg[0]
        partners = [(1 / 3) * xbl + sg2 * Rg[0] for sg2 in (1, -1)]
        require(any(np.allclose(conj(y_a), p) for p in partners), "U maps one hypercharge to the other")
    print("PASS  the two solutions are conjugate under U = G6 G8 G10 G11 in Spin(10): they describe the same "
          "physics with the orientation of the colour complex structure (3 vs 3bar) reversed")

    # Canonical representative: orient B-L so that kappa = +1/3; then su(2)_L is the 'L' triple.
    chosen = [x for x in sols if x[0] == "R"]
    r_name, w_name, kappa, _ = chosen[0]
    require(sorted(sg for *_, sg in chosen) == [-1, 1], chosen)
    sigma = 1
    r_tri, w_tri = Rg, Lg
    gy = kappa * xbl + sigma * r_tri[0]
    print("PASS  with the orientation kappa = +1/3, su(2)_L is the 'L' (self-dual) triple and "
          "Y = (1/3)(B-L plane) + T3 of the 'R' triple on the left-handed space W")
    print("INFO  the sign sigma of T3_R is not fixed: it is the Weyl reflection of su(2)_R (u^c <-> d^c)")

    # Electric charge, signed.
    expected_q = Counter({4: 6, -2: 6, -4: 6, 2: 6, 0: 4, -6: 2, 6: 2})
    got_q = Counter(int(round(6 * v[0])) for v in joint_values([qop(w_tri[0] + gy)]))
    require(got_q == expected_q, got_q)
    print("PASS  Q = T3_L + Y on W: u_L 2/3, d_L -1/3, u^c -2/3, d^c 1/3, e_L -1, e^c +1, neutrinos 0 (x2 spin)")

    cw = cas(w_tri)
    hist_w = Counter(int(v[0] > 1e-6) for v in joint_values([cw]))
    require(hist_w == {1: 16, 0: 16}, hist_w)
    print("PASS  weak su(2)_L Casimir on W: 16 doublet states and 16 singlet states")

    # --- full Standard Model algebra and its commutant ---------------------
    sm = su3 + list(w_tri) + [gy]
    require(len(sm) == 12 and closes(sm), "SM algebra closes")
    for x in su3:
        for y in list(w_tri) + [gy]:
            require(np.allclose(commutator(x, y), 0), "su(3) commutes with su(2)_L and Y")
    for x in w_tri:
        require(np.allclose(commutator(x, gy), 0), "su(2)_L commutes with Y")
    for k, m in s.biv.items():
        if s.klass(k) == "S":
            for x in sm:
                require(np.allclose(commutator(m, x), 0), "spin(1,3) commutes with the Standard Model")
    print("PASS  Standard Model su(3) + su(2)_L + u(1)_Y: 12 generators, closed, commuting with spin(1,3)")

    # --- Cartan weights of W ----------------------------------------------------
    ops = [qop(s.T(*p)) for p in PLANES]
    raw = joint_values(ops)
    weights = []
    for w in raw:
        r = tuple(round(2 * x) / 2 for x in w)
        require(all(abs(x - y) < 1e-8 and abs(abs(y) - 0.5) < 1e-8 for x, y in zip(w, r)), w)
        weights.append(r)
    cnt = Counter(weights)
    require(len(cnt) == 16 and set(cnt.values()) == {2}, cnt)
    parities = {sum(1 for x in w if x < 0) % 2 for w in cnt}
    require(len(parities) == 1, parities)
    parity = parities.pop()
    print(f"PASS  Cartan weights of W: 16 distinct weights (+-1/2)^5, all with {'odd' if parity else 'even'} "
          "numbers of minus signs, each twice (spin): the 16 of SO(10) times the spin doublet")
    return SMFrame(sorted(cnt), parity, w_name, r_name, kappa, sigma,
                   s=s, basis=basis, su3=su3, weak_gens=list(w_tri), gy=gy, xbl=xbl)


def main() -> SMFrame:
    s = Spin113()
    check_clifford(s)
    check_spin_algebra(s)
    basis = chirality(s)
    return check_pati_salam_and_sm(s, basis)


if __name__ == "__main__":
    main()
