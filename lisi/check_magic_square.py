#!/usr/bin/env python3
"""Triality algebras, the magic square, and the Z3 grading E8 = (E6 + SU(3)) + (27,3) + (27bar,3bar).

Topics of A. G. Lisi, "Division Algebras, Triality, and Exceptional Magic" (arXiv:2609.12112).  Everything
below is computed from the standard definitions (Cayley-Dickson algebras, triality algebra tri(A), the
Barton-Sudbery / Tits formula for the magic square), not transcribed from the paper; the results agree with
the paper's Section 3 (tri(C) = u(1)+u(1), tri(H) = su(2)^3, tri(O) = so(8)) and its compound triality
decompositions (7.1), (8.1), (9.1).  The Z3 grading of step 4 is the family grading of the chirality theorem;
Lisi's own Theta is a different order-3 grading, treated in check_lisi_theta.py.

1. Build R, C, H, O by Cayley-Dickson doubling; check they are composition algebras.
2. tri(A) = {(a, b, c) in so(A)^3 : a(xy) = b(x) y + x c(y)}: exact nullspace dimension.
   Expected 0, 2, 9, 28.
3. Magic square dim L(A, B) = tri(A) + tri(B) + 3 dim A dim B, against the known Freudenthal-Tits table.
4. Z3 grading of the E8 root system by the SU(3)_M triality class: eigenspaces 86 + 81 + 81 (the
   3-symmetric space E8 / (E6 x SU(3)) has dimension 162), tied to the repo's chirality theorem.
5. E8 = L(O, O): 248 = 28 + 28 + 3 x 64 agrees with the D4 x D4 root count of check_triality_d4d4.py.

Requires sympy.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product

import sympy as sp

from check_e6_su3_bridge import ALPHA, BETA
from e8 import dot, e8_roots, require


# --- Cayley-Dickson algebras -------------------------------------------------------------------

def cd_mult(n: int):
    """Return (mult, conj) on integer lists of length n (n = 1, 2, 4, 8)."""
    if n == 1:
        return (lambda x, y: [x[0] * y[0]]), (lambda x: list(x))
    h = n // 2
    m_h, c_h = cd_mult(h)

    def add(u, v):
        return [a + b for a, b in zip(u, v)]

    def sub(u, v):
        return [a - b for a, b in zip(u, v)]

    def conj(x):
        return c_h(x[:h]) + [-t for t in x[h:]]

    def mult(x, y):
        a, b, c, d = x[:h], x[h:], y[:h], y[h:]
        # (a, b)(c, d) = (a c - d* b, d a + b c*)
        return sub(m_h(a, c), m_h(c_h(d), b)) + add(m_h(d, a), m_h(b, c_h(c)))

    return mult, conj


def basis(n: int, k: int):
    return [1 if j == k else 0 for j in range(n)]


def composition_check(n: int) -> None:
    mult, conj = cd_mult(n)
    # |xy|^2 = |x|^2 |y|^2 on all pairs of basis sums (a spanning sample)
    vecs = [basis(n, k) for k in range(n)] + [[1] * n, [1, -1] * (n // 2) if n > 1 else [1]]
    for x, y in product(vecs, repeat=2):
        nx, ny, nxy = (sum(t * t for t in v) for v in (x, y, mult(x, y)))
        require(nxy == nx * ny, (n, x, y))


def tri_dim(n: int) -> int:
    """Dimension of tri(A) for the Cayley-Dickson algebra of dimension n (exact)."""
    mult, _ = cd_mult(n)
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]  # skew generators E_ij - E_ji
    npair = len(pairs)
    nun = 3 * npair  # unknown coefficients of a, b, c
    if nun == 0:
        return 0

    def skew_apply(which: int, coefs_index: int, vec):
        """Image of `vec` under the skew generator number `coefs_index` of block `which` -> (column weights)."""
        i, j = pairs[coefs_index]
        out = [0] * n
        out[i] += vec[j]
        out[j] -= vec[i]
        return out

    rows = []
    for p in range(n):
        for q in range(n):
            x, y = basis(n, p), basis(n, q)
            xy = mult(x, y)
            # one equation per output component r: a(xy)_r - (b(x) y)_r - (x c(y))_r = 0
            eqs = [[0] * nun for _ in range(n)]
            for k in range(npair):
                ax = skew_apply(0, k, xy)  # contributes to column k
                bx = skew_apply(1, k, x)
                cy = skew_apply(2, k, y)
                bxy = mult(bx, y)
                xcy = mult(x, cy)
                for r in range(n):
                    eqs[r][k] += ax[r]
                    eqs[r][npair + k] -= bxy[r]
                    eqs[r][2 * npair + k] -= xcy[r]
            rows.extend(eqs)
    mat = sp.Matrix(rows)
    return nun - mat.rank()


def main() -> None:
    names = {1: "R", 2: "C", 4: "H", 8: "O"}
    for n in (1, 2, 4, 8):
        composition_check(n)
    mult8, _ = cd_mult(8)
    e = [basis(8, k) for k in range(8)]
    nonassoc = any(mult8(mult8(e[i], e[j]), e[k]) != mult8(e[i], mult8(e[j], e[k]))
                   for i in range(8) for j in range(8) for k in range(8))
    require(nonassoc, "O is not associative")
    print("PASS  Cayley-Dickson algebras R, C, H, O are composition algebras (|xy|^2 = |x|^2 |y|^2); O is not associative")

    tri = {n: tri_dim(n) for n in (1, 2, 4, 8)}
    require(tri == {1: 0, 2: 2, 4: 9, 8: 28}, tri)
    print("PASS  triality algebras tri(R), tri(C), tri(H), tri(O) have dimensions 0, 2, 9, 28 "
          "(u(1)^2, so(3)^3, so(8)), computed as exact nullspaces of a(xy) = b(x)y + x c(y)")

    dims = {n: n for n in (1, 2, 4, 8)}
    table = [[tri[a] + tri[b] + 3 * dims[a] * dims[b] for b in (1, 2, 4, 8)] for a in (1, 2, 4, 8)]
    known = [[3, 8, 21, 52], [8, 16, 35, 78], [21, 35, 66, 133], [52, 78, 133, 248]]
    require(table == known, table)
    print("PASS  magic square dim L(A,B) = tri(A) + tri(B) + 3 dim A dim B reproduces the Freudenthal-Tits table "
          "(rows R, C, H, O: " + "; ".join(",".join(map(str, r)) for r in table) + ")")

    # --- E8 = L(O, O) against the roots ---------------------------------------------------------
    roots = e8_roots()
    require(len(roots) + 8 == 248 == tri[8] + tri[8] + 3 * 8 * 8, "248 = 28 + 28 + 3 x 64")
    d4_roots = sum(1 for r in roots if sum(1 for x in r[:4] if x) == 2 and not any(r[4:]))
    require(d4_roots + 4 == tri[8], (d4_roots, tri[8]))
    print("PASS  E8 = L(O,O): 248 = 28 + 28 + 3 x 64; tri(O) = so(8) is the D4 with 24 roots + 4 Cartan, "
          "matching the D4 x D4 root count")

    # --- Z3 grading from SU(3)_M --------------------------------------------------------------------
    def chi(r) -> int:
        l1, l2 = Fraction(dot(r, ALPHA), 4), Fraction(dot(r, BETA), 4)
        require(l1.denominator == 1 and l2.denominator == 1, (l1, l2))
        return (int(l1) + 2 * int(l2)) % 3

    counts = {0: 8, 1: 0, 2: 0}  # the Cartan subalgebra is in the 0-eigenspace
    for r in roots:
        counts[chi(r)] += 1
    require(counts == {0: 86, 1: 81, 2: 81}, counts)
    require(counts[0] == 78 + 8 and counts[1] == 27 * 3, counts)
    # additivity: chi is a grading (chi(r + s) = chi(r) + chi(s) whenever r + s is a root)
    rootset = set(roots)
    for r in roots:
        for s in roots:
            t = tuple(a + b for a, b in zip(r, s))
            if t in rootset:
                require(chi(t) == (chi(r) + chi(s)) % 3, (r, s))
    print("PASS  the SU(3)_M triality class (l1 + 2 l2) mod 3 is a Z3 grading of E8 with eigenspaces "
          "86 + 81 + 81 = (E6 + SU(3)) + (27,3) + (27bar,3bar); E8 / (E6 x SU(3)) is a 3-symmetric space "
          "of dimension 162 -- the Z3 form of the chirality theorem")


if __name__ == "__main__":
    main()
