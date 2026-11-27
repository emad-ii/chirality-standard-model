#!/usr/bin/env python3
"""Place the D4 x D4 triality against SU(4) = centralizer of SO(10), SU(3)_M and spin(1,3)_C.

Setting (root level, exact Fractions).  In E8 > SO(10) x SU(4) the centralizer SU(4) = A3 of
SO(10) holds the horizontal SU(3)_M (an A2) and the Lorentz roots.  Fix one of the five f_i of the
SO(10) frame; then

    D4b = SO(10) roots orthogonal to f_i  (24 roots),   D4a = E8 roots orthogonal to D4b (24 roots),

and E8 > D4a x D4b with 240 = 24 + 24 + 3 x 64.  A3 lies inside D4a and so does A2 = SU(3)_M.
Because every (8,8) block is the Cartesian product of weight classes, triality acts on the two D4
factors *independently*, so it can be chosen to fix A2 pointwise.  We construct that triality T'
explicitly and verify what it does:

  * D4a = A3_V u A3_S u A3_C: three SU(4)'s that pairwise meet in exactly SU(3)_M; T' permutes them,
    so it carries SU(4) (and the SO(10) it centralizes) to two other pairs sharing D4b;
  * T' fixes SU(3)_M pointwise: it commutes with the family 3 and acts inside each 27 as
    8v -> 8c -> 8s together with a cycle of the three SO(8) singlets;
  * on the Lorentz roots: each A3 root pair shares one su(2) with SU(3)_M; T' fixes it and permutes
    the other su(2) among three different SU(4)'s.

The repo's explicit triality T of check_triality_d4d4.py moves this A2; T' is a different member of
the same family of trialities (they differ by Weyl elements of the two D4's) and is constructed
directly here.
Requires sympy and numpy (through the model modules).
"""

from __future__ import annotations

import contextlib
import io
from collections import Counter, defaultdict
from fractions import Fraction as F

import sympy as sp

import match_e8_spin113 as m5
from check_e6_su3_bridge import ALPHA, BETA
from e8 import e8_roots, require
from match_e8_d7 import add, dp, neg, scale, vec_f

Vec = tuple
ZERO = tuple(F(0) for _ in range(8))


def lin(coefs, vecs) -> Vec:
    return tuple(sum((c * v[j] for c, v in zip(coefs, vecs)), F(0)) for j in range(8))


def to_sp(x: F):
    return sp.Rational(x.numerator, x.denominator)


def from_sp(x) -> F:
    return F(int(x.p), int(x.q))


class Part:
    """Orthogonal projection onto the span of a list of vectors."""

    def __init__(self, basis):
        self.basis = list(basis)
        k = len(self.basis)
        g = sp.Matrix(k, k, lambda i, j: to_sp(dp(self.basis[i], self.basis[j])))
        require(g.det() != 0, "dependent basis")
        self.gi = g.inv()

    def coef(self, v: Vec):
        rhs = sp.Matrix([to_sp(dp(v, q)) for q in self.basis])
        return [from_sp(x) for x in self.gi * rhs]

    def proj(self, v: Vec) -> Vec:
        return lin(self.coef(v), self.basis)


def greedy_basis(vs, k):
    chosen = []
    for v in vs:
        cand = chosen + [v]
        rank = sp.Matrix([[to_sp(x) for x in u] for u in cand]).rank()
        if rank == len(cand):
            chosen = cand
        if len(chosen) == k:
            return chosen
    raise AssertionError("not enough independent vectors")


def classes_of(weights):
    """Split D4 minimal weights (norm 1) into the three classes 8v, 8s, 8c.

    Inside a class the inner products are 0, +-1; between classes they are +-1/2.
    """
    ws = sorted(weights)
    parent = {w: w for w in ws}

    def find(w):
        while parent[w] != w:
            parent[w] = parent[parent[w]]
            w = parent[w]
        return w

    for u in ws:
        for v in ws:
            if dp(u, v) in (0, 1, -1):
                parent[find(u)] = find(v)
    groups = defaultdict(set)
    for w in ws:
        groups[find(w)].add(w)
    cls = list(groups.values())
    require(sorted(len(c) for c in cls) == [8, 8, 8], [len(c) for c in cls])
    return cls


def automorphisms(rs, basis):
    """All isometries of span(rs) permuting rs, as lists of images of `basis`."""
    gram = [[dp(u, v) for v in basis] for u in basis]
    out = []

    def rec(k, imgs):
        if k == len(basis):
            out.append(list(imgs))
            return
        for r in rs:
            if dp(r, r) == gram[k][k] and all(dp(r, imgs[j]) == gram[k][j] for j in range(k)):
                imgs.append(r)
                rec(k + 1, imgs)
                imgs.pop()

    rec(0, [])
    return out


def analyse(i: int, ctx: dict) -> dict:
    roots, fs, a0, b0, a2m, m, so10_part = (ctx[k] for k in ("roots", "fs", "a0", "b0", "a2m", "m", "so10_part"))
    rootset = set(roots)

    def v5(r):
        return tuple(dp(r, f) for f in fs)

    d5 = [r for r in roots if sum(c * c for c in v5(r)) == 2]
    a3 = {r for r in roots if not any(v5(r))}
    d4b = sorted(r for r in d5 if v5(r)[i] == 0)
    require(len(d4b) == 24, len(d4b))
    d4b_set = set(d4b)
    d4a = sorted(r for r in roots if all(dp(r, q) == 0 for q in d4b))
    d4a_set = set(d4a)
    require(len(d4a) == 24, len(d4a))
    require(a3 <= d4a_set and a2m <= a3, "A3 and SU(3)_M lie in D4a")
    rest = [r for r in roots if r not in d4a_set and r not in d4b_set]
    require(len(rest) == 192, len(rest))

    # --- orthogonal splitting R^8 = (A2 plane) + P + span(D4b) -------------------------------------------
    part_b = Part(greedy_basis(d4b, 4))
    part_a = Part(greedy_basis(d4a, 4))
    part_m = Part([a0, b0])

    wa = {part_a.proj(r) for r in rest}
    wb = {part_b.proj(r) for r in rest}
    require(len(wa) == 24 and len(wb) == 24, (len(wa), len(wb)))
    require(all(dp(w, w) == 1 for w in wa | wb), "weights have norm 1")
    cls_a, cls_b = classes_of(wa), classes_of(wb)
    cid_a = {w: k for k, c in enumerate(cls_a) for w in c}
    cid_b = {w: k for k, c in enumerate(cls_b) for w in c}

    # The 192 roots are the three blocks (8X, 8X): match the classes of the two factors.
    pairing, block = {}, defaultdict(set)
    for r in rest:
        ka, kb = cid_a[part_a.proj(r)], cid_b[part_b.proj(r)]
        require(pairing.setdefault(ka, kb) == kb, "class of D4b is determined by the class of D4a")
        block[ka].add(r)
    require(sorted(pairing.values()) == [0, 1, 2] and all(len(s) == 64 for s in block.values()), pairing)
    for ka, s in block.items():
        require({part_a.proj(r) for r in s} == cls_a[ka] and {part_b.proj(r) for r in s} == cls_b[pairing[ka]]
                and len({(part_a.proj(r), part_b.proj(r)) for r in s}) == 64,
                "each block is the full product 8X x 8X")

    # The weights of D4a orthogonal to SU(3)_M form a hexagon in the plane P orthogonal to A2.
    singlets = [w for w in wa if dp(w, a0) == 0 and dp(w, b0) == 0]
    require(len(singlets) == 6, len(singlets))
    f_i = fs[i]
    require(f_i in singlets, "f_i is an A2-singlet weight of D4a")
    w0_ = f_i
    w1_ = next(w for w in sorted(singlets) if dp(w, w0_) == F(1, 2))
    w2_ = add(w1_, neg(w0_))
    require(set(singlets) == {w0_, w1_, w2_, neg(w0_), neg(w1_), neg(w2_)}, "hexagon")
    classes_hex = [cid_a[w] for w in (w0_, w1_, w2_)]
    require(len(set(classes_hex)) == 3, classes_hex)
    require(all(cid_a[neg(w)] == cid_a[w] for w in (w0_, w1_, w2_)), "opposite hexagon vertices share a class")
    cv, c1, c2 = classes_hex  # class of f_i (the class A3 = roots orthogonal to f_i belongs to), and the others
    part_p = Part([w0_, w1_])
    basis8 = [w0_, w1_, a0, b0] + part_b.basis
    for u in (w0_, w1_):
        require(all(dp(u, v) == 0 for v in [a0, b0] + part_b.basis), "P is orthogonal to A2 and to D4b")
    require(all(dp(a0, q) == 0 and dp(b0, q) == 0 for q in part_b.basis), "A2 is orthogonal to D4b")
    require(sp.Matrix([[to_sp(x) for x in u] for u in basis8]).rank() == 8, "splitting spans R^8")

    # --- the triality T' fixing SU(3)_M pointwise ------------------------------------------------------
    # on P: rotation by 120 degrees, w_k -> w_(k+2) (hexagon), so classes cv -> c2 -> c1 -> cv
    def rot(u: Vec) -> Vec:
        c0, c1_ = part_p.coef(u)
        return lin([c0, c1_], [w2_, neg(w0_)])

    class_map_a = {cv: c2, c2: c1, c1: cv}
    class_map_b = {pairing[k]: pairing[v] for k, v in class_map_a.items()}
    autos = automorphisms(d4b, part_b.basis)
    require(len(autos) == 1152, len(autos))
    valid = []
    for imgs in autos:
        def g(u, imgs=imgs):
            return lin(part_b.coef(u), imgs)

        if {g(r) for r in d4b} != d4b_set:
            continue
        if any({g(w) for w in cls_b[k]} != cls_b[v] for k, v in class_map_b.items()):
            continue
        if not all(g(g(g(q))) == q for q in part_b.basis):
            continue
        valid.append(imgs)
    require(valid, "no order-3 automorphism of D4b with the matching class cycle")
    imgs_b = valid[0]

    def tri(v: Vec) -> Vec:
        return add(add(part_m.proj(v), rot(part_p.proj(v))), lin(part_b.coef(v), imgs_b))

    require({tri(r) for r in roots} == rootset, "T' permutes the E8 roots")
    require(all(tri(tri(tri(r))) == r for r in roots) and any(tri(r) != r for r in roots), "T' has order 3")
    require(all(tri(x) == x for x in (a0, b0)), "T' fixes SU(3)_M pointwise")
    require({tri(r) for r in d4a} == d4a_set and {tri(r) for r in d4b} == d4b_set, "T' preserves both 28's")
    for ka, kb in pairing.items():
        require({tri(r) for r in block[ka]} == block[class_map_a[ka]], "T' cycles the three 64 blocks")
    require(all(class_map_a[k] != k for k in class_map_a), "no block fixed")

    # --- three SU(4)'s in D4a ---------------------------------------------------------------------------
    hexw = {cv: w0_, c1: w1_, c2: w2_}
    a3x = {k: {r for r in d4a if dp(r, w) == 0} for k, w in hexw.items()}
    require(all(len(s) == 12 and a2m <= s for s in a3x.values()), "three A3's containing SU(3)_M")
    require(a3x[cv] == a3, "the SU(4) centralizing SO(10) is the A3 orthogonal to f_i")
    keys = list(a3x)
    require(all(a3x[x] & a3x[y] == a2m for x in keys for y in keys if x != y), "pairwise intersection is SU(3)_M")
    require(a3x[cv] | a3x[c1] | a3x[c2] == d4a_set, "D4a = A3 u A3' u A3''")
    require({tri(r) for r in a3x[cv]} == a3x[c2] and {tri(r) for r in a3x[c2]} == a3x[c1]
            and {tri(r) for r in a3x[c1]} == a3x[cv], "T' permutes the three SU(4)'s cyclically")

    # --- the SO(10)'s -----------------------------------------------------------------------------------
    d5_set = set(d5)
    d5_1 = {tri(r) for r in d5_set}
    d5_2 = {tri(r) for r in d5_1}
    require(d5_set & d5_1 == d4b_set and d5_1 & d5_2 == d4b_set and d5_set & d5_2 == d4b_set,
            "the three SO(10)'s meet exactly in D4b")
    for k, dk in enumerate((d5_set, d5_1, d5_2)):
        cen = {r for r in roots if all(dp(r, s) == 0 for s in dk)}
        require(cen == a3x[[cv, c2, c1][k]], "centralizer of the k-th SO(10) is the k-th SU(4)")

    # --- Lorentz roots: orthogonal pairs in A3 ---------------------------------------------------------
    cl, seen = [], set()
    for r in sorted(a3):
        key = frozenset({r, neg(r)})
        if key not in seen:
            seen.add(key)
            cl.append(sorted(key))
    pairs = [(c1_, c2_) for k, c1_ in enumerate(cl) for c2_ in cl[k + 1:] if dp(c1_[0], c2_[0]) == 0]
    require(len(pairs) == 3, len(pairs))
    orth_dp = set()
    for c1_, c2_ in pairs:
        shared, other = (c1_, c2_) if c1_[0] in a2m else (c2_, c1_)
        require(shared[0] in a2m and other[0] not in a2m, "one su(2) inside SU(3)_M, one outside")
        rs, ro = shared[0], other[0]
        require(tri(rs) == rs, "T' fixes the su(2) that lies in SU(3)_M")
        o1, o2 = tri(ro), tri(tri(ro))
        require(ro in a3x[cv] and o1 in a3x[c2] and o2 in a3x[c1], "the other su(2) moves to the other SU(4)'s")
        require(not ({o1, neg(o1)} & {ro, neg(ro)}) and not ({o2, neg(o2)} & {ro, neg(ro)}), "three distinct roots")
        require(dp(rs, o1) == 0 and dp(rs, o2) == 0, "images stay orthogonal to the shared su(2)")
        # the roots of D4a orthogonal to the shared root form A1^3: ro, T'ro, T'^2 ro are its three su(2)'s
        orth_dp |= {dp(ro, o1), dp(o1, o2), dp(ro, o2)}
        a1_cubed = {r for r in d4a if dp(r, rs) == 0}
        require(len(a1_cubed) == 6 and {ro, neg(ro), o1, neg(o1), o2, neg(o2)} == a1_cubed,
                "the three images are exactly the three su(2)'s of the A1^3 centralizing the shared su(2) in D4a")
    require(orth_dp == {F(0)}, orth_dp)

    # --- action on the 27, the 16 and the 10 --------------------------------------------------------------
    w27 = {vec_f(r["w"]) for fam in m.families.values() for r in fam}
    require(len(w27) == 27, len(w27))
    require({tri(w) for w in w27} == w27, "T' preserves each 27 (it fixes the family labels)")
    sing = [w for w in w27 if not any(part_b.proj(w))]
    require(len(sing) == 3, len(sing))
    others = defaultdict(list)
    for w in w27:
        p = part_b.proj(w)
        if any(p):
            others[cid_b[p]].append(w)
    require(sorted(len(v) for v in others.values()) == [8, 8, 8], {k: len(v) for k, v in others.items()})
    for k, v in others.items():
        require({tri(w) for w in v} == set(others[class_map_b[k]]), "T' cycles 8v -> 8c -> 8s inside the 27")
    require({tri(w) for w in sing} == set(sing) and all(tri(w) != w for w in sing), "T' cycles the three singlets")
    p16 = Counter(cid_b[part_b.proj(vec_f(r["w"]))] for r in m.families["16"])
    p10 = Counter(cid_b[part_b.proj(vec_f(r["w"]))] for r in m.families["10"] if any(part_b.proj(vec_f(r["w"]))))
    require(sorted(p16.values()) == [8, 8] and sorted(p10.values()) == [8], (p16, p10))
    require(set(p16) | set(p10) == set(range(3)) and not (set(p16) & set(p10)),
            "16 = 8 + 8 and 10 = 8 + 1 + 1 under SO(8)")
    w16 = {vec_f(r["w"]) for r in m.families["16"]}
    overlap = len({tri(w) for w in w16} & w16)

    # which Standard Model states do the three singlets contain?
    names = []
    for w in sorted(sing):
        for fam, recs in m.families.items():
            for r in recs:
                if vec_f(r["w"]) == w:
                    names.append((fam, r.get("color"), r.get("su2"), r.get("T3"), r.get("Y"), r.get("Q")))
    return {"M_fun": tri, "names": names, "overlap16": overlap, "valid": len(valid), "cycle": (cv, c2, c1)}


def main() -> None:
    with contextlib.redirect_stdout(io.StringIO()):
        data = m5.main()
    fs = [vec_f(f) for f in next(iter(data["solutions"].values()))[2]]
    roots = [tuple(F(x, 2) for x in r) for r in e8_roots()]
    a0 = tuple(F(x, 2) for x in ALPHA)
    b0 = tuple(F(x, 2) for x in BETA)
    a2m = {a0, b0, add(a0, b0), neg(a0), neg(b0), neg(add(a0, b0))}
    ctx = {"roots": roots, "fs": fs, "a0": a0, "b0": b0, "a2m": a2m, "m": data["m"], "so10_part": data["so10_part"]}

    results = {}
    for i in range(5):
        results[i] = analyse(i, ctx)
    print("PASS  for each of the five SO(8) < SO(10) (one f_i singled out): E8 > D4a x D4b with A3 and SU(3)_M in "
          "D4a; the (8,8) blocks are full products 8X x 8X, so triality acts on the two D4's independently")
    print("PASS  the A2-singlet weights of D4a form a hexagon in the plane orthogonal to SU(3)_M; its three "
          "opposite pairs lie one in each of 8v, 8s, 8c")
    print("PASS  D4a = A3 u A3' u A3'': three SU(4)'s pairwise meeting exactly in SU(3)_M")
    print("PASS  explicit order-3 triality T' = (120 degree rotation of that plane) + (triality of D4b) permutes the "
          "240 roots, fixes SU(3)_M pointwise, cycles (8,8)v -> (8,8)c -> (8,8)s, and permutes the three SU(4)'s "
          "cyclically")
    print("PASS  T' carries (SO(10), SU(4)) to two other pairs; the three SO(10)'s meet exactly in D4b and each is "
          "centralized by one of the three SU(4)'s")
    print("PASS  each of the three A3 root pairs (candidates for spin(1,3)_C) shares one su(2) with SU(3)_M; T' fixes "
          "it and moves the other su(2) into the other two SU(4)'s")
    print("PASS  T' fixes the family labels (acts inside each 27): 27 = 8v + 8s + 8c + 3 singlets, cycled; "
          "16 = 8 + 8, 10 = 8 + 1 + 1 under SO(8), so T' does not preserve the SO(10) split 1 + 16 + 10")
    for i in range(5):
        r = results[i]
        print(f"INFO  f_{i + 1}: T' maps the 16 of the 27 to a set sharing {r['overlap16']} of 16 weights with it; "
              f"singlets of the 27 under SO(8)_{i + 1}: {[(n[0], n[1], n[2], str(n[4])) for n in r['names']]}")

    # Conjugacy classes in W(E8): T' against the family cycle c = s_a s_b, as 8 x 8 rational matrices.
    tri = results[0]["M_fun"]
    cols = []
    for k in range(8):
        e = tuple(F(1) if j == k else F(0) for j in range(8))
        cols.append(tri(e))
    mat = sp.Matrix(8, 8, lambda r_, c_: to_sp(cols[c_][r_]))
    x = sp.symbols("x")
    pa = sp.Matrix([to_sp(v) for v in a0])
    pb = sp.Matrix([to_sp(v) for v in b0])
    c_mat = (sp.eye(8) - pa * pa.T) * (sp.eye(8) - pb * pb.T)  # roots of norm 2: s_r = 1 - r r^T
    cp_t = sp.factor(mat.charpoly(x).as_expr())
    cp_c = sp.factor(c_mat.charpoly(x).as_expr())
    cp_tc = sp.factor((mat * c_mat).charpoly(x).as_expr())
    require(cp_t == (x - 1) ** 4 * (x**2 + x + 1) ** 2, cp_t)
    require(cp_c == (x - 1) ** 6 * (x**2 + x + 1), cp_c)
    require(mat * c_mat == c_mat * mat, "T' commutes with the family cycle")
    require((mat * c_mat) ** 3 == sp.eye(8) and mat * c_mat != sp.eye(8), "T' c has order 3")
    require(cp_tc == (x - 1) ** 2 * (x**2 + x + 1) ** 3, cp_tc)
    print("PASS  T' (class A2 x A2: det(x - T') = (x-1)^4 (x^2+x+1)^2) commutes with the family Coxeter element "
          "c = s_a s_b (class A2); T'c has order 3 and class 3 x A2 (det = (x-1)^2 (x^2+x+1)^3): the two 3's are "
          "independent, commuting order-3 elements")

    # The naive triality T of check_triality_d4d4 (standard coordinates) is one of the family but does not fix this
    # A2: show the contrast on the standard frame.
    from check_triality_d4d4 import triality_on_d4

    def t_std(r):
        lo = triality_on_d4(tuple(F(v, 2) for v in r[:4]))
        hi = triality_on_d4(tuple(F(v, 2) for v in r[4:]))
        return tuple(2 * v for v in lo + hi)

    a_std = tuple(int(v) for v in ALPHA)
    require(t_std(a_std) != a_std, "the naive T of check_triality_d4d4 moves this A2")
    print("PASS  contrast: the explicit triality of check_triality_d4d4.py moves this A2; the triality commuting with "
          "SU(3)_M is a different member of the same family (differing by Weyl elements of the two D4's)")


if __name__ == "__main__":
    main()
