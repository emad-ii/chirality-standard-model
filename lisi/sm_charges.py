#!/usr/bin/env python3
"""Standard Model quantum numbers inside the 27 of E6, from the E8 roots (sympy).

The 27 of the E6 x SU(3)_M branching E8 > E6 x SU(3) is the set of E6 weights
carried by the E8 roots over one weight of the 3 (`check_e6_su3_bridge.py`).
Fixing one weight w0 of the 27 (true coordinates, <w0, w0> = 4/3) gives
E6 > SO(10) x U(1):

    27 = 1 + 16 + 10     with  <w, w0> = 4/3, 1/3, -2/3,

and the 40 SO(10) roots are the E6 roots orthogonal to w0.  Inside SO(10) one
A2 x A1 -- roots a, b (SU(3) colour) and g (SU(2)_L) -- and one hypercharge
vector Y are selected, and every weight is then read off by inner products:

    colour class  from the Dynkin labels (<w, a>, <w, b>)
    weak isospin  T3 = <w, g> / 2           (a doublet iff <w, g> != 0)
    hypercharge   Y  = <w, Y>               Q = T3 + Y

`python3 sm_charges.py` asserts, with exact rationals only:

* 27 = 1 + 16 + 10, 40 SO(10) roots, a, b, g roots of SO(10) forming A2 x A1,
  Y orthogonal to a, b, g, w0 and to the horizontal SU(3)_M;
* the 16 is exactly Q_L, u^c, d^c, L, nu^c, e^c, and the 10 is D, D^c, H_d, H_u;
* sum Y = sum Y^3 = sum Q = sum Q^3 = 0 over the 16, and the mixed
  SU(2)^2 Y and SU(3)^2 Y sums vanish; the 10 is vector-like;
* Y takes the SU(5) pattern on the 40 SO(10) roots.

Provenance.  This module was rewritten from `THEORY.md` section 2 and from
`report/sm_charges.tex`, which the original generated: the vectors w0, a, b, g
and Y below are the ones printed there.  The original file was not in the
repository when the rewrite was made.  `make_report.py` regenerates
`report/sm_charges.tex` from `build()`, and the result matches the committed
file, which is the test that the rewrite computes what the original did.
Nothing here derives the physical Standard Model; it checks that the pair
contains one generation's quantum numbers.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F

import sympy as sp

from check_e6_su3_bridge import ALPHA, BETA, THREE, THREE_BAR, e6_part
from e8 import e8_roots, inner, require

Rat = sp.Rational

# The vectors, in true coordinates (doubled E8 coordinates halved).
W0 = (F(-2, 3), F(-2, 3), F(-2, 3), F(0), F(0), F(0), F(0), F(0))
A_ROOT = (F(0), F(0), F(0), F(1), F(1), F(0), F(0), F(0))
B_ROOT = (F(0), F(0), F(0), F(-1), F(0), F(1), F(0), F(0))
G_ROOT = (F(0), F(0), F(0), F(0), F(0), F(0), F(1), F(1))
Y_VEC = (F(0), F(0), F(0), F(1, 3), F(-1, 3), F(1, 3), F(1, 2), F(-1, 2))

# E6 U(1) value <w, w0> of each part of the 27.
FAMILY_OF = {F(4, 3): "1", F(1, 3): "16", F(-2, 3): "10"}

# The Standard Model content, as {(colour, su(2) dimension, Y): weights}.
SM_16 = {
    ("3", 2, Rat(1, 6)): 6,  # Q_L
    ("3b", 1, Rat(-2, 3)): 3,  # u^c
    ("3b", 1, Rat(1, 3)): 3,  # d^c
    ("1", 2, Rat(-1, 2)): 2,  # L
    ("1", 1, Rat(0)): 1,  # nu^c
    ("1", 1, Rat(1)): 1,  # e^c
}
SM_10 = {
    ("3", 1, Rat(-1, 3)): 3,  # D
    ("3b", 1, Rat(1, 3)): 3,  # D^c
    ("1", 2, Rat(1, 2)): 2,  # H_u
    ("1", 2, Rat(-1, 2)): 2,  # H_d
}
NAMES_16 = {
    ("3", 2, Rat(1, 6)): "Q_L",
    ("3b", 1, Rat(-2, 3)): "u^c",
    ("3b", 1, Rat(1, 3)): "d^c",
    ("1", 2, Rat(-1, 2)): "L",
    ("1", 1, Rat(0)): "nu^c",
    ("1", 1, Rat(1)): "e^c",
}


def dp(u, v) -> F:
    return sum((x * y for x, y in zip(u, v)), F(0))


def rat(x: F) -> sp.Rational:
    return Rat(x.numerator, x.denominator)


def column(v) -> sp.Matrix:
    return sp.Matrix([rat(x) for x in v])


@dataclass
class Model:
    """The Standard Model reading of the 27, as sympy column vectors."""

    w0: sp.Matrix
    a: sp.Matrix
    b: sp.Matrix
    g: sp.Matrix
    Y: sp.Matrix
    d5_roots: list  # the 40 SO(10) roots, as tuples of Fractions
    families: dict  # "1", "16", "10" -> list of weight records


def colour_class(label: tuple) -> str:
    if label == (0, 0):
        return "1"
    if label in THREE:
        return "3"
    require(label in THREE_BAR, label)
    return "3b"


def build() -> Model:
    """Read the 27 off the E8 roots.  Exact; every step is asserted."""
    roots = e8_roots()
    by_label: dict = {}
    for r in roots:
        by_label.setdefault((inner(r, ALPHA), inner(r, BETA)), []).append(r)
    # one weight of the 3 fixes the copy of the 27 (the same set sits over each)
    w27 = sorted({e6_part(r) for r in by_label[sorted(THREE)[0]]})
    require(len(w27) == 27 and W0 in w27, "w0 is a weight of the 27")
    e6_roots = [e6_part(r) for r in by_label[(0, 0)]]
    d5 = [r for r in e6_roots if dp(r, W0) == 0]
    require(len(e6_roots) == 72 and len(d5) == 40, (len(e6_roots), len(d5)))

    families: dict = {"1": [], "16": [], "10": []}
    for w in w27:
        name = FAMILY_OF[dp(w, W0)]
        label = (dp(w, A_ROOT), dp(w, B_ROOT))
        t3 = Rat(1, 2) * rat(dp(w, G_ROOT))
        y = rat(dp(w, Y_VEC))
        families[name].append({
            "w": column(w),
            "color": colour_class(label),
            "su2": 2 if dp(w, G_ROOT) != 0 else 1,
            "T3": t3,
            "Y": y,
            "Q": t3 + y,
        })
    require({k: len(v) for k, v in families.items()} == {"1": 1, "16": 16, "10": 10},
            {k: len(v) for k, v in families.items()})
    return Model(column(W0), column(A_ROOT), column(B_ROOT), column(G_ROOT),
                 column(Y_VEC), d5, families)


def content(records) -> Counter:
    """Multiset of (colour, su(2) dimension, Y) over a list of weight records."""
    return Counter((r["color"], r["su2"], r["Y"]) for r in records)


def _sum(records, f) -> sp.Rational:
    return sp.nsimplify(sum(f(r) for r in records))


def main() -> Model:
    m = build()
    f16, f10, f1 = m.families["16"], m.families["10"], m.families["1"]
    d5 = set(m.d5_roots)

    # --- the subalgebras and the hypercharge vector ---------------------------------
    require(all(x in d5 for x in (A_ROOT, B_ROOT, G_ROOT)), "a, b, g are SO(10) roots")
    require(dp(A_ROOT, A_ROOT) == dp(B_ROOT, B_ROOT) == dp(G_ROOT, G_ROOT) == 2, "norm 2")
    require(dp(A_ROOT, B_ROOT) == -1, "a, b span an A2")
    require(dp(G_ROOT, A_ROOT) == dp(G_ROOT, B_ROOT) == 0, "g commutes with the A2")
    alpha = tuple(F(x, 2) for x in ALPHA)
    beta = tuple(F(x, 2) for x in BETA)
    require(all(dp(Y_VEC, v) == 0 for v in (A_ROOT, B_ROOT, G_ROOT, W0, alpha, beta)),
            "Y is orthogonal to a, b, g, w0 and the horizontal SU(3)")
    print("PASS  E6 > SO(10) x U(1): 72 E6 roots, 40 of them orthogonal to w0 = SO(10); "
          "a, b (A2, colour) and g (SU(2)_L) are SO(10) roots, Y commutes with all of them")

    # --- 27 = 1 + 16 + 10 ----------------------------------------------------------
    require(len(f1) + len(f16) + len(f10) == 27, "27")
    require(sorted({dp(tuple(F(x.p, x.q) for x in r["w"]), W0) for r in f16}) == [F(1, 3)], "16")
    print("PASS  27 = 1 + 16 + 10 with <w, w0> = 4/3, 1/3, -2/3 (E6 U(1) charges 4 : 1 : -2)")

    # --- Standard Model content ----------------------------------------------------
    require(dict(content(f16)) == SM_16, dict(content(f16)))
    require(dict(content(f10)) == SM_10, dict(content(f10)))
    require(content(f1) == Counter({("1", 1, Rat(0)): 1}) and f1[0]["Q"] == 0, "singlet")
    print("PASS  the 16 is Q_L (3,2)_1/6, u^c (3b,1)_-2/3, d^c (3b,1)_1/3, L (1,2)_-1/2, "
          "nu^c (1,1)_0, e^c (1,1)_1; the 10 is D, D^c, H_u, H_d; the extra singlet has Y = Q = 0")
    charges = Counter((NAMES_16[k], q) for k in SM_16 for q in
                      sorted({r["Q"] for r in f16 if (r["color"], r["su2"], r["Y"]) == k}))
    require(charges[("e^c", Rat(1))] == 1 and charges[("L", Rat(-1))] == 1
            and charges[("L", Rat(0))] == 1 and charges[("nu^c", Rat(0))] == 1,
            "electric charges")
    require(sorted({r["Q"] for r in f16}) == [-1, Rat(-2, 3), Rat(-1, 3), 0, Rat(1, 3), Rat(2, 3), 1],
            sorted({r["Q"] for r in f16}))
    print("PASS  electric charges Q = T3 + Y of the 16 are 0, +-1/3, +-2/3, +-1 as they should be")

    # --- anomaly-type sums ---------------------------------------------------------
    for label, power in (("Y", 1), ("Y^3", 3)):
        require(_sum(f16, lambda r: r["Y"] ** power) == 0, label)
        require(_sum(f10, lambda r: r["Y"] ** power) == 0, label + " (10)")
    for label, power in (("Q", 1), ("Q^3", 3)):
        require(_sum(f16, lambda r: r["Q"] ** power) == 0, label)
    require(_sum(f16, lambda r: r["T3"] ** 2 * r["Y"]) == 0, "SU(2)^2 Y")
    # SU(3)^2 Y: each colour triplet or antitriplet has index 1/2
    require(_sum([r for r in f16 if r["color"] != "1"], lambda r: Rat(1, 3) * r["Y"]) == 0,
            "SU(3)^2 Y")
    print("PASS  over the 16: sum Y = sum Y^3 = sum Q = sum Q^3 = 0 (exact), and the mixed "
          "SU(2)^2 Y and SU(3)^2 Y sums vanish; the 10 is vector-like (its Y sums cancel)")

    # --- the SU(5) pattern of Y on the SO(10) roots --------------------------------
    pattern = Counter(abs(dp(r, Y_VEC)) for r in d5)
    require(dict(pattern) == {F(0): 8, F(5, 6): 12, F(1, 6): 12, F(2, 3): 6, F(1): 2}, dict(pattern))
    print("PASS  Y on the 40 SO(10) roots: 8 at 0, 12 at +-5/6, 12 at +-1/6, 6 at +-2/3, 2 at +-1 "
          "(the standard hypercharge, not a flipped one)")
    return m


if __name__ == "__main__":
    main()
