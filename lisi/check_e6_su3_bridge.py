#!/usr/bin/env python3
"""E8 > E6 x SU(3): the family structure used by this repository's theorem.

Builds the pair from the root system alone and checks the branching

    248 = (78, 1) + (1, 8) + (27, 3) + (27bar, 3bar)

root by root, then verifies the E6 cubic structure of the 27 (the invariant
whose existence is why E6 is anomaly-free despite being chiral).
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations
from fractions import Fraction

from e8 import Vec, e8_roots, inner, require, self_tests

# SU(3)_M = A2 spanned by two E8 roots with inner product -1.
ALPHA: Vec = (2, -2, 0, 0, 0, 0, 0, 0)
BETA: Vec = (0, 2, -2, 0, 0, 0, 0, 0)

# Dynkin labels (<r,alpha>, <r,beta>) of SU(3) weights.
THREE = {(1, 0), (-1, 1), (0, -1)}
THREE_BAR = {(0, 1), (1, -1), (-1, 0)}
ADJOINT = {(2, -1), (-1, 2), (1, 1), (-2, 1), (1, -2), (-1, -1)}


def e6_part(r: Vec) -> tuple[Fraction, ...]:
    """Component of a doubled root orthogonal to the A2 plane (true coords)."""
    # Solve for projection onto span(alpha, beta) with the A2 Cartan matrix.
    a, b = inner(r, ALPHA), inner(r, BETA)
    # inverse Cartan of A2 = (1/3) [[2,1],[1,2]]
    ca = Fraction(2 * a + b, 3)
    cb = Fraction(a + 2 * b, 3)
    return tuple(
        Fraction(x, 2) - ca * Fraction(p, 2) - cb * Fraction(q, 2)
        for x, p, q in zip(r, ALPHA, BETA)
    )


def main() -> None:
    self_tests()
    roots = e8_roots()
    require(inner(ALPHA, BETA) == -1 and inner(ALPHA, ALPHA) == 2, "A2 pair")

    by_label: dict[tuple[int, int], list[Vec]] = defaultdict(list)
    for r in roots:
        by_label[(inner(r, ALPHA), inner(r, BETA))].append(r)

    # --- dimension count by SU(3) weight ---------------------------------
    n_e6 = len(by_label[(0, 0)])
    n_adj = sum(len(by_label[k]) for k in ADJOINT)
    require(n_e6 == 72, n_e6)  # roots of E6
    require(n_adj == 6, n_adj)  # roots of SU(3)
    for k in THREE | THREE_BAR:
        require(len(by_label[k]) == 27, (k, len(by_label[k])))
    require(set(by_label) == {(0, 0)} | THREE | THREE_BAR | ADJOINT, set(by_label))
    require(n_e6 + n_adj + 6 * 27 == 240, "root partition")
    # Dimensions: 78 + 8 + 81 + 81 = 248 (Cartan: 6 + 2 = 8 included in 78, 8)
    require(78 + 8 + 27 * 3 * 2 == 248, "dimension sum")

    # --- the 27 is the same E6 weight set over each SU(3) weight ----------
    sets_3 = [frozenset(e6_part(r) for r in by_label[k]) for k in sorted(THREE)]
    sets_3b = [frozenset(e6_part(r) for r in by_label[k]) for k in sorted(THREE_BAR)]
    require(all(len(s) == 27 for s in sets_3 + sets_3b), "27 distinct weights")
    require(len(set(sets_3)) == 1, "same 27 over each weight of the 3")
    require(len(set(sets_3b)) == 1, "same 27bar over each weight of the 3bar")
    w27 = sets_3[0]
    w27bar = sets_3b[0]
    require(w27bar == frozenset(tuple(-x for x in w) for w in w27), "27bar = -27")
    require(w27 != w27bar, "27 is not self-conjugate (complex type)")
    require(not (w27 & w27bar), "27 and 27bar share no weights")

    # --- E6 cubic invariant: weight triples summing to zero ---------------
    triples = [
        t
        for t in combinations(sorted(w27), 3)
        if all(sum(c) == 0 for c in zip(*t))
    ]
    require(len(triples) == 45, len(triples))  # 45 tritangent planes
    # Each weight lies in exactly 5 of the 45 triples (45 * 3 / 27 = 5).
    per_weight: dict[tuple[Fraction, ...], int] = defaultdict(int)
    for t in triples:
        for w in t:
            per_weight[w] += 1
    require(set(per_weight.values()) == {5} and len(per_weight) == 27, "5 per weight")

    print("PASS  E8 > E6 x SU(3): 240 = 72 + 6 + 6*27 (162)")
    print("PASS  27 repeated over each weight of the 3; 27bar = -27, no shared weights")
    print("PASS  E6 cubic invariant on the 27: 45 zero-sum weight triples, 5 per weight")


if __name__ == "__main__":
    main()
