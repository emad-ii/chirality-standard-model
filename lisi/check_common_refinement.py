#!/usr/bin/env python3
"""Common refinement of E6 x SU(3) and D4 x D4 inside E8.

SU(3)_M = A2 sits inside the first D4 (coordinates 1-3).  Its centralizer E6
then contains the second D4 (coordinates 5-8).  We compute, from roots only:

* how the 72 roots of E6 split among the D4 x D4 blocks,
* how each 27 (one per weight of the 3) decomposes under the second D4.

Expected: 72 = 24 + 16 + 32, and 27 = 8v + 8s + 8c + 1 + 1 + 1, i.e. the
triality triple appears inside every 27.
"""

from __future__ import annotations

from collections import Counter, defaultdict

from check_e6_su3_bridge import ADJOINT, ALPHA, BETA, THREE, THREE_BAR
from check_triality_d4d4 import block_class
from e8 import Vec, e8_roots, inner, require, self_tests


def d4_type(hi: tuple[int, ...]) -> str:
    """Type of a doubled D4 weight (coords 5-8 of a root)."""
    nz = sum(1 for x in hi if x)
    if nz == 0:
        return "1"
    if nz == 1:
        return "8v"
    if nz == 2:
        return "28"
    require(nz == 4, hi)
    return "8s" if sum(1 for x in hi if x < 0) % 2 == 0 else "8c"


def main() -> None:
    self_tests()
    roots = e8_roots()
    by_label: dict[tuple[int, int], list[Vec]] = defaultdict(list)
    for r in roots:
        by_label[(inner(r, ALPHA), inner(r, BETA))].append(r)

    # --- E6 roots against the D4 x D4 blocks -------------------------------
    e6 = by_label[(0, 0)]
    split = Counter(block_class(r) for r in e6)
    require(split == {"28b": 24, "8v x 8v": 16, "8s x 8s": 16, "8c x 8c": 16}, split)
    # The first D4 contributes no root: A2 fills its rank-3 part.
    require(split["28a"] == 0, "no root of the first D4 centralizes A2")
    print("PASS  E6 roots = 24 (second D4) + 16 + 16 + 16 across (8v,8v),(8s,8s),(8c,8c)")

    # --- each 27 under the second D4 ---------------------------------------
    for label in sorted(THREE | THREE_BAR):
        c = Counter(d4_type(r[4:]) for r in by_label[label])
        require(c == {"8v": 8, "8s": 8, "8c": 8, "1": 3}, (label, c))
    require(ADJOINT, "adjoint labels defined")
    print("PASS  every 27 = 8v + 8s + 8c + 1 + 1 + 1 under the second D4 (triality triple in E6)")

    # --- which D4 x D4 block feeds each SU(3) weight ----------------------
    table = {}
    for label in sorted(THREE | THREE_BAR):
        table[label] = dict(Counter(block_class(r) for r in by_label[label]))
    for label, row in table.items():
        require(sum(row.values()) == 27, row)
    print("INFO  block content of each 27 (SU(3) Dynkin label -> D4 x D4 blocks):")
    for label, row in table.items():
        print(f"        {label!s:8} {row}")


if __name__ == "__main__":
    main()
