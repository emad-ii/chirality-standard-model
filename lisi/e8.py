#!/usr/bin/env python3
"""Exact E8 root system helpers (standard library only).

Roots are stored in *doubled* integer coordinates so every arithmetic step is
exact.  With r = 2 * (true coordinates):

* 112 roots of shape (+-2, +-2, 0^6) in any positions,
* 128 roots of shape (+-1)^8 with an even number of minus signs.

The true inner product is dot(r, s) / 4, so every root has norm 2 and the
inner product of two roots lies in {-2, -1, 0, 1, 2}.
"""

from __future__ import annotations

from itertools import combinations, product
from pathlib import Path
import sys

# Reuse the repository's always-on invariant checker.
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verification" / "python"))
from verification_checks import VerificationFailure, require  # noqa: E402

Vec = tuple[int, ...]


def e8_roots() -> list[Vec]:
    """Return the 240 roots of E8 in doubled integer coordinates."""
    roots: list[Vec] = []
    for i, j in combinations(range(8), 2):
        for si, sj in product((2, -2), repeat=2):
            v = [0] * 8
            v[i], v[j] = si, sj
            roots.append(tuple(v))
    for signs in product((1, -1), repeat=8):
        if signs.count(-1) % 2 == 0:
            roots.append(tuple(signs))
    require(len(roots) == 240, len(roots))
    return roots


def dot(a: Vec, b: Vec) -> int:
    """Raw dot product of doubled vectors (true inner product is dot / 4)."""
    return sum(x * y for x, y in zip(a, b))


def inner(a: Vec, b: Vec) -> int:
    """True inner product of two doubled E8 roots (always an integer)."""
    d = dot(a, b)
    require(d % 4 == 0, (a, b))
    return d // 4


def neg(a: Vec) -> Vec:
    return tuple(-x for x in a)


def add(a: Vec, b: Vec) -> Vec:
    return tuple(x + y for x, y in zip(a, b))


def self_tests() -> None:
    """Sanity checks that make the rest of the package trustworthy."""
    roots = e8_roots()
    rootset = set(roots)
    require(len(rootset) == 240, "duplicate roots")
    require(all(inner(r, r) == 2 for r in roots), "all roots have norm 2")
    require(all(neg(r) in rootset for r in roots), "root system is symmetric")
    # Integrality and closure: for roots a, b with <a,b> = -1, a + b is a root.
    for a in roots:
        for b in roots:
            c = inner(a, b)
            require(-2 <= c <= 2, c)
            if c == -1:
                require(add(a, b) in rootset, "closure under addition")
    # Each root has 56 neighbours at each of inner product 1 and -1, 126 at 0
    # (126 = 2 * 63, the E7 roots orthogonal to a given root).
    r0 = roots[0]
    counts = {c: 0 for c in (-2, -1, 0, 1, 2)}
    for s in roots:
        counts[inner(r0, s)] += 1
    require(counts == {-2: 1, -1: 56, 0: 126, 1: 56, 2: 1}, counts)


if __name__ == "__main__":
    self_tests()
    print("PASS  E8 root system: 240 roots, norm 2, closed, E7 = 126 orthogonal roots")
