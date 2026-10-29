#!/usr/bin/env python3
"""E8 > D4 x D4 and triality: the structure behind Lisi's three generations.

Checks, from the root system alone,

    248 = (28, 1) + (1, 28) + (8v, 8v) + (8s, 8s) + (8c, 8c)

and builds an order-3 linear map (triality, applied to both D4 factors at once)
that permutes the E8 roots and cycles the three 64-dimensional blocks.  This is
the mathematical fact Lisi uses to obtain three generations; it is *not* the
same mechanism as the SU(3)_M family symmetry in the chirality theorem.
"""

from __future__ import annotations

from fractions import Fraction

from e8 import Vec, e8_roots, require, self_tests


def block_class(r: Vec) -> str:
    """Classify a root by its (D4 x D4) block."""
    lo, hi = r[:4], r[4:]
    nz_lo = sum(1 for x in lo if x)
    nz_hi = sum(1 for x in hi if x)
    if nz_lo == 2 and nz_hi == 0:
        return "28a"
    if nz_lo == 0 and nz_hi == 2:
        return "28b"
    if nz_lo == 1 and nz_hi == 1:
        return "8v x 8v"
    require(nz_lo == 4 and nz_hi == 4, r)  # half-integer roots
    p_lo = sum(1 for x in lo if x < 0) % 2
    p_hi = sum(1 for x in hi if x < 0) % 2
    require(p_lo == p_hi, "total parity is even")
    return "8s x 8s" if p_lo == 0 else "8c x 8c"


def reflect_doubled(x: tuple[Fraction, ...], n: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    nn = sum(c * c for c in n)
    k = 2 * sum(a * b for a, b in zip(x, n)) / nn
    return tuple(a - k * b for a, b in zip(x, n))


def triality_on_d4(x: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    """Order-3 map on R^4 cycling the weights of 8v, 8s, 8c (F4 Weyl element)."""
    h = (Fraction(1, 2),) * 4
    e1 = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))
    return reflect_doubled(reflect_doubled(x, e1), h)


def main() -> None:
    self_tests()
    roots = e8_roots()
    rootset = set(roots)

    counts: dict[str, int] = {}
    for r in roots:
        k = block_class(r)
        counts[k] = counts.get(k, 0) + 1
    require(
        counts == {"28a": 24, "28b": 24, "8v x 8v": 64, "8s x 8s": 64, "8c x 8c": 64},
        counts,
    )
    require(sum(counts.values()) == 240, "partition of the 240 roots")
    print("PASS  E8 > D4 x D4: 240 = 24 + 24 + 64 + 64 + 64 (roots of (28,1),(1,28),(8,8) x 3)")

    # --- triality on both D4 factors simultaneously ------------------------
    def apply(r: Vec) -> Vec:
        lo = triality_on_d4(tuple(Fraction(x, 2) for x in r[:4]))
        hi = triality_on_d4(tuple(Fraction(x, 2) for x in r[4:]))
        out = []
        for c in lo + hi:
            d = 2 * c
            require(d.denominator == 1, d)
            out.append(int(d))
        return tuple(out)

    image = [apply(r) for r in roots]
    require(set(image) == rootset, "map preserves the E8 root set")

    # A single D4 reflection pair has order 3 on the weight lattice of D4.
    def cube(r: Vec) -> Vec:
        return apply(apply(apply(r)))

    require(all(cube(r) == r for r in roots), "map has order 3 on roots")
    require(any(apply(r) != r for r in roots), "map is not the identity")

    # It cycles the three 64-blocks (and fixes the two 28-blocks as sets).
    cycle = {}
    for r in roots:
        cycle.setdefault(block_class(r), set()).add(block_class(apply(r)))
    require(cycle["28a"] == {"28a"} and cycle["28b"] == {"28b"}, cycle)
    blocks64 = ["8v x 8v", "8s x 8s", "8c x 8c"]
    require(all(len(cycle[b]) == 1 for b in blocks64), cycle)
    targets = [next(iter(cycle[b])) for b in blocks64]
    require(sorted(targets) == sorted(blocks64), "permutes the three 64-blocks")
    require(len(set(targets)) == 3 and all(t != b for t, b in zip(targets, blocks64)), "no 64-block fixed")
    print("PASS  triality is an order-3 automorphism of the E8 roots permuting (8,8)v -> (8,8)s -> (8,8)c")


if __name__ == "__main__":
    main()
