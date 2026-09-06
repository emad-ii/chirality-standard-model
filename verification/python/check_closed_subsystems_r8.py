#!/usr/bin/env python3
"""Exact additive-closure census in the standard R^8 E6 model.

Coordinates are twice the usual coordinates, so every root has norm squared
8 and its Cartan pairing with another root is their integer dot product / 4.
The primary census enumerates positive simple systems; this census does not.

Completeness: encode a sign-stable root set by its 36 possible opposite pairs.
Starting with the empty set, adjoin each absent pair and repeatedly add every
ambient root that is a sum of two present roots. This terminates (only 36 pairs
can be added) at the least sign-stable, additively closed superset. Every closed
subsystem T is reached: adjoin its pairs one at a time, and every intermediate
closure stays inside T. Deduplicating already examined seeds or closed sets
does not remove any outgoing extension. In particular, full-rank proper sets
are still extended; there is no rank cutoff or preselected list of types.

Conversely, these closures are root subsystems: in this simply laced model,
reflection in a present root sends another root to itself, its negative, or
their sum/difference. Sign and additive closure therefore imply reflection
closure. A separate coordinate-level check validates sign/additive closure
of every enumerated set without using the enumeration's pair-sum table.

Only after enumeration do we recover components and their indecomposable
lexicographically positive roots. Exact R8 ranks, Cartan matrices and connected
ADE Dynkin graphs identify their types; root counts are additional checks,
never the source of a type label. All validation survives python -O.
"""

from collections import Counter, deque
from functools import lru_cache
from math import gcd

from verification_checks import VerificationFailure, require


def vector(*entries):
    return tuple(entries)


SIMPLE = (
    vector(1, -1, -1, -1, -1, -1, -1, 1),
    vector(2, 2, 0, 0, 0, 0, 0, 0),
    vector(-2, 2, 0, 0, 0, 0, 0, 0),
    vector(0, -2, 2, 0, 0, 0, 0, 0),
    vector(0, 0, -2, 2, 0, 0, 0, 0),
    vector(0, 0, 0, -2, 2, 0, 0, 0),
)
RANK = 6


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def subtract(x, y):
    return tuple(a - b for a, b in zip(x, y))


def negate(x):
    return tuple(-a for a in x)


def reflect_simple(root, i):
    mirror = SIMPLE[i]
    coefficient = dot(root, mirror)
    require(coefficient % 4 == 0)
    return subtract(root, tuple((coefficient // 4) * x for x in mirror))


def orbit(seed):
    seen, queue = {seed}, deque([seed])
    while queue:
        root = queue.popleft()
        for i in range(RANK):
            image = reflect_simple(root, i)
            if image not in seen:
                seen.add(image)
                queue.append(image)
    return frozenset(seen)


def determinant(matrix):
    """Exact Bareiss determinant, including singular matrices."""
    n = len(matrix)
    if n == 0:
        return 1
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot_row = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot_row is None:
                return 0
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * pivot - a[i][k] * a[k][j]
                require(numerator % previous == 0, "inexact Bareiss division")
                a[i][j] = numerator // previous
        previous = pivot
    return sign * a[-1][-1]


def span_rank(vectors):
    """Gaussian elimination in eight coordinates, using only integers."""
    rows = [list(row) for row in vectors]
    require(all(len(row) == 8 and all(type(x) is int for x in row)
                for row in rows), "expected integer R8 vectors")
    rank = 0
    for col in range(8):
        pivot = next((j for j in range(rank, len(rows)) if rows[j][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][col]
        for j in range(rank + 1, len(rows)):
            coefficient = rows[j][col]
            if coefficient:
                row = [scale * x - coefficient * y
                       for x, y in zip(rows[j], rows[rank])]
                divisor = gcd(*row)
                rows[j] = [x // divisor for x in row] if divisor else row
        rank += 1
    return rank


def dynkin_type(cartan):
    """Identify a connected finite ADE graph of rank at most six."""
    n = len(cartan)
    require(1 <= n <= RANK and all(len(row) == n for row in cartan),
            "invalid Cartan shape")
    require(all(type(cartan[i][j]) is int
                and cartan[i][j] == cartan[j][i]
                and (cartan[i][j] == 2 if i == j else cartan[i][j] in (0, -1))
                for i in range(n) for j in range(n)), "invalid Cartan entries")
    adjacent = [{j for j in range(n) if cartan[i][j] == -1} for i in range(n)]
    reached, queue = {0}, [0]
    for i in queue:
        for j in sorted(adjacent[i] - reached):
            reached.add(j)
            queue.append(j)
    require(len(reached) == n, "disconnected Dynkin graph")
    require(sum(map(len, adjacent)) == 2 * (n - 1), "Dynkin graph is not a tree")
    require(all(determinant([list(row[:k]) for row in cartan[:k]]) > 0
                for k in range(1, n + 1)), "Cartan matrix is not positive definite")
    degrees = [len(row) for row in adjacent]
    if max(degrees) <= 2:
        return f"A{n}"
    branches = [i for i in range(n) if degrees[i] == 3]
    require(max(degrees) == 3 and len(branches) == 1,
            "unsupported Dynkin branching")
    branch = branches[0]
    arms = []
    for neighbour in adjacent[branch]:
        previous, current, length = branch, neighbour, 1
        while adjacent[current] - {previous}:
            following, = adjacent[current] - {previous}
            previous, current = current, following
            length += 1
        arms.append(length)
    arms.sort()
    if n >= 4 and arms == [1, 1, n - 3]:
        return f"D{n}"
    require(n == 6 and arms == [1, 2, 2], "unsupported Dynkin arms")
    return "E6"


def validate_closed(system, ambient):
    """Validate actual signed coordinates, independently of the pair rules."""
    require(system <= ambient, "nonambient root")
    require(all(negate(root) in system for root in system), "missing negative root")
    ordered = sorted(system)
    for i, a in enumerate(ordered):
        for b in ordered[i:]:
            total = tuple(x + y for x, y in zip(a, b))
            require(total not in ambient or total in system, "missing root sum")


@lru_cache(maxsize=2_048)
def component_signature(piece):
    """Recover and verify a simple system, then return (root count, rank, type)."""
    require(piece and all(len(root) == 8 and dot(root, root) == 8 for root in piece),
            "invalid component roots")
    positive = {root for root in piece if root > (0,) * 8}
    simple = tuple(sorted(root for root in positive
                          if not any(subtract(root, other) in positive
                                     for other in positive)))
    rank = span_rank(sorted(piece))
    require(len(simple) == rank and span_rank(simple) == rank,
            "simple roots do not form a component basis")
    products = [[dot(a, b) for b in simple] for a in simple]
    require(all(value % 4 == 0 for row in products for value in row),
            "nonintegral Cartan pairing")
    kind = dynkin_type([[value // 4 for value in row] for row in products])

    # Check that the recovered simple roots really generate this whole piece.
    generated = set(simple) | {negate(root) for root in simple}
    require(generated <= piece, "simple root negatives are missing")
    queue = sorted(generated)
    for root in queue:
        for mirror in simple:
            pairing = dot(root, mirror)
            require(pairing % 4 == 0, "nonintegral reflection pairing")
            image = subtract(root, tuple((pairing // 4) * x for x in mirror))
            require(image in piece, "component is not reflection closed")
            if image not in generated:
                generated.add(image)
                queue.append(image)
    require(generated == piece, "simple roots do not generate the component")
    expected_size = (rank * (rank + 1) if kind.startswith("A") else
                     2 * rank * (rank - 1) if kind.startswith("D") else 72)
    require(len(piece) == expected_size, "Dynkin type/root-count mismatch")
    return len(piece), rank, kind


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


class RootPairs:
    """Opposite-pair masks and coordinate-derived additive implications."""

    def __init__(self, roots):
        self.roots = frozenset(roots)
        require(len(self.roots) == 72
                and all(len(root) == 8 and dot(root, root) == 8
                        for root in self.roots),
                "invalid ambient E6 roots")
        validate_closed(self.roots, self.roots)
        require(component_signature(self.roots) == (72, RANK, "E6"),
                "ambient R8 system is not E6")
        self.positive = tuple(sorted(root for root in self.roots if root > (0,) * 8))
        require(len(self.positive) == 36, "expected 36 opposite pairs")
        self.full = (1 << len(self.positive)) - 1
        self.pair_bit = {signed: 1 << i for i, root in enumerate(self.positive)
                         for signed in (root, negate(root))}
        rules = [[] for _ in self.positive]
        self.adjacent = []
        for i, a in enumerate(self.positive):
            self.adjacent.append(sum(1 << j for j, b in enumerate(self.positive)
                                     if dot(a, b)))
            for j, b in enumerate(self.positive):
                if j == i:
                    continue  # 0 and twice a root are not ambient roots.
                additions = 0
                for left in (a, negate(a)):
                    for right in (b, negate(b)):
                        total = tuple(x + y for x, y in zip(left, right))
                        additions |= self.pair_bit.get(total, 0)
                if additions:
                    rules[i].append((1 << j, additions))
        self.rules = tuple(tuple(row) for row in rules)

    def root_set(self, mask):
        require(type(mask) is int and 0 <= mask <= self.full, "invalid pair mask")
        return frozenset(signed for i in indices(mask)
                         for signed in (self.positive[i], negate(self.positive[i])))

    def adjoin(self, closed, i):
        """Saturate one extension; the caller supplies an already closed mask."""
        require(type(closed) is int and 0 <= closed <= self.full
                and type(i) is int and 0 <= i < len(self.positive),
                "invalid adjoining input")
        mask = closed | (1 << i)
        pending = mask ^ closed
        while pending:
            bit = pending & -pending
            pending ^= bit
            for partner, additions in self.rules[bit.bit_length() - 1]:
                if mask & partner:
                    new = additions & ~mask
                    mask |= new
                    pending |= new
        return mask

    def enumerate(self):
        seen, tested, queue = {0}, {0}, [0]
        for closed in queue:
            for i in indices(self.full ^ closed):
                seed = closed | (1 << i)
                if seed in tested:
                    continue
                tested.add(seed)
                enlarged = self.adjoin(closed, i)
                if enlarged not in seen:
                    seen.add(enlarged)
                    queue.append(enlarged)
        return seen

    def signature(self, mask):
        system = self.root_set(mask)
        validate_closed(system, self.roots)
        remaining, pieces = mask, []
        while remaining:
            pending = remaining & -remaining
            piece = 0
            while pending:
                bit = pending & -pending
                pending ^= bit
                piece |= bit
                remaining &= ~bit
                pending |= self.adjacent[bit.bit_length() - 1] & remaining
            pieces.append(component_signature(self.root_set(piece)))
        rank = span_rank(sorted(system))
        require(rank == sum(row[1] for row in pieces), "component rank mismatch")
        pieces.sort(key=lambda row: (-row[1], row[2]))
        return len(system), rank, "+".join(row[2] for row in pieces)


def validate_maximal_types(actual):
    require(actual == Counter({
        (40, 5, "D5"): 27,
        (32, 6, "A5+A1"): 36,
        (18, 6, "A2+A2+A2"): 40,
    }), "maximal rank/Dynkin-type census mismatch")


def negative_controls(model, maximal_types):
    """Exercise real validation paths, including same-size type impostors."""
    def rejects(function, *args, reason):
        try:
            function(*args)
        except VerificationFailure as error:
            require(reason in str(error), ("unexpected rejection", str(error)))
        else:
            raise VerificationFailure(f"negative control accepted: {reason}")

    rejects(dynkin_type, [[2, 1], [1, 2]], reason="invalid Cartan entries")
    rejects(dynkin_type, [[2, -1], [0, 2]], reason="invalid Cartan entries")
    rejects(dynkin_type, [[2, 0], [0, 2]], reason="disconnected Dynkin graph")
    rejects(dynkin_type, [[2, -1, -1], [-1, 2, -1], [-1, -1, 2]],
            reason="not a tree")
    affine_d4 = [[2 if i == j else -1 if i == 0 or j == 0 else 0
                  for j in range(5)] for i in range(5)]
    rejects(dynkin_type, affine_d4, reason="not positive definite")

    a, b = SIMPLE[0], SIMPLE[2]
    unsigned = frozenset((a,))
    unsaturated = frozenset((a, negate(a), b, negate(b)))
    rejects(validate_closed, unsigned, model.roots, reason="missing negative")
    rejects(validate_closed, unsaturated, model.roots, reason="missing root sum")
    rejects(validate_closed, frozenset({(0,) * 8}), model.roots, reason="nonambient")
    rejects(model.root_set, -1, reason="invalid pair mask")
    rejects(model.root_set, model.full + 1, reason="invalid pair mask")
    rejects(model.adjoin, 0, len(model.positive), reason="invalid adjoining input")

    # Six roots can be A2 or 3A1: graph and coordinate rank must distinguish them.
    a2 = model.adjoin(model.pair_bit[a], model.pair_bit[b].bit_length() - 1)
    orthogonal = (SIMPLE[0], SIMPLE[1], SIMPLE[4])
    three_a1 = sum(model.pair_bit[root] for root in orthogonal)
    require(model.signature(a2) == (6, 2, "A2"), "A2 control failed")
    require(model.signature(three_a1) == (6, 3, "A1+A1+A1"), "3A1 control failed")
    rejects(component_signature, model.root_set(three_a1),
            reason="disconnected Dynkin graph")
    for bad_key in ((40, 5, "A5"), (40, 6, "D5")):
        corrupted = maximal_types.copy()
        corrupted[bad_key] = corrupted.pop((40, 5, "D5"))
        rejects(validate_maximal_types, corrupted, reason="rank/Dynkin-type census")


def census(*, include_subsystems=False):
    model = RootPairs(orbit(SIMPLE[0]))
    subsystems = model.enumerate()
    require(len(subsystems) == 5_079 and 0 in subsystems and model.full in subsystems,
            "closed-subsystem universe mismatch")
    # Validate every subsystem, not just the eventual maximal representatives.
    signatures = {mask: model.signature(mask) for mask in sorted(subsystems)}
    proper = sorted(subsystems - {model.full},
                    key=lambda mask: (mask.bit_count(), mask), reverse=True)
    maximal = [mask for i, mask in enumerate(proper)
               if not any(mask & larger == mask for larger in proper[:i])]
    maximal_types = Counter(signatures[mask] for mask in maximal)
    require(len(maximal) == 103, "maximal proper count mismatch")
    validate_maximal_types(maximal_types)
    negative_controls(model, maximal_types)
    # Keep the certificate consumer's exact schema, deriving values from the scan.
    names = Counter()
    for (_, _, kind), count in maximal_types.items():
        names["A2^3" if kind == "A2+A2+A2" else kind] += count
    result = {
        "closed_subsystems": len(subsystems),
        "maximal_proper": len(maximal),
        "maximal_types": dict(names),
    }
    if include_subsystems:
        return (result, frozenset(model.root_set(mask) for mask in subsystems),
                frozenset(model.root_set(mask) for mask in maximal))
    return result


def main():
    result = census()
    print("Closed-subsystem census passed (independent R8 realization)")
    print(f"closed subsystems={result['closed_subsystems']:,}; "
          f"maximal proper={result['maximal_proper']}")
    print("maximal types: " + ", ".join(
        f"{kind}={result['maximal_types'][kind]}" for kind in ("D5", "A5+A1", "A2^3")
    ))
    print("enumeration: exhaustive root-pair adjoining and additive closure")
    print("all subsystems: exact R8 ranks, simple roots and Cartan/Dynkin types verified")
    print("negative controls: invalid graphs, types, ranks and closure rejected")


if __name__ == "__main__":
    main()
