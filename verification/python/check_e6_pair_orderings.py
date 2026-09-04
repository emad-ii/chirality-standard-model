#!/usr/bin/env python3
"""Check group d_chi for the restricted 27 in the pair-first E6 census.

Weight cancellation alone computes a torus invariant.  It computes group
d_chi here only after verifying that the restricted character is a sum of
minuscule characters (including trivial characters).  This is not a general
irreducible-character decomposition routine.
"""

from collections import Counter
from collections.abc import Mapping
from functools import lru_cache
from itertools import combinations_with_replacement, product

import verify_e6_extrema as e6

from verification_checks import VerificationFailure, require


def _require_vector(vector, label):
    require(isinstance(vector, tuple) and len(vector) == e6.N
            and all(type(x) is int for x in vector),
            f"{label} must be a tuple of six integers")


def _weight_multiplicities(weights):
    items = weights.items() if isinstance(weights, Mapping) else (
        (weight, 1) for weight in weights
    )
    character = Counter()
    for weight, multiplicity in items:
        _require_vector(weight, "weight")
        require(type(multiplicity) is int and multiplicity >= 0,
                "weight multiplicities must be nonnegative integers")
        if multiplicity:
            character[weight] += multiplicity
    return character


@lru_cache(maxsize=1)
def _ambient_roots():
    return e6.orbit(e6.E[0], e6.reflect_root)


def _root_set(parent_roots):
    roots = tuple(parent_roots)
    for root in roots:
        _require_vector(root, "root")
    roots = frozenset(roots)
    require(roots <= _ambient_roots(), "parent contains a non-E6 root")
    return roots


def _restrict(character, roots):
    restricted = Counter()
    for weight, multiplicity in character.items():
        restricted[tuple(e6.pairing(weight, root) for root in roots)] += multiplicity
    return restricted


def _torus_remainder(multiplicities):
    return sum(
        max(mult - multiplicities.get(tuple(-x for x in restricted), 0), 0)
        for restricted, mult in multiplicities.items()
    )


def torus_chiral_dimension(weights, parent_roots):
    """Cancel opposite weights on the torus spanned by supplied E6 coroots.

Accept an iterable of six-integer E6 Dynkin-label tuples (repetition records
multiplicity), or a mapping from such tuples to nonnegative integer counts.
Zero counts are ignored.  Roots use E6 simple-root coordinates and need not
form a closed subsystem.  Using all supplied roots gives the same restriction
as any basis of their span.  This does NOT in general compute group d_chi.
"""
    character = _weight_multiplicities(weights)
    roots = _root_set(parent_roots)
    return _torus_remainder(_restrict(character, sorted(roots)))


@lru_cache(maxsize=4096)
def _parent_data(roots):
    """Derive and reconstruct the subsystem; no parent-type or d_chi lookup."""
    require(e6.closed(roots, _ambient_roots()), "parent is not a closed root subsystem")
    positive = {root for root in roots if min(root) >= 0}
    sums = {e6.add(a, b) for a, b in product(positive, repeat=2)}
    simple = tuple(sorted(positive - sums))
    # Ambient Dynkin labels of the new simple roots, computed from the metric.
    simple_labels = tuple(
        tuple(sum(e6.C[i][j] * root[j] for j in range(e6.N))
              for i in range(e6.N))
        for root in simple
    )
    cartan = tuple(tuple(e6.pairing(a, b) for b in simple_labels) for a in simple)
    require(all(cartan[i][i] == 2 for i in range(len(simple)))
            and all(cartan[i][j] in (-1, 0)
                    for i in range(len(simple)) for j in range(len(simple)) if i != j),
            "invalid parent simple roots")
    generated, pending = set(simple), list(simple)
    while pending:
        root = pending.pop()
        for alpha, labels in zip(simple, simple_labels):
            pairing = e6.pairing(root, labels)
            image = tuple(x - pairing * a for x, a in zip(root, alpha))
            require(image in roots, "parent reflection leaves the subsystem")
            if image not in generated:
                generated.add(image)
                pending.append(image)
    require(generated == roots, "simple roots do not reconstruct the parent")
    return simple, cartan


def minuscule_restricted_d_chi(weights, parent_roots):
    """Group d_chi for verified sums of minuscule restricted characters only.

Inputs have the same format as torus_chiral_dimension, but parent_roots must
be a closed E6 root subsystem.  Every supported weight must pair in {-1,0,1}
with EVERY parent coroot, and restricted multiplicities must be Weyl invariant.
Invalid or unsupported inputs raise VerificationFailure, even under python -O.

These conditions make each dominant orbit representative minuscule or zero.
Its irreducible character is exactly its Weyl orbit, with weight multiplicity
one.  Weyl invariance therefore gives a nonnegative integral sum of these
irreducibles.  Distinct orbits are disjoint, and duality negates an orbit, so
opposite-weight cancellation equals sum |m_U-m_U*| dim(U) over unordered
non-self-dual pairs.  Self-dual orbits contribute zero.  No claim is made for
non-minuscule characters or for additional central torus factors.
"""
    character = _weight_multiplicities(weights)
    roots = _root_set(parent_roots)
    simple, cartan = _parent_data(roots)
    require(all(e6.pairing(weight, root) in (-1, 0, 1)
                for weight in character for root in roots),
            "restricted character is not minuscule: unsupported group d_chi input")
    restricted = _restrict(character, simple)
    for weight, multiplicity in restricted.items():
        for i, row in enumerate(cartan):
            reflected = tuple(x - weight[i] * a for x, a in zip(weight, row))
            require(restricted.get(reflected, 0) == multiplicity,
                    "restricted weight multiplicities are not Weyl invariant")
    return _torus_remainder(restricted)


def self_test():
    """Silent adversarial checks, also run by the certificate's census call."""
    def rejects(function, weights, roots, reason):
        try:
            function(weights, roots)
        except VerificationFailure as error:
            require(reason in str(error), ("unexpected rejection", str(error)))
        else:
            require(False, ("accepted invalid input", function.__name__, reason))

    def symmetric_cube(weights):
        return Counter(
            tuple(sum(weight[i] for weight in triple) for i in range(e6.N))
            for triple in combinations_with_replacement(sorted(weights), 3)
        )

    alpha, beta = e6.E[0], e6.E[2]
    a2 = frozenset((alpha, beta, e6.add(alpha, beta),
                    e6.neg(alpha), e6.neg(beta), e6.neg(e6.add(alpha, beta))))
    defining3 = (alpha, (-1, 0, 1, 0, 0, 0), e6.neg(beta))
    sym3 = symmetric_cube(defining3)
    require(sum(sym3.values()) == 10 and torus_chiral_dimension(sym3, a2) == 3,
            "SU3 Sym^3(3) torus counterexample")
    rejects(minuscule_restricted_d_chi, sym3, a2, "not minuscule")
    # Its simple-root labels are only 0 or 1, but the alpha+beta pairing is 2.
    rejects(minuscule_restricted_d_chi, [e6.add(alpha, beta)], a2, "not minuscule")

    roots = _ambient_roots()
    weights27 = e6.orbit(e6.E[0], e6.reflect_weight)
    sym27 = symmetric_cube(weights27)
    require(sum(sym27.values()) == 3654 and len(sym27) == 1522
            and torus_chiral_dimension(sym27, roots) == 459,
            "E6 Sym^3(27) torus counterexample")
    rejects(minuscule_restricted_d_chi, sym27, roots, "not minuscule")
    require(minuscule_restricted_d_chi(weights27, roots) == 27,
            "E6 defining minuscule character")

    zero = (0,) * e6.N
    a1 = frozenset((alpha, e6.neg(alpha)))
    for function in (torus_chiral_dimension, minuscule_restricted_d_chi):
        require(function([alpha, e6.neg(alpha)], a1) == 0, "self-dual minuscule A1")
        require(function({zero: 4}, a2) == function({}, a2) == 0, "trivial characters")
        require(function(defining3, ()) == 0, "empty parent")
        require(function(defining3, a2) == 3, "A2 defining minuscule character")
        mixed = Counter({weight: 3 for weight in defining3})
        mixed.update({e6.neg(weight): 1 for weight in defining3})
        mixed[zero] = 4
        require(function(mixed, a2) == 6, "unequal irreducible multiplicities")
        require(function(list(mixed.elements()), a2) == 6, "repeated input weights")
        dual = {e6.neg(weight): mult for weight, mult in mixed.items()}
        require(function(dual, a2) == 6, "dual invariance")
        balanced = Counter(defining3) + Counter(e6.neg(w) for w in defining3)
        require(function(balanced, a2) == 0, "balanced dual pair")
        mixed[e6.add(alpha, beta)] = 0
        require(function(mixed, a2) == 6, "zero multiplicity is absent support")
        for bad in (-1, 0.5, 1.0, True):
            rejects(function, {alpha: bad}, a1, "nonnegative integers")
        # Opposite signs must not disappear by coalescing equal restrictions.
        rejects(function, {alpha: 2, e6.add(alpha, e6.E[1]): -1}, a1,
                "nonnegative integers")
        for bad in ((1, 0), (1.0, 0, 0, 0, 0, 0), (True, 0, 0, 0, 0, 0)):
            rejects(function, [bad], a1, "six integers")
            rejects(function, [], [bad], "six integers")
        rejects(function, [], [zero], "non-E6 root")
        rejects(function, [], [e6.add(alpha, alpha)], "non-E6 root")

    rejects(minuscule_restricted_d_chi, defining3[:-1], a2, "Weyl invariant")
    uneven = Counter(defining3)
    uneven[alpha] += 1
    rejects(minuscule_restricted_d_chi, uneven, a2, "Weyl invariant")
    for incomplete, expected in (
        ((alpha,), 0), ((alpha, e6.neg(alpha), beta, e6.neg(beta)), 3),
    ):
        require(torus_chiral_dimension(defining3, incomplete) == expected,
                "torus restriction needs no root closure")
        rejects(minuscule_restricted_d_chi, defining3, incomplete, "closed root subsystem")


def census():
    self_test()
    roots = e6.orbit(e6.E[0], e6.reflect_root)
    weights = e6.orbit(e6.E[0], e6.reflect_weight)
    D = {
        weight: frozenset(root for root in roots if e6.pairing(weight, root) == 0)
        for weight in weights
    }
    root_pairs = {min(root, e6.neg(root)) for root in roots}
    A = {
        alpha: frozenset(
            root for root in roots
            if root in (alpha, e6.neg(alpha)) or e6.root_inner(alpha, root) == 0
        )
        for alpha in root_pairs
    }
    highest = max((root for root in roots if min(root) >= 0), key=sum)
    theta0 = frozenset(root for root in roots if root[highest.index(3)] % 3 == 0)
    thetas = e6.orbit(theta0, e6.reflect_set)

    # Cache each distinct parent root system once.
    parent_sets = set()
    for d_set, a_set in product(D.values(), A.values()):
        parent_sets.add(d_set & a_set)
    for d_set, theta in product(D.values(), thetas):
        parent_sets.add(d_set & theta)
    for a_set, theta in product(A.values(), thetas):
        parent_sets.add(a_set & theta)
    require(len(parent_sets) == 2466, "complete pair-parent universe")
    d_chi_by_parent = {
        parent: minuscule_restricted_d_chi(weights, parent) for parent in parent_sets
    }
    require(Counter(d_chi_by_parent.values()) == Counter({
        0: 540, 12: 1080, 15: 216, 16: 270, 27: 360,
    }), "all 2466 restricted-27 parent values")

    cells = {}
    for (weight, d_set), (alpha, a_set), theta in product(D.items(), A.items(), thetas):
        profile = (len(d_set & a_set), len(d_set & theta), len(a_set & theta))
        common = len(d_set & a_set & theta)
        key = (profile, common)
        values = (
            d_chi_by_parent[d_set & a_set],
            d_chi_by_parent[d_set & theta],
            d_chi_by_parent[a_set & theta],
        )
        cells.setdefault(key, values)
        require(cells[key] == values)

    expected = {
        ((20, 10, 14), 8): (15, 12, 27),
        ((20, 10, 6), 4): (15, 12, 0),
        ((16, 10, 14), 10): (16, 12, 27),
        ((16, 10, 14), 6): (16, 12, 27),
        ((16, 10, 6), 6): (16, 12, 0),
        ((16, 10, 6), 2): (16, 12, 0),
    }
    require(cells == expected)
    return cells


def main():
    cells = census()
    print("Pair-first d_chi check passed")
    print("columns: d_chi(H_DA), d_chi(H_DTheta), d_chi(H_ATheta)")
    for key in sorted(cells):
        print(f"profile={key[0]}, common roots={key[1]}: {cells[key]}")


if __name__ == "__main__":
    main()
