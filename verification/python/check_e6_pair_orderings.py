#!/usr/bin/env python3
"""Check group d_chi for the restricted 27 in the pair-first E6 census.

Weight cancellation alone computes a torus invariant.  It computes group
d_chi here only after verifying that the restricted character is a sum of
minuscule characters (including trivial characters).  This is not a general
irreducible-character decomposition routine.
"""

from collections import Counter, namedtuple
from collections.abc import Mapping
from functools import lru_cache
from itertools import combinations_with_replacement, permutations, product

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


ParentStructure = namedtuple(
    "ParentStructure", "type root_count rank semisimple_dimension"
)


@lru_cache(maxsize=4096)
def _pair_structure(roots):
    roots = _root_set(roots)
    simple, _ = _parent_data(roots)
    rank = e6.rank(roots)  # Exact row reduction, not a type-to-rank lookup.
    require(rank == len(simple), "parent rank disagrees with its simple roots")
    sizes = sorted((len(c) for c in e6.components(roots)), reverse=True)
    names = {2: "A1", 6: "A2", 12: "A3", 20: "A4"}
    require(all(n in names for n in sizes), "unsupported pair parent")
    kind = "+".join(names[n] for n in sizes)
    require((kind, rank) in {
        ("A4", 4), ("A3+A1+A1", 5), ("A2+A1+A1", 4),
        ("A2+A2+A1", 5), ("A1+A1+A1", 3),
    }, "unsupported pair parent")
    return ParentStructure(kind, len(roots), rank, rank + len(roots))


def unique_greatest(scores):
    """Return the position of a strict maximum of three exact integer scores."""
    require(isinstance(scores, (tuple, list)) and len(scores) == 3
            and all(type(n) is int and n >= 0 for n in scores),
            "expected three nonnegative integer scores")
    require(scores.count(max(scores)) == 1, "greatest score is tied")
    return scores.index(max(scores))


def select_intrinsic_pair(parents):
    """Select by both roots and rank+roots, without pair labels or d_chi.

    Supply three frozensets of E6 roots, of the supported pair-parent types.
    This checks closure and type, but does not certify a common source triple;
    census() checks every actual triple. Ties or disagreement fail closed.
    Dimensions are semisimple: no central torus dimension is included.
    """
    require(isinstance(parents, (tuple, list)) and len(parents) == 3
            and all(isinstance(parent, frozenset) for parent in parents),
            "expected three parent root frozensets")
    # Validate before the cache: float/bool coordinates can hash like integers.
    data = tuple(_pair_structure(_root_set(parent)) for parent in parents)
    winner = unique_greatest(tuple(row.root_count for row in data))
    require(winner == unique_greatest(tuple(row.semisimple_dimension for row in data)),
            "root-count and semisimple-dimension selectors disagree")
    return winner


def _rejects(function, *args):
    *inputs, reason = args
    try:
        function(*inputs)
    except VerificationFailure as error:
        require(reason in str(error), ("unexpected rejection", str(error)))
    else:
        require(False, ("accepted invalid input", function.__name__, reason))


def self_test():
    """Silent adversarial checks, also run by the certificate's census call."""
    rejects = _rejects
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
    require(unique_greatest((16, 10, 14)) == 0
            and unique_greatest((14, 21, 19)) == 1, "strict structural maxima")
    for bad in ((), (1, 2), (1, 2, 3, 4), "123", {0: 1, 1: 2, 2: 3},
                (True, 2, 3), (1.0, 2, 3), (-1, 2, 3)):
        rejects(unique_greatest, bad, "three nonnegative integer scores")
    for tied in ((20, 20, 10), (24, 14, 24), (0, 0, 0)):
        rejects(unique_greatest, tied, "tied")
    for bad in (None, (), (roots, roots), (roots, roots, set(roots))):
        rejects(select_intrinsic_pair, bad, "three parent root frozensets")
    for unsupported in (a2, roots, frozenset()):
        rejects(select_intrinsic_pair, (unsupported,) * 3, "unsupported pair parent")
    rejects(select_intrinsic_pair, (frozenset((alpha,)),) * 3,
            "closed root subsystem")
    rejects(select_intrinsic_pair, (frozenset(((0,) * e6.N,)),) * 3, "non-E6 root")
    rejects(select_intrinsic_pair, (frozenset(((1, 0),)),) * 3, "six integers")
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


def census(*, include_structure=False):
    """Return the existing d_chi cells; optionally also return selector evidence."""
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
    require((len(set(D.values())), len(set(A.values())), len(thetas)) == (27, 36, 40),
            "complete triple universe")

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
    structure = {parent: _pair_structure(parent) for parent in parent_sets}
    parent_counts = Counter(
        (*structure[parent], d_chi_by_parent[parent]) for parent in parent_sets
    )
    require(parent_counts == Counter({
        ("A4", 20, 4, 24, 15): 216,
        ("A3+A1+A1", 16, 5, 21, 16): 270,
        ("A2+A1+A1", 10, 4, 14, 12): 1080,
        ("A2+A2+A1", 14, 5, 19, 27): 360,
        ("A1+A1+A1", 6, 3, 9, 0): 540,
    }), "calculated pair-parent types, ranks, dimensions and d_chi")
    for parent in parent_sets:
        for i in range(e6.N):
            image = e6.reflect_set(parent, i)
            require(image in structure and structure[image] == structure[parent]
                    and d_chi_by_parent[image] == d_chi_by_parent[parent],
                    "pair-parent invariance under every simple reflection")

    cells = {}
    structural_cells, representatives = {}, {}
    cell_counts, rank_winners, chiral_winners = Counter(), Counter(), Counter()
    for (weight, d_set), (alpha, a_set), theta in product(D.items(), A.items(), thetas):
        parents = (d_set & a_set, d_set & theta, a_set & theta)
        data = tuple(structure[parent] for parent in parents)
        profile = tuple(row.root_count for row in data)
        common = len(d_set & a_set & theta)
        key = (profile, common)
        values = (
            d_chi_by_parent[d_set & a_set],
            d_chi_by_parent[d_set & theta],
            d_chi_by_parent[a_set & theta],
        )
        selected = select_intrinsic_pair(parents)
        require(selected == 0, "DA must be the unique structural greatest pair")
        require(tuple(i for i, value in enumerate(values) if value in (15, 16))
                == (selected,), "structural selector iff d_chi is 15 or 16")
        ranks = tuple(row.rank for row in data)
        dimensions = tuple(row.semisimple_dimension for row in data)
        rank_best = tuple(i for i, rank in enumerate(ranks) if rank == max(ranks))
        rank_winners[rank_best] += 1
        chiral_winners[unique_greatest(values)] += 1
        cell_counts[key] += 1
        structural_cells.setdefault(key, (ranks, dimensions))
        require(structural_cells[key] == (ranks, dimensions), "structural cell uniformity")
        representatives.setdefault(key, parents)
        cells.setdefault(key, values)
        require(cells[key] == values)

    require(sum(cell_counts.values()) == 38_880, "all triples checked")
    require(rank_winners == Counter({(0,): 16200, (2,): 4320,
                                     (0, 1): 12960, (0, 2): 5400}),
            "rank alone must exhibit ties and wrong selections")
    require(chiral_winners == Counter({0: 29160, 2: 9720}),
            "maximizing d_chi must disagree on 9720 triples")
    for parents in representatives.values():
        for order in permutations(range(3)):
            require(select_intrinsic_pair(tuple(parents[i] for i in order))
                    == order.index(0), "selector depends on pair labelling")
        _rejects(select_intrinsic_pair, (parents[0], parents[0], parents[1]), "tied")
        for zero in (0.0, False):
            malformed = frozenset(tuple(zero if x == 0 else x for x in root)
                                  for root in parents[0])
            require(malformed == parents[0], "exercise equal cache keys")
            _rejects(select_intrinsic_pair, (malformed, *parents[1:]), "six integers")

    expected = {
        ((20, 10, 14), 8): (15, 12, 27),
        ((20, 10, 6), 4): (15, 12, 0),
        ((16, 10, 14), 10): (16, 12, 27),
        ((16, 10, 14), 6): (16, 12, 27),
        ((16, 10, 6), 6): (16, 12, 0),
        ((16, 10, 6), 2): (16, 12, 0),
    }
    require(cells == expected)
    if include_structure:
        columns = ["H_DA", "H_DTheta", "H_ATheta"]
        return cells, {
            "semisimple_dimension_definition": "rank + root_count (no central torus)",
            "columns": columns,
            "triples_checked": sum(cell_counts.values()),
            "distinct_pair_parents": len(parent_sets),
            "unique_greatest_root_count_pair": columns[0],
            "unique_greatest_semisimple_dimension_pair": columns[0],
            "equivalent_to_d_chi_15_or_16": True,
            "pair_parent_types": [
                dict(zip(("type", "root_count", "rank", "semisimple_dimension", "d_chi"), row),
                     distinct_parents=count)
                for row, count in sorted(parent_counts.items())
            ],
            "cells": [
                {"profile": list(profile), "common_root_count": common,
                 "count": cell_counts[profile, common], "ranks": list(ranks),
                 "semisimple_dimensions": list(dimensions)}
                for (profile, common), (ranks, dimensions) in sorted(structural_cells.items())
            ],
            "rank_maximizers": [
                {"pairs": [columns[i] for i in winners], "triples": count}
                for winners, count in sorted(rank_winners.items())
            ],
            "d_chi_maximizers": [
                {"pair": columns[i], "triples": count}
                for i, count in sorted(chiral_winners.items())
            ],
        }
    return cells


def main():
    cells = census()
    print("Pair-first d_chi check passed")
    print("columns: d_chi(H_DA), d_chi(H_DTheta), d_chi(H_ATheta)")
    for key in sorted(cells):
        print(f"profile={key[0]}, common roots={key[1]}: {cells[key]}")
    print("Structural ordering PASS: 38880 triples, 2466 parents; roots and rank+roots "
          "uniquely select H_DA iff d_chi in {15,16}")


if __name__ == "__main__":
    main()
