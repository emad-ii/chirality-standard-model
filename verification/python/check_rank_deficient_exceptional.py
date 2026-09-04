#!/usr/bin/env python3
"""Necessary-condition census for rank-deficient semisimple h in exceptional g.

The checker enumerates every compact semisimple factor multiset of smaller
rank, every nontrivial irreducible factor representation inside the exact
per-ambient dimension bound, and then applies, in order:

  * the quotient-dimension equation;
  * complex type;
  * existence of a nonzero cubic-radical factor;
  * integrality of every Dynkin embedding index.

Quadratic indices are normalized by T(ad_h)=h^vee, equivalently by taking
long roots to have squared length 2.  The output is an emptiness certificate
for a necessary locus; it is not an embedding classification.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from fractions import Fraction
from itertools import combinations_with_replacement
from math import gcd, lcm
from pathlib import Path
from typing import Any

from verification_checks import require


# ---------------------------------------------------------------------------
# Cartan matrices
# ---------------------------------------------------------------------------

def path_cartan(r: int) -> list[list[int]]:
    C = [[0] * r for _ in range(r)]
    for i in range(r):
        C[i][i] = 2
    for i in range(r - 1):
        C[i][i + 1] = C[i + 1][i] = -1
    return C


def A(r: int) -> list[list[int]]:
    return path_cartan(r)


def B(r: int) -> list[list[int]]:
    C = path_cartan(r)
    C[r - 2][r - 1], C[r - 1][r - 2] = -2, -1
    return C


def Ctype(r: int) -> list[list[int]]:
    C = path_cartan(r)
    C[r - 2][r - 1], C[r - 1][r - 2] = -1, -2
    return C


def D(r: int) -> list[list[int]]:
    C = [[0] * r for _ in range(r)]
    for i in range(r):
        C[i][i] = 2
    for i in range(r - 3):
        C[i][i + 1] = C[i + 1][i] = -1
    C[r - 3][r - 2] = C[r - 2][r - 3] = -1
    C[r - 3][r - 1] = C[r - 1][r - 3] = -1
    return C


def simply_laced(r: int, edges: list[tuple[int, int]]) -> list[list[int]]:
    C = [[0] * r for _ in range(r)]
    for i in range(r):
        C[i][i] = 2
    for i, j in edges:
        C[i][j] = C[j][i] = -1
    return C


def E6() -> list[list[int]]:
    return simply_laced(6, [(0, 2), (2, 3), (3, 4), (4, 5), (1, 3)])


def E7() -> list[list[int]]:
    return simply_laced(7, [(0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 3)])


def E8() -> list[list[int]]:
    return simply_laced(8, [(0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (1, 3)])


def F4() -> list[list[int]]:
    return [[2, -1, 0, 0], [-1, 2, -2, 0], [0, -1, 2, -1], [0, 0, -1, 2]]


def G2() -> list[list[int]]:
    return [[2, -1], [-3, 2]]


def algebra_types(max_rank: int = 8) -> list[tuple[str, int, int, int, list[list[int]], str]]:
    out: list[tuple[str, int, int, int, list[list[int]], str]] = []
    for r in range(1, max_rank + 1):
        out.append((f"A{r}", r, r * (r + 2), r + 1, A(r), "A"))
    for r in range(2, max_rank + 1):
        out.append((f"B{r}", r, r * (2 * r + 1), 2 * r - 1, B(r), "B"))
        out.append((f"C{r}", r, r * (2 * r + 1), r + 1, Ctype(r), "C"))
    for r in range(4, max_rank + 1):
        out.append((f"D{r}", r, r * (2 * r - 1), 2 * r - 2, D(r), "D"))
    out += [
        ("G2", 2, 14, 4, G2(), "G2"),
        ("F4", 4, 52, 9, F4(), "F4"),
        ("E6", 6, 78, 12, E6(), "E6"),
        ("E7", 7, 133, 18, E7(), "E7"),
        ("E8", 8, 248, 30, E8(), "E8"),
    ]
    return sorted(out, key=lambda x: (x[1], x[0]))


# ---------------------------------------------------------------------------
# Root and representation arithmetic
# ---------------------------------------------------------------------------

def symmetrizer(C: list[list[int]]) -> list[int]:
    r = len(C)
    d: list[Fraction | None] = [None] * r
    d[0] = Fraction(1)
    queue = [0]
    while queue:
        i = queue.pop()
        for j in range(r):
            if i == j or C[i][j] == 0:
                continue
            value = d[i] * Fraction(C[j][i], C[i][j])
            if d[j] is None:
                d[j] = value
                queue.append(j)
            else:
                require(d[j] == value)
    den = 1
    for x in d:
        require(x is not None)
        den = lcm(den, x.denominator)
    values = [int(x * den) for x in d if x is not None]
    common = 0
    for x in values:
        common = gcd(common, x)
    return [x // common for x in values]


def generate_roots(C: list[list[int]]) -> set[tuple[int, ...]]:
    r = len(C)
    roots: set[tuple[int, ...]] = set()
    queue: deque[tuple[int, ...]] = deque()
    for i in range(r):
        e = [0] * r
        e[i] = 1
        for root in (tuple(e), tuple(-x for x in e)):
            roots.add(root)
            queue.append(root)
    while queue:
        root = queue.popleft()
        for i in range(r):
            pairing = sum(root[j] * C[j][i] for j in range(r))
            reflected = list(root)
            reflected[i] -= pairing
            reflected_t = tuple(reflected)
            if reflected_t not in roots:
                roots.add(reflected_t)
                queue.append(reflected_t)
    return roots


def root_inner(a: tuple[int, ...], b: tuple[int, ...], C: list[list[int]], d: list[int]) -> Fraction:
    return sum(
        Fraction(a[i] * C[i][j] * d[j] * b[j])
        for i in range(len(C))
        for j in range(len(C))
    )


def positive_roots(C: list[list[int]]) -> list[tuple[int, ...]]:
    return [root for root in generate_roots(C) if all(x >= 0 for x in root) and any(root)]


def coroot_coefficients(root: tuple[int, ...], C: list[list[int]], d: list[int]) -> list[Fraction]:
    norm = root_inner(root, root, C, d)
    return [Fraction(2 * root[i] * d[i], norm) for i in range(len(C))]


def inverse_matrix(C: list[list[int]]) -> list[list[Fraction]]:
    n = len(C)
    M = [
        [Fraction(C[i][j]) for j in range(n)]
        + [Fraction(int(i == j)) for j in range(n)]
        for i in range(n)
    ]
    for col in range(n):
        pivot = next(row for row in range(col, n) if M[row][col])
        M[col], M[pivot] = M[pivot], M[col]
        scale = M[col][col]
        M[col] = [x / scale for x in M[col]]
        for row in range(n):
            if row != col and M[row][col]:
                scale = M[row][col]
                M[row] = [M[row][j] - scale * M[col][j] for j in range(2 * n)]
    return [row[n:] for row in M]


def representation_data(
    labels: tuple[int, ...] | list[int],
    C: list[list[int]],
    cache: dict[tuple[int, ...], tuple[int, Fraction]],
) -> tuple[int, Fraction]:
    key = tuple(labels)
    if key in cache:
        return cache[key]

    d = symmetrizer(C)
    dimension = Fraction(1)
    for root in positive_roots(C):
        coeff = coroot_coefficients(root, C, d)
        dimension *= Fraction(
            sum(coeff[i] * (key[i] + 1) for i in range(len(C))),
            sum(coeff),
        )
    require(dimension.denominator == 1)

    # Fundamental-weight Gram matrix.  Dividing by max(d) normalizes long
    # roots to squared length 2; this is the convention T(ad)=h^vee.
    n = len(C)
    C_inv = inverse_matrix(C)
    simple_gram = [[Fraction(C[i][j] * d[j], max(d)) for j in range(n)] for i in range(n)]
    fundamental_gram = [
        [
            sum(
                C_inv[i][a] * simple_gram[a][b] * C_inv[j][b]
                for a in range(n)
                for b in range(n)
            )
            for j in range(n)
        ]
        for i in range(n)
    ]
    c2 = sum(
        Fraction(key[i]) * fundamental_gram[i][j] * (key[j] + 2)
        for i in range(n)
        for j in range(n)
    ) / 2
    cache[key] = (dimension.numerator, c2)
    return cache[key]


def dual_labels(kind: str, labels: tuple[int, ...]) -> tuple[int, ...]:
    labels_l = list(labels)
    r = len(labels_l)
    if kind == "A":
        return tuple(reversed(labels_l))
    if kind == "D" and r % 2 == 1:
        labels_l[-1], labels_l[-2] = labels_l[-2], labels_l[-1]
    if kind == "E6":
        return (labels_l[5], labels_l[1], labels_l[4], labels_l[3], labels_l[2], labels_l[0])
    return tuple(labels_l)


def cubic_eigenvalue_A(labels: tuple[int, ...]) -> Fraction:
    N = len(labels) + 1
    rows = [sum(labels[i:]) for i in range(N - 1)] + [0]
    shifted = [Fraction(rows[i] + N - 1 - i) for i in range(N)]
    mean = sum(shifted) / N
    return sum((x - mean) ** 3 for x in shifted)


def enumerate_representations(
    algebra: tuple[str, int, int, int, list[list[int]], str],
    max_dimension: int,
) -> list[tuple[tuple[int, ...], int, Fraction, bool, bool]]:
    name, rank, dim_h, _hvee, C, kind = algebra
    del name
    cache: dict[tuple[int, ...], tuple[int, Fraction]] = {}
    out: list[tuple[tuple[int, ...], int, Fraction, bool, bool]] = []

    bounds: list[int] = []
    for i in range(rank):
        k = 0
        while True:
            labels = [0] * rank
            labels[i] = k + 1
            dim, _ = representation_data(labels, C, cache)
            if dim > max_dimension:
                break
            k += 1
        bounds.append(k)

    def recurse(i: int, partial: list[int]) -> None:
        if i == rank:
            if not any(partial):
                return
            dim, c2 = representation_data(partial, C, cache)
            if dim > max_dimension:
                return
            T = Fraction(dim) * c2 / dim_h
            labels = tuple(partial)
            complex_type = labels != dual_labels(kind, labels)
            cubic_safe = kind != "A" or cubic_eigenvalue_A(labels) == 0
            out.append((labels, dim, T, complex_type, cubic_safe))
            return

        for k in range(bounds[i] + 1):
            partial.append(k)
            labels = partial + [0] * (rank - i - 1)
            dim, _ = representation_data(labels, C, cache)
            if dim <= max_dimension:
                recurse(i + 1, partial)
            partial.pop()

    recurse(0, [])
    return sorted(out, key=lambda x: (x[1], x[0]))


ALGEBRAS = algebra_types(8)
ALG = {entry[0]: entry for entry in ALGEBRAS}
AMBIENTS = [
    ("G2", 2, 14, 4),
    ("F4", 4, 52, 9),
    ("E6", 6, 78, 12),
    ("E7", 7, 133, 18),
    ("E8", 8, 248, 30),
]
EXPECTED_BOUNDS = {"G2": 0, "F4": 23, "E6": 36, "E7": 65, "E8": 121}
REPRESENTATIONS = {
    algebra[0]: enumerate_representations(algebra, max(EXPECTED_BOUNDS.values()))
    for algebra in ALGEBRAS
}


def factor_multisets(start: int, rank_left: int, dim_left: int, current: list[str]):
    yield tuple(current)
    for index in range(start, len(ALGEBRAS)):
        name, rank, dim_h, _hvee, _C, _kind = ALGEBRAS[index]
        if rank > rank_left or dim_h > dim_left:
            continue
        current.append(name)
        yield from factor_multisets(index, rank_left - rank, dim_left - dim_h, current)
        current.pop()


def per_ambient_dimension_bounds() -> dict[str, int]:
    bounds: dict[str, int] = {}
    for name, rank, dim_g, _hvee in AMBIENTS:
        values: list[int] = []
        for factors in factor_multisets(0, rank - 1, dim_g - 2, []):
            if not factors:
                continue
            dim_h = sum(ALG[factor][2] for factor in factors)
            difference = dim_g - dim_h
            if difference > 0 and difference % 2 == 0:
                values.append(difference // 2)
        bounds[name] = max(values, default=0)
    require(bounds == EXPECTED_BOUNDS)
    return bounds


def adjoint_labels(C: list[list[int]]) -> tuple[int, ...]:
    highest = max(
        (root for root in generate_roots(C) if all(x >= 0 for x in root)),
        key=sum,
    )
    return tuple(sum(highest[k] * C[k][j] for k in range(len(C))) for j in range(len(C)))


def check_index_normalization() -> None:
    # Counts use labelled presentations: B2 and C2 remain separate entries.
    # Their node swap must preserve every enumerated representation and index.
    require(B(2) == [list(reversed(row)) for row in reversed(Ctype(2))],
            "B2/C2 Cartan node-swap convention")
    swapped_B2 = {
        (tuple(reversed(labels)), dim, T, complex_type, cubic_safe)
        for labels, dim, T, complex_type, cubic_safe in REPRESENTATIONS["B2"]
    }
    require(swapped_B2 == set(REPRESENTATIONS["C2"]),
            "B2/C2 representation and index equivalence within the census bound")
    for name, _rank, _dim_h, hvee, C, _kind in ALGEBRAS:
        dim, c2 = representation_data(adjoint_labels(C), C, {})
        T = Fraction(dim) * c2 / ALG[name][2]
        require(T == hvee, (name, T, hvee))

    controls = [
        ("A2", (1, 0), Fraction(1, 2)),
        ("B3", (1, 0, 0), Fraction(1)),
        ("C3", (1, 0, 0), Fraction(1, 2)),
        ("D4", (1, 0, 0, 0), Fraction(1)),
        ("G2", (1, 0), Fraction(1)),
        ("F4", (0, 0, 0, 1), Fraction(3)),
        ("E6", (1, 0, 0, 0, 0, 0), Fraction(3)),
    ]
    for name, labels, expected in controls:
        _alg_name, _rank, dim_h, _hvee, C, _kind = ALG[name]
        dim, c2 = representation_data(labels, C, {})
        T = Fraction(dim) * c2 / dim_h
        require(T == expected, (name, labels, T, expected))


def representation_key(rep: tuple[tuple[int, ...], int, Fraction, bool, bool]):
    labels, dim, T, complex_type, cubic_safe = rep
    return (dim, labels, T, complex_type, cubic_safe)


def fraction_record(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def run_census() -> dict[str, Any]:
    bounds = per_ambient_dimension_bounds()
    result: dict[str, Any] = {
        "normalization": {
            "long_root_squared_length": 2,
            "T_adjoint": "h_dual",
            "positive_controls": {
                "A2_fundamental": "1/2",
                "B3_vector": "1",
                "C3_vector": "1/2",
                "D4_vector": "1",
                "G2_7": "1",
                "F4_26": "3",
                "E6_27": "3",
            },
        },
        "dimension_bounds": bounds,
        "ambients": {},
    }

    final_candidates: list[dict[str, Any]] = []
    for g_name, g_rank, dim_g, hvee_g in AMBIENTS:
        counts = {
            "factor_multisets": 0,
            "dimension_matched_representation_products": 0,
            "complex_type_products": 0,
            "nonzero_radical_products": 0,
            "integral_index_products": 0,
        }
        audit_rows: list[dict[str, Any]] = []

        for factors in factor_multisets(0, g_rank - 1, dim_g - 2, []):
            if not factors:
                continue
            dim_h = sum(ALG[name][2] for name in factors)
            difference = dim_g - dim_h
            if difference <= 0 or difference % 2:
                continue
            dim_V = difference // 2
            require(dim_V <= bounds[g_name])
            counts["factor_multisets"] += 1

            options = [
                [rep for rep in REPRESENTATIONS[name] if rep[1] <= dim_V]
                for name in factors
            ]
            chosen: list[tuple[tuple[int, ...], int, Fraction, bool, bool]] = []

            def choose(i: int, product_dimension: int) -> None:
                if i == len(factors):
                    if product_dimension != dim_V:
                        return
                    counts["dimension_matched_representation_products"] += 1
                    if not any(rep[3] for rep in chosen):
                        return
                    counts["complex_type_products"] += 1
                    if not any(rep[4] for rep in chosen):
                        return
                    counts["nonzero_radical_products"] += 1

                    indices: list[Fraction] = []
                    failed_factors: list[int] = []
                    for j, (_labels, dim, T, _complex, _safe) in enumerate(chosen):
                        multiplicity = dim_V // dim
                        index = (Fraction(ALG[factors[j]][3]) + 2 * T * multiplicity) / hvee_g
                        indices.append(index)
                        if index.denominator != 1:
                            failed_factors.append(j)

                    row = {
                        "ambient": g_name,
                        "factors": list(factors),
                        "dim_h": dim_h,
                        "dim_V": dim_V,
                        "representations": [
                            {
                                "factor": factors[j],
                                "dynkin_labels": list(rep[0]),
                                "dimension": rep[1],
                                "quadratic_index": fraction_record(rep[2]),
                                "complex_type": rep[3],
                                "cubic_coefficient_zero": rep[4],
                                "embedding_index": fraction_record(indices[j]),
                            }
                            for j, rep in enumerate(chosen)
                        ],
                        "failed_index_factors": failed_factors,
                    }
                    audit_rows.append(row)
                    if not failed_factors:
                        counts["integral_index_products"] += 1
                        final_candidates.append(row)
                    return

                for rep in options[i]:
                    if i > 0 and factors[i] == factors[i - 1]:
                        if representation_key(rep) < representation_key(chosen[-1]):
                            continue
                    dim = rep[1]
                    new_product = product_dimension * dim
                    if new_product > dim_V or dim_V % new_product:
                        continue
                    chosen.append(rep)
                    choose(i + 1, new_product)
                    chosen.pop()

            choose(0, 1)

        result["ambients"][g_name] = {
            "rank": g_rank,
            "dimension": dim_g,
            "dual_coxeter_number": hvee_g,
            "max_dim_V": bounds[g_name],
            "counts": counts,
            "pre_index_candidates": audit_rows,
        }

    result["surviving_candidates"] = final_candidates
    require(not final_candidates)
    return result


def print_summary(result: dict[str, Any]) -> None:
    print("quadratic-index normalization.............. passed")
    for name, _rank, _dim, _hvee in AMBIENTS:
        data = result["ambients"][name]
        c = data["counts"]
        print(
            f"{name}: max dim(V)={data['max_dim_V']}; "
            f"factor multisets={c['factor_multisets']}; "
            f"dimension matches={c['dimension_matched_representation_products']}; "
            f"complex={c['complex_type_products']}; "
            f"safe={c['nonzero_radical_products']}; "
            f"integral indices={c['integral_index_products']}"
        )
    print("rank-deficient exceptional safe candidates=0")
    print("all exceptional rank-deficient sieve checks passed")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-audit", type=Path)
    args = parser.parse_args()

    check_index_normalization()
    result = run_census()
    if args.write_audit is not None:
        args.write_audit.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print_summary(result)


if __name__ == "__main__":
    main()
