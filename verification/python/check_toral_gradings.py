#!/usr/bin/env python3
"""Direct finite census of semisimple inner 2- and 3-gradings.

The script works from Cartan matrices only.  It generates the exceptional
root systems, enumerates every nonzero root-lattice functional modulo 2 and
3 up to the Weyl action, and retains those whose grade-zero root system has
full rank.  For order three it further requires a connected grade-one weight
graph, the irreducibility condition used in the paper.
"""

from collections import deque
from itertools import product

from check_order_three_gradings import (
    CARTAN,
    EXPECTED_ROOT_COUNTS,
    component_type,
    connected_components_by_nonorthogonality,
    generate_roots,
    grade_one_components,
    matrix_rank,
)

from verification_checks import require

EXPECTED_THREE = {
    "G2": (("A2",), 3),
    "F4": (("A2", "A2"), 18),
    "E6": (("A2", "A2", "A2"), 27),
    "E7": (("A2", "A5"), 45),
    "E8": (("A2", "E6"), 81, ("A8",), 84),
}
EXPECTED_TWO = {
    "G2": 1,
    "F4": 2,
    "E6": 1,
    "E7": 2,
    "E8": 2,
}


def grading_orbit(C: list[list[int]], start: tuple[int, ...], modulus: int) -> set[tuple[int, ...]]:
    orbit = {start}
    queue = deque([start])
    while queue:
        grading = queue.popleft()
        for i in range(len(C)):
            reflected = tuple(
                (grading[j] - C[j][i] * grading[i]) % modulus
                for j in range(len(C))
            )
            if reflected not in orbit:
                orbit.add(reflected)
                queue.append(reflected)
    return orbit


def subsystem_type(roots: set[tuple[int, ...]], C: list[list[int]]) -> tuple[str, ...]:
    components = connected_components_by_nonorthogonality(roots, C)
    return tuple(sorted(component_type(component, C) for component in components))


def enumerate_gradings(name: str, C: list[list[int]], modulus: int):
    roots = generate_roots(C)
    require(len(roots) == EXPECTED_ROOT_COUNTS[name])
    rank = len(C)
    seen: set[tuple[int, ...]] = set()
    rows = []
    for grading in product(range(modulus), repeat=rank):
        if not any(grading) or grading in seen:
            continue
        orbit = grading_orbit(C, grading, modulus)
        seen.update(orbit)
        rep = min(orbit)
        grades = {
            k: {
                root
                for root in roots
                if sum(root[i] * rep[i] for i in range(rank)) % modulus == k
            }
            for k in range(modulus)
        }
        if matrix_rank(list(grades[0])) != rank:
            continue
        rows.append(
            (
                rep,
                subsystem_type(grades[0], C),
                tuple(len(grades[k]) for k in range(modulus)),
                grade_one_components(grades[1], grades[0]),
            )
        )
    return rows


def main() -> None:
    three_rows = []
    for name, C in CARTAN.items():
        rows2 = enumerate_gradings(name, C, 2)
        require(len(rows2) == EXPECTED_TWO[name])
        # In every semisimple involutive row the odd root graph is connected.
        # Compact conjugation preserves that graph because -1 = 1 mod 2, so
        # the quotient is self-conjugate rather than of complex type.
        require(all(row[3] == [row[2][1]] for row in rows2))

        rows3 = enumerate_gradings(name, C, 3)
        good3 = [
            row
            for row in rows3
            if row[2][1] == row[2][2] and row[3] == [row[2][1]]
        ]
        if name != "E8":
            expected_type, expected_dim = EXPECTED_THREE[name]
            require(len(good3) == 1)
            require(good3[0][1] == expected_type)
            require(good3[0][2][1] == expected_dim)
        else:
            require(len(good3) == 2)
            got = {(row[1], row[2][1]) for row in good3}
            expected = {
                (EXPECTED_THREE[name][0], EXPECTED_THREE[name][1]),
                (EXPECTED_THREE[name][2], EXPECTED_THREE[name][3]),
            }
            require(got == expected)
        three_rows.extend((name, row[1], row[2][1]) for row in good3)

    expected_rows = {
        ("G2", ("A2",), 3),
        ("F4", ("A2", "A2"), 18),
        ("E6", ("A2", "A2", "A2"), 27),
        ("E7", ("A2", "A5"), 45),
        ("E8", ("A2", "E6"), 81),
        ("E8", ("A8",), 84),
    }
    require(set(three_rows) == expected_rows)

    for name, types, dimension in sorted(three_rows):
        print(f"{name}: {'+'.join(types)}; dim(g1)={dimension}")
    print("all semisimple involutive quotients are self-conjugate")
    print("all direct toral grading checks passed")


if __name__ == "__main__":
    main()
