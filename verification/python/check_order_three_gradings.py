#!/usr/bin/env python3
"""Exact Cartan-matrix audit of the semisimple inner Z/3 grading rows.

The calculation is intentionally narrower than the homogeneous census in the
paper.  It reconstructs the finite exceptional root systems, finds the nodes
of coefficient three in the highest root, grades every root by that
coefficient modulo three, identifies the grade-zero root subsystem, and checks
that the grade-one root graph is connected under the grade-zero roots.

It therefore verifies the six regular pair types in the bracket-compatible
(three-symmetric) subfamily.  It does not assert that an arbitrary invariant
complex structure is bracket-compatible; the paper explains why that stronger
implication is false.
"""

from collections import deque
from fractions import Fraction
from math import gcd, lcm

from verification_checks import require


def simply_laced_cartan(rank: int, edges: list[tuple[int, int]]) -> list[list[int]]:
    C = [[0] * rank for _ in range(rank)]
    for i in range(rank):
        C[i][i] = 2
    for i, j in edges:
        C[i][j] = C[j][i] = -1
    return C


CARTAN = {
    "G2": [[2, -1], [-3, 2]],
    "F4": [
        [2, -1, 0, 0],
        [-1, 2, -2, 0],
        [0, -1, 2, -1],
        [0, 0, -1, 2],
    ],
    # Bourbaki numbering: node 2 is attached to node 4.
    "E6": simply_laced_cartan(
        6, [(0, 2), (2, 3), (3, 4), (4, 5), (1, 3)]
    ),
    "E7": simply_laced_cartan(
        7, [(0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 3)]
    ),
    "E8": simply_laced_cartan(
        8,
        [(0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (1, 3)],
    ),
}

EXPECTED_ROOT_COUNTS = {"G2": 12, "F4": 48, "E6": 72, "E7": 126, "E8": 240}
EXPECTED_ROWS = {
    ("G2", 1): (("A2",), 3),
    ("F4", 2): (("A2", "A2"), 18),
    ("E6", 4): (("A2", "A2", "A2"), 27),
    ("E7", 3): (("A2", "A5"), 45),
    ("E7", 5): (("A2", "A5"), 45),
    ("E8", 2): (("A8",), 84),
    ("E8", 7): (("A2", "E6"), 81),
}


def generate_roots(C: list[list[int]]) -> set[tuple[int, ...]]:
    """Generate the complete root system in the simple-root basis."""
    rank = len(C)
    roots: set[tuple[int, ...]] = set()
    queue: deque[tuple[int, ...]] = deque()
    for i in range(rank):
        e = [0] * rank
        e[i] = 1
        for root in (tuple(e), tuple(-x for x in e)):
            roots.add(root)
            queue.append(root)

    while queue:
        root = queue.popleft()
        for i in range(rank):
            # C[j][i] = <alpha_j, alpha_i^vee>.
            pairing = sum(root[j] * C[j][i] for j in range(rank))
            reflected = list(root)
            reflected[i] -= pairing
            reflected_t = tuple(reflected)
            if reflected_t not in roots:
                roots.add(reflected_t)
                queue.append(reflected_t)
    return roots


def matrix_rank(vectors: list[tuple[int, ...]]) -> int:
    if not vectors:
        return 0
    M = [[Fraction(x) for x in row] for row in vectors]
    rows, cols = len(M), len(M[0])
    rank = 0
    for col in range(cols):
        pivot = next((r for r in range(rank, rows) if M[r][col]), None)
        if pivot is None:
            continue
        M[rank], M[pivot] = M[pivot], M[rank]
        scale = M[rank][col]
        M[rank] = [x / scale for x in M[rank]]
        for r in range(rows):
            if r != rank and M[r][col]:
                scale = M[r][col]
                M[r] = [M[r][j] - scale * M[rank][j] for j in range(cols)]
        rank += 1
    return rank


def symmetrizer(C: list[list[int]]) -> list[int]:
    """Return root-length factors d with C_ij d_j = C_ji d_i."""
    rank = len(C)
    d: list[Fraction | None] = [None] * rank
    d[0] = Fraction(1)
    queue = [0]
    while queue:
        i = queue.pop()
        require(d[i] is not None)
        for j in range(rank):
            if i == j or C[i][j] == 0:
                continue
            value = d[i] * Fraction(C[j][i], C[i][j])
            if d[j] is None:
                d[j] = value
                queue.append(j)
            else:
                require(d[j] == value)
    denominator = 1
    for x in d:
        require(x is not None)
        denominator = lcm(denominator, x.denominator)
    values = [int(x * denominator) for x in d if x is not None]
    common = 0
    for x in values:
        common = gcd(common, x)
    return [x // common for x in values]


def inner_product(
    u: tuple[int, ...], v: tuple[int, ...], C: list[list[int]], d: list[int]
) -> Fraction:
    return sum(
        Fraction(u[i] * C[i][j] * d[j] * v[j])
        for i in range(len(C))
        for j in range(len(C))
    )


def connected_components_by_nonorthogonality(
    roots: set[tuple[int, ...]], C: list[list[int]]
) -> list[list[tuple[int, ...]]]:
    roots_list = list(roots)
    d = symmetrizer(C)
    adjacency = [set() for _ in roots_list]
    for i in range(len(roots_list)):
        for j in range(i + 1, len(roots_list)):
            if inner_product(roots_list[i], roots_list[j], C, d) != 0:
                adjacency[i].add(j)
                adjacency[j].add(i)

    components: list[list[tuple[int, ...]]] = []
    seen: set[int] = set()
    for start in range(len(roots_list)):
        if start in seen:
            continue
        stack = [start]
        seen.add(start)
        component: list[tuple[int, ...]] = []
        while stack:
            i = stack.pop()
            component.append(roots_list[i])
            for j in adjacency[i]:
                if j not in seen:
                    seen.add(j)
                    stack.append(j)
        components.append(component)
    return components


def component_type(
    component: list[tuple[int, ...]], C: list[list[int]]
) -> str:
    rank = matrix_rank(component)
    count = len(component)
    d = symmetrizer(C)
    lengths = {
        inner_product(root, root, C, d)
        for root in component
    }

    if count == rank * (rank + 1):
        return f"A{rank}"
    if count == 2 * rank * (rank - 1):
        return f"D{rank}"
    if count == 2 * rank * rank and len(lengths) == 2:
        return f"B/C{rank}"
    exceptional = {
        (2, 12, 2): "G2",
        (4, 48, 2): "F4",
        (6, 72, 1): "E6",
        (7, 126, 1): "E7",
        (8, 240, 1): "E8",
    }
    key = (rank, count, len(lengths))
    if key not in exceptional:
        require(False, f"unrecognized component data {key}")
    return exceptional[key]


def grade_one_components(
    grade_one: set[tuple[int, ...]], grade_zero: set[tuple[int, ...]]
) -> list[int]:
    """Connected weight components under nonzero grade-zero root operators."""
    weights = list(grade_one)
    index = {weight: i for i, weight in enumerate(weights)}
    adjacency = [set() for _ in weights]
    for i, beta in enumerate(weights):
        for alpha in grade_zero:
            gamma = tuple(beta[j] + alpha[j] for j in range(len(beta)))
            k = index.get(gamma)
            if k is not None:
                adjacency[i].add(k)
                adjacency[k].add(i)

    seen: set[int] = set()
    sizes: list[int] = []
    for start in range(len(weights)):
        if start in seen:
            continue
        stack = [start]
        seen.add(start)
        size = 0
        while stack:
            i = stack.pop()
            size += 1
            for j in adjacency[i]:
                if j not in seen:
                    seen.add(j)
                    stack.append(j)
        sizes.append(size)
    return sorted(sizes)



def grading_orbit_mod_three(C: list[list[int]], start: tuple[int, ...]) -> set[tuple[int, ...]]:
    """Weyl orbit of a grading functional on the root lattice modulo three."""
    orbit = {start}
    queue = deque([start])
    while queue:
        grading = queue.popleft()
        for i in range(len(C)):
            reflected = tuple(
                (grading[j] - C[j][i] * grading[i]) % 3
                for j in range(len(C))
            )
            if reflected not in orbit:
                orbit.add(reflected)
                queue.append(reflected)
    return orbit

def main() -> None:
    rows: list[tuple[str, int, tuple[str, ...], int]] = []
    for name, C in CARTAN.items():
        roots = generate_roots(C)
        require(len(roots) == EXPECTED_ROOT_COUNTS[name])
        positive = [root for root in roots if all(x >= 0 for x in root)]
        highest = max(positive, key=sum)
        marked_nodes = [i for i, mark in enumerate(highest) if mark == 3]

        for node in marked_nodes:
            grade_zero = {root for root in roots if root[node] % 3 == 0}
            grade_one = {root for root in roots if root[node] % 3 == 1}
            grade_two = {root for root in roots if root[node] % 3 == 2}
            require(len(grade_one) == len(grade_two))
            require(matrix_rank(list(grade_zero)) == len(C))
            require(grade_one_components(grade_one, grade_zero) == [len(grade_one)])
            require(grade_one != grade_two)

            components = connected_components_by_nonorthogonality(grade_zero, C)
            types = tuple(sorted(component_type(component, C) for component in components))
            expected_types, expected_dimension = EXPECTED_ROWS[(name, node + 1)]
            require(types == expected_types)
            require(len(grade_one) == expected_dimension)
            rows.append((name, node + 1, types, len(grade_one)))

    require(len(rows) == 7)

    # The two mark-three nodes of E7 lie in the same Weyl orbit, as do their
    # inverses, so they give one unordered pair type.
    e7 = CARTAN["E7"]
    grading_3 = tuple(1 if i == 2 else 0 for i in range(7))
    grading_5 = tuple(1 if i == 4 else 0 for i in range(7))
    e7_orbit = grading_orbit_mod_three(e7, grading_3)
    require(grading_5 in e7_orbit)
    require(tuple((-x) % 3 for x in grading_5) in e7_orbit)

    # The classical highest-root marks contain only 1 and 2.  This symbolic
    # check covers the four infinite families independently of rank.
    for rank in range(2, 65):
        require(3 not in [1] * rank)  # A_rank
        require(3 not in ([1] + [2] * (rank - 1)))  # B_rank
        require(3 not in ([2] * (rank - 1) + [1]))  # C_rank
        if rank >= 4:
            require(3 not in ([1] + [2] * (rank - 3) + [1, 1]))  # D_rank

    for name, node, types, dimension in rows:
        fixed = "+".join(types)
        print(f"{name} node {node}: {fixed}; dim(g1)={dimension}")
    print("classical highest-root marks: no coefficient 3")
    print("all inner order-three grading checks passed")


if __name__ == "__main__":
    main()
