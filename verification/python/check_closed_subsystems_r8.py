#!/usr/bin/env python3
"""Independent closed-subsystem census in the standard R^8 E6 model."""

from collections import Counter, deque
from fractions import Fraction

from verification_checks import require


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
                a[i][j] = (a[i][j] * pivot - a[i][k] * a[k][j]) // previous
        previous = pivot
    return sign * a[-1][-1]


def inverse(matrix):
    n = len(matrix)
    a = [[Fraction(value) for value in row] +
         [Fraction(int(i == j)) for j in range(n)]
         for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if a[i][col])
        a[col], a[pivot] = a[pivot], a[col]
        scale = a[col][col]
        a[col] = [value / scale for value in a[col]]
        for i in range(n):
            if i == col:
                continue
            scale = a[i][col]
            if scale:
                a[i] = [x - scale * y for x, y in zip(a[i], a[col])]
    return [row[n:] for row in a]


def census():
    roots = orbit(SIMPLE[0])
    require(len(roots) == 72 and all(dot(root, root) == 8 for root in roots))

    cartan = [[dot(a, b) // 4 for b in SIMPLE] for a in SIMPLE]
    cartan_inverse = inverse(cartan)

    def simple_coordinates(root):
        pairings = [Fraction(dot(root, simple), 4) for simple in SIMPLE]
        return tuple(sum(cartan_inverse[i][j] * pairings[j]
                         for j in range(RANK)) for i in range(RANK))

    positive = tuple(sorted(
        root for root in roots if all(value >= 0 for value in simple_coordinates(root))
    ))
    require(len(positive) == 36)

    def inner(root, old):
        value = dot(root, old)
        require(value % 4 == 0)
        return value // 4

    def reflect_in(root, mirror):
        coefficient = inner(root, mirror)
        return subtract(root, tuple(coefficient * x for x in mirror))

    def generated_subsystem(simple_roots):
        seen = set(simple_roots) | {negate(root) for root in simple_roots}
        queue = list(seen)
        for root in queue:
            for mirror in simple_roots:
                image = reflect_in(root, mirror)
                require(image in roots)
                if image not in seen:
                    seen.add(image)
                    queue.append(image)
        return frozenset(seen)

    subsystems = {frozenset()}

    def extend(chosen, start, gram):
        for j in range(start, len(positive)):
            root = positive[j]
            products = [inner(root, old) for old in chosen]
            if any(value > 0 for value in products):
                continue
            enlarged_gram = [row + [products[i]] for i, row in enumerate(gram)]
            enlarged_gram.append(products + [2])
            if determinant(enlarged_gram) <= 0:
                continue
            enlarged = chosen + [root]
            subsystems.add(generated_subsystem(enlarged))
            if len(enlarged) < RANK:
                extend(enlarged, j + 1, enlarged_gram)

    extend([], 0, [])

    full = roots
    proper = sorted((system for system in subsystems if system != full),
                    key=len, reverse=True)
    maximal = [
        system for i, system in enumerate(proper)
        if not any(system < larger for larger in proper[:i])
    ]

    def components(system):
        remaining = set(system)
        pieces = []
        while remaining:
            start = remaining.pop()
            piece, queue = {start}, [start]
            while queue:
                root = queue.pop()
                neighbours = {other for other in remaining if dot(root, other) != 0}
                remaining -= neighbours
                piece |= neighbours
                queue.extend(neighbours)
            pieces.append(piece)
        return pieces

    names = {2: "A1", 6: "A2", 18: "A2+A2+A2", 32: "A5+A1", 40: "D5"}
    maximal_types = Counter((len(system), names[len(system)]) for system in maximal)
    expected = Counter({(40, "D5"): 27, (32, "A5+A1"): 36,
                        (18, "A2+A2+A2"): 40})
    require(len(subsystems) == 5_079)
    require(len(maximal) == 103)
    require(maximal_types == expected)
    require(all(sum(len(piece) for piece in components(system)) == len(system)
               for system in maximal))

    return {
        "closed_subsystems": len(subsystems),
        "maximal_proper": len(maximal),
        "maximal_types": {"D5": 27, "A5+A1": 36, "A2^3": 40},
    }


def main():
    result = census()
    print("Closed-subsystem census passed (independent R8 realization)")
    print(f"closed subsystems={result['closed_subsystems']:,}; "
          f"maximal proper={result['maximal_proper']}")
    print("maximal types: D5=27, A5+A1=36, A2^3=40")


if __name__ == "__main__":
    main()
