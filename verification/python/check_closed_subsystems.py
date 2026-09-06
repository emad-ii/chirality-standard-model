#!/usr/bin/env python3
"""Enumerate every closed E6 root subsystem from its positive simple system."""

from collections import Counter

import verify_e6_extrema as e6

from verification_checks import require


def determinant(matrix):
    """Exact Bareiss determinant for a small integer matrix."""
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


def census(*, include_subsystems=False):
    roots = frozenset(e6.orbit(e6.E[0], e6.reflect_root))
    positive = tuple(sorted(root for root in roots if min(root) >= 0))
    require(len(roots) == 72 and len(positive) == 36)

    def reflect_in(root, mirror):
        coefficient = e6.root_inner(root, mirror)
        return tuple(x - coefficient * y for x, y in zip(root, mirror))

    def generated_subsystem(simple_roots):
        seen = set(simple_roots) | {e6.neg(root) for root in simple_roots}
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
            products = [e6.root_inner(root, old) for old in chosen]
            if any(value > 0 for value in products):
                continue
            enlarged_gram = [row + [products[i]] for i, row in enumerate(gram)]
            enlarged_gram.append(products + [2])
            if determinant(enlarged_gram) <= 0:
                continue
            enlarged = chosen + [root]
            subsystems.add(generated_subsystem(enlarged))
            if len(enlarged) < e6.N:
                extend(enlarged, j + 1, enlarged_gram)

    extend([], 0, [])

    # Explicit ambient additive closure check for every generated subsystem.
    for system in subsystems:
        for left in system:
            for right in system:
                total = tuple(a + b for a, b in zip(left, right))
                require(total not in roots or total in system,
                        "simple-root census produced a nonclosed subsystem")

    full = frozenset(roots)
    proper = sorted((system for system in subsystems if system != full),
                    key=len, reverse=True)
    maximal = [
        system for i, system in enumerate(proper)
        if not any(system < larger for larger in proper[:i])
    ]
    maximal_types = Counter(
        (len(system), e6.rank(system), e6.root_type(system)) for system in maximal
    )
    expected = Counter({
        (40, 5, "D5"): 27,
        (32, 6, "A5+A1"): 36,
        (18, 6, "A2+A2+A2"): 40,
    })
    require(len(subsystems) == 5_079)
    require(len(maximal) == 103)
    require(maximal_types == expected)

    result = {
        "closed_subsystems": len(subsystems),
        "maximal_proper": len(maximal),
        "maximal_types": {"D5": 27, "A5+A1": 36, "A2^3": 40},
    }
    if include_subsystems:
        return result, frozenset(subsystems), frozenset(maximal)
    return result


def main():
    result = census()
    print("Closed-subsystem census passed (simple-root realization)")
    print(f"closed subsystems={result['closed_subsystems']:,}; "
          f"maximal proper={result['maximal_proper']}")
    print("maximal types: D5=27, A5+A1=36, A2^3=40")


if __name__ == "__main__":
    main()
