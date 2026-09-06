#!/usr/bin/env python3
"""Arithmetic audits used in the classical rank-deficient proof.

The manuscript proof is uniform in rank.  This script combines bounded
regression checks for its Cartan equations and A-type cubic identity with
exact symbolic polynomial checks for the all-rank odd-D monotonicity step and
exact E6 dimension calculations.  Silent boundary regressions also distinguish
SU(N) inner automorphisms from their lifts and trace type-A representation
cubics.  The bounds are explicit below; the bounded loops audit the formulas
and do not replace the manuscript's all-rank proof or correct its wording.
"""

from collections import deque
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import comb, factorial, gcd, lcm

from verification_checks import VerificationFailure, require


MAX_REGRESSION_RANK = 32
MAX_A_COEFFICIENT = 5
MAX_PHASE_N = 8
MAX_TRACE_N = 9
MAX_TABLEAU_N = 5


def require_rejected(check, detail):
    # Only an intentional verification failure counts, never an indexing,
    # factorial, or division error.  Unexpected acceptance fails closed.
    try:
        check()
    except VerificationFailure:
        return
    require(False, detail)


def poly_mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def poly_product(*factors):
    out = [1]
    for factor in factors:
        out = poly_mul(out, list(factor))
    return out


def poly_sub(p, q):
    n = max(len(p), len(q))
    return [
        (p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0)
        for i in range(n)
    ]


def poly_shift(p, shift):
    # Coefficients in ascending powers; substitute r=n+shift.
    out = [0] * len(p)
    for power, coefficient in enumerate(p):
        for k in range(power + 1):
            out[k] += coefficient * comb(power, k) * shift ** (power - k)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def path_cartan(r):
    C = [[0] * r for _ in range(r)]
    for i in range(r):
        C[i][i] = 2
    for i in range(r - 1):
        C[i][i + 1] = C[i + 1][i] = -1
    return C


def A(r):
    return path_cartan(r)


def B(r):
    C = path_cartan(r)
    C[r - 2][r - 1], C[r - 1][r - 2] = -2, -1
    return C


def Ctype(r):
    C = path_cartan(r)
    C[r - 2][r - 1], C[r - 1][r - 2] = -1, -2
    return C


def D(r):
    C = [[0] * r for _ in range(r)]
    for i in range(r):
        C[i][i] = 2
    for i in range(r - 3):
        C[i][i + 1] = C[i + 1][i] = -1
    C[r - 3][r - 2] = C[r - 2][r - 3] = -1
    C[r - 3][r - 1] = C[r - 1][r - 3] = -1
    return C


def simply_laced(r, edges):
    C = [[0] * r for _ in range(r)]
    for i in range(r):
        C[i][i] = 2
    for i, j in edges:
        C[i][j] = C[j][i] = -1
    return C


def E6():
    return simply_laced(6, [(0, 2), (2, 3), (3, 4), (4, 5), (1, 3)])


def E7():
    return simply_laced(7, [(0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 3)])


def E8():
    return simply_laced(8, [(0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (1, 3)])


def F4():
    return [[2, -1, 0, 0], [-1, 2, -2, 0], [0, -1, 2, -1], [0, 0, -1, 2]]


def G2():
    return [[2, -1], [-3, 2]]


def generate_roots(C):
    r = len(C)
    roots, queue = set(), deque()
    for i in range(r):
        e = [0] * r
        e[i] = 1
        for a in (tuple(e), tuple(-x for x in e)):
            roots.add(a)
            queue.append(a)
    while queue:
        a = queue.popleft()
        for i in range(r):
            pairing = sum(a[j] * C[j][i] for j in range(r))
            b = list(a)
            b[i] -= pairing
            b = tuple(b)
            if b not in roots:
                roots.add(b)
                queue.append(b)
    return roots


def highest_root_labels(C):
    roots = generate_roots(C)
    theta = max((a for a in roots if all(x >= 0 for x in a)), key=sum)
    return tuple(sum(theta[k] * C[k][j] for k in range(len(C))) for j in range(len(C)))



def theta_labels(kind, r, C):
    if kind == "A":
        if r == 1:
            return (2,)
        return (1,) + (0,) * (r - 2) + (1,)
    if kind == "B":
        if r == 2:
            return (0, 2)
        return (0, 1) + (0,) * (r - 2)
    if kind == "C":
        return (2,) + (0,) * (r - 1)
    if kind == "D":
        return (0, 1) + (0,) * (r - 2)
    return highest_root_labels(C)

def dual_labels(kind, labels):
    labels = list(labels)
    r = len(labels)
    if kind == "A":
        return tuple(reversed(labels))
    if kind == "D" and r % 2:
        labels[-1], labels[-2] = labels[-2], labels[-1]
    if kind == "E6":
        return (labels[5], labels[1], labels[4], labels[3], labels[2], labels[0])
    return tuple(labels)


def symmetrizer(C):
    r = len(C)
    d = [None] * r
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
        den = lcm(den, x.denominator)
    values = [int(x * den) for x in d]
    common = 0
    for x in values:
        common = gcd(common, x)
    return [x // common for x in values]


def inner(a, b, C, d):
    return sum(
        Fraction(a[i] * C[i][j] * d[j] * b[j])
        for i in range(len(C))
        for j in range(len(C))
    )


def coroot_coeff(a, C, d):
    aa = inner(a, a, C, d)
    return [Fraction(2 * a[i] * d[i], aa) for i in range(len(C))]


def rep_dimension(labels, C):
    d = symmetrizer(C)
    answer = Fraction(1)
    for root in generate_roots(C):
        if not (all(x >= 0 for x in root) and any(root)):
            continue
        coeff = coroot_coeff(root, C, d)
        answer *= Fraction(
            sum(coeff[i] * (labels[i] + 1) for i in range(len(C))),
            sum(coeff),
        )
    require(answer.denominator == 1)
    return answer.numerator


def c3_A(labels):
    N = len(labels) + 1
    rows = [sum(labels[i:]) for i in range(N - 1)] + [0]
    shifted = [Fraction(rows[i] + N - 1 - i) for i in range(N)]
    mean = sum(shifted) / N
    return sum((x - mean) ** 3 for x in shifted)


def dual_permutation(kind, r):
    if kind == "A":
        return list(reversed(range(r)))
    if kind == "D" and r % 2:
        return list(range(r - 2)) + [r - 1, r - 2]
    if kind == "E6":
        return [5, 1, 4, 3, 2, 0]
    return list(range(r))


def solve_lambda_plus_dual(theta, kind):
    r = len(theta)
    p = dual_permutation(kind, r)
    seen = set()
    partial = [0] * r
    solutions = []

    def rec(orbits, idx):
        if idx == len(orbits):
            solutions.append(tuple(partial))
            return
        orbit = orbits[idx]
        if len(orbit) == 1:
            j = orbit[0]
            if theta[j] % 2:
                return
            partial[j] = theta[j] // 2
            rec(orbits, idx + 1)
            return
        j, k = orbit
        if theta[j] != theta[k]:
            return
        for value in range(theta[j] + 1):
            partial[j] = value
            partial[k] = theta[j] - value
            rec(orbits, idx + 1)

    orbits = []
    for i in range(r):
        if i in seen:
            continue
        j = p[i]
        orbit = tuple(sorted({i, j}))
        seen.update(orbit)
        orbits.append(orbit)
    rec(orbits, 0)
    return solutions


def solve_cartan_equations():
    types = [
        ("A", 1, A(1)), ("B", 2, B(2)), ("C", 2, Ctype(2)),
        ("G2", 2, G2()), ("F4", 4, F4()),
        ("E6", 6, E6()), ("E7", 7, E7()), ("E8", 8, E8()),
    ]
    for r in range(2, MAX_REGRESSION_RANK + 1):
        types.append(("A", r, A(r)))
        types.append(("B", r, B(r)))
        types.append(("C", r, Ctype(r)))
        if r >= 4:
            types.append(("D", r, D(r)))

    for kind, r, C in types:
        theta = theta_labels(kind, r, C)
        p = dual_permutation(kind, r)
        cartan_solutions = solve_lambda_plus_dual(theta, kind)
        half_solutions = []
        if all(x % 2 == 0 for x in theta):
            half_solutions = [tuple(x // 2 for x in theta)]
        fixed_solutions = []
        for i in range(r):
            if p[i] != i:
                continue
            nums = [theta[j] + C[i][j] for j in range(r)]
            if all(x >= 0 and x % 2 == 0 for x in nums):
                labels = tuple(x // 2 for x in nums)
                if labels[i] > 0:
                    fixed_solutions.append((i, labels))

        allowed_cartan = set()
        if kind == "A":
            allowed_cartan = {tuple([1] + [0] * (r - 1)), tuple([0] * (r - 1) + [1])}
        elif kind == "C":
            allowed_cartan = {tuple([1] + [0] * (r - 1))}
        elif kind == "B" and r == 2:
            allowed_cartan = {(0, 1)}
        require(set(cartan_solutions) == allowed_cartan)

        allowed_half = set()
        if (kind == "A" and r == 1) or kind == "C":
            allowed_half = {tuple([1] + [0] * (r - 1))}
        elif kind == "B" and r == 2:
            allowed_half = {(0, 1)}
        require(set(half_solutions) == allowed_half)

        for i, labels in fixed_solutions:
            if kind == "B":
                require(labels == tuple(1 if j == 0 else 0 for j in range(r)) or (r == 3 and labels == (0, 0, 1)))
            elif kind == "D":
                require(labels == tuple(1 if j == 0 else 0 for j in range(r)) or (r == 4 and labels in {(0, 0, 1, 0), (0, 0, 0, 1)}))
            elif kind == "C":
                require(r == 2 and labels == (0, 1))
            elif kind == "A":
                require((r, labels) in {(1, (2,)), (3, (0, 1, 0))})
            elif kind == "G2":
                require(labels == (1, 0))
            else:
                require(False, (kind, r, i, labels))


def signed_A_pair_cubic(N, a, i):
    require(N >= 3 and a >= 1 and 1 <= i < N and 2 * i != N,
            ("distinct dual support nodes required", N, a, i))
    distance = N - 2 * i
    return -6 * a * (1 if distance > 0 else -1) * (2 * a + abs(distance))


def check_A_cubic_formula():
    # Universal algebraic step, independent of shifted-weight evaluation:
    # (x-1)^3 + (y+1)^3 - x^3 - y^3 = 3(x+y)(1+y-x).
    require(poly_sub(poly_product((-1, 1), (-1, 1), (-1, 1)),
                     [0, 0, 0, 1]) == [-1, 3, -3, 0])
    require(poly_sub(poly_product((1, 1), (1, 1), (1, 1)),
                     [0, 0, 0, 1]) == [1, 3, 3, 0])
    # The centered coordinates of 2*lambda pair to zero.  At either support
    # node x-y=2a+1 and x+y=sgn(N-2i)*(2a+abs(N-2i)), giving the signed formula.
    for N in range(3, MAX_REGRESSION_RANK + 1):
        C = A(N - 1)
        for i in range(1, N):
            if i == N - i:
                continue
            for a in range(1, MAX_A_COEFFICIENT + 1):
                labels = [0] * (N - 1)
                labels[i - 1] = a
                labels[N - i - 1] = a
                mu = [2 * x for x in labels]
                for j in range(N - 1):
                    mu[j] -= C[i - 1][j]
                actual = c3_A(tuple(mu))
                require(actual == signed_A_pair_cubic(N, a, i), (N, a, i))
                require(actual != 0 and c3_A(tuple(reversed(mu))) == -actual)

    # Printed expression at N=4, a=1, i=3: 0; actual mu=(2,1,0): 24.
    actual = c3_A((2, 1, 0))
    printed = -6 * 1 * (2 * 1 + 4 - 2 * 3)
    require(actual == 24 and printed == 0)
    require_rejected(lambda: require(actual == printed), "old unsigned formula accepted")
    for i in (0, 2, 4):
        require_rejected(lambda: signed_A_pair_cubic(4, 1, i),
                         ("invalid dual support accepted", i))


def su_phase_invariants(phases):
    """Orders and fixed-algebra dimensions for eigenvalues exp(2*pi*i*phase)."""
    phases = tuple(Fraction(p) % 1 for p in phases)
    N = len(phases)
    require(N >= 2 and sum(phases).denominator == 1, "lift must lie in SU(N)")
    element_order = lcm(*(p.denominator for p in phases))
    automorphism_order = 1
    fixed_dimension = N - 1  # The diagonal Cartan is fixed.
    center_dimension = N - 1
    components = list(range(N))
    for i, j in combinations(range(N), 2):
        automorphism_order = lcm(automorphism_order, (phases[i] - phases[j]).denominator)
        if phases[i] != phases[j]:
            continue
        fixed_dimension += 2  # Both root spaces E_ij and E_ji are fixed.
        # Central diagonal coordinates must agree along every fixed root.
        # Each edge joining components adds one independent equality.
        if components[i] != components[j]:
            old, new = components[j], components[i]
            components = [new if c == old else c for c in components]
            center_dimension -= 1
    return element_order, automorphism_order, fixed_dimension, center_dimension


def require_order_three_inner(phases):
    invariants = su_phase_invariants(phases)
    require(invariants[1] == 3, "census requires a nonidentity inner order-three automorphism")
    return invariants


def check_SU_order_three_boundaries():
    central = (Fraction(1, 3),) * 3
    require(su_phase_invariants(central) == (3, 1, 8, 0))
    require_rejected(lambda: require_order_three_inner(central),
                     "central order-three element admitted to the census")
    # All SU(3) lifts of this automorphism differ by these three central shifts.
    # Their cube is the same nonidentity central element; every lift has order 9.
    for shift in range(3):
        phases = tuple(p + Fraction(shift, 3)
                       for p in (Fraction(-1, 9), Fraction(-1, 9), Fraction(2, 9)))
        invariants = require_order_three_inner(phases)
        require(invariants == (9, 3, 4, 1))
        require(all((3 * p) % 1 == Fraction(2, 3) for p in phases))
        require_rejected(lambda: require(invariants[0] == 3),
                         "old order-three lift restriction accepted")

    # Exhaust ordered three-block multiplicities, including empty blocks.
    # Subtracting the mean produces a determinant-one lift, without requiring
    # the lift itself to have order 3.  This is a bounded SU census only.
    for N in range(2, MAX_PHASE_N + 1):
        for n0 in range(N + 1):
            for n1 in range(N - n0 + 1):
                blocks = (n0, n1, N - n0 - n1)
                mean = Fraction(blocks[1] + 2 * blocks[2], 3 * N)
                phases = tuple(Fraction(j, 3) - mean
                               for j, count in enumerate(blocks) for _ in range(count))
                _, order, fixed, center = su_phase_invariants(phases)
                occupied = sum(count > 0 for count in blocks)
                require(fixed == sum(count * count for count in blocks) - 1)
                require(center == occupied - 1, (N, blocks))
                if occupied == 1:
                    require(order == 1 and center == 0 and fixed == N * N - 1)
                    require_rejected(lambda: require_order_three_inner(phases),
                                     ("identity automorphism admitted", N, blocks))
                else:
                    require_order_three_inner(phases)
                    require(order == 3 and center > 0 and fixed < N * N - 1)


def normalized_A_cubic(labels, dimension):
    N = len(labels) + 1
    require(N >= 3, "defining cubic normalization exists only for N >= 3")
    return Fraction(dimension * c3_A(labels), N * c3_A((1,) + (0,) * (N - 2)))


def exterior_cubic_index(N, k):
    require(N >= 3 and 1 <= k <= N - 1, ("exterior index domain", N, k))
    return Fraction((N - 2 * k) * factorial(N - 3),
                    factorial(k - 1) * factorial(N - k - 1))


def symmetric_cubic_index(N, k):
    require(N >= 3 and k >= 1, ("symmetric index domain", N, k))
    return Fraction((N + 2 * k) * factorial(N + k),
                    factorial(N + 2) * factorial(k - 1))


def tensor_power_weights(N, k, exterior=False):
    # Monomial bases: unordered k-tuples, with repetition only for Sym^k.
    choices = combinations if exterior else combinations_with_replacement
    return [tuple(indices.count(j) for j in range(N))
            for indices in choices(range(N), k)]


def cartan_trace_cubic(weights, N):
    # Trace the full polarized cubic on H_j=E_jj-E_NN, not sampled diagonals.
    # Repeated weights retain their multiplicities.  These symmetric tensor
    # entries determine the entire Cartan cubic (and hence the invariant cubic).
    restricted = [tuple(w[j] - w[-1] for j in range(N - 1)) for w in weights]
    return tuple(sum(w[i] * w[j] * w[k] for w in restricted)
                 for i, j, k in combinations_with_replacement(range(N - 1), 3))


def tableau_weights(labels):
    # Semistandard tableaux independently construct the character of a general
    # type-A highest weight: weakly increasing rows, strictly increasing columns.
    N = len(labels) + 1
    rows = [sum(labels[i:]) for i in range(N - 1)]
    cells = [(i, j) for i, length in enumerate(rows) for j in range(length)]
    filled = {}
    counts = [0] * N
    weights = []

    def visit(position):
        if position == len(cells):
            weights.append(tuple(counts))
            return
        i, j = cells[position]
        lower = max(filled[i, j - 1] if j else 0,
                    filled[i - 1, j] + 1 if i else 0)
        for entry in range(lower, N):
            filled[i, j] = entry
            counts[entry] += 1
            visit(position + 1)
            counts[entry] -= 1

    visit(0)
    return weights


def check_A_trace_cubic_boundaries():
    require(c3_A((1,)) == 0)
    require_rejected(lambda: normalized_A_cubic((1,), 2), "SU(2) normalization accepted")
    require_rejected(lambda: symmetric_cubic_index(2, 2), "SU(2) assigned index N+4")
    require_rejected(lambda: exterior_cubic_index(2, 1), "SU(2) exterior index accepted")
    for N in range(2, MAX_TRACE_N + 1):
        defining = cartan_trace_cubic(tensor_power_weights(N, 1), N)
        require(any(defining) == (N >= 3))
        for exterior in (False, True):
            degrees = range(N + 1) if exterior else range(MAX_A_COEFFICIENT + 1)
            for k in degrees:
                weights = tensor_power_weights(N, k, exterior)
                dimension = comb(N, k) if exterior else comb(N + k - 1, k)
                require(len(weights) == dimension)
                trace = cartan_trace_cubic(weights, N)
                trivial = k == 0 or (exterior and k == N)
                if N == 2 or trivial:
                    require(not any(trace), ("zero cubic boundary", N, k, exterior))
                    if trivial:
                        require(dimension == 1)
                    continue
                labels = [0] * (N - 1)
                if exterior:
                    labels[k - 1] = 1
                    index = exterior_cubic_index(N, k)
                    require(exterior_cubic_index(N, N - k) == -index)
                else:
                    labels[0] = k
                    index = symmetric_cubic_index(N, k)
                    if k == 2:
                        require(index == N + 4)
                require(trace == tuple(index * value for value in defining), (N, k, exterior))
                require(normalized_A_cubic(labels, dimension) == index, (N, k, exterior))
        for k in (-1, 0, N, N + 1):
            require_rejected(lambda: exterior_cubic_index(N, k),
                             ("invalid exterior index accepted", N, k))

    # Bounded mixed highest weights as well as powers of the defining module:
    # N=2..5 and total Dynkin coefficient <=2, including trivial and dual cases.
    for N in range(2, MAX_TABLEAU_N + 1):
        defining = cartan_trace_cubic(tensor_power_weights(N, 1), N)
        for labels in product(range(3), repeat=N - 1):
            if sum(labels) > 2:
                continue
            weights = tableau_weights(labels)
            dimension = rep_dimension(labels, A(N - 1))
            require(len(weights) == dimension, ("tableau dimension", N, labels))
            trace = cartan_trace_cubic(weights, N)
            if N == 2:
                require(not any(trace) and c3_A(labels) == 0)
            else:
                index = normalized_A_cubic(labels, dimension)
                require(trace == tuple(index * value for value in defining), (N, labels))
                dual_trace = cartan_trace_cubic(tableau_weights(tuple(reversed(labels))), N)
                require(dual_trace == tuple(-value for value in trace), ("dual cubic", N, labels))


def dim_D_coordinates(coords):
    r = len(coords)
    answer = Fraction(1)
    for i in range(r):
        for j in range(i + 1, r):
            answer *= Fraction(coords[i] - coords[j] + j - i, j - i)
            answer *= Fraction(
                coords[i] + coords[j] + 2 * r - i - j - 2,
                2 * r - i - j - 2,
            )
    require(answer.denominator == 1)
    return answer.numerator


def check_D_odd_gaps():
    # Exact polynomial proof that the two displayed ratio sequences decrease.
    # For a=1, R(r+1)/R(r) has numerator
    # r^2(r+2)(2r+3) and denominator (r-1)(r+1)(r+5)(2r+1).
    numerator_1 = poly_product((0, 1), (0, 1), (2, 1), (3, 2))
    denominator_1 = poly_product((-1, 1), (1, 1), (5, 1), (1, 2))
    difference_1 = poly_shift(poly_sub(denominator_1, numerator_1), 5)
    require(difference_1 == [365, 259, 57, 4])
    require(all(value > 0 for value in difference_1))

    # For a=2, the corresponding ratio is
    # r^2(r+3)^3(r+4)(2r+5)(2r+7) divided by
    # (r-1)(r+2)^2(r+6)(r+7)(r+9)(2r+1)(2r+3).
    numerator_2 = poly_product(
        (0, 1), (0, 1),
        (3, 1), (3, 1), (3, 1),
        (4, 1), (5, 2), (7, 2),
    )
    denominator_2 = poly_product(
        (-1, 1), (2, 1), (2, 1), (6, 1), (7, 1), (9, 1),
        (1, 2), (3, 2),
    )
    difference_2 = poly_shift(poly_sub(denominator_2, numerator_2), 5)
    require(difference_2 == [
        22_419_744, 24_455_216, 11_162_622, 2_769_860,
        404_090, 34_692, 1_624, 32,
    ])
    require(all(value > 0 for value in difference_2))

    require(Fraction(22, 35) < Fraction(2, 3))
    require(Fraction(1_274, 8_019) < Fraction(1, 6))

    for r in range(5, 32, 2):
        H = r * (2 * r - 1)
        for a in (1, 2):
            W = dim_D_coordinates([a] * (r - 1) + [0])
            M = dim_D_coordinates([2 * a] * (r - 2) + [2 * a - 1, 1])
            if a == 1:
                expected = Fraction(36 * (r - 1) * (2 * r + 1), r * (r + 2) * (r + 3) * (r + 4))
                require(W == comb(2 * r, r - 1))
                require(expected <= Fraction(2, 3))
            else:
                expected = Fraction(
                    5_376_000 * (r - 1) * (r + 2) * (2 * r + 1) * (2 * r + 3) ** 2 * (2 * r + 5),
                    r * (r + 1) * (r + 3) ** 2 * (r + 4) ** 3 * (r + 5) ** 3 * (r + 6) ** 2 * (r + 7) * (r + 8),
                )
                require(expected <= Fraction(1, 6))
                require(W > comb(2 * r, r - 1))
            require(Fraction(4 * M, W * W) == expected)
            require(W >= H)
            require(W * (W - 1) // 2 - H - 2 * M > 0)


def check_E6_gaps():
    C = E6()
    expected = {
        ((0, 5), 1): (650, 78975, 52897),
        ((0, 5), 2): (85293, 314269956, 3008865288),
        ((2, 4), 1): (70070, 252808452, 1949250433),
        ((2, 4), 2): (221077350, 64821173232816, 24307954884506865),
    }
    for (pair, a), target in expected.items():
        labels = [0] * 6
        for i in pair:
            labels[i] = a
        mu = [2 * x for x in labels]
        for j in range(6):
            mu[j] -= C[pair[0]][j]
        W = rep_dimension(labels, C)
        M = rep_dimension(mu, C)
        gap = W * (W - 1) // 2 - 78 - 2 * M
        require((W, M, gap) == target)


def main():
    solve_cartan_equations()
    check_A_cubic_formula()
    check_SU_order_three_boundaries()
    check_A_trace_cubic_boundaries()
    check_D_odd_gaps()
    check_E6_gaps()
    print(f"Cartan-product regressions (rank <= {MAX_REGRESSION_RANK}).... passed")
    print(
        f"A-type cubic regressions (N <= {MAX_REGRESSION_RANK}, "
        f"a <= {MAX_A_COEFFICIENT}).. passed"
    )
    print("D-odd symbolic all-rank inequalities...... passed")
    print("E6 dual-support dimension checks.......... passed")
    print("all classical rank-deficient checks passed")


if __name__ == "__main__":
    main()
