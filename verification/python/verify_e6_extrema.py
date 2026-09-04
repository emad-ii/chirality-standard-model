#!/usr/bin/env python3
"""Exhaustively verify the two E6 intersection extrema and their classical incidence data."""

from collections import Counter, defaultdict, deque
from fractions import Fraction
from itertools import combinations, product

from verification_checks import require

# Bourbaki numbering: 1--3--4--5--6, with node 2 attached to 4.
C = (
    (2, 0, -1, 0, 0, 0),
    (0, 2, 0, -1, 0, 0),
    (-1, 0, 2, -1, 0, 0),
    (0, -1, -1, 2, -1, 0),
    (0, 0, 0, -1, 2, -1),
    (0, 0, 0, 0, -1, 2),
)
N = len(C)
E = tuple(tuple(int(i == j) for j in range(N)) for i in range(N))


def neg(v):
    return tuple(-x for x in v)


def add(u, v):
    return tuple(x + y for x, y in zip(u, v))


def pairing(weight, root):
    return sum(x * y for x, y in zip(weight, root))


def root_inner(u, v):
    return sum(u[i] * C[i][j] * v[j] for i in range(N) for j in range(N))


def reflect_root(root, i):
    out = list(root)
    out[i] -= sum(root[j] * C[j][i] for j in range(N))
    return tuple(out)


def reflect_weight(weight, i):
    return tuple(weight[j] - weight[i] * C[i][j] for j in range(N))


def reflect_set(S, i):
    return frozenset(reflect_root(a, i) for a in S)


def orbit(seed, step):
    seen, queue = {seed}, deque([seed])
    while queue:
        x = queue.popleft()
        for i in range(N):
            y = step(x, i)
            if y not in seen:
                seen.add(y)
                queue.append(y)
    return frozenset(seen)


def row_reduce(vectors):
    rows = [list(map(Fraction, v)) for v in vectors]
    r = 0
    for c in range(N):
        pivot = next((j for j in range(r, len(rows)) if rows[j][c]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        q = rows[r][c]
        rows[r] = [x / q for x in rows[r]]
        for j, row in enumerate(rows):
            if j != r and row[c]:
                q = row[c]
                rows[j] = [x - q * y for x, y in zip(row, rows[r])]
        r += 1
    return rows, r


def rank(vectors):
    return row_reduce(vectors)[1]


def inverse(matrix):
    rows = [
        list(map(Fraction, row)) + [Fraction(i == j) for j in range(N)]
        for i, row in enumerate(matrix)
    ]
    for c in range(N):
        pivot = next(j for j in range(c, N) if rows[j][c])
        rows[c], rows[pivot] = rows[pivot], rows[c]
        q = rows[c][c]
        rows[c] = [x / q for x in rows[c]]
        for j in range(N):
            if j != c and rows[j][c]:
                q = rows[j][c]
                rows[j] = [x - q * y for x, y in zip(rows[j], rows[c])]
    return tuple(tuple(row[N:]) for row in rows)


C_INV = inverse(C)


def weight_inner(u, v):
    return sum(u[i] * C_INV[i][j] * v[j] for i in range(N) for j in range(N))


def components(S):
    remaining, answer = set(S), []
    while remaining:
        start = remaining.pop()
        component, queue = {start}, [start]
        while queue:
            a = queue.pop()
            adjacent = {b for b in remaining if root_inner(a, b)}
            remaining -= adjacent
            component |= adjacent
            queue.extend(adjacent)
        answer.append(frozenset(component))
    return tuple(sorted(answer, key=lambda x: (len(x), sorted(x))))


def root_type(S):
    size_to_type = {2: "A1", 6: "A2", 12: "A3", 20: "A4", 30: "A5", 40: "D5"}
    sizes = sorted((len(c) for c in components(S)), reverse=True)
    return "+".join(size_to_type[n] for n in sizes)


def closed(S, roots):
    return all(neg(a) in S for a in S) and all(
        add(a, b) not in roots or add(a, b) in S for a in S for b in S
    )


def check_subsystems(sets, roots, count, size, dimension):
    require(len(sets) == count)
    require({(len(S), rank(S), closed(S, roots)) for S in sets} == {
        (size, dimension, True)
    })


def main():
    roots = orbit(E[0], reflect_root)
    highest = max((a for a in roots if min(a) >= 0), key=sum)
    require(len(roots) == 72 and highest == (1, 2, 2, 3, 2, 1))
    require(all(root_inner(a, a) == 2 for a in roots))

    # Bit masks make the Weyl-orbit checks independent of Python's
    # object-heavy frozenset representation.
    root_list = sorted(roots)
    root_index = {root: i for i, root in enumerate(root_list)}
    reflection_permutations = tuple(
        tuple(root_index[reflect_root(root, i)] for root in root_list)
        for i in range(N)
    )

    def set_mask(S):
        return sum(1 << root_index[root] for root in S)

    def permute_mask(mask, permutation):
        out = 0
        while mask:
            bit = mask & -mask
            index = bit.bit_length() - 1
            out |= 1 << permutation[index]
            mask -= bit
        return out

    def tuple_mask_orbit(seed):
        seen, queue = {seed}, deque([seed])
        while queue:
            item = queue.popleft()
            for permutation in reflection_permutations:
                image = tuple(permute_mask(mask, permutation) for mask in item)
                if image not in seen:
                    seen.add(image)
                    queue.append(image)
        return frozenset(seen)

    # The E6 Weyl group order is used only in orbit-stabilizer divisions.
    weyl_order = 51_840

    weights = orbit(E[0], reflect_weight)  # Dynkin labels of W omega_1
    D = {w: frozenset(a for a in roots if pairing(w, a) == 0) for w in weights}
    root_pairs = {min(a, neg(a)) for a in roots}
    A = {
        a: frozenset(b for b in roots if b in (a, neg(a)) or root_inner(a, b) == 0)
        for a in root_pairs
    }
    theta0 = frozenset(a for a in roots if a[highest.index(3)] % 3 == 0)
    Thetas = orbit(theta0, reflect_set)
    D_sets, A_sets = frozenset(D.values()), frozenset(A.values())
    D_masks = {d: set_mask(d) for d in D_sets}
    A_masks = {a: set_mask(a) for a in A_sets}
    Theta_masks = {theta: set_mask(theta) for theta in Thetas}
    check_subsystems(D_sets, roots, 27, 40, 5)
    check_subsystems(A_sets, roots, 36, 32, 6)
    check_subsystems(Thetas, roots, 40, 18, 6)

    theta_factors = {}
    for theta in Thetas:
        factors = components(theta)
        require(tuple(map(len, factors)) == (6, 6, 6))
        theta_factors[theta] = {a: factor for factor in factors for a in factor}

    DA = Counter(
        (pairing(w, a) != 0, len(d & q))
        for (w, d), (a, q) in product(D.items(), A.items())
    )
    DT = Counter(len(d & t) for d, t in product(D_sets, Thetas))
    AT = Counter((a in t, len(q & t)) for (a, q), t in product(A.items(), Thetas))
    require(DA == Counter({(False, 16): 540, (True, 20): 432}))
    require(DT == Counter({10: 1_080}))
    require(AT == Counter({(False, 6): 1_080, (True, 14): 360}))
    pairwise_maxima = max(n for _, n in DA), max(DT), max(n for _, n in AT)

    profiles, common_sizes = Counter(), Counter()
    cells = defaultdict(set)
    cell_types = defaultdict(set)
    pairwise, total = set(), set()
    pairwise_by_dt, total_by_dt = defaultdict(list), defaultdict(list)
    pairwise_intersections, total_intersections = Counter(), Counter()

    for (w, d), (a, q), theta in product(D.items(), A.items(), Thetas):
        profile = len(d & q), len(d & theta), len(q & theta)
        common = d & q & theta
        profiles[profile] += 1
        common_sizes[(profile, len(common))] += 1

        is_pairwise = profile == pairwise_maxima
        factor = theta_factors[theta].get(a)
        nontrivial_on_factor = factor is not None and any(
            pairing(w, b) != 0 for b in factor
        )
        is_total = a in theta and pairing(w, a) == 0 and nontrivial_on_factor
        require(is_total == (len(common) == 10))

        triple = (D_masks[d], A_masks[q], Theta_masks[theta])
        cells[profile, len(common)].add(triple)
        cell_types[profile, len(common)].add(root_type(common))
        if is_pairwise:
            require((len(common), rank(common)) == (8, 3))
            pairwise.add(triple)
            pairwise_by_dt[d, theta].append((q, common))
            pairwise_intersections[common] += 1
        if is_total:
            require((len(common), rank(common)) == (10, 4))
            total.add(triple)
            total_by_dt[d, theta].append((q, common))
            total_intersections[common] += 1

    require(profiles == Counter({
        (20, 10, 14): 4_320,
        (20, 10, 6): 12_960,
        (16, 10, 14): 5_400,
        (16, 10, 6): 16_200,
    }))
    require(common_sizes == Counter({
        ((16, 10, 6), 2): 12_960,
        ((20, 10, 6), 4): 12_960,
        ((16, 10, 6), 6): 3_240,
        ((16, 10, 14), 6): 3_240,
        ((20, 10, 14), 8): 4_320,
        ((16, 10, 14), 10): 2_160,
    }))
    expected_types = {
        ((16, 10, 6), 2): {"A1"},
        ((20, 10, 6), 4): {"A1+A1"},
        ((16, 10, 6), 6): {"A1+A1+A1"},
        ((16, 10, 14), 6): {"A1+A1+A1"},
        ((20, 10, 14), 8): {"A2+A1"},
        ((16, 10, 14), 10): {"A2+A1+A1"},
    }
    require(dict(cell_types) == expected_types)
    require({key for key, types in cell_types.items() if any("A2" in t for t in types)} == {
        ((20, 10, 14), 8), ((16, 10, 14), 10)
    })

    require(len(pairwise) == 4_320 and len(total) == 2_160)

    require(len(cells) == 6)
    for triples in cells.values():
        require(tuple_mask_orbit(next(iter(triples))) == frozenset(triples))

    pairwise_orbit = tuple_mask_orbit(next(iter(pairwise)) )
    total_orbit = tuple_mask_orbit(next(iter(total)))
    require(pairwise_orbit == frozenset(pairwise))
    require(total_orbit == frozenset(total))
    require(weyl_order // len(pairwise_orbit) == 12)
    require(weyl_order // len(total_orbit) == 24)

    require(len(pairwise_intersections) == 720)
    require(Counter(pairwise_intersections.values()) == Counter({6: 720}))
    require(len(total_intersections) == 1_080)
    require(Counter(total_intersections.values()) == Counter({2: 1_080}))
    require(set(pairwise_by_dt) == set(total_by_dt) and len(pairwise_by_dt) == 1_080)
    require(Counter(map(len, pairwise_by_dt.values())) == Counter({4: 1_080}))
    require(Counter(map(len, total_by_dt.values())) == Counter({2: 1_080}))
    require(all(len({common for _, common in entries}) == 1
               for entries in total_by_dt.values()))

    labelled_containments, inclusions = 0, set()
    for key in pairwise_by_dt:
        d, theta = key
        for q_p, r_p in pairwise_by_dt[key]:
            for q_t, r_t in total_by_dt[key]:
                require(r_p < r_t)
                require((d & q_p) & (d & q_t) == r_p)
                require(rank((d & q_p) | (d & q_t)) == rank(d & q_t))
                labelled_containments += 1
                inclusions.add((set_mask(r_p), set_mask(r_t)))
    require(labelled_containments == 8_640 and len(inclusions) == 2_160)
    inclusion_orbit = tuple_mask_orbit(next(iter(inclusions)))
    require(inclusion_orbit == frozenset(inclusions))

    # Classical cubic-surface incidence carried by the 27 weights.
    require({weight_inner(w, w) for w in weights} == {Fraction(4, 3)})
    require(Counter(
        weight_inner(u, v) for u, v in combinations(weights, 2)
    ) == Counter({Fraction(1, 3): 216, Fraction(-2, 3): 135}))

    tritangents = {
        frozenset((u, v, neg(add(u, v))))
        for u, v in combinations(weights, 2)
        if neg(add(u, v)) in weights and len({u, v, neg(add(u, v))}) == 3
    }
    require(len(tritangents) == 45)
    require(orbit(
        next(iter(tritangents)),
        lambda T, i: frozenset(reflect_weight(w, i) for w in T),
    ) == frozenset(tritangents))

    double_sixes = set()
    for a in root_pairs:
        plus = {w for w in weights if pairing(w, a) > 0}
        minus = {w for w in weights if pairing(w, a) < 0}
        require((len(plus), len(minus)) == (6, 6))
        require({weight_inner(u, v) for u, v in combinations(plus, 2)} == {
            Fraction(1, 3)
        })
        require({weight_inner(u, v) for u, v in combinations(minus, 2)} == {
            Fraction(1, 3)
        })
        require(Counter(weight_inner(u, v) for u in plus for v in minus) == Counter({
            Fraction(-2, 3): 30,
            Fraction(1, 3): 6,
        }))
        double_sixes.add(frozenset(plus | minus))
    require(len(double_sixes) == 36)

    nine_line_sets, partitions = set(), set()
    for theta in Thetas:
        blocks = frozenset(
            frozenset(w for w in weights if all(pairing(w, a) == 0 for a in factor))
            for factor in components(theta)
        )
        require(sorted(map(len, blocks)) == [9, 9, 9])
        require(len(set().union(*blocks)) == 27)
        partitions.add(blocks)
        nine_line_sets |= set(blocks)
    require(len(partitions) == 40 and len(nine_line_sets) == 120)
    require(all(sum(T <= block for T in tritangents) == 6 for block in nine_line_sets))

    print("E6 extremal-incidence verification passed")
    print(f"roots={len(roots)}, |W|={weyl_order:,}, subsystem orbits=(27, 36, 40)")
    print(f"triples={sum(profiles.values()):,}")
    print(f"pairwise maximizers={len(pairwise):,}, stabilizer={weyl_order//len(pairwise):,}")
    print(f"common maximizers={len(total):,}, stabilizer={weyl_order//len(total):,}")
    print(f"joint-profile orbits={len(cells)}")
    for key in sorted(common_sizes):
        t = next(iter(cell_types[key]))
        print(f"profile={key[0]}, common roots={key[1]}, type={t}: {common_sizes[key]:,}")
    print("A2 occurs exactly in the pairwise- and common-maximal cells")
    print(f"distinct inclusions={len(inclusions):,}; labelled realizations={labelled_containments:,}")
    print("cubic-surface data: 27 lines, 36 double-sixes, 45 tritangents, 40 triads")


if __name__ == "__main__":
    main()
