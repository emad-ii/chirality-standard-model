#!/usr/bin/env python3
"""Check the left-right interchange symmetry of the E6 extremal contexts."""

from collections import Counter, deque
from functools import cache

import verify_e6_extrema as e6

from verification_checks import require


def generate_weyl_permutations(roots):
    root_list = sorted(roots)
    index = {root: i for i, root in enumerate(root_list)}
    simple = tuple(
        bytes(index[e6.reflect_root(root, j)] for root in root_list)
        for j in range(e6.N)
    )
    identity = bytes(range(len(root_list)))
    seen, queue = {identity}, deque([identity])
    while queue:
        permutation = queue.popleft()
        for reflection in simple:
            image = bytes(reflection[permutation[i]] for i in range(len(root_list)))
            if image not in seen:
                seen.add(image)
                queue.append(image)
    require(len(seen) == 51_840)
    return root_list, index, simple, tuple(seen)


def set_mask(roots, index):
    return sum(1 << index[root] for root in roots)


def permute_mask(mask, permutation):
    out = 0
    while mask:
        bit = mask & -mask
        i = bit.bit_length() - 1
        out |= 1 << permutation[i]
        mask -= bit
    return out


def orbit_pair(seed, simple):
    seen, queue = {seed}, deque([seed])
    while queue:
        d_mask, theta_mask = queue.popleft()
        for reflection in simple:
            image = (
                permute_mask(d_mask, reflection),
                permute_mask(theta_mask, reflection),
            )
            if image not in seen:
                seen.add(image)
                queue.append(image)
    return frozenset(seen)


def check_actual_chains(root_list, root_index, simple, d_sets, thetas, contexts):
    """Distinguish labelled extrema from regular connected-chain data.

    Use the existing E6 realization, not an independent root construction.
    SP = D & AP and ST = D & AT are the derived parents; KP and KT have
    roots RP = SP & Theta and RT = ST & Theta, but retain the Cartan spans
    of SP and ST.  Root intersections alone do not specify these chains.
    """
    ds = {set_mask(d, root_index) for d in d_sets.values()}
    ts = {set_mask(t, root_index) for t in thetas}
    require(contexts == {(d, t) for d in ds for t in ts}
            and len(contexts) == 1_080, "actual-chain contexts")
    a_masks = {
        set_mask((r for r in root_list
                  if r in (a, e6.neg(a)) or e6.root_inner(a, r) == 0), root_index)
        for a in root_list if a < e6.neg(a)
    }
    require(len(a_masks) == 36, "actual-chain A1+A5 parents")
    projections = {}
    for d, t in contexts:
        require((d & t).bit_count() == 10, "actual-chain context intersection")
        pairwise = [a for a in a_masks
                    if (d & a).bit_count() == 20 and (a & t).bit_count() == 14]
        common = [a for a in a_masks if (d & a & t).bit_count() == 10]
        require(len(pairwise) == 4 and len(common) == 2, "actual-chain extrema counts")
        require(len({d & a for a in common}) == 1,
                "redundant AT labels must have identical derived parents")
        for ap in pairwise:
            for at in common:
                sp, st = d & ap, d & at
                projections[d, ap, at, t] = (d, sp, st, sp & t, st & t)
    multiplicities = Counter(projections.values())
    chains = set(multiplicities)
    require(len(projections) == 8_640 and len(chains) == 4_320
            and set(multiplicities.values()) == {2}, "actual-chain projection fibres")

    @cache
    def span(mask):
        # Unique reduced row-echelon basis over Q (positive roots suffice).
        rows, rank = e6.row_reduce([
            r for i, r in enumerate(root_list) if mask & (1 << i) and min(r) >= 0
        ])
        return tuple(tuple(row) for row in rows[:rank])

    canonical = {}
    for chain in chains:
        d, sp, st, rp, rt = chain
        require(sp.bit_count() == 20 and st.bit_count() == 16
                and rp.bit_count() == 8 and rt.bit_count() == 10 and rp & rt == rp,
                "actual-chain roots and containment")
        require((len(span(sp)), len(span(st)), len(span(rp)), len(span(rt)))
                == (4, 5, 3, 4) and span(st) == span(d),
                "actual-chain Cartan spans")
        canonical[chain] = (d, st, rp, span(sp), rt, span(st))
    require(len(set(canonical.values())) == len(chains),
            "retained parents and canonical rational-span chains must be bijective")

    @cache
    def images(mask):
        return tuple(permute_mask(mask, reflection) for reflection in simple)

    def image(item, j):
        return tuple(images(mask)[j] for mask in item)

    def tuple_orbit(seed, universe, labelled=False):
        seen, queue = {seed}, deque([seed])
        while queue:
            item = queue.popleft()
            for j in range(len(simple)):
                moved = image(item, j)
                require(moved in universe, "actual-chain Weyl closure")
                if labelled:
                    require(projections[moved] == image(projections[item], j),
                            "actual-chain projection must be Weyl equivariant")
                if moved not in seen:
                    seen.add(moved)
                    queue.append(moved)
        return seen

    first = tuple_orbit(min(projections), projections, labelled=True)
    remainder = projections.keys() - first
    require(len(first) == len(remainder) == 4_320, "labelled-chain orbit sizes")
    require(tuple_orbit(min(remainder), projections, labelled=True) == remainder,
            "labelled chains must have exactly two Weyl orbits")
    require(tuple_orbit(min(chains), chains) == chains,
            "actual chains must form one Weyl orbit")


def main():
    roots = e6.orbit(e6.E[0], e6.reflect_root)
    highest = max((root for root in roots if min(root) >= 0), key=sum)
    root_list, root_index, simple, weyl = generate_weyl_permutations(roots)

    weights = e6.orbit(e6.E[0], e6.reflect_weight)
    d_sets = {
        weight: frozenset(root for root in roots if e6.pairing(weight, root) == 0)
        for weight in weights
    }
    theta0 = frozenset(root for root in roots if root[highest.index(3)] % 3 == 0)
    thetas = e6.orbit(theta0, e6.reflect_set)

    weight, d_set = next(iter(d_sets.items()))
    theta = next(iter(thetas))
    d_mask, theta_mask = set_mask(d_set, root_index), set_mask(theta, root_index)
    contexts = orbit_pair((d_mask, theta_mask), simple)
    require(len(contexts) == len(d_sets) * len(thetas) == 1_080)

    factors = e6.components(theta)
    trivial = [factor for factor in factors if all(e6.pairing(weight, root) == 0 for root in factor)]
    nontrivial = [factor for factor in factors if factor not in trivial]
    require(len(trivial) == 1 and len(nontrivial) == 2)
    color, left, right = trivial[0], nontrivial[0], nontrivial[1]
    color_mask, left_mask, right_mask = (
        set_mask(color, root_index), set_mask(left, root_index), set_mask(right, root_index)
    )

    rho_masks = []
    for factor in nontrivial:
        pairs = {
            min(root, e6.neg(root))
            for root in factor
            if e6.pairing(weight, root) == 0
        }
        require(len(pairs) == 1)
        root = next(iter(pairs))
        rho_masks.append((1 << root_index[root]) | (1 << root_index[e6.neg(root)]))
    rho_left, rho_right = rho_masks

    stabilizer = [
        permutation for permutation in weyl
        if permute_mask(d_mask, permutation) == d_mask
        and permute_mask(theta_mask, permutation) == theta_mask
    ]
    kernel, exchange = [], []
    for permutation in stabilizer:
        image_left = permute_mask(left_mask, permutation)
        image_right = permute_mask(right_mask, permutation)
        require(permute_mask(color_mask, permutation) == color_mask)
        if image_left == left_mask and image_right == right_mask:
            kernel.append(permutation)
            require(permute_mask(rho_left, permutation) == rho_left)
            require(permute_mask(rho_right, permutation) == rho_right)
        else:
            require(image_left == right_mask and image_right == left_mask)
            exchange.append(permutation)
            require(permute_mask(rho_left, permutation) == rho_right)
            require(permute_mask(rho_right, permutation) == rho_left)

    common_maximum = color_mask | rho_left | rho_right
    pairwise_left = color_mask | rho_left
    pairwise_right = color_mask | rho_right
    require(all(permute_mask(common_maximum, p) == common_maximum for p in stabilizer))
    require(all(
        permute_mask(pairwise_left, p) == pairwise_right
        and permute_mask(pairwise_right, p) == pairwise_left
        for p in exchange
    ))
    require(len(stabilizer) == 48 and len(kernel) == len(exchange) == 24)

    check_actual_chains(root_list, root_index, simple, d_sets, thetas, contexts)

    print("contexts in one Weyl orbit", len(contexts))
    print("context stabilizer order", len(stabilizer))
    print("factor-preserving kernel", len(kernel))
    print("factor-exchanging coset", len(exchange))
    print("common maximum fixed; pairwise maxima exchanged")


if __name__ == "__main__":
    main()
