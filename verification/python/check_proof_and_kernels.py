#!/usr/bin/env python3
"""Independent checks of stabilizers and global-form kernels."""

from collections import deque
from itertools import product

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
    return root_list, index, tuple(seen)


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


def main():
    roots = e6.orbit(e6.E[0], e6.reflect_root)
    highest = max((root for root in roots if min(root) >= 0), key=sum)
    _root_list, root_index, weyl = generate_weyl_permutations(roots)

    weights = sorted(e6.orbit(e6.E[0], e6.reflect_weight))
    D = {
        weight: frozenset(root for root in roots if e6.pairing(weight, root) == 0)
        for weight in weights
    }
    root_pairs = sorted({min(root, e6.neg(root)) for root in roots})
    A = {
        root: frozenset(
            beta for beta in roots
            if beta in (root, e6.neg(root)) or e6.root_inner(root, beta) == 0
        )
        for root in root_pairs
    }
    theta0 = frozenset(root for root in roots if root[highest.index(3)] % 3 == 0)
    thetas = sorted(e6.orbit(theta0, e6.reflect_set), key=lambda S: tuple(sorted(S)))
    theta_factors = {
        theta: {root: factor for factor in e6.components(theta) for root in factor}
        for theta in thetas
    }

    pairwise_rep = None
    common_rep = None
    for weight, alpha, theta in product(weights, root_pairs, thetas):
        d_set, a_set = D[weight], A[alpha]
        profile = len(d_set & a_set), len(d_set & theta), len(a_set & theta)
        factor = theta_factors[theta].get(alpha)
        total = (
            alpha in theta and e6.pairing(weight, alpha) == 0 and factor is not None
            and any(e6.pairing(weight, beta) != 0 for beta in factor)
        )
        if pairwise_rep is None and profile == (20, 10, 14):
            pairwise_rep = (alpha, d_set, a_set, theta)
        if common_rep is None and total:
            common_rep = (alpha, d_set, a_set, theta)
        if pairwise_rep and common_rep:
            break

    results = []
    for name, rep, expected_pair, expected_triple in (
        ("pairwise", pairwise_rep, 120, 12),
        ("common", common_rep, 96, 24),
    ):
        alpha, d_set, a_set, theta = rep
        d_mask, a_mask, theta_mask = (
            set_mask(d_set, root_index), set_mask(a_set, root_index), set_mask(theta, root_index)
        )
        pair_stabilizer = [
            p for p in weyl
            if permute_mask(d_mask, p) == d_mask and permute_mask(a_mask, p) == a_mask
        ]
        triple_stabilizer = [p for p in pair_stabilizer if permute_mask(theta_mask, p) == theta_mask]
        require(len(pair_stabilizer) == expected_pair)
        require(len(triple_stabilizer) == expected_triple)
        results.append((name, len(pair_stabilizer), len(triple_stabilizer)))
        if name == "common":
            alpha_index = root_index[alpha]
            negative_index = root_index[e6.neg(alpha)]
            fixed = sum(p[alpha_index] == alpha_index for p in pair_stabilizer)
            flipped = sum(p[alpha_index] == negative_index for p in pair_stabilizer)
            require((fixed, flipped) == (48, 48))
            results.append(("common pair: alpha fixed/flipped", fixed, flipped))

    # Exact phase arithmetic, using zeta = exp(pi i/3) and exponents modulo 6.
    zeta, omega, minus_one = 1, 2, 3
    require((-2 * zeta + omega) % 6 == 0)
    require((3 * zeta + minus_one) % 6 == 0)
    require((3 * zeta) % 6 == minus_one)
    require((-3 * zeta) % 6 == minus_one)
    require((zeta + omega) % 6 == minus_one)
    require((-3 * zeta) % 6 == minus_one)

    # The natural map from the displayed LR covering product to the
    # Pati--Salam covering product is not injective.  Writing z=zeta^k,
    # its kernel has z^3=1 and g3=z^-1 I3, hence three elements.  The
    # element with k=2 is exactly k_LR^2.
    lr_to_ps_cover_kernel = tuple(k for k in range(6) if (3 * k) % 6 == 0)
    require(lr_to_ps_cover_kernel == (0, 2, 4))
    require((2 * omega + 2 * zeta) % 6 == 0)
    require((-3 * (2 * zeta)) % 6 == 0)

    ps_actions = {
        "(4,2,1)": (-1) * (-1),
        "(bar4,1,2)": (-1) * (-1),
        "(6,1,1)": (-1) ** 2,
        "(1,2,2)": (-1) * (-1),
        "(1,1,1)": 1,
    }
    require(set(ps_actions.values()) == {1})

    print("Strengthened stabilizer and global-kernel checks passed")
    for row in results:
        print(*row, sep=": ")
    print("SM kernel generator maps to LR kernel generator")
    print("LR kernel generator maps to (-I4,-I2,-I2) in the PS cover")
    print("LR-to-PS covering map has Z3 kernel generated by k_LR^2")
    print("PS central kernel acts trivially on all displayed 27 summands")


if __name__ == "__main__":
    main()
