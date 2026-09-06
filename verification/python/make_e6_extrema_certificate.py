#!/usr/bin/env python3
"""Create a deterministic JSON certificate for the E6 extremal scan."""

from collections import Counter, defaultdict
import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

import check_closed_subsystems as closed_simple
import check_closed_subsystems_r8 as closed_r8
import check_e6_pair_orderings as pair_orderings
import verify_e6_extrema as e6

from verification_checks import require

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
EXPECTED_DIR = REPO_ROOT / "verification" / "expected"
CERTIFICATE_DIR = REPO_ROOT / "verification" / "certificates"


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def encode_set(S, root_index):
    return [root_index[r] for r in sorted(S)]


def root_type(S):
    size_to_type = {2: "A1", 6: "A2", 12: "A3", 20: "A4", 30: "A5", 40: "D5"}
    sizes = sorted((len(c) for c in e6.components(S)), reverse=True)
    return "+".join(size_to_type.get(n, f"roots_{n}") for n in sizes)


def main(output: Path | None = None):
    closed_census, simple_systems, simple_maximal = closed_simple.census(include_subsystems=True)
    r8_census, r8_systems, r8_maximal = closed_r8.census(include_subsystems=True)
    require(r8_census == closed_census)
    # Compare the actual 5,079 sets, not merely matching summary counts.
    # This coordinate bridge is used only after both independent enumerations.
    def to_r8(systems):
        return frozenset(frozenset(tuple(
            sum(root[i] * closed_r8.SIMPLE[i][j] for i in range(6))
            for j in range(8)) for root in system) for system in systems)
    require([[closed_r8.dot(a, b) // 4 for b in closed_r8.SIMPLE]
             for a in closed_r8.SIMPLE] == [list(row) for row in e6.C],
            "coordinate bridge does not preserve the Cartan matrix")
    require(to_r8(simple_systems) == r8_systems,
            "independent censuses disagree on the complete subsystem sets")
    require(to_r8(simple_maximal) == r8_maximal,
            "independent censuses disagree on the maximal subsystem sets")
    d_chi_cells, intrinsic_selector = pair_orderings.census(include_structure=True)
    roots_set = e6.orbit(e6.E[0], e6.reflect_root)
    roots = sorted(roots_set)
    # One-based numbering is easier to inspect in a static certificate.
    root_index = {root: i + 1 for i, root in enumerate(roots)}

    weights = sorted(e6.orbit(e6.E[0], e6.reflect_weight))
    D = {w: frozenset(a for a in roots_set if e6.pairing(w, a) == 0) for w in weights}
    root_pairs = sorted({min(a, e6.neg(a)) for a in roots_set})
    A = {
        a: frozenset(
            b for b in roots_set
            if b in (a, e6.neg(a)) or e6.root_inner(a, b) == 0
        )
        for a in root_pairs
    }
    highest = max((a for a in roots_set if min(a) >= 0), key=sum)
    theta0 = frozenset(a for a in roots_set if a[highest.index(3)] % 3 == 0)
    theta_sets = e6.orbit(theta0, e6.reflect_set)
    thetas = sorted(theta_sets, key=lambda S: encode_set(S, root_index))

    theta_factors = {}
    for theta in thetas:
        theta_factors[theta] = {a: factor for factor in e6.components(theta) for a in factor}

    simple_reflections = []
    for i in range(e6.N):
        simple_reflections.append([
            root_index[e6.reflect_root(root, i)] for root in roots
        ])

    pairwise_counts = {
        "D_A": Counter(),
        "D_Theta": Counter(),
        "A_Theta": Counter(),
    }
    for w, a in product(weights, root_pairs):
        pairwise_counts["D_A"][(e6.pairing(w, a) != 0, len(D[w] & A[a]))] += 1
    for w, theta in product(weights, thetas):
        pairwise_counts["D_Theta"][len(D[w] & theta)] += 1
    for a, theta in product(root_pairs, thetas):
        pairwise_counts["A_Theta"][(a in theta, len(A[a] & theta))] += 1

    pairwise_maxima = (20, 10, 14)
    cells = Counter()
    representatives = {}
    pairwise = set()
    total = set()
    pairwise_by_dt = defaultdict(list)
    total_by_dt = defaultdict(list)
    pairwise_common = Counter()
    total_common = Counter()

    for w, a, theta in product(weights, root_pairs, thetas):
        d, q = D[w], A[a]
        profile = (len(d & q), len(d & theta), len(q & theta))
        common = d & q & theta
        key = (profile, len(common))
        cells[key] += 1
        representatives.setdefault(key, (w, a, theta, d, q, common))

        triple = (d, q, theta)
        if profile == pairwise_maxima:
            pairwise.add(triple)
            pairwise_by_dt[(d, theta)].append((q, common))
            pairwise_common[common] += 1

        factor = theta_factors[theta].get(a)
        nontrivial = factor is not None and any(e6.pairing(w, b) != 0 for b in factor)
        if a in theta and e6.pairing(w, a) == 0 and nontrivial:
            total.add(triple)
            total_by_dt[(d, theta)].append((q, common))
            total_common[common] += 1

    triple_step = lambda triple, i: tuple(e6.reflect_set(S, i) for S in triple)
    rep_records = []
    for key in sorted(representatives):
        profile, common_size = key
        w, a, theta, d, q, common = representatives[key]
        triple = (d, q, theta)
        orbit_size = len(e6.orbit(triple, triple_step))
        require(orbit_size == cells[key])
        rep_records.append({
            "profile": list(profile),
            "common_root_count": common_size,
            "cell_count": cells[key],
            "D_root_indices": encode_set(d, root_index),
            "A_root_indices": encode_set(q, root_index),
            "Theta_root_indices": encode_set(theta, root_index),
            "common_type": root_type(common),
        })

    inclusions = set()
    labelled = 0
    for key in sorted(pairwise_by_dt, key=lambda x: (encode_set(x[0], root_index), encode_set(x[1], root_index))):
        for _, r_p in pairwise_by_dt[key]:
            for _, r_t in total_by_dt[key]:
                require(r_p < r_t)
                inclusions.add((r_p, r_t))
                labelled += 1

    file_names = [
        "verification/python/run_all.py",
        "formal/scripts/generate_lean_data.py",
        "formal/scripts/check_generated_data.py",
        "verification/python/regenerate.py",
        "verification/python/source_snapshot.py",
        "verification/python/verification_checks.py",
        "verification/python/verify_e6_extrema.py",
        "verification/python/verify_e6_extrema_r8_fast.py",
        "verification/expected/verify_e6_extrema_output.txt",
        "verification/expected/verify_e6_extrema_r8_output.txt",
        "verification/python/check_closed_subsystems.py",
        "verification/python/check_closed_subsystems_r8.py",
        "verification/expected/check_closed_subsystems_output.txt",
        "verification/expected/check_closed_subsystems_r8_output.txt",
        "verification/python/check_proof_and_kernels.py",
        "verification/expected/check_proof_and_kernels_output.txt",
        "verification/python/check_e6_context_symmetry.py",
        "verification/expected/check_e6_context_symmetry_output.txt",
        "verification/python/check_e6_pair_orderings.py",
        "verification/expected/check_e6_pair_orderings_output.txt",
        "verification/python/check_order_three_gradings.py",
        "verification/expected/check_order_three_gradings_output.txt",
        "verification/python/check_toral_gradings.py",
        "verification/expected/check_toral_gradings_output.txt",
        "verification/python/check_cubic_radical_selection.py",
        "verification/expected/check_cubic_radical_selection_output.txt",
        "verification/python/check_rank_deficient_exceptional.py",
        "verification/expected/check_rank_deficient_exceptional_output.txt",
        "verification/python/make_exceptional_rank_deficient_audit.py",
        "verification/certificates/exceptional_rank_deficient_audit.json",
        "verification/python/check_rank_deficient_classical.py",
        "verification/expected/check_rank_deficient_classical_output.txt",
        "verification/python/make_e6_extrema_certificate.py",
    ]
    hashes = {name: digest(REPO_ROOT / name) for name in file_names}

    cert = {
        "certificate_version": 8,
        "description": "Deterministic certificate for the direct homogeneous census, the exceptional rank-deficient no-go audit, the E6 extremal-intersection theorems, and the complete six-cell color classification.",
        "coordinate_convention": {
            "root_coordinates": "Coefficients in the Bourbaki simple-root basis 1--3--4--5--6, with node 2 attached to node 4.",
            "root_numbering": "One-based lexicographic order on the 72 root-coordinate tuples listed below.",
            "weight_coordinates": "Dynkin labels in the same Bourbaki numbering.",
        },
        "cartan_matrix": [list(row) for row in e6.C],
        "highest_root_coefficients": list(highest),
        "roots": [list(root) for root in roots],
        "simple_reflection_permutations": simple_reflections,
        "finite_object_counts": {
            "roots": 72,
            "weyl_group_order": 51_840,
            "closed_subsystems": closed_census["closed_subsystems"],
            "maximal_proper_closed_subsystems": closed_census["maximal_proper"],
            "maximal_proper_types": closed_census["maximal_types"],
            "D5_orbit": 27,
            "A5_plus_A1_orbit": 36,
            "A2_cubed_orbit": 40,
            "triple_space": 38_880,
        },
        "pairwise_distributions": {
            "D5__A5_plus_A1": [
                {"pairing_nonzero": bool(flag), "intersection_roots": n, "count": count}
                for (flag, n), count in sorted(pairwise_counts["D_A"].items())
            ],
            "D5__A2_cubed": [
                {"intersection_roots": n, "count": count}
                for n, count in sorted(pairwise_counts["D_Theta"].items())
            ],
            "A5_plus_A1__A2_cubed": [
                {"alpha_pair_contained": bool(flag), "intersection_roots": n, "count": count}
                for (flag, n), count in sorted(pairwise_counts["A_Theta"].items())
            ],
        },
        "joint_distribution": [
            {"profile": list(profile), "common_root_count": common, "count": count}
            for (profile, common), count in sorted(cells.items())
        ],
        "common_root_count_distribution": [
            {"common_root_count": common,
             "count": sum(count for (profile, n), count in cells.items() if n == common)}
            for common in sorted({n for _, n in cells})
        ],
        "cell_representatives": rep_records,
        "d_chi": {
            "definition": "sum over unordered non-self-dual pairs {U,U*} of |m_U-m_U*| dim(U)",
            "columns": ["H_DA", "H_DTheta", "H_ATheta"],
            "cells": [
                {
                    "profile": list(profile),
                    "common_root_count": common,
                    "H_DA": values[0],
                    "H_DTheta": values[1],
                    "H_ATheta": values[2],
                }
                for (profile, common), values in sorted(d_chi_cells.items())
            ],
            "unique_15_or_16_parent": "H_DA",
        },
        "intrinsic_pair_selector": intrinsic_selector,
        "color_factor_classification": {
            "cells_with_A2_component": [
                {"profile": [20, 10, 14], "common_root_count": 8, "common_type": "A2+A1"},
                {"profile": [16, 10, 14], "common_root_count": 10, "common_type": "A2+A1+A1"},
            ],
            "all_other_cells_have_only_A1_components": True,
            "equivalent_to_two_extremal_classes": True,
        },
        "context_symmetry": {
            "D_Theta_contexts": 1_080,
            "single_Weyl_orbit": True,
            "context_stabilizer_order": 48,
            "factor_preserving_kernel_order": 24,
            "factor_exchanging_coset_size": 24,
            "common_maximum_fixed": True,
            "pairwise_maximum_root_systems_exchanged": True,
        },
        "extrema": {
            "pairwise": {
                "maximizers": len(pairwise),
                "orbit_size": len(pairwise),
                "stabilizer_order": 12,
                "distinct_common_subsystems": len(pairwise_common),
                "triples_per_common_subsystem": 6,
            },
            "common": {
                "maximizers": len(total),
                "orbit_size": len(total),
                "stabilizer_order": 24,
                "distinct_common_subsystems": len(total_common),
                "triples_per_common_subsystem": 2,
                "triples_per_D_Theta_pair": 2,
                "common_subsystem_independent_of_A_choice": True,
            },
            "nested_pairs": {
                "labelled_ordered_pairs": labelled,
                "distinct_root_subsystem_inclusions": len(inclusions),
            },
        },
        "sha256": hashes,
    }

    out = output if output is not None else CERTIFICATE_DIR / "e6_extrema_certificate.json"
    out.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n")
    print(out.name, digest(out), out.stat().st_size)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    main(args.output)
