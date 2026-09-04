#!/usr/bin/env python3
"""Derive the six full-rank Cartan cubic tests directly from root data.

This verifier does not import the cubic-index table printed in the paper.  For
every irreducible order-three grading found by the Cartan-matrix census, it
constructs the trace cubic on the grade-one weights and contracts it against
coroot bases of every grade-zero simple component.

The finite calculation determines which component restrictions vanish.  The
standard invariant-theory step identifying those vanishing restrictions with
simple ideals in the radical remains part of the manuscript proof.
"""

from __future__ import annotations

from fractions import Fraction

from check_order_three_gradings import (
    CARTAN,
    connected_components_by_nonorthogonality,
    generate_roots,
    matrix_rank,
)
from check_rank_deficient_exceptional import root_inner, symmetrizer
from check_toral_gradings import enumerate_gradings, subsystem_type

from verification_checks import require


TYPE_DIMENSIONS = {
    "A1": 3,
    "A2": 8,
    "A5": 35,
    "A8": 80,
    "E6": 78,
}


def independent_root_basis(
    roots: set[tuple[int, ...]],
) -> list[tuple[int, ...]]:
    """Choose an exact row basis from a finite root component."""
    basis: list[tuple[int, ...]] = []
    rank = 0
    for root in sorted(roots):
        candidate_rank = matrix_rank(basis + [root])
        if candidate_rank > rank:
            basis.append(root)
            rank = candidate_rank
    return basis


def on_simple_coroot(
    root: tuple[int, ...], simple: int, cartan: list[list[int]]
) -> int:
    return sum(root[j] * cartan[j][simple] for j in range(len(cartan)))


def on_root_coroot(
    weight: tuple[int, ...], root: tuple[int, ...], cartan: list[list[int]]
) -> Fraction:
    d = symmetrizer(cartan)
    return (
        2
        * root_inner(weight, root, cartan, d)
        / root_inner(root, root, cartan, d)
    )


def component_contraction(
    grade_one: set[tuple[int, ...]],
    component: set[tuple[int, ...]],
    cartan: list[list[int]],
) -> tuple[bool, tuple[tuple[int, ...], int, int, Fraction] | None]:
    """Test T(beta^vee, h_i, h_j) on exact spanning sets."""
    rank = len(cartan)
    basis = independent_root_basis(component)
    require(len(basis) == matrix_rank(list(component)))
    for beta in basis:
        beta_values = {
            weight: on_root_coroot(weight, beta, cartan)
            for weight in grade_one
        }
        for i in range(rank):
            for j in range(i, rank):
                value = sum(
                    beta_values[weight]
                    * on_simple_coroot(weight, i, cartan)
                    * on_simple_coroot(weight, j, cartan)
                    for weight in grade_one
                )
                if value:
                    return False, (beta, i, j, value)
    return True, None


def candidate_rows(name: str, cartan: list[list[int]]):
    roots = generate_roots(cartan)
    for representative, types, sizes, components in enumerate_gradings(
        name, cartan, 3
    ):
        if sizes[1] != sizes[2] or components != [sizes[1]]:
            continue
        grades = {
            grade: {
                root
                for root in roots
                if sum(
                    root[i] * representative[i] for i in range(len(cartan))
                )
                % 3
                == grade
            }
            for grade in range(3)
        }
        require(subsystem_type(grades[0], cartan) == types)
        yield representative, types, grades


def main() -> None:
    observed = []
    for name, cartan in CARTAN.items():
        for representative, types, grades in candidate_rows(name, cartan):
            components = connected_components_by_nonorthogonality(
                grades[0], cartan
            )
            typed_components = [
                (subsystem_type(component, cartan)[0], component)
                for component in components
            ]
            typed_components.sort(
                key=lambda item: (item[0], tuple(sorted(item[1])))
            )

            cubic_null = []
            witnesses = []
            for component_type, component in typed_components:
                is_zero, witness = component_contraction(
                    grades[1], component, cartan
                )
                if is_zero:
                    cubic_null.append(component_type)
                else:
                    require(witness is not None)
                    witnesses.append((component_type, str(witness[3])))

            null_dimension = sum(TYPE_DIMENSIONS[item] for item in cubic_null)
            row = (
                name,
                types,
                len(grades[1]),
                tuple(cubic_null),
                null_dimension,
            )
            observed.append(row)
            print(
                f"{name}: {'+'.join(types)}; dim(V)={len(grades[1])}; "
                f"Cartan-cubic-null="
                f"{'+'.join(cubic_null) if cubic_null else '0'}; "
                f"nonzero witnesses={witnesses}; grading={representative}"
            )

    expected = {
        ("G2", ("A2",), 3, (), 0),
        ("F4", ("A2", "A2"), 18, (), 0),
        ("E6", ("A2", "A2", "A2"), 27, (), 0),
        ("E7", ("A2", "A5"), 45, (), 0),
        ("E8", ("A8",), 84, (), 0),
        ("E8", ("A2", "E6"), 81, ("E6",), 78),
    }
    require(set(observed) == expected)
    print(
        "PASS: root-derived Cartan trace cubics uniquely retain "
        "E8/(E6+A2)"
    )


if __name__ == "__main__":
    main()
