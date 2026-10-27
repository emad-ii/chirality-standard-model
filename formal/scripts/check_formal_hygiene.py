#!/usr/bin/env python3
"""Guard the public Lean surface and audit its admitted axioms."""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys


REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_FILES = [REPO_ROOT / "CubicAnomaly.lean", *sorted((REPO_ROOT / "CubicAnomaly").rglob("*.lean"))]
FORBIDDEN = re.compile(
    r"\b(?:axiom|extern|implemented_by|sorry|admit|unsafe)\b|"
    r"\bpartial\s+def\b"
)
PUBLIC_THEOREM = re.compile(
    r"\b(?P<modifiers>(?:(?:protected|private|public|noncomputable)\s+)*)"
    r"(?:theorem|lemma)\s+(?P<name>[^\s:({]+)"
)
THEOREM_KEYWORD = re.compile(r"\b(?:theorem|lemma)\b")
SUPPORTED_THEOREM_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
NATIVE_AXIOMS = {"propext", "Lean.ofReduceBool", "Lean.trustCompiler", "Quot.sound"}
KERNEL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_AUDIT = REPO_ROOT / "formal" / "AxiomAudit.lean"
NATIVE_THEOREMS = frozenset(
    {
        'CubicAnomaly.Classification.Exceptional.cartan_cubic_selector',
        'CubicAnomaly.Classification.Exceptional.exceptional_order_two_odd_graphs_connected',
        'CubicAnomaly.Classification.Exceptional.exceptional_toral_census',
        'CubicAnomaly.Classification.Selection.finite_cubic_selection_exists',
        'CubicAnomaly.Classification.Selection.finite_cubic_selection_exists_unique',
        'CubicAnomaly.Classification.Selection.finite_cubic_selection_iff',
        'CubicAnomaly.Classification.Selection.finite_cubic_selection_unique',
        'CubicAnomaly.E6.a2_occurs_exactly_on_two_extremal_cells',
        'CubicAnomaly.E6.common_maximal_multiplicity_valid',
        'CubicAnomaly.E6.context_counts_valid',
        'CubicAnomaly.E6.e6_root_table_valid',
        'CubicAnomaly.E6.extrema_counts_and_bounds_valid',
        'CubicAnomaly.E6.finite_certificate_valid',
        'CubicAnomaly.E6.intrinsic_da_dimension_ordering',
        'CubicAnomaly.E6.intrinsic_da_root_count_ordering',
        'CubicAnomaly.E6.intrinsic_da_root_count_ordering_of_orbit_membership',
        'CubicAnomaly.E6.intrinsic_pair_data_valid',
        'CubicAnomaly.E6.intrinsic_pair_dimensions_of_orbit_membership',
        'CubicAnomaly.E6.intrinsic_pair_signatures',
        'CubicAnomaly.E6.labelled_containments_valid',
        'CubicAnomaly.E6.pairwise_common_multiplicity_valid',
        'CubicAnomaly.E6.six_cell_distribution_valid',
        'CubicAnomaly.E6.six_cell_orbits_classified_valid',
        'CubicAnomaly.E6.six_weyl_orbits_partition_triple_space',
        'CubicAnomaly.E6.subsystem_orbit_sizes_valid',
        'CubicAnomaly.E6.subsystem_orbit_types_and_sizes_valid',
        'CubicAnomaly.E6.triple_space_has_38880_distinct_elements',
        'CubicAnomaly.E6.triple_space_has_38880_elements',
        'CubicAnomaly.E6.triple_universe_orbit_membership',
    }
)
KERNEL_THEOREMS = frozenset(
    {
        'CubicAnomaly.Classification.AllRank.all_rank_structural_reduction',
        'CubicAnomaly.Classification.AllRank.hermitian_half_cubic_radical_membership',
        'CubicAnomaly.Classification.Classical.classical_lattice_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.classical_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.classical_order_three_span_drop',
        'CubicAnomaly.Classification.Classical.classical_root_ternary_bounds',
        'CubicAnomaly.Classification.Classical.classical_zero_grade_lift_zero',
        'CubicAnomaly.Classification.Classical.classical_zero_grade_span_le_ker',
        'CubicAnomaly.Classification.Classical.cubic_coordinate_shift',
        'CubicAnomaly.Classification.Classical.e6_dual_support_arithmetic_gaps',
        'CubicAnomaly.Classification.Classical.lattice_order_three_coordinate_extension',
        'CubicAnomaly.Classification.Classical.oddD_binomial_candidate_not_exhausted',
        'CubicAnomaly.Classification.Classical.oddD_binomial_dimension_lower_bound',
        'CubicAnomaly.Classification.Classical.oddD_dimension_gap_one',
        'CubicAnomaly.Classification.Classical.oddD_dimension_gap_two',
        'CubicAnomaly.Classification.Classical.oddD_exterior_square_not_exhausted_one',
        'CubicAnomaly.Classification.Classical.oddD_exterior_square_not_exhausted_two',
        'CubicAnomaly.Classification.Classical.oddD_ratio_one_lt_two_thirds',
        'CubicAnomaly.Classification.Classical.oddD_ratio_two_lt_one_sixth',
        'CubicAnomaly.Classification.Classical.root_lattice_order_three_coordinate_extension',
        'CubicAnomaly.Classification.Classical.sum_zero_lattice_coordinate_extension',
        'CubicAnomaly.Classification.Classical.typeA_dual_support_cubic',
        'CubicAnomaly.Classification.Classical.typeA_dual_support_cubic_ne_zero',
        'CubicAnomaly.Classification.Classical.typeA_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.typeA_root_lattice_contains_difference',
        'CubicAnomaly.Classification.Classical.typeA_root_lattice_sum_zero',
        'CubicAnomaly.Classification.Classical.typeA_support_cubic_formula',
        'CubicAnomaly.Classification.Classical.typeA_support_cubic_nonzero',
        'CubicAnomaly.Classification.Classical.typeB_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.typeB_root_lattice_contains_doubled',
        'CubicAnomaly.Classification.Classical.typeC_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.typeC_root_lattice_contains_doubled',
        'CubicAnomaly.Classification.Classical.typeD_order_three_rank_drop',
        'CubicAnomaly.Classification.Classical.typeD_root_lattice_contains_doubled',
        'CubicAnomaly.Classification.Classical.typeD_weyl_dimension_one_lower_bound',
        'CubicAnomaly.Classification.Classical.typeD_weyl_dimension_two_lower_bound',
        'CubicAnomaly.Classification.Classical.typeD_weyl_exterior_gap_one',
        'CubicAnomaly.Classification.Classical.typeD_weyl_exterior_gap_two',
        'CubicAnomaly.Classification.Classical.typeD_weyl_ratio_one',
        'CubicAnomaly.Classification.Classical.typeD_weyl_ratio_two',
        'CubicAnomaly.Classification.CompactSimple.ambient_simple_of_compact_complex_complement',
        'CubicAnomaly.Classification.CompactSimple.compact_pair_ambient_simple',
        'CubicAnomaly.Classification.CubicRadical.center_eq_bot_of_irreducible_hermitian_realization',
        'CubicAnomaly.Classification.CubicRadical.center_eq_bot_of_scalar_center_and_nonzero_cubic_radical',
        'CubicAnomaly.Classification.CubicRadical.central_generator_scalar_of_irreducible',
        'CubicAnomaly.Classification.CubicRadical.equivariant_scalar_of_real_eigenvector',
        'CubicAnomaly.Classification.CubicRadical.generator_radical_eq_bot_of_scalar',
        'CubicAnomaly.Classification.CubicRadical.hermitian_scalar_of_irreducible_realization',
        'CubicAnomaly.Classification.CubicRadical.hermitian_trace_square_eq_zero_iff',
        'CubicAnomaly.Classification.CubicRadical.matrix_cubic_radical_trivial_of_scalar',
        'CubicAnomaly.Classification.CubicRadical.matrix_trace_cubic_invariant',
        'CubicAnomaly.Classification.CubicRadical.matrix_trace_cubic_scalar',
        'CubicAnomaly.Classification.CubicRadical.mem_radical_iff',
        'CubicAnomaly.Classification.CubicRadical.no_nonzero_scalar_of_nonzero_matrix_cubic_radical',
        'CubicAnomaly.Classification.CubicRadical.radical_eq_bot_iff',
        'CubicAnomaly.Classification.CubicRadical.scaled_commutator_of_action',
        'CubicAnomaly.Classification.CubicRadical.trace_cubic_form_invariant',
        'CubicAnomaly.Classification.CubicRadical.trace_cubic_form_invariant_of_scaled_commutator',
        'CubicAnomaly.Classification.HermitianRealization.all_rank_structural_reduction_of_commutant',
        'CubicAnomaly.Classification.HermitianRealization.hermitian_half_exists_of_commutant',
        'CubicAnomaly.Classification.RootReduction.bilinear_closed_root_subsystem_saturated',
        'CubicAnomaly.Classification.RootReduction.closed_root_subsystem_saturated',
        'CubicAnomaly.Classification.RootReduction.crystallographic_closed_root_subsystem_saturated',
        'CubicAnomaly.Classification.RootReduction.crystallographic_proper_closed_root_subsystem_lattice_ne',
        'CubicAnomaly.Classification.RootReduction.proper_closed_root_subsystem_lattice_ne',
        'CubicAnomaly.Classification.RootReduction.three_class_noninvolutive_nsmul',
        'CubicAnomaly.Classification.RootReduction.three_class_noninvolutive_order',
        'CubicAnomaly.Classification.Structural.ambient_center_eq_bot_of_complex_complement',
        'CubicAnomaly.Classification.Structural.commutant_complex_structure_square',
        'CubicAnomaly.Classification.Structural.compact_abelian_ideal_le_center',
        'CubicAnomaly.Classification.Structural.compact_complex_centroid_abelian',
        'CubicAnomaly.Classification.Structural.compact_complex_commutant_irreducible',
        'CubicAnomaly.Classification.Structural.compact_orthogonal_complement_isCompl',
        'CubicAnomaly.Classification.Structural.compact_pair_reduction_to_semisimple_ambient',
        'CubicAnomaly.Classification.Structural.compact_semisimple_of_center_eq_bot',
        'CubicAnomaly.Classification.Structural.effective_invariant_complement_faithful',
        'CubicAnomaly.Classification.Structural.intermediate_eq_of_irreducible_complement',
        'CubicAnomaly.Classification.Structural.invariant_complement_projection_equivariant',
        'CubicAnomaly.Classification.Structural.irreducible_of_complex_commutant',
        'CubicAnomaly.Classification.Structural.maximal_of_irreducible_complement',
        'CubicAnomaly.Classification.Structural.no_fixed_vector_of_irreducible_complex_structure',
        'CubicAnomaly.Classification.Structural.quotient_complement_equiv_apply_mk',
    }
)

EXPORTED_THEOREMS = NATIVE_THEOREMS | KERNEL_THEOREMS
EXPORTED_THEOREM_BASENAMES = frozenset(
    qualified.rsplit(".", 1)[-1] for qualified in EXPORTED_THEOREMS
)
AXIOM_TARGET = re.compile(
    r"(?m)^\s*#print\s+axioms\s+([A-Za-z0-9_.']+)\s*$"
)
AXIOM_RECEIPT = re.compile(
    r"'(?P<target>[A-Za-z0-9_.']+)'\s+(?:"
    r"depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"does not depend on any axioms)",
    re.DOTALL,
)


def strip_comments_and_strings(source: str) -> str:
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
            continue
        if in_string:
            if source[index] == "\\" and index + 1 < len(source):
                result.extend("  ")
                index += 2
            elif source[index] == '"':
                in_string = False
                result.append(" ")
                index += 1
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
            continue
        if pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            newline = source.find("\n", index)
            if newline == -1:
                result.extend(" " * (len(source) - index))
                break
            result.extend(" " * (newline - index))
            index = newline
        elif source[index] == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(source[index])
            index += 1
    return "".join(result)


def duplicates(values: list[str]) -> list[str]:
    return sorted(name for name in set(values) if values.count(name) > 1)


def source_theorem_names(cleaned_source: str) -> list[str]:
    """Read all declarations regardless of line layout; reject unsupported names.

    Basenames must remain unique across the project. Lean's named receipts
    independently verify the fully qualified targets in the explicit manifest.
    Comments and strings must have been stripped before calling this function.
    """
    declarations = list(PUBLIC_THEOREM.finditer(cleaned_source))
    if len(declarations) != len(THEOREM_KEYWORD.findall(cleaned_source)):
        raise ValueError("Unrecognized theorem/lemma declaration syntax")
    names: list[str] = []
    for match in declarations:
        name = match.group("name")
        if not SUPPORTED_THEOREM_NAME.fullmatch(name):
            raise ValueError(f"Unsupported theorem identifier for the export audit: {name!r}")
        if "private" not in match.group("modifiers").split():
            names.append(name.rsplit(".", 1)[-1])
    return names


def source_scanner_self_tests() -> int:
    positives = {
        "theorem ordinary : True := by trivial": ["ordinary"],
        "public theorem explicit_public : True := by trivial": ["explicit_public"],
        "omit [Nontrivial M] in theorem same_line : True := by trivial": ["same_line"],
        "@[simp] protected theorem qualified.name : True := by trivial": ["name"],
        "private theorem hidden : True := by trivial": [],
        "private\nlemma hidden : True := by trivial": [],
        "/- public theorem ignored : False -/ theorem real : True := by trivial": ["real"],
        'def s := "theorem ignored : False"\ntheorem actual : True := by trivial': ["actual"],
    }
    for source, expected in positives.items():
        found = source_theorem_names(strip_comments_and_strings(source))
        if found != expected:
            raise AssertionError(f"Incorrect theorem scan: {source!r}: {found}")
    for source in ("theorem α : True := by trivial", "theorem «has space» : True := by trivial",
                   "theorem : True := by trivial"):
        try:
            source_theorem_names(strip_comments_and_strings(source))
        except ValueError:
            continue
        raise AssertionError(f"Scanner silently accepted unsupported syntax: {source!r}")
    print("PASS  export scanner handles modifiers, qualified names and inline declarations")
    return 0


def axiom_manifest_failures(
    theorem_names: list[str], audit_source: str
) -> list[str]:
    failures: list[str] = []

    duplicate_theorems = duplicates(theorem_names)
    if duplicate_theorems:
        failures.append(
            "Exported theorem basenames must be unique for an unambiguous "
            f"axiom manifest: {duplicate_theorems}"
        )

    discovered_basenames = set(theorem_names)
    if discovered_basenames != EXPORTED_THEOREM_BASENAMES:
        failures.append(
            "Discovered public theorem basenames differ from the explicit "
            "exported surface: "
            f"missing={sorted(EXPORTED_THEOREM_BASENAMES - discovered_basenames)}, "
            f"unknown={sorted(discovered_basenames - EXPORTED_THEOREM_BASENAMES)}"
        )

    cleaned_audit = strip_comments_and_strings(audit_source)
    audited_targets = AXIOM_TARGET.findall(cleaned_audit)
    duplicate_targets = duplicates(audited_targets)
    if duplicate_targets:
        failures.append(
            f"Axiom audit contains duplicate fully qualified targets: {duplicate_targets}"
        )

    audited_target_set = set(audited_targets)
    if audited_target_set != EXPORTED_THEOREMS:
        failures.append(
            "Axiom audit targets differ from the explicit fully qualified "
            "exported surface: "
            f"missing={sorted(EXPORTED_THEOREMS - audited_target_set)}, "
            f"unknown={sorted(audited_target_set - EXPORTED_THEOREMS)}"
        )

    return failures


def manifest_self_tests() -> int:
    """Exercise every export, including selector claims, without running Lean."""
    targets = sorted(EXPORTED_THEOREMS)
    names = sorted(EXPORTED_THEOREM_BASENAMES)
    audit_lines = [f"#print axioms {target}" for target in targets]
    audit = "\n".join(audit_lines)
    if axiom_manifest_failures(names, audit):
        raise AssertionError("The complete exported surface must pass")

    negative_cases = 0

    def rejected(label: str, candidate_names: list[str], candidate_audit: str) -> None:
        nonlocal negative_cases
        if not axiom_manifest_failures(candidate_names, candidate_audit):
            raise AssertionError(f"Manifest accepted {label}")
        negative_cases += 1

    for target in targets:
        basename = target.rsplit(".", 1)[-1]
        line = f"#print axioms {target}"

        def replace_target(replacement: str) -> str:
            return "\n".join(replacement if entry == line else entry for entry in audit_lines)

        rejected(f"missing theorem {target}", [name for name in names if name != basename], audit)
        rejected(f"missing receipt {target}", names, replace_target(""))
        rejected(f"wrong namespace {target}", names, replace_target(f"#print axioms Wrong.{basename}"))
        rejected(f"commented receipt {target}", names, replace_target(f"/- {line} -/"))

    rejected("unknown public theorem", names + ["unlisted_selector"], audit)
    rejected("duplicate public theorem", names + [names[0]], audit)
    rejected("unknown receipt", names, audit + "\n#print axioms Wrong.unlisted_selector")
    rejected("duplicate receipt", names, audit + f"\n#print axioms {targets[0]}")
    print(f"PASS  explicit axiom manifest: positive control and {negative_cases} negative self-tests")
    return 0


def axiom_receipt_failures(output: str) -> list[str]:
    """Match every receipt to its named theorem and its declared trust class."""
    failures: list[str] = []
    if NATIVE_THEOREMS & KERNEL_THEOREMS:
        failures.append("A theorem cannot belong to both trust classes")
    receipts = list(AXIOM_RECEIPT.finditer(output))
    targets = [match.group("target") for match in receipts]
    repeated = duplicates(targets)
    if repeated:
        failures.append(f"Duplicate axiom receipts: {repeated}")
    found_targets = set(targets)
    if found_targets != EXPORTED_THEOREMS:
        failures.append(
            "Axiom receipt targets differ from the exported surface: "
            f"missing={sorted(EXPORTED_THEOREMS - found_targets)}, "
            f"unknown={sorted(found_targets - EXPORTED_THEOREMS)}"
        )
    for match in receipts:
        target = match.group("target")
        found = {
            name.strip()
            for name in (match.group("axioms") or "").replace("\n", " ").split(",")
            if name.strip()
        }
        if target in NATIVE_THEOREMS and found != NATIVE_AXIOMS:
            failures.append(
                f"{target}: native-computation receipt differs from the exact set: "
                f"missing={sorted(NATIVE_AXIOMS - found)}, "
                f"unexpected={sorted(found - NATIVE_AXIOMS)}"
            )
        elif target in KERNEL_THEOREMS and not found <= KERNEL_AXIOMS:
            failures.append(
                f"{target}: deductive proof has nonfoundational dependencies: "
                f"{sorted(found - KERNEL_AXIOMS)}"
            )
    return failures


def receipt_self_tests() -> int:
    """Reject missing, mislabeled, duplicate, and over-trusting proof receipts."""
    native = sorted(NATIVE_THEOREMS)
    kernel = sorted(KERNEL_THEOREMS)

    def receipt(target: str, axioms: set[str]) -> str:
        if not axioms:
            return f"'{target}' does not depend on any axioms"
        return f"'{target}' depends on axioms: [{', '.join(sorted(axioms))}]"

    lines = {
        target: receipt(target, NATIVE_AXIOMS if target in NATIVE_THEOREMS else KERNEL_AXIOMS)
        for target in sorted(EXPORTED_THEOREMS)
    }

    def check(label: str, candidate: list[str], expected_failure: bool) -> None:
        failed = bool(axiom_receipt_failures("\n".join(candidate)))
        if failed != expected_failure:
            raise AssertionError(f"Unexpected receipt-audit result for {label}")

    check("complete receipts", list(lines.values()), False)
    check("reordered receipts", list(reversed(list(lines.values()))), False)
    for target in lines:
        check(f"missing {target}", [line for name, line in lines.items() if name != target], True)
    first = next(iter(lines))
    check("duplicate", [*lines.values(), lines[first]], True)
    check("unknown", [*lines.values(), receipt("Wrong.unknown", set())], True)
    changed = dict(lines)
    changed[first] = receipt("Wrong." + first, KERNEL_AXIOMS)
    check("mislabeled", list(changed.values()), True)
    if native:
        changed = dict(lines)
        changed[native[0]] = receipt(native[0], NATIVE_AXIOMS - {"Lean.trustCompiler"})
        check("missing native compiler dependency", list(changed.values()), True)
    if kernel:
        for target in kernel:
            changed = dict(lines)
            changed[target] = receipt(target, set())
            check(f"axiom-free {target}", list(changed.values()), False)
            changed[target] = receipt(target, KERNEL_AXIOMS | {"Lean.trustCompiler"})
            check(f"compiler dependency in {target}", list(changed.values()), True)
            changed[target] = receipt(target, KERNEL_AXIOMS | {"sorryAx"})
            check(f"unfinished proof in {target}", list(changed.values()), True)
    print("PASS  named axiom receipts and separate native/deductive trust classes")
    return 0


def self_tests() -> int:
    source_scanner_self_tests()
    manifest_self_tests()
    return receipt_self_tests()


def main() -> int:
    self_tests()
    failures: list[str] = []
    theorem_names: list[str] = []
    for path in LEAN_FILES:
        cleaned = strip_comments_and_strings(path.read_text())
        try:
            theorem_names.extend(source_theorem_names(cleaned))
        except ValueError as error:
            failures.append(f"{path.relative_to(REPO_ROOT)}: {error}")
        match = FORBIDDEN.search(cleaned)
        if match:
            line = cleaned.count("\n", 0, match.start()) + 1
            failures.append(f"{path.relative_to(REPO_ROOT)}:{line}: forbidden proof escape: {match.group(0).strip()}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1

    failures = axiom_manifest_failures(theorem_names, AXIOM_AUDIT.read_text())
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1

    result = subprocess.run(
        ["lake", "env", "lean", "formal/AxiomAudit.lean"],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode != 0:
        print(result.stdout, file=sys.stderr)
        return result.returncode
    failures = axiom_receipt_failures(result.stdout)
    if failures:
        print("\n".join(failures), file=sys.stderr)
        print(result.stdout, file=sys.stderr)
        return 1
    print(f"PASS  no proof escapes; all {len(theorem_names)} exported theorems audited")
    print(f"PASS  {len(NATIVE_THEOREMS)} exact native-computation receipts: "
          + ", ".join(sorted(NATIVE_AXIOMS)))
    print(f"PASS  {len(KERNEL_THEOREMS)} deductive receipts use only: "
          + ", ".join(sorted(KERNEL_AXIOMS)))
    return 0


if __name__ == "__main__":
    raise SystemExit(self_tests() if sys.argv[1:] == ["--self-test"] else main())
