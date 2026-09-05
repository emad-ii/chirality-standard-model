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
    r"(?m)^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?P<modifiers>(?:(?:protected|private)\s+)*)"
    r"(?:theorem|lemma)\s+(?P<name>[A-Za-z0-9_']+)"
)
ALLOWED_AXIOMS = {"propext", "Lean.ofReduceBool", "Lean.trustCompiler", "Quot.sound"}
AXIOM_AUDIT = REPO_ROOT / "formal" / "AxiomAudit.lean"
EXPORTED_THEOREMS = frozenset(
    {
        "CubicAnomaly.Classification.Exceptional.exceptional_toral_census",
        "CubicAnomaly.Classification.Exceptional.exceptional_order_two_odd_graphs_connected",
        "CubicAnomaly.Classification.Exceptional.cartan_cubic_selector",
        "CubicAnomaly.E6.finite_certificate_valid",
        "CubicAnomaly.E6.e6_root_table_valid",
        "CubicAnomaly.E6.subsystem_orbit_types_and_sizes_valid",
        "CubicAnomaly.E6.subsystem_orbit_sizes_valid",
        "CubicAnomaly.E6.triple_space_has_38880_elements",
        "CubicAnomaly.E6.triple_space_has_38880_distinct_elements",
        "CubicAnomaly.E6.intrinsic_pair_data_valid",
        "CubicAnomaly.E6.intrinsic_pair_signatures",
        "CubicAnomaly.E6.triple_universe_orbit_membership",
        "CubicAnomaly.E6.intrinsic_da_root_count_ordering_of_orbit_membership",
        "CubicAnomaly.E6.intrinsic_pair_dimensions_of_orbit_membership",
        "CubicAnomaly.E6.intrinsic_da_root_count_ordering",
        "CubicAnomaly.E6.intrinsic_da_dimension_ordering",
        "CubicAnomaly.E6.six_cell_distribution_valid",
        "CubicAnomaly.E6.six_weyl_orbits_partition_triple_space",
        "CubicAnomaly.E6.six_cell_orbits_classified_valid",
        "CubicAnomaly.E6.extrema_counts_and_bounds_valid",
        "CubicAnomaly.E6.a2_occurs_exactly_on_two_extremal_cells",
        "CubicAnomaly.E6.pairwise_common_multiplicity_valid",
        "CubicAnomaly.E6.common_maximal_multiplicity_valid",
        "CubicAnomaly.E6.context_counts_valid",
        "CubicAnomaly.E6.labelled_containments_valid",
    }
)
EXPORTED_THEOREM_BASENAMES = frozenset(
    qualified.rsplit(".", 1)[-1] for qualified in EXPORTED_THEOREMS
)
AXIOM_TARGET = re.compile(
    r"(?m)^\s*#print\s+axioms\s+([A-Za-z0-9_.']+)\s*$"
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


def main() -> int:
    manifest_self_tests()
    failures: list[str] = []
    theorem_names: list[str] = []
    for path in LEAN_FILES:
        cleaned = strip_comments_and_strings(path.read_text())
        theorem_names.extend(
            match.group("name")
            for match in PUBLIC_THEOREM.finditer(cleaned)
            if "private" not in match.group("modifiers").split()
        )
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
    receipts = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout, re.DOTALL)
    expected_receipts = len(EXPORTED_THEOREMS)
    if len(receipts) != expected_receipts:
        print(
            f"Could not parse all {expected_receipts} #print axioms receipts.",
            file=sys.stderr,
        )
        print(result.stdout, file=sys.stderr)
        return 1
    for receipt in receipts:
        found = {name.strip() for name in receipt.replace("\n", " ").split(",") if name.strip()}
        if found != ALLOWED_AXIOMS:
            print(
                "Lean axiom receipt differs from the required exact set: "
                f"missing={sorted(ALLOWED_AXIOMS - found)}, "
                f"unexpected={sorted(found - ALLOWED_AXIOMS)}",
                file=sys.stderr,
            )
            return 1
    print(f"PASS  no proof escapes; all {len(theorem_names)} exported theorems audited")
    print("PASS  exact native_decide trust receipt: " + ", ".join(sorted(ALLOWED_AXIOMS)))
    return 0


if __name__ == "__main__":
    raise SystemExit(manifest_self_tests() if sys.argv[1:] == ["--self-test"] else main())
