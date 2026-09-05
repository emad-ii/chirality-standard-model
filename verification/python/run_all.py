#!/usr/bin/env python3
"""Run the mathematical verifiers and compare deterministic artifacts.

The independent programs produce exact expected output and two deterministic
JSON artifacts.  This runner compares those records and checks certificate
arithmetic, source hashes and the generated Lean binding.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

from verification_checks import VerificationFailure as VerificationError, require


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
EXPECTED_DIR = REPO_ROOT / "verification" / "expected"
CERTIFICATE_DIR = REPO_ROOT / "verification" / "certificates"

OUTPUT_CHECKS = (
    ("primary E6 realization", "verify_e6_extrema.py", "verify_e6_extrema_output.txt"),
    ("independent R8 realization", "verify_e6_extrema_r8_fast.py", "verify_e6_extrema_r8_output.txt"),
    ("context symmetry", "check_e6_context_symmetry.py", "check_e6_context_symmetry_output.txt"),
    ("stabilizers and kernels", "check_proof_and_kernels.py", "check_proof_and_kernels_output.txt"),
    ("pair-first d_chi table", "check_e6_pair_orderings.py", "check_e6_pair_orderings_output.txt"),
    ("closed-subsystem census", "check_closed_subsystems.py", "check_closed_subsystems_output.txt"),
    ("independent R8 census", "check_closed_subsystems_r8.py", "check_closed_subsystems_r8_output.txt"),
    ("secondary order-three audit", "check_order_three_gradings.py", "check_order_three_gradings_output.txt"),
    ("direct toral grading census", "check_toral_gradings.py", "check_toral_gradings_output.txt"),
    ("root-derived cubic selector", "check_cubic_radical_selection.py", "check_cubic_radical_selection_output.txt"),
    ("exceptional rank-deficient sieve", "check_rank_deficient_exceptional.py", "check_rank_deficient_exceptional_output.txt"),
    ("classical rank-deficient arithmetic", "check_rank_deficient_classical.py", "check_rank_deficient_classical_output.txt"),
)


def run_python(script: str, *arguments: str, timeout: int) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment["PYTHONHASHSEED"] = "42"
    return subprocess.run(
        [sys.executable, *(["-O"] * sys.flags.optimize), str(SCRIPT_DIR / script), *arguments],
        cwd=SCRIPT_DIR,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )


def require_success(result: subprocess.CompletedProcess[str], label: str) -> None:
    if result.returncode != 0:
        raise VerificationError(
            f"{label} failed with exit code {result.returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def compare_bytes(actual: bytes, expected_path: Path, label: str) -> None:
    expected = expected_path.read_bytes()
    if actual == expected:
        return
    diff = "".join(
        difflib.unified_diff(
            expected.decode(errors="replace").splitlines(keepends=True),
            actual.decode(errors="replace").splitlines(keepends=True),
            fromfile=str(expected_path),
            tofile=f"regenerated:{label}",
        )
    )
    raise VerificationError(f"deterministic output differs for {label}\n{diff}")


def check_output(item: tuple[str, str, str], timeout: int) -> tuple[str, float]:
    label, script, expected_name = item
    started = time.monotonic()
    result = run_python(script, timeout=timeout)
    require_success(result, label)
    compare_bytes(result.stdout.encode(), EXPECTED_DIR / expected_name, label)
    return label, time.monotonic() - started


def check_generated_artifacts(temp_dir: Path, timeout: int) -> list[tuple[str, float]]:
    results: list[tuple[str, float]] = []
    generated = (
        (
            "exceptional audit reproduction",
            "make_exceptional_rank_deficient_audit.py",
            CERTIFICATE_DIR / "exceptional_rank_deficient_audit.json",
        ),
        (
            "E6 certificate reproduction",
            "make_e6_extrema_certificate.py",
            CERTIFICATE_DIR / "e6_extrema_certificate.json",
        ),
    )
    for label, script, expected_path in generated:
        started = time.monotonic()
        output = temp_dir / expected_path.name
        result = run_python(script, "--output", str(output), timeout=timeout)
        require_success(result, label)
        compare_bytes(output.read_bytes(), expected_path, label)
        results.append((label, time.monotonic() - started))
    return results


def check_certificate_digest() -> tuple[str, float]:
    started = time.monotonic()
    certificate = CERTIFICATE_DIR / "e6_extrema_certificate.json"
    digest_file = CERTIFICATE_DIR / "e6_extrema_certificate.sha256"
    fields = digest_file.read_text().strip().split()
    if len(fields) != 2 or fields[1] != certificate.name:
        raise VerificationError(f"malformed digest file: {digest_file}")
    actual = hashlib.sha256(certificate.read_bytes()).hexdigest()
    if actual != fields[0]:
        raise VerificationError(f"certificate digest mismatch: expected {fields[0]}, got {actual}")
    return "certificate SHA-256", time.monotonic() - started


def _certificate_mapping(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise VerificationError(f"certificate field {label} is not an object")
    return value


def _certificate_sequence(value: object, label: str) -> list[object]:
    if not isinstance(value, list):
        raise VerificationError(f"certificate field {label} is not an array")
    return value


def _certificate_integer(value: object, label: str) -> int:
    if type(value) is not int or value < 0:
        raise VerificationError(
            f"certificate field {label} is not a nonnegative integer"
        )
    return value


def _mapping_integer(mapping: dict[str, object], key: str, label: str) -> int:
    if key not in mapping:
        raise VerificationError(f"certificate field {label}.{key} is missing")
    return _certificate_integer(mapping[key], f"{label}.{key}")


def validate_certificate_semantic_contract(certificate: dict[str, object]) -> None:
    """Check summary fields against the independent mathematical verifiers."""
    expected_blocks = {
        "pairwise_distributions": {
            "D5__A5_plus_A1": [
                {"pairing_nonzero": False, "intersection_roots": 16, "count": 540},
                {"pairing_nonzero": True, "intersection_roots": 20, "count": 432},
            ],
            "D5__A2_cubed": [{"intersection_roots": 10, "count": 1_080}],
            "A5_plus_A1__A2_cubed": [
                {"alpha_pair_contained": False, "intersection_roots": 6, "count": 1_080},
                {"alpha_pair_contained": True, "intersection_roots": 14, "count": 360},
            ],
        },
        "d_chi": {
            "definition": (
                "sum over unordered non-self-dual pairs {U,U*} of "
                "|m_U-m_U*| dim(U)"
            ),
            "columns": ["H_DA", "H_DTheta", "H_ATheta"],
            "cells": [
                {"profile": list(profile), "common_root_count": common,
                 "H_DA": da, "H_DTheta": dt, "H_ATheta": at}
                for profile, common, da, dt, at in (
                    ((16, 10, 6), 2, 16, 12, 0),
                    ((16, 10, 6), 6, 16, 12, 0),
                    ((16, 10, 14), 6, 16, 12, 27),
                    ((16, 10, 14), 10, 16, 12, 27),
                    ((20, 10, 6), 4, 15, 12, 0),
                    ((20, 10, 14), 8, 15, 12, 27),
                )
            ],
            "unique_15_or_16_parent": "H_DA",
        },
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
                "maximizers": 4_320, "orbit_size": 4_320, "stabilizer_order": 12,
                "distinct_common_subsystems": 720, "triples_per_common_subsystem": 6,
            },
            "common": {
                "maximizers": 2_160, "orbit_size": 2_160, "stabilizer_order": 24,
                "distinct_common_subsystems": 1_080, "triples_per_common_subsystem": 2,
                "triples_per_D_Theta_pair": 2,
                "common_subsystem_independent_of_A_choice": True,
            },
            "nested_pairs": {
                "labelled_ordered_pairs": 8_640,
                "distinct_root_subsystem_inclusions": 2_160,
            },
        },
    }
    for label, expected in expected_blocks.items():
        actual = _certificate_mapping(certificate.get(label), label)
        require(
            json.dumps(actual, sort_keys=True) == json.dumps(expected, sort_keys=True),
            f"certificate semantic block {label} disagrees with independently tested results",
        )


def validate_certificate_counts(certificate: dict[str, object]) -> None:
    """Cross-check finite counts, distributions, representatives and extrema."""
    finite = _certificate_mapping(certificate.get("finite_object_counts"), "finite_object_counts")
    counts = {key: _mapping_integer(finite, key, "finite_object_counts") for key in (
        "roots", "weyl_group_order", "closed_subsystems", "maximal_proper_closed_subsystems",
        "D5_orbit", "A5_plus_A1_orbit", "A2_cubed_orbit", "triple_space",
    )}
    roots = _certificate_sequence(certificate.get("roots"), "roots")
    require(len(roots) == counts["roots"], "root payload does not match root count")
    d, a, theta = (counts[key] for key in ("D5_orbit", "A5_plus_A1_orbit", "A2_cubed_orbit"))
    require(d * a * theta == counts["triple_space"], "orbit sizes do not generate triple_space")
    maximal = _certificate_mapping(finite.get("maximal_proper_types"), "maximal_proper_types")
    require(maximal == {"D5": d, "A5+A1": a, "A2^3": theta}, "maximal types disagree with orbits")
    require(d + a + theta == counts["maximal_proper_closed_subsystems"], "wrong maximal total")
    highest = _certificate_sequence(certificate.get("highest_root_coefficients"), "highest_root_coefficients")
    for value in highest:
        _certificate_integer(value, "highest_root_coefficients")

    pairwise = _certificate_mapping(certificate.get("pairwise_distributions"), "pairwise_distributions")
    for key, total in (("D5__A5_plus_A1", d * a), ("D5__A2_cubed", d * theta),
                       ("A5_plus_A1__A2_cubed", a * theta)):
        entries = _certificate_sequence(pairwise.get(key), key)
        seen: set[int] = set()
        observed = 0
        for value in entries:
            row = _certificate_mapping(value, key)
            root_count = _mapping_integer(row, "intersection_roots", key)
            require(root_count not in seen, f"duplicate pairwise row in {key}")
            seen.add(root_count)
            observed += _mapping_integer(row, "count", key)
        require(observed == total, f"pairwise distribution {key} has the wrong total")

    def cells(field: str, count_field: str) -> dict[tuple[tuple[int, ...], int], int]:
        result = {}
        for value in _certificate_sequence(certificate.get(field), field):
            row = _certificate_mapping(value, field)
            profile = tuple(_certificate_integer(n, field) for n in
                            _certificate_sequence(row.get("profile"), field))
            require(len(profile) == 3, f"{field} profile must have three entries")
            key = (profile, _mapping_integer(row, "common_root_count", field))
            require(key not in result, f"duplicate {field} cell {key}")
            if field == "cell_representatives":
                root_type = row.get("common_type")
                require(isinstance(root_type, str) and
                        re.fullmatch(r"[A-G][0-9]+(?:\+[A-G][0-9]+)*", root_type),
                        f"invalid representative root type: {root_type}")
            result[key] = _mapping_integer(row, count_field, field)
        return result

    joint = cells("joint_distribution", "count")
    require(len(joint) == 6, "certificate must define six joint cells")
    require(joint == cells("cell_representatives", "cell_count"), "joint cells disagree with representatives")
    require(sum(joint.values()) == counts["triple_space"], "joint counts do not sum to triple_space")
    aggregate: Counter[int] = Counter()
    for (_, common), count in joint.items():
        aggregate[common] += count
    common_rows = []
    for value in _certificate_sequence(
        certificate.get("common_root_count_distribution"), "common_root_count_distribution"
    ):
        row = _certificate_mapping(value, "common_root_count_distribution")
        common_rows.append((_mapping_integer(row, "common_root_count", "common distribution"),
                            _mapping_integer(row, "count", "common distribution")))
    require(common_rows == sorted(aggregate.items()), "common-root multiplicities disagree with joint counts")

    extrema = _certificate_mapping(certificate.get("extrema"), "extrema")
    contexts = _certificate_mapping(certificate.get("context_symmetry"), "context_symmetry")
    context_count = _mapping_integer(contexts, "D_Theta_contexts", "context_symmetry")
    require(context_count > 0, "context count must be positive")
    choices = []
    for label in ("pairwise", "common"):
        row = _certificate_mapping(extrema.get(label), f"extrema.{label}")
        values = {key: _mapping_integer(row, key, label) for key in (
            "maximizers", "orbit_size", "stabilizer_order",
            "distinct_common_subsystems", "triples_per_common_subsystem",
        )}
        require(values["orbit_size"] == values["maximizers"], f"{label} extremum is not a single orbit")
        require(values["stabilizer_order"] * values["maximizers"] == counts["weyl_group_order"],
                f"{label} orbit/stabilizer data are inconsistent")
        require(values["distinct_common_subsystems"] * values["triples_per_common_subsystem"]
                == values["maximizers"], f"{label} common-subsystem multiplicity is inconsistent")
        quotient, remainder = divmod(values["maximizers"], context_count)
        require(remainder == 0, f"{label} extremal triples do not divide evenly among contexts")
        choices.append(quotient)
    nested = _certificate_mapping(extrema.get("nested_pairs"), "extrema.nested_pairs")
    require(_mapping_integer(nested, "labelled_ordered_pairs", "extrema.nested_pairs")
            == context_count * choices[0] * choices[1], "labelled inclusion count is inconsistent")


def validate_certificate_source_hashes(certificate: dict[str, object]) -> None:
    """Recompute every source/fixture hash published by the certificate."""

    hashes = _certificate_mapping(certificate.get("sha256"), "sha256")
    expected_paths = {
        "verification/python/run_all.py",
        "verification/python/verification_checks.py",
        "verification/python/make_e6_extrema_certificate.py",
        "verification/python/make_exceptional_rank_deficient_audit.py",
        "verification/certificates/exceptional_rank_deficient_audit.json",
    }
    for _, script, fixture in OUTPUT_CHECKS:
        expected_paths.add(f"verification/python/{script}")
        expected_paths.add(f"verification/expected/{fixture}")

    actual_paths = set(hashes)
    if actual_paths != expected_paths:
        raise VerificationError(
            "certificate source-hash inventory differs from the mathematical inputs: "
            f"missing={sorted(expected_paths - actual_paths)}, "
            f"extra={sorted(actual_paths - expected_paths)}"
        )

    repository_root = REPO_ROOT.resolve()
    for relative_name in sorted(expected_paths):
        relative = Path(relative_name)
        if relative.is_absolute() or ".." in relative.parts:
            raise VerificationError(
                f"certificate source hash has unsafe path: {relative_name}"
            )
        source = REPO_ROOT / relative
        if source.is_symlink() or not source.is_file():
            raise VerificationError(
                f"certificate source hash does not name a regular file: {relative_name}"
            )
        resolved = source.resolve()
        if repository_root not in resolved.parents:
            raise VerificationError(
                f"certificate source hash escapes the repository: {relative_name}"
            )
        recorded = hashes[relative_name]
        if not isinstance(recorded, str) or not re.fullmatch(r"[0-9a-f]{64}", recorded):
            raise VerificationError(
                f"certificate source hash is malformed for {relative_name}"
            )
        live = hashlib.sha256(source.read_bytes()).hexdigest()
        if recorded != live:
            raise VerificationError(
                f"certificate source hash is stale for {relative_name}: "
                f"expected {live}, got {recorded}"
            )


def validate_generated_lean_binding(
    generated_data: str, certificate: dict[str, object], digest: str
) -> None:
    """Bind the generated Lean module to the exact JSON bytes and schema."""
    required_markers = (
        f"SHA-256: {digest}",
        f'def certificateSha256 : String := "{digest}"',
        f'def certificateVersion : Nat := {certificate["certificate_version"]}',
    )
    if any(marker not in generated_data for marker in required_markers):
        raise VerificationError(
            "generated Lean data does not identify the committed certificate "
            "bytes and schema"
        )


def check_certificate_consistency() -> tuple[str, float]:
    """Check mathematical summaries, source hashes and the generated Lean binding."""
    started = time.monotonic()
    certificate_path = CERTIFICATE_DIR / "e6_extrema_certificate.json"
    certificate = _certificate_mapping(json.loads(certificate_path.read_text()), "root")
    require(certificate.get("certificate_version") == 8, "unexpected E6 certificate schema version")
    validate_certificate_semantic_contract(certificate)
    validate_certificate_counts(certificate)
    validate_certificate_source_hashes(certificate)
    generated_data = (REPO_ROOT / "CubicAnomaly" / "E6" / "Data.lean").read_text()
    digest = hashlib.sha256(certificate_path.read_bytes()).hexdigest()
    validate_generated_lean_binding(generated_data, certificate, digest)
    return "certificate consistency", time.monotonic() - started


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2, help="parallel verifier processes (default: 2)")
    parser.add_argument("--timeout", type=int, default=1800, help="seconds allowed per verifier")
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout < 1:
        parser.error("--jobs and --timeout must be positive")

    started = time.monotonic()
    completed: list[tuple[str, float]] = []
    try:
        with tempfile.TemporaryDirectory(prefix="cubic-anomaly-verification-") as temporary:
            completed.extend(check_generated_artifacts(Path(temporary), args.timeout))
        completed.append(check_certificate_digest())
        completed.append(check_certificate_consistency())
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = [executor.submit(check_output, item, args.timeout) for item in OUTPUT_CHECKS]
            results = {}
            for future in as_completed(futures):
                label, seconds = future.result()
                results[label] = (label, seconds)
        completed.extend(results[label] for label, _, _ in OUTPUT_CHECKS)
    except (VerificationError, subprocess.TimeoutExpired, OSError, ValueError) as error:
        print(f"FAILED: {error}", file=sys.stderr)
        return 1

    for label, seconds in completed:
        print(f"PASS  {label:<41} {seconds:7.2f}s")
    print(f"PASS  all {len(completed)} mathematical checks{'':<17} {time.monotonic() - started:7.2f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
