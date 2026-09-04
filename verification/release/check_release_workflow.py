#!/usr/bin/env python3
"""Validate and execute-test the fail-closed release-ref workflow contract.

This checker deliberately protects two small security-sensitive workflow jobs with
an exact-shape contract. It is not a general YAML or shell-program analyser. The
extracted identity script is also run against disposable local Git repositories so
the checked text has executable evidence for its intended ref semantics.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github" / "workflows" / "ci.yml"

EXPECTED_HEADER = """\
name: Release CI

on:
  push:
    branches:
      - main
      - "release-v*"
    tags: ["v*"]
  pull_request:
  workflow_dispatch:

permissions:
  contents: read

concurrency:
  group: release-ci-${{ github.ref }}
  cancel-in-progress: true

jobs:
"""

EXPECTED_IDENTITY_SCRIPT = """\
set -euo pipefail

if [[ "$EVENT_NAME" != push && "$EVENT_NAME" != workflow_dispatch ]]; then
  echo "::error::Unsupported release-evidence event: $EVENT_NAME"
  exit 1
fi

main_ref="refs/heads/${MAIN_BRANCH}"
tag_ref="refs/tags/${RELEASE_TAG}"
launcher_ref="refs/heads/${RELEASE_BRANCH}"

case "$EVENT_REF" in
  "$main_ref"|"$tag_ref"|"$launcher_ref")
    ;;
  *)
    echo "::error::Release evidence must be triggered from main, v0.1.0, or release-v0.1.0"
    exit 1
    ;;
esac

git fetch \\
  --no-tags \\
  --no-recurse-submodules \\
  --depth=1 \\
  origin \\
  "+${main_ref}:refs/release-integrity/main" \\
  "+${tag_ref}:refs/release-integrity/tag" \\
  "+${launcher_ref}:refs/release-integrity/launcher"

tag_type="$(git cat-file -t refs/release-integrity/tag)"
if [[ "$tag_type" != tag ]]; then
  echo "::error::v0.1.0 must be an annotated tag; found object type: $tag_type"
  exit 1
fi

head_commit="$(git rev-parse --verify --end-of-options 'HEAD^{commit}')"
event_commit="$(git rev-parse --verify --end-of-options "${EVENT_SHA}^{commit}")"
main_commit="$(git rev-parse --verify --end-of-options 'refs/release-integrity/main^{commit}')"
tag_commit="$(git rev-parse --verify --end-of-options 'refs/release-integrity/tag^{commit}')"
launcher_commit="$(git rev-parse --verify --end-of-options 'refs/release-integrity/launcher^{commit}')"

if [[ "$head_commit" != "$event_commit" ]]; then
  echo "::error::Checked-out HEAD does not match the triggering event SHA"
  exit 1
fi

if [[ "$head_commit" != "$tag_commit" ]]; then
  echo "::error::Triggering ref and canonical tag resolve to different commits"
  echo "trigger: $head_commit"
  echo "tag:     $tag_commit"
  exit 1
fi

if [[ "$main_commit" != "$tag_commit" || "$main_commit" != "$launcher_commit" ]]; then
  echo "::error::main, v0.1.0, and release-v0.1.0 do not resolve to one commit"
  echo "main:     $main_commit"
  echo "tag:      $tag_commit"
  echo "launcher: $launcher_commit"
  exit 1
fi

if [[ "$event_commit" != "$main_commit" ]]; then
  echo "::error::Triggering run is not executing the canonical release commit"
  echo "event:     $event_commit"
  echo "canonical: $main_commit"
  exit 1
fi

printf 'canonical_commit=%s\\n' "$main_commit" >> "$GITHUB_OUTPUT"
echo "Exact release identity verified: $main_commit"
"""

EXPECTED_IDENTITY_JOB = (
    """\
  release-ref-integrity:
    name: Exact three-way release identity
    if: github.event_name != 'pull_request'
    runs-on: ubuntu-24.04
    timeout-minutes: 5
    outputs:
      canonical_commit: ${{ steps.compare.outputs.canonical_commit }}
    steps:
      - name: Check out triggering commit
        uses: actions/checkout@d23441a48e516b6c34aea4fa41551a30e30af803 # v6.1.0
        with:
          fetch-depth: 1
          ref: ${{ github.sha }}
      - name: Compare main, annotated tag, and release launcher
        id: compare
        shell: bash
        env:
          EVENT_NAME: ${{ github.event_name }}
          EVENT_REF: ${{ github.ref }}
          EVENT_SHA: ${{ github.sha }}
          MAIN_BRANCH: main
          RELEASE_TAG: v0.1.0
          RELEASE_BRANCH: release-v0.1.0
        run: |
"""
    + textwrap.indent(EXPECTED_IDENTITY_SCRIPT.rstrip("\n"), "          ")
)

EXPECTED_NOTEBOOK_JOB = """\
  notebook:
    name: Executable notebook
    needs: [release-ref-integrity]
    if: >-
      always() &&
      (github.event_name == 'pull_request' ||
       needs.release-ref-integrity.result == 'success')
    runs-on: ubuntu-24.04
    timeout-minutes: 30
    steps:
      - name: Check out repository
        uses: actions/checkout@d23441a48e516b6c34aea4fa41551a30e30af803 # v6.1.0
      - name: Set up Python
        uses: actions/setup-python@ece7cb06caefa5fff74198d8649806c4678c61a1 # v6.3.0
        with:
          python-version: "3.12"
          cache: pip
          cache-dependency-path: requirements-notebook.txt
      - name: Install notebook runtime
        run: python -m pip install -r requirements-notebook.txt
      - name: Stress-test notebook provenance guards
        run: |
          python notebooks/check_notebook_freshness.py --self-test
          PYTHONOPTIMIZE=1 python notebooks/check_notebook_freshness.py --self-test
      - name: Check canonical notebook source matches its builder
        run: >-
          python notebooks/check_notebook_freshness.py
          --source-only
          --notebook Cubic_Anomaly_Master_Verification.ipynb
      - name: Execute notebook in a clean kernel
        env:
          EXPECTED_COMMIT_SHA: ${{ github.sha }}
          EXPECTED_CANONICAL_TAG_COMMIT: ${{ needs.release-ref-integrity.outputs.canonical_commit }}
        run: |
          mkdir -p build/notebook
          python -m jupyter nbconvert \\
            --execute --to notebook \\
            --output Cubic_Anomaly_Master_Verification.executed \\
            --output-dir build/notebook \\
            --ExecutePreprocessor.timeout=1200 \\
            Cubic_Anomaly_Master_Verification.ipynb
      - name: Fully validate executed notebook
        env:
          EXPECTED_COMMIT_SHA: ${{ github.sha }}
          EXPECTED_CANONICAL_TAG_COMMIT: ${{ needs.release-ref-integrity.outputs.canonical_commit }}
        run: |
          args=(
            --notebook build/notebook/Cubic_Anomaly_Master_Verification.executed.ipynb
            --require-verified-provenance
            --expected-commit-sha "$EXPECTED_COMMIT_SHA"
          )
          if [[ "$GITHUB_EVENT_NAME" != pull_request ]]; then
            test -n "$EXPECTED_CANONICAL_TAG_COMMIT"
            args+=(
              --require-canonical-release-provenance
              --expected-canonical-release-sha "$EXPECTED_CANONICAL_TAG_COMMIT"
            )
          fi
          python notebooks/check_notebook_freshness.py "${args[@]}"
      - name: Upload executed notebook
        if: always()
        uses: actions/upload-artifact@b7c566a772e6b6bfb58ed0dc250532a479d7789f # v6.0.0
        with:
          name: executed-verification-notebook
          if-no-files-found: warn
          path: build/notebook/Cubic_Anomaly_Master_Verification.executed.ipynb"""

EXPECTED_GATE_SCRIPT = """\
set -euo pipefail
if [[ "$GITHUB_EVENT_NAME" == pull_request ]]; then
  test "$REF_RESULT" = skipped
else
  test "$REF_RESULT" = success
fi
test "$PYTHON_RESULT" = success
test "$NOTEBOOK_RESULT" = success
test "$LEAN_RESULT" = success
test "$PAPER_RESULT" = success
"""

EXPECTED_GATE_JOB = (
    """\
  release-gate:
    name: Release gate
    if: always()
    needs: [release-ref-integrity, python-verification, notebook, lean, paper]
    runs-on: ubuntu-24.04
    steps:
      - name: Require every verification lane
        shell: bash
        env:
          REF_RESULT: ${{ needs.release-ref-integrity.result }}
          PYTHON_RESULT: ${{ needs.python-verification.result }}
          NOTEBOOK_RESULT: ${{ needs.notebook.result }}
          LEAN_RESULT: ${{ needs.lean.result }}
          PAPER_RESULT: ${{ needs.paper.result }}
        run: |
"""
    + textwrap.indent(EXPECTED_GATE_SCRIPT.rstrip("\n"), "          ")
)

EXPECTED_SELF_TEST_STEP = """\
      - name: Stress-test the release-workflow contract
        run: |
          python verification/release/check_release_workflow.py --self-test
          PYTHONOPTIMIZE=1 python verification/release/check_release_workflow.py --self-test"""

JOB_KEY = re.compile(r"^  ([A-Za-z0-9_-]+):$")
STEP_START = re.compile(r"^      - (?:name:|uses:|run:|shell:)")


class ContractError(RuntimeError):
    """Raised when the hosted release-ref contract is weakened or ambiguous."""


def _job_bounds(source: str, name: str) -> tuple[int, int]:
    lines = source.splitlines(keepends=True)
    key = f"  {name}:"
    starts = [i for i, line in enumerate(lines) if line.rstrip("\r\n") == key]
    if len(starts) != 1:
        raise ContractError(f"expected exactly one {name!r} job, found {len(starts)}")
    start = starts[0]
    end = len(lines)
    for index in range(start + 1, len(lines)):
        if JOB_KEY.fullmatch(lines[index].rstrip("\r\n")):
            end = index
            break
    return start, end


def _extract_job(source: str, name: str) -> str:
    lines = source.splitlines(keepends=True)
    start, end = _job_bounds(source, name)
    return "".join(lines[start:end]).rstrip("\r\n")


def _replace_job(source: str, name: str, replacement: str) -> str:
    lines = source.splitlines(keepends=True)
    start, end = _job_bounds(source, name)
    suffix = "\n" if end < len(lines) or source.endswith("\n") else ""
    return (
        "".join(lines[:start])
        + replacement.rstrip("\r\n")
        + suffix
        + "".join(lines[end:])
    )


def _extract_steps(job: str) -> list[str]:
    lines = job.splitlines(keepends=True)
    starts = [
        i for i, line in enumerate(lines) if STEP_START.match(line.rstrip("\r\n"))
    ]
    steps = []
    for position, start in enumerate(starts):
        end = starts[position + 1] if position + 1 < len(starts) else len(lines)
        steps.append("".join(lines[start:end]).rstrip("\r\n"))
    return steps


def _extract_identity_script(identity_job: str) -> str:
    marker = "        run: |\n"
    if identity_job.count(marker) != 1:
        raise ContractError("identity job must contain exactly one literal run block")
    indented = identity_job.split(marker, 1)[1]
    script_lines = []
    for line in indented.splitlines():
        if line and not line.startswith("          "):
            raise ContractError("identity run block has an unexpected indentation boundary")
        script_lines.append(line[10:] if line else "")
    return "\n".join(script_lines) + "\n"


def _first_difference(actual: str, expected: str) -> str:
    actual_lines = actual.splitlines()
    expected_lines = expected.splitlines()
    for index in range(max(len(actual_lines), len(expected_lines))):
        got = actual_lines[index] if index < len(actual_lines) else "<missing>"
        want = expected_lines[index] if index < len(expected_lines) else "<end>"
        if got != want:
            return f"line {index + 1}: expected {want!r}, found {got!r}"
    return "unknown byte-level difference"


def validate(source: str) -> None:
    """Enforce the exact protected jobs and their only trusted invocation."""

    failures = []
    if not source.startswith(EXPECTED_HEADER):
        failures.append("workflow header/triggers/permissions differ from the protected form")

    try:
        identity_job = _extract_job(source, "release-ref-integrity")
        if identity_job != EXPECTED_IDENTITY_JOB:
            failures.append(
                "release-ref-integrity differs from the protected form ("
                + _first_difference(identity_job, EXPECTED_IDENTITY_JOB)
                + ")"
            )
        notebook_job = _extract_job(source, "notebook")
        if notebook_job != EXPECTED_NOTEBOOK_JOB:
            failures.append(
                "notebook differs from the protected provenance form ("
                + _first_difference(notebook_job, EXPECTED_NOTEBOOK_JOB)
                + ")"
            )
        gate_job = _extract_job(source, "release-gate")
        if gate_job != EXPECTED_GATE_JOB:
            failures.append(
                "release-gate differs from the protected form ("
                + _first_difference(gate_job, EXPECTED_GATE_JOB)
                + ")"
            )
        python_job = _extract_job(source, "python-verification")
        self_test_steps = [
            step for step in _extract_steps(python_job) if step == EXPECTED_SELF_TEST_STEP
        ]
        if len(self_test_steps) != 1:
            failures.append(
                "python-verification must contain exactly one unmodified "
                "workflow-checker self-test step"
            )
    except ContractError as error:
        failures.append(str(error))

    if "continue-on-error" in source:
        failures.append("continue-on-error is forbidden in the release workflow")
    if failures:
        raise ContractError("; ".join(failures))


def _replace_exact_once(source: str, old: str, new: str, label: str) -> str:
    count = source.count(old)
    if count != 1:
        raise ContractError(
            f"mutation fixture {label!r} expected one target, found {count}"
        )
    return source.replace(old, new, 1)


def _identity_mutation(source: str, label: str, old: str, new: str) -> str:
    job = _extract_job(source, "release-ref-integrity")
    mutated_job = _replace_exact_once(job, old, new, label)
    return _replace_job(source, "release-ref-integrity", mutated_job)


def _notebook_mutation(source: str, label: str, old: str, new: str) -> str:
    job = _extract_job(source, "notebook")
    mutated_job = _replace_exact_once(job, old, new, label)
    return _replace_job(source, "notebook", mutated_job)


def _semantic_mutations(source: str) -> dict[str, str]:
    """Return release-identity and notebook-provenance weakening fixtures."""

    return {
        "early successful exit": _identity_mutation(
            source,
            "early successful exit",
            "          set -euo pipefail\n\n          if [[",
            "          set -euo pipefail\n          exit 0\n\n          if [[",
        ),
        "neutralized failure exit": _identity_mutation(
            source,
            "neutralized failure exit",
            '            echo "::error::Unsupported release-evidence event: $EVENT_NAME"\n            exit 1',
            '            echo "::error::Unsupported release-evidence event: $EVENT_NAME"\n            true',
        ),
        "forged annotated-tag type": _identity_mutation(
            source,
            "forged annotated-tag type",
            '          tag_type="$(git cat-file -t refs/release-integrity/tag)"',
            "          tag_type=tag",
        ),
        "main ref rebound to tag": _identity_mutation(
            source,
            "main ref rebound to tag",
            '          launcher_ref="refs/heads/${RELEASE_BRANCH}"\n\n          case',
            '          launcher_ref="refs/heads/${RELEASE_BRANCH}"\n          main_ref="$tag_ref"\n\n          case',
        ),
        "collapsed commit variables": _identity_mutation(
            source,
            "collapsed commit variables",
            """          main_commit="$(git rev-parse --verify --end-of-options 'refs/release-integrity/main^{commit}')"
          tag_commit="$(git rev-parse --verify --end-of-options 'refs/release-integrity/tag^{commit}')"
          launcher_commit="$(git rev-parse --verify --end-of-options 'refs/release-integrity/launcher^{commit}')""",
            """          main_commit="$head_commit"
          tag_commit="$head_commit"
          launcher_commit="$head_commit""",
        ),
        "comment decoy with disabled check": _identity_mutation(
            source,
            "comment decoy with disabled check",
            '          if [[ "$tag_type" != tag ]]; then',
            '          # if [[ "$tag_type" != tag ]]; then\n          if false; then',
        ),
        "identity job continue-on-error": _identity_mutation(
            source,
            "identity job continue-on-error",
            "    timeout-minutes: 5\n    outputs:",
            "    timeout-minutes: 5\n    continue-on-error: true\n    outputs:",
        ),
        "notebook detached from identity job": _notebook_mutation(
            source,
            "notebook detached from identity job",
            "    needs: [release-ref-integrity]\n    if: >-",
            "    needs: []\n    if: >-",
        ),
        "canonical identity receipt removed from execution": _notebook_mutation(
            source,
            "canonical identity receipt removed from execution",
            """      - name: Execute notebook in a clean kernel
        env:
          EXPECTED_COMMIT_SHA: ${{ github.sha }}
          EXPECTED_CANONICAL_TAG_COMMIT: ${{ needs.release-ref-integrity.outputs.canonical_commit }}""",
            '''      - name: Execute notebook in a clean kernel
        env:
          EXPECTED_COMMIT_SHA: ${{ github.sha }}
          EXPECTED_CANONICAL_TAG_COMMIT: ""''',
        ),
        "canonical release validation disabled": _notebook_mutation(
            source,
            "canonical release validation disabled",
            """              --require-canonical-release-provenance
              --expected-canonical-release-sha""",
            """              --expected-canonical-release-sha""",
        ),
    }


def mutation_test(source: str) -> None:
    """Require rejection of every previously accepted semantic weakening."""

    validate(source)
    accepted = []
    mutations = _semantic_mutations(source)
    for label, mutated in mutations.items():
        if mutated == source:
            raise ContractError(f"mutation fixture {label!r} made no change")
        try:
            validate(mutated)
        except ContractError:
            continue
        accepted.append(label)
    if accepted:
        raise ContractError("validator accepted semantic mutations: " + ", ".join(accepted))


def _run(
    command: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    check: bool = True,
    timeout: int = 30,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        command,
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    if check and result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise ContractError(f"command failed: {' '.join(command)}: {detail}")
    return result


def _git(cwd: Path, *arguments: str) -> str:
    # Disposable fixtures must not invoke a contributor's signer or hooks.
    return _run([
        "git", "-c", "commit.gpgSign=false", "-c", "tag.gpgSign=false",
        "-c", "core.hooksPath=/dev/null", "-c", "init.templateDir=",
        *arguments,
    ], cwd=cwd).stdout.strip()


@dataclass(frozen=True)
class GitFixture:
    remote: Path
    commit_a: str
    commit_b: str
    tag_a: str
    tag_b: str


def _build_git_fixture(root: Path) -> GitFixture:
    remote = root / "remote.git"
    seed = root / "seed"
    remote.mkdir()
    seed.mkdir()
    _git(remote, "init", "--bare", "--quiet")
    _git(seed, "init", "--quiet")
    _git(seed, "config", "user.name", "Release Contract Test")
    _git(seed, "config", "user.email", "release-contract@example.invalid")
    # Exercise signing isolation even when the caller has no signing defaults.
    _git(seed, "config", "commit.gpgSign", "true")
    _git(seed, "config", "tag.gpgSign", "true")
    _git(seed, "config", "gpg.program", str(seed / "missing-test-signer"))

    payload = seed / "payload.txt"
    payload.write_text("commit A\n", encoding="utf-8")
    _git(seed, "add", "payload.txt")
    _git(seed, "commit", "--quiet", "-m", "fixture A")
    commit_a = _git(seed, "rev-parse", "HEAD")
    payload.write_text("commit B\n", encoding="utf-8")
    _git(seed, "commit", "--quiet", "-am", "fixture B")
    commit_b = _git(seed, "rev-parse", "HEAD")

    _git(seed, "tag", "-a", "fixture-a", commit_a, "-m", "fixture A tag")
    _git(seed, "tag", "-a", "fixture-b", commit_b, "-m", "fixture B tag")
    tag_a = _git(seed, "rev-parse", "refs/tags/fixture-a")
    tag_b = _git(seed, "rev-parse", "refs/tags/fixture-b")
    _git(seed, "remote", "add", "origin", str(remote))
    _git(
        seed,
        "push",
        "--quiet",
        "origin",
        f"{commit_a}:refs/heads/fixture-a",
        f"{commit_b}:refs/heads/fixture-b",
        "refs/tags/fixture-a",
        "refs/tags/fixture-b",
    )
    return GitFixture(remote, commit_a, commit_b, tag_a, tag_b)


def _set_ref(remote: Path, ref: str, target: str | None) -> None:
    if target is None:
        _git(remote, "update-ref", "-d", ref)
    else:
        _git(remote, "update-ref", ref, target)


@dataclass(frozen=True)
class Scenario:
    name: str
    main: str | None = "a"
    tag: str | None = "a"
    launcher: str | None = "a"
    lightweight_tag: bool = False
    event_name: str = "push"
    event_ref: str = "refs/heads/main"
    event_commit: str = "a"
    head_commit: str | None = None
    should_pass: bool = False


def _commit(fixture: GitFixture, label: str) -> str:
    if label == "a":
        return fixture.commit_a
    if label == "b":
        return fixture.commit_b
    raise ContractError(f"unknown fixture commit label: {label}")


def _configure_scenario(fixture: GitFixture, scenario: Scenario) -> None:
    main_target = _commit(fixture, scenario.main) if scenario.main else None
    launcher_target = _commit(fixture, scenario.launcher) if scenario.launcher else None
    if scenario.tag is None:
        tag_target = None
    elif scenario.lightweight_tag:
        tag_target = _commit(fixture, scenario.tag)
    else:
        tag_target = fixture.tag_a if scenario.tag == "a" else fixture.tag_b
    _set_ref(fixture.remote, "refs/heads/main", main_target)
    _set_ref(fixture.remote, "refs/tags/v0.1.0", tag_target)
    _set_ref(fixture.remote, "refs/heads/release-v0.1.0", launcher_target)


def _run_scenario(
    fixture: GitFixture, script: str, scenario: Scenario, root: Path
) -> tuple[subprocess.CompletedProcess[str], Path]:
    _configure_scenario(fixture, scenario)
    runner = root / f"runner-{scenario.name}"
    runner.mkdir()
    _git(runner, "init", "--quiet")
    _git(runner, "remote", "add", "origin", str(fixture.remote))
    _git(
        runner,
        "fetch",
        "--quiet",
        "--no-tags",
        "origin",
        "+refs/heads/fixture-a:refs/remotes/origin/fixture-a",
        "+refs/heads/fixture-b:refs/remotes/origin/fixture-b",
    )
    event_commit = _commit(fixture, scenario.event_commit)
    head_commit = _commit(fixture, scenario.head_commit or scenario.event_commit)
    _git(runner, "checkout", "--quiet", "--detach", head_commit)
    output_path = runner / "github-output.txt"
    environment = os.environ.copy()
    environment.update(
        {
            "EVENT_NAME": scenario.event_name,
            "EVENT_REF": scenario.event_ref,
            "EVENT_SHA": event_commit,
            "MAIN_BRANCH": "main",
            "RELEASE_TAG": "v0.1.0",
            "RELEASE_BRANCH": "release-v0.1.0",
            "GIT_TERMINAL_PROMPT": "0",
            "GITHUB_OUTPUT": str(output_path),
        }
    )
    result = _run(
        ["bash", "-c", script],
        cwd=runner,
        env=environment,
        check=False,
        timeout=30,
    )
    return result, output_path


def executable_scenario_test(source: str) -> None:
    """Execute the protected shell against positive and negative Git states."""

    validate(source)
    script = _extract_identity_script(_extract_job(source, "release-ref-integrity"))
    if script != EXPECTED_IDENTITY_SCRIPT:
        raise ContractError("extracted identity script differs from the executable contract")

    scenarios = [
        Scenario("aligned-push-main", event_ref="refs/heads/main", should_pass=True),
        Scenario("aligned-push-tag", event_ref="refs/tags/v0.1.0", should_pass=True),
        Scenario(
            "aligned-push-launcher",
            event_ref="refs/heads/release-v0.1.0",
            should_pass=True,
        ),
        Scenario(
            "aligned-dispatch-main",
            event_name="workflow_dispatch",
            event_ref="refs/heads/main",
            should_pass=True,
        ),
        Scenario(
            "aligned-dispatch-tag",
            event_name="workflow_dispatch",
            event_ref="refs/tags/v0.1.0",
            should_pass=True,
        ),
        Scenario(
            "aligned-dispatch-launcher",
            event_name="workflow_dispatch",
            event_ref="refs/heads/release-v0.1.0",
            should_pass=True,
        ),
        Scenario(
            "divergent-main",
            main="b",
            event_ref="refs/tags/v0.1.0",
        ),
        Scenario("divergent-tag", tag="b"),
        Scenario("divergent-launcher", launcher="b"),
        Scenario("lightweight-tag", lightweight_tag=True),
        Scenario("missing-main", main=None),
        Scenario("missing-tag", tag=None),
        Scenario("missing-launcher", launcher=None),
        Scenario(
            "stale-event-sha",
            main="b",
            tag="b",
            launcher="b",
            event_commit="a",
        ),
        Scenario("head-event-mismatch", head_commit="b"),
        Scenario("unsupported-ref", event_ref="refs/heads/other"),
        Scenario("unsupported-event", event_name="schedule"),
    ]

    failures = []
    with tempfile.TemporaryDirectory(prefix="release-workflow-contract-") as temporary:
        temporary_root = Path(temporary)
        fixture = _build_git_fixture(temporary_root)
        for scenario in scenarios:
            result, output_path = _run_scenario(
                fixture, script, scenario, temporary_root
            )
            passed = result.returncode == 0
            if passed != scenario.should_pass:
                output = (result.stdout + result.stderr).strip().replace("\n", " | ")
                failures.append(
                    f"{scenario.name}: expected "
                    f"{'success' if scenario.should_pass else 'failure'}, "
                    f"got exit {result.returncode}: {output}"
                )
                continue
            receipt = (
                output_path.read_text(encoding="utf-8")
                if output_path.is_file()
                else ""
            )
            if scenario.should_pass:
                if scenario.main is None:
                    failures.append(f"{scenario.name}: passing case has no main ref")
                    continue
                expected_receipt = (
                    f"canonical_commit={_commit(fixture, scenario.main)}\n"
                )
                if receipt != expected_receipt:
                    failures.append(
                        f"{scenario.name}: expected canonical output receipt "
                        f"{expected_receipt.strip()!r}, found {receipt.strip()!r}"
                    )
            elif receipt:
                failures.append(
                    f"{scenario.name}: failing case emitted canonical output receipt"
                )
    if failures:
        raise ContractError("; ".join(failures))


def self_test(source: str) -> None:
    mutation_test(source)
    executable_scenario_test(source)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help=(
            "also reject semantic release/provenance bypasses and execute "
            "positive/negative disposable-Git scenarios"
        ),
    )
    args = parser.parse_args()
    try:
        source = WORKFLOW.read_text(encoding="utf-8")
        if args.self_test:
            self_test(source)
        else:
            validate(source)
    except (ContractError, OSError, subprocess.SubprocessError) as error:
        print(f"FAIL release workflow contract: {error}")
        return 1
    print("PASS exact main/tag/launcher release-workflow contract")
    if args.self_test:
        print(f"PASS {len(_semantic_mutations(source))} semantic workflow mutation tests")
        print("PASS 17 executable disposable-Git scenarios")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
