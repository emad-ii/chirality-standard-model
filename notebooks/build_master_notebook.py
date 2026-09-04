#!/usr/bin/env python3
"""Build the single reader-facing master verification notebook."""

import argparse
import inspect
from pathlib import Path

import nbformat as nbf

from check_notebook_freshness import (
    PINNED_COLAB_REF,
    RELEASE_INPUT_DIGEST_DOMAIN,
    RELEASE_INPUT_EXCLUDED_DIRECTORY_NAMES,
    RELEASE_INPUT_EXCLUDED_FILES,
    RELEASE_INPUT_ROOT_DIRECTORIES,
    RELEASE_INPUT_ROOT_FILES,
    SafeGitHubAPIRedirectHandler,
    SafeGitHubArchiveRedirectHandler,
    classify_canonical_release_binding,
    classify_commit_binding,
    format_provenance_receipt,
    git_repository_root,
    is_release_input_path,
    local_git_head,
    normalize_optional_commit_sha,
    peel_github_tag_payload,
    release_input_digest,
    release_input_files,
    relevant_input_state,
    select_expected_commit,
    valid_nonzero_hex,
)


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUTPUT = HERE.parent / "Cubic_Anomaly_Master_Verification.ipynb"
EXPECTED_RELEASE_INPUT_SHA256 = release_input_digest(ROOT)


RUNTIME_HELPERS = "\n\n".join(
    inspect.getsource(item).strip()
    for item in (
        is_release_input_path,
        release_input_files,
        release_input_digest,
        valid_nonzero_hex,
        normalize_optional_commit_sha,
        select_expected_commit,
        classify_commit_binding,
        classify_canonical_release_binding,
        peel_github_tag_payload,
        git_repository_root,
        local_git_head,
        relevant_input_state,
        format_provenance_receipt,
        SafeGitHubAPIRedirectHandler,
        SafeGitHubArchiveRedirectHandler,
    )
)


def markdown(cell_id: str, text: str):
    return nbf.v4.new_markdown_cell(text.strip(), id=cell_id)


def code(cell_id: str, text: str, *, tags: tuple[str, ...] = ()):
    cell = nbf.v4.new_code_cell(text.strip(), id=cell_id)
    if tags:
        cell["metadata"]["tags"] = list(tags)
    return cell


def setup_source(template: str) -> str:
    """Fill the setup cell with the current self-reference-safe content pin."""

    replacements = {
        "__PINNED_COLAB_REF__": repr(PINNED_COLAB_REF),
        "__EXPECTED_RELEASE_INPUT_SHA256__": EXPECTED_RELEASE_INPUT_SHA256,
        "__RELEASE_INPUT_DIGEST_DOMAIN__": repr(RELEASE_INPUT_DIGEST_DOMAIN),
        "__RELEASE_INPUT_ROOT_FILES__": repr(RELEASE_INPUT_ROOT_FILES),
        "__RELEASE_INPUT_ROOT_DIRECTORIES__": repr(RELEASE_INPUT_ROOT_DIRECTORIES),
        "__RELEASE_INPUT_EXCLUDED_FILES__": repr(
            tuple(sorted(RELEASE_INPUT_EXCLUDED_FILES))
        ),
        "__RELEASE_INPUT_EXCLUDED_DIRECTORY_NAMES__": repr(
            tuple(sorted(RELEASE_INPUT_EXCLUDED_DIRECTORY_NAMES))
        ),
        "__RUNTIME_HELPERS__": RUNTIME_HELPERS,
    }
    for marker, value in replacements.items():
        template = template.replace(marker, value)
    return template


notebook = nbf.v4.new_notebook()
notebook["metadata"] = {
    "colab": {
        "include_colab_link": True,
        "name": "Cubic Anomaly — Master Verification",
        "provenance": [],
        "toc_visible": True,
    },
    "kernelspec": {
        "display_name": "Python 3",
        "language": "python",
        "name": "python3",
    },
    "language_info": {"name": "python", "version": "3"},
}
notebook["cells"] = [
    markdown(
        "overview",
        r"""
<p align="center">
  <a href="https://colab.research.google.com/github/emad-ii/cubic-anomaly-standard-model/blob/v0.1.0/Cubic_Anomaly_Master_Verification.ipynb"><img src="https://colab.research.google.com/assets/colab-badge.svg" alt="Open in Colab"></a>
  <a href="https://github.com/emad-ii/cubic-anomaly-standard-model"><img src="https://img.shields.io/badge/source-GitHub-0f233f?logo=github" alt="GitHub repository"></a>
  <a href="https://github.com/emad-ii/cubic-anomaly-standard-model/blob/v0.1.0/paper/paper.pdf"><img src="https://img.shields.io/badge/read-paper-b7791f" alt="Read the paper"></a>
  <a href="https://github.com/emad-ii/cubic-anomaly-standard-model/actions/workflows/ci.yml?query=branch%3Arelease-v0.1.0+event%3Apush"><img src="https://img.shields.io/badge/full_gate-GitHub_Actions-2088FF?logo=githubactions&amp;logoColor=white" alt="View the release launcher gate"></a>
</p>

# From the Cubic Anomaly to the Standard Model

## Master verification notebook

**One guided run. Six exceptional grading rows. Two independent $E_6$
realizations. Exactly 38,880 triples. Named finite Lean theorems.**

This notebook rebuilds the finite $E_6$ incidence calculation from the Cartan
matrix, reproduces it through an independent $\mathbb R^8$ realization, checks
the deterministic certificate, and runs the complete Python release audit.

> **Proof allocation.** This notebook reconstructs the exact finite evidence.
> Lean checks the exceptional root-data census, its Cartan trace-cubic selector,
> and the concrete finite incidence claims. The paper proves the compact-Lie
> and invariant-theoretic bridges around those finite calculations. The named
> complete-matter interpretation (M) supplies the final family-number reading.
"""
    ),
    markdown(
        "evidence-map",
        r"""
## What this run establishes

| Layer | This notebook's role | Strongest authority |
| --- | --- | --- |
| Exceptional full-rank census | Exhausts inner toral gradings and derives the Cartan trace-cubic selector | Lean 4 + independent exact Python |
| Finite $E_6$ incidence | Reconstructs and independently reproduces the complete calculation | Lean 4 + `native_decide` |
| Broader finite/arithmetic audits | Runs all distributed exact Python checks | Deterministic Python outputs |
| Classification theorem | Links each executable result to the compact-Lie and invariant-theory bridges | Proved in the manuscript; finite exceptional stage also Lean checked |
| Physical family interpretation | Applies the chiral index to complete matter | Explicit assumption (M) |

The numerical target is the paper's finite spine:

$$
72\text{ roots},\qquad 27\cdot36\cdot40=38{,}880\text{ triples},
$$

with six simultaneous Weyl cells, 4,320 pairwise maximizers, 2,160 common
maximizers, 8,640 labelled containment incidences, and 2,160 distinct
root-subsystem inclusions.
"""
    ),
    markdown(
        "setup-guide",
        r"""
## 1 · Setup

GitHub Codespaces is the primary one-click route for the complete environment.
You can also run the notebook from a local checkout or Colab.

Because this repository is private, the supported direct Colab bootstrap is for
the repository owner. GitHub fine-grained tokens do not support collaborator
access to another user's private repository, and this project does not
recommend the broader classic-token workaround. Collaborators should use
Codespaces. The owner completes two setup steps:

1. Authorize Colab to open the private notebook from GitHub, or download the
   `.ipynb` and choose **File → Upload notebook** in Colab.
2. Create a fine-grained GitHub token restricted to this repository with
   **Contents: read-only**. Add it through Colab's key icon as the secret
   `GITHUB_TOKEN`, and permit this notebook to access it.

Never paste a token into a code cell. The setup cell reads the secret without
printing it, resolves `v0.1.0` to its peeled full commit SHA, and downloads a
temporary archive by that SHA. Record the displayed commit and compare it with
the review target. The embedded digest validates the listed release inputs; it
does not make the tag immutable. Once the repository is public, the same cell
works without a token.
"""
    ),
    code(
        "setup",
        setup_source(
        '''
from __future__ import annotations

from contextlib import redirect_stdout
from hashlib import sha256
from html import escape
from io import BytesIO
import io
import json
import os
from pathlib import Path
from pathlib import PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
import time
from urllib.error import HTTPError
from urllib.parse import quote, urlparse
from urllib.request import build_opener, HTTPRedirectHandler, Request
from zipfile import ZipFile

from IPython.display import HTML, display


REPO_SLUG = "emad-ii/cubic-anomaly-standard-model"
PINNED_COLAB_REF = __PINNED_COLAB_REF__
REPO_REF = PINNED_COLAB_REF
EXPECTED_RELEASE_INPUT_SHA256 = "__EXPECTED_RELEASE_INPUT_SHA256__"
RELEASE_INPUT_DIGEST_DOMAIN = __RELEASE_INPUT_DIGEST_DOMAIN__
RELEASE_INPUT_ROOT_FILES = __RELEASE_INPUT_ROOT_FILES__
RELEASE_INPUT_ROOT_DIRECTORIES = __RELEASE_INPUT_ROOT_DIRECTORIES__
RELEASE_INPUT_EXCLUDED_FILES = __RELEASE_INPUT_EXCLUDED_FILES__
RELEASE_INPUT_EXCLUDED_DIRECTORY_NAMES = __RELEASE_INPUT_EXCLUDED_DIRECTORY_NAMES__
PROVENANCE_RECEIPT_MARKER = "RELEASE INPUT PROVENANCE RECEIPT v2"

# The complete exact-Python release gate is intentionally on by default.
RUN_COMPLETE_PYTHON_AUDIT = True

# Lean is authoritative for the finite theorem bundle, but installing the
# version-selected toolchain is too heavy for an instant Colab tour. Set this to True only when
# `lake` is already available (for example, in the repository devcontainer).
RUN_LEAN_IF_AVAILABLE = False


def find_repo_root(start: Path) -> Path | None:
    for candidate in (start, *start.parents):
        marker = candidate / "verification" / "python" / "verify_e6_extrema.py"
        if marker.is_file():
            return candidate
    return None


def colab_secret(name: str) -> str | None:
    try:
        from google.colab import userdata  # type: ignore[import-not-found]

        return userdata.get(name)
    except Exception:
        return None


def running_in_colab() -> bool:
    try:
        import google.colab  # type: ignore[import-not-found]  # noqa: F401

        return True
    except ImportError:
        return False


__RUNTIME_HELPERS__


def safe_extract(archive: bytes, destination: Path) -> Path:
    destination.mkdir(parents=True, exist_ok=True)
    base = destination.resolve()
    with ZipFile(BytesIO(archive)) as zipped:
        for member in zipped.infolist():
            target = (base / member.filename).resolve()
            if target != base and base not in target.parents:
                raise RuntimeError("Refusing an unsafe path in the source archive.")
        zipped.extractall(base)
    roots = [path for path in base.iterdir() if path.is_dir()]
    if len(roots) != 1:
        raise RuntimeError("The downloaded repository archive had an unexpected layout.")
    return roots[0]


def github_headers(token: str | None) -> dict[str, str]:
    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "cubic-anomaly-master-notebook",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    return headers


def github_json(
    url: str, headers: dict[str, str], *, token_available: bool, label: str
) -> object:
    SafeGitHubAPIRedirectHandler.require_api_url(url)
    request = Request(url, headers=headers)
    opener = build_opener(SafeGitHubAPIRedirectHandler())
    try:
        with opener.open(request, timeout=60) as response:
            SafeGitHubAPIRedirectHandler.require_api_url(response.geturl())
            return json.loads(response.read())
    except HTTPError as error:
        if error.code in {401, 403, 404} and not token_available:
            raise RuntimeError(
                "This repository is private. The supported Colab bootstrap uses "
                "an owner-created fine-grained GitHub token restricted to this "
                "repository with Contents: read-only as the GITHUB_TOKEN secret. "
                "This project does not recommend broader classic tokens; repository "
                "collaborators should use Codespaces."
            ) from None
        raise RuntimeError(
            f"GitHub could not read {label} (HTTP {error.code}); confirm that "
            "the release tag exists and the token can read the repository."
        ) from None
    except (json.JSONDecodeError, UnicodeDecodeError):
        raise RuntimeError(f"GitHub returned invalid JSON for {label}.") from None


def resolve_github_tag_commit(
    headers: dict[str, str], *, token_available: bool
) -> str:
    qualified_ref = f"tags/{REPO_REF}"
    encoded_ref = quote(qualified_ref, safe="/")
    ref_payload = github_json(
        f"https://api.github.com/repos/{REPO_SLUG}/git/ref/{encoded_ref}",
        headers,
        token_available=token_available,
        label=f"release tag {REPO_REF!r}",
    )
    tag_payload = None
    if isinstance(ref_payload, dict):
        ref_object = ref_payload.get("object")
        if isinstance(ref_object, dict) and ref_object.get("type") == "tag":
            tag_object_sha = ref_object.get("sha")
            if not isinstance(tag_object_sha, str) or not valid_nonzero_hex(
                tag_object_sha, 40
            ):
                raise RuntimeError("GitHub returned an invalid annotated-tag SHA.")
            tag_payload = github_json(
                f"https://api.github.com/repos/{REPO_SLUG}/git/tags/{tag_object_sha}",
                headers,
                token_available=token_available,
                label=f"annotated tag object for {REPO_REF!r}",
            )
    try:
        return peel_github_tag_payload(REPO_REF, ref_payload, tag_payload)
    except ValueError as error:
        raise RuntimeError(
            f"GitHub did not resolve {REPO_REF!r} to a commit: {error}"
        ) from None


def download_repo_for_colab() -> tuple[Path, str, str]:
    token = colab_secret("GITHUB_TOKEN")
    headers = github_headers(token)
    revision = resolve_github_tag_commit(headers, token_available=bool(token))

    request = Request(
        f"https://api.github.com/repos/{REPO_SLUG}/zipball/{revision}",
        headers=headers,
    )
    opener = build_opener(SafeGitHubArchiveRedirectHandler())
    try:
        with opener.open(request, timeout=120) as response:
            SafeGitHubArchiveRedirectHandler.require_archive_url(response.geturl())
            archive = response.read()
    except HTTPError as error:
        if error.code in {401, 403, 404} and not token:
            raise RuntimeError(
                "This repository is private. The supported Colab bootstrap uses "
                "an owner-created fine-grained GitHub token restricted to this "
                "repository with Contents: read-only as the GITHUB_TOKEN secret. "
                "This project does not recommend broader classic tokens; repository "
                "collaborators should use Codespaces."
            ) from None
        raise RuntimeError(
            f"GitHub archive download failed with HTTP {error.code}; "
            "check repository access and rerun."
        ) from None

    destination = Path(tempfile.mkdtemp(prefix="cubic-anomaly-source-", dir="/content"))
    archive_digest = sha256(archive).hexdigest()
    return safe_extract(archive, destination), revision, archive_digest


source_archive_digest = None
if running_in_colab():
    REPO_ROOT, source_revision, source_archive_digest = download_repo_for_colab()
    source_label = f"{REPO_SLUG} release archive"
    source_mode = "colab-archive"
    identity_job_commit = None
    archive_value = source_archive_digest
    local_head_value = "not-applicable"
    relevant_state = "not-applicable"
else:
    REPO_ROOT = find_repo_root(Path.cwd().resolve())
    if REPO_ROOT is None:
        raise RuntimeError("Run this notebook from inside the repository checkout.")
    source_revision = local_git_head(REPO_ROOT)
    source_mode = "local-git" if source_revision is not None else "local-tree"
    source_label = (
        "local Git checkout" if source_revision is not None
        else "local source tree without Git metadata"
    )
    identity_job_commit = os.environ.get("EXPECTED_CANONICAL_TAG_COMMIT")
    archive_value = "not-applicable"
    local_head_value = source_revision or "unavailable"
    relevant_state = relevant_input_state(REPO_ROOT)

try:
    commit_binding, commit_basis, commit_target = classify_commit_binding(
        mode=source_mode,
        source_commit=source_revision,
        local_head=source_revision,
        relevant_state=relevant_state,
        github_sha=os.environ.get("GITHUB_SHA"),
        expected_sha=os.environ.get("EXPECTED_COMMIT_SHA"),
    )
    release_binding, release_basis, release_target = (
        classify_canonical_release_binding(
            mode=source_mode,
            resolved_tag_commit=(
                source_revision if source_mode == "colab-archive" else None
            ),
            identity_job_commit=identity_job_commit,
            commit_binding=commit_binding,
            commit_target=commit_target,
        )
    )
except ValueError as error:
    raise RuntimeError(f"Source provenance check failed: {error}") from None

tag_commit_value = (
    release_target if release_target != "not-supplied" else "not-supplied"
)

actual_release_input_sha256 = release_input_digest(REPO_ROOT)
if actual_release_input_sha256 != EXPECTED_RELEASE_INPUT_SHA256:
    raise RuntimeError(
        "Release-input content does not match this notebook's embedded digest: "
        f"expected {EXPECTED_RELEASE_INPUT_SHA256}, "
        f"found {actual_release_input_sha256}."
    )

PYTHON_DIR = REPO_ROOT / "verification" / "python"
CERTIFICATE_DIR = REPO_ROOT / "verification" / "certificates"
sys.path.insert(0, str(PYTHON_DIR))

import verify_e6_extrema as e6
from verification_checks import require

provenance_receipt = format_provenance_receipt(
    mode=source_mode,
    release_digest=actual_release_input_sha256,
    commit_binding=commit_binding,
    commit_basis=commit_basis,
    commit_target=commit_target,
    release_binding=release_binding,
    release_basis=release_basis,
    release_target=release_target,
    tag_commit=tag_commit_value,
    archive_digest=archive_value,
    local_head=local_head_value,
    relevant_state=relevant_state,
)
all_provenance_verified = commit_binding == release_binding == "VERIFIED"
receipt_color = "#0f766e" if all_provenance_verified else "#b45309"
receipt_background = "#f4faf8" if all_provenance_verified else "#fff7ed"
commit_note = (
    "Execution is bound to the expected commit."
    if commit_binding == "VERIFIED"
    else (
        "Execution commit provenance is UNVERIFIED; the content digest remains "
        "independently checked."
    )
)
release_note = (
    f"The canonical {REPO_REF} identity is verified."
    if release_binding == "VERIFIED"
    else "Canonical tag identity is not established by this notebook execution."
)
display(HTML(f"""
<pre style="border:1px solid {receipt_color};border-radius:10px;padding:14px 18px;
            background:{receipt_background};white-space:pre-wrap;word-break:break-all">{escape(provenance_receipt)}</pre>
"""))
display(HTML(f"""
<div style="border:1px solid {receipt_color};border-left:5px solid {receipt_color};
            border-radius:10px;padding:14px 18px;background:{receipt_background}">
  <div style="margin-top:6px"><b>Ready.</b> Source loaded from
    <code>{escape(source_label)}</code></div>
  <div style="margin-top:8px"><b>Execution commit binding: {commit_binding}</b> ·
    {escape(commit_note)}</div>
  <div style="margin-top:8px"><b>Canonical release binding: {release_binding}</b> ·
    {escape(release_note)}</div>
  <div style="margin-top:8px">Python {escape(sys.version.split()[0])} ·
    complete Python audit
    <b>{'enabled' if RUN_COMPLETE_PYTHON_AUDIT else 'disabled'}</b></div>
</div>
"""))
'''
        ),
        tags=("parameters",),
    ),
    markdown(
        "exceptional-selector-guide",
        r"""
## 2 · Exhaust the finite exceptional selector

Before specializing to $E_6$, reconstruct the roots of $G_2$, $F_4$, $E_6$,
$E_7$, and $E_8$ from their Cartan matrices. The first exact program exhausts
all inner toral gradings modulo two and three and recovers the six full-rank,
complex-type rows. The second independently derives the trace cubic from the
grade-one weights rather than importing the paper's cubic-index table.

The surviving Cartan restriction is the $E_6$ factor in
$E_8\supset E_6+A_2$. Turning that vanishing restriction into the full radical
statement uses the invariant-theory argument proved in the manuscript.
"""
    ),
    code(
        "exceptional-selector",
        """
def run_exact_verifier(filename: str) -> str:
    result = subprocess.run(
        [sys.executable, str(PYTHON_DIR / filename)],
        cwd=PYTHON_DIR,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(f"{filename} failed:\\n{result.stderr}")
    return result.stdout.strip()


toral_output = run_exact_verifier("check_toral_gradings.py")
cubic_selector_output = run_exact_verifier("check_cubic_radical_selection.py")

require("E8: A2+E6; dim(g1)=81" in toral_output)
require("E8: A8; dim(g1)=84" in toral_output)
require("all direct toral grading checks passed" in toral_output)
require("E8: A2+E6; dim(V)=81; Cartan-cubic-null=E6" in cubic_selector_output)
require("uniquely retain E8/(E6+A2)" in cubic_selector_output)

print(toral_output)
print()
print(cubic_selector_output)
"""
    ),
    markdown(
        "e6-roots-guide",
        r"""
## 3 · Reconstruct the $E_6$ roots

Start with one simple root and close under the six reflections encoded by the
Bourbaki $E_6$ Cartan matrix. No list of 72 roots is imported for this step.
"""
    ),
    code(
        "e6-roots",
        """
roots = e6.orbit(e6.E[0], e6.reflect_root)
positive_roots = [root for root in roots if min(root) >= 0]
highest_root = max(positive_roots, key=sum)

require(len(roots) == 72)
require(len(positive_roots) == 36)
require(highest_root == (1, 2, 2, 3, 2, 1))
require(all(e6.root_inner(root, root) == 2 for root in roots))

root_summary = {
    "roots": len(roots),
    "positive roots": len(positive_roots),
    "highest-root coefficients": highest_root,
    "squared lengths": sorted({e6.root_inner(root, root) for root in roots}),
}
root_summary
"""
    ),
    markdown(
        "subsystem-orbits-guide",
        r"""
## 4 · Build the three maximal-subsystem orbits

The selected $D_5$, $A_5+A_1$, and $A_2^3$ witnesses generate Weyl orbits of
sizes 27, 36, and 40. Their Cartesian product is the complete incidence search
space—not a sample.
"""
    ),
    code(
        "subsystem-orbits",
        """
weights = e6.orbit(e6.E[0], e6.reflect_weight)
d_by_weight = {
    weight: frozenset(root for root in roots if e6.pairing(weight, root) == 0)
    for weight in weights
}
root_pairs = {min(root, e6.neg(root)) for root in roots}
a_by_root = {
    root: frozenset(
        other
        for other in roots
        if other in (root, e6.neg(root)) or e6.root_inner(root, other) == 0
    )
    for root in root_pairs
}
theta_seed = frozenset(root for root in roots if root[highest_root.index(3)] % 3 == 0)
theta_orbit = e6.orbit(theta_seed, e6.reflect_set)

d_orbit = frozenset(d_by_weight.values())
a_orbit = frozenset(a_by_root.values())

require((len(d_orbit), len(a_orbit), len(theta_orbit)) == (27, 36, 40))
require({len(item) for item in d_orbit} == {40})
require({len(item) for item in a_orbit} == {32})
require({len(item) for item in theta_orbit} == {18})

triple_space = len(d_orbit) * len(a_orbit) * len(theta_orbit)
require(triple_space == 38_880)

orbit_summary = {
    "D5 orbit": len(d_orbit),
    "A5+A1 orbit": len(a_orbit),
    "A2^3 orbit": len(theta_orbit),
    "complete triple space": triple_space,
}
orbit_summary
"""
    ),
    markdown(
        "incidence-guide",
        r"""
## 5 · Exhaust the incidence problem

The primary implementation computes every triple, its three pairwise
intersections, and its common intersection. Explicit runtime checks enforce
the six-cell distribution and the extremal counts reported in the paper.
"""
    ),
    code(
        "incidence",
        """
primary_output = io.StringIO()
started = time.perf_counter()
with redirect_stdout(primary_output):
    e6.main()
primary_seconds = time.perf_counter() - started

print(primary_output.getvalue().strip())
print(f"elapsed={primary_seconds:.2f}s")
"""
    ),
    markdown(
        "r8-guide",
        r"""
## 6 · Reproduce it independently in $\mathbb R^8$

This second program uses a different coordinate realization and Weyl action.
Agreement is therefore a genuine implementation cross-check, not merely a
second invocation of the same functions.
"""
    ),
    code(
        "r8",
        """
started = time.perf_counter()
r8_result = subprocess.run(
    [sys.executable, str(PYTHON_DIR / "verify_e6_extrema_r8_fast.py")],
    cwd=PYTHON_DIR,
    text=True,
    capture_output=True,
    check=False,
)
r8_seconds = time.perf_counter() - started
if r8_result.returncode != 0:
    raise RuntimeError("The independent R8 verifier failed:\\n" + r8_result.stderr)

print(r8_result.stdout.strip())
print(f"elapsed={r8_seconds:.2f}s")
"""
    ),
    markdown(
        "certificate-guide",
        r"""
## 7 · Validate the deterministic certificate

The certificate carries coordinates, reflection permutations, and orbit seeds
into the Lean data generator. The early SHA-256 receipt checks the certificate
against its recorded checksum; it does not claim independent reproduction.
The complete audit in the next step regenerates the certificate byte-for-byte.
The expected theorem counts are stated independently in Lean, which recomputes
them from the certificate's finite witness data.
"""
    ),
    code(
        "certificate",
        '''
certificate_path = CERTIFICATE_DIR / "e6_extrema_certificate.json"
certificate_bytes = certificate_path.read_bytes()
certificate = json.loads(certificate_bytes)
recorded_digest = (CERTIFICATE_DIR / "e6_extrema_certificate.sha256").read_text().split()[0]
actual_digest = sha256(certificate_bytes).hexdigest()

require(certificate["certificate_version"] == 8)
require(recorded_digest == actual_digest)

finite = certificate["finite_object_counts"]
extrema = certificate["extrema"]
summary = {
    "roots": finite["roots"],
    "triple space": finite["triple_space"],
    "Weyl cells": len(certificate["joint_distribution"]),
    "pairwise maximizers": extrema["pairwise"]["maximizers"],
    "common maximizers": extrema["common"]["maximizers"],
    "labelled containment incidences": extrema["nested_pairs"]["labelled_ordered_pairs"],
}
expected_summary = {
    "roots": 72,
    "triple space": 38_880,
    "Weyl cells": 6,
    "pairwise maximizers": 4_320,
    "common maximizers": 2_160,
    "labelled containment incidences": 8_640,
}
require(summary == expected_summary)

rows = "".join(
    f"<tr><td style='padding:6px 18px 6px 0'>{escape(label)}</td>"
    f"<td style='padding:6px 0;text-align:right'><b>{value:,}</b></td></tr>"
    for label, value in summary.items()
)
display(HTML(f"""
<div style="display:inline-block;border:1px solid #d7c28d;border-radius:12px;
            padding:16px 22px;background:#fffaf0;min-width:360px">
  <div style="color:#8a5b13;font-size:12px;font-weight:700;letter-spacing:.08em">
    CERTIFICATE CHECKSUM CONSISTENT
  </div>
  <table style="margin-top:8px">{rows}</table>
  <div style="margin-top:10px;color:#566;font-size:12px">
    SHA-256 <code>{actual_digest[:16]}…{actual_digest[-8:]}</code>
  </div>
</div>
"""))
'''
    ),
    markdown(
        "full-audit-guide",
        r"""
## 8 · Run the complete executable audit

This is the same standard-library Python gate used by CI. It checks all twelve
recorded verifier outputs, regenerates both JSON artifacts in temporary paths,
compares them byte-for-byte, verifies the certificate digest, and checks the
release's statement/layout bridges. It is enabled by default in this master
notebook.

The chiral-dimension check validates the minuscule restriction that makes
opposite-weight cancellation equivalent to cancelling whole irreducibles;
nonminuscule counterexamples are rejected. Boundary regressions also test both
dual-node orientations, order-three automorphism lifts, and the cubic-index
rank restrictions used in the manuscript.

The context check distinguishes 8,640 labelled extrema pairings from 4,320
actual chains in one Weyl orbit, including their Cartan spans. The exceptional
sieve counts labelled Cartan presentations; its redundant $B_2/C_2$ entries
have identical representation and index data after exchanging the nodes.
"""
    ),
    code(
        "full-audit",
        """
full_audit_passed = False
if RUN_COMPLETE_PYTHON_AUDIT:
    started = time.perf_counter()
    completed = subprocess.run(
        [sys.executable, str(PYTHON_DIR / "run_all.py"), "--jobs", "2"],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    audit_seconds = time.perf_counter() - started
    print(completed.stdout.strip())
    if completed.returncode != 0:
        raise RuntimeError("The complete Python audit failed:\\n" + completed.stderr)
    full_audit_passed = "PASS  all 16 release checks" in completed.stdout
    require(full_audit_passed)
    print(f"notebook audit elapsed={audit_seconds:.2f}s")
else:
    print("Complete Python audit disabled by notebook parameter.")
"""
    ),
    markdown(
        "lean-guide",
        r"""
## 9 · Run the formal lane when available

The version/source-pinned Lean/Mathlib build runs as a separate CI lane under
its disclosed trust model. In the supplied devcontainer—or another environment
with `lake` installed—the optional cell below rebuilds the formal claim bundle
and reruns the axiom/hygiene audit.

The two principal Lean surfaces are
[`CubicAnomaly/Classification/Exceptional.lean`](https://github.com/emad-ii/cubic-anomaly-standard-model/blob/v0.1.0/CubicAnomaly/Classification/Exceptional.lean)
and
[`CubicAnomaly/E6/Claims.lean`](https://github.com/emad-ii/cubic-anomaly-standard-model/blob/v0.1.0/CubicAnomaly/E6/Claims.lean).
"""
    ),
    code(
        "lean",
        """
lean_build_passed = None
if RUN_LEAN_IF_AVAILABLE:
    lake = shutil.which("lake")
    if lake is None:
        raise RuntimeError("RUN_LEAN_IF_AVAILABLE is true, but `lake` is not installed.")
    for command in (
        [sys.executable, "formal/scripts/check_generated_data.py"],
        [lake, "build"],
        [sys.executable, "formal/scripts/check_formal_hygiene.py"],
    ):
        result = subprocess.run(command, cwd=REPO_ROOT, text=True, capture_output=True)
        print(result.stdout.strip())
        if result.returncode != 0:
            raise RuntimeError(result.stderr or f"Command failed: {command[0]}")
    lean_build_passed = True
    print("Lean build, generated-data check, and formal-hygiene audit passed.")
else:
    print(
        "Lean status: see the required GitHub Actions release lane, or set "
        "RUN_LEAN_IF_AVAILABLE=True when `lake` is installed."
    )
"""
    ),
    markdown(
        "result-heading",
        r"""
## Result · Evidence by layer
"""
    ),
    code(
        "result",
        '''
require(root_summary["roots"] == 72)
require(orbit_summary["complete triple space"] == 38_880)
require(summary == expected_summary)
require(r8_result.returncode == 0)
if RUN_COMPLETE_PYTHON_AUDIT:
    require(full_audit_passed)

audit_label = "PASS" if full_audit_passed else "NOT RUN"
lean_label = "PASS" if lean_build_passed else "SEE CI"
certificate_label = "REPRODUCED" if full_audit_passed else "CHECKSUM ONLY"
display(HTML(f"""
<div style="border:1px solid #0f766e;border-radius:14px;overflow:hidden;max-width:780px">
  <div style="padding:18px 22px;background:#0f233f;color:white">
    <div style="font-size:12px;font-weight:700;letter-spacing:.1em;color:#9dd9ca">
      MASTER NOTEBOOK VERDICT
    </div>
    <div style="font-size:24px;font-weight:700;margin-top:4px">Finite computation reproduced</div>
  </div>
  <div style="padding:18px 22px;background:#f8fbfa">
    <table>
      <tr><td style="padding:5px 28px 5px 0">Cartan-matrix $E_6$ route</td><td><b>PASS</b></td></tr>
      <tr><td style="padding:5px 28px 5px 0">Exceptional toral/cubic selector</td><td><b>PASS</b></td></tr>
      <tr><td style="padding:5px 28px 5px 0">Independent R<sup>8</sup> route</td><td><b>PASS</b></td></tr>
      <tr><td style="padding:5px 28px 5px 0">Deterministic certificate</td><td><b>{certificate_label}</b></td></tr>
      <tr><td style="padding:5px 28px 5px 0">Complete Python audit</td><td><b>{audit_label}</b></td></tr>
      <tr><td style="padding:5px 28px 5px 0">Version/source-pinned Lean theorem bundle</td><td><b>{lean_label}</b></td></tr>
      <tr><td style="padding:5px 28px 5px 0">Execution commit binding</td><td><b>{commit_binding}</b></td></tr>
      <tr><td style="padding:5px 28px 5px 0">Canonical release binding</td><td><b>{release_binding}</b></td></tr>
    </table>
  </div>
</div>
"""))
'''
    ),
    markdown(
        "result-by-layer",
        r"""
### The result by layer

- **Formally checked in Lean:** the complete exceptional inner-toral
  order-three census, the order-two odd-root connectivity check, the
  root-derived Cartan cubic selector, and the concrete finite $E_6$
  root/reflection table, subsystem orbit sizes, all 38,880 triples, six-cell
  partition and distribution, both extrema, the exact root-closure and rank
  signatures of the two distinguished six-root components, multiplicities,
  contexts, and 8,640 labelled containment incidences.
- **Computationally verified here:** the same incidence result through two
  independent exact implementations, plus the broader finite and arithmetic
  audit suite.
- **Proved in the manuscript:** the structural bridge
  from the homogeneous hypotheses to the finite census, the invariant-theory
  bridge from Cartan restriction to radical ideals, the rank-deficient and
  infinite-family arguments, the standard simply-laced classification used to
  name the finite root-system signatures, global subgroup integration, and
  representation branching.
- **Physical interpretation:** assumption (M) turns the chiral index into a
  complete observed family count.

For claim-by-claim status, read
[`docs/CLAIM_STATUS.md`](https://github.com/emad-ii/cubic-anomaly-standard-model/blob/v0.1.0/docs/CLAIM_STATUS.md).
For the exact trust model and next formalization phases, read
[`docs/FORMALIZATION_BOUNDARY.md`](https://github.com/emad-ii/cubic-anomaly-standard-model/blob/v0.1.0/docs/FORMALIZATION_BOUNDARY.md).
"""
    ),
]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=OUTPUT,
        help="Notebook path (defaults to the canonical repository notebook).",
    )
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    nbf.write(notebook, args.output)
    print(args.output)


if __name__ == "__main__":
    main()
