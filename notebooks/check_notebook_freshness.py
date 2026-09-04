#!/usr/bin/env python3
"""Check that the committed notebook's source surface matches its builder."""

from __future__ import annotations

import argparse
import ast
from hashlib import sha256
from html.parser import HTMLParser
import json
from pathlib import Path
from pathlib import PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
from urllib.error import HTTPError
from urllib.parse import urlparse
from urllib.request import build_opener, HTTPRedirectHandler, Request


ROOT = Path(__file__).resolve().parents[1]
BUILDER = ROOT / "notebooks" / "build_master_notebook.py"
CANONICAL = ROOT / "Cubic_Anomaly_Master_Verification.ipynb"
CERTIFICATE = ROOT / "verification" / "certificates" / "e6_extrema_certificate.json"
PINNED_COLAB_REF = "v0.1.0"
RELEASE_INPUT_DIGEST_DOMAIN = b"cubic-anomaly-release-input-bundle-v2\0"
RELEASE_INPUT_ROOT_FILES = (
    ".gitattributes",
    ".gitignore",
    "CITATION.cff",
    "CONTRIBUTING.md",
    "CubicAnomaly.lean",
    "Cubic_Anomaly_Master_Verification.ipynb",
    "LICENSE.md",
    "Makefile",
    "README.md",
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
    "requirements-notebook.txt",
)
RELEASE_INPUT_ROOT_DIRECTORIES = (
    ".devcontainer",
    ".github",
    "CubicAnomaly",
    "docs",
    "formal",
    "notebooks",
    "paper",
    "verification",
)
RELEASE_INPUT_EXCLUDED_FILES = frozenset(
    {
        "Cubic_Anomaly_Master_Verification.ipynb",
        "docs/AUDIT.md",
    }
)
RELEASE_INPUT_EXCLUDED_DIRECTORY_NAMES = frozenset(
    {".cache", ".git", "__pycache__", "build", "cache"}
)
PROVENANCE_RECEIPT_MARKER = "RELEASE INPUT PROVENANCE RECEIPT v2"
PROVENANCE_RECEIPT_RE = re.compile(
    rf"^{re.escape(PROVENANCE_RECEIPT_MARKER)} "
    r"Source mode: (?P<mode>colab-archive|local-git|local-tree) "
    r"Pinned Colab ref: (?P<ref>\S+) "
    r"Content binding: (?P<content>VERIFIED) "
    r"RELEASE INPUT SHA-256: (?P<release>[0-9a-f]+) "
    r"Execution commit binding: (?P<commit_binding>VERIFIED|UNVERIFIED) "
    r"Execution commit basis: (?P<commit_basis>ARCHIVE_DOWNLOADED_BY_COMMIT_SHA|HEAD_EQUALS_GITHUB_SHA|HEAD_EQUALS_EXPECTED_SHA|HEAD_EQUALS_BOTH|NO_EXPECTED_SHA|NO_GIT_METADATA|DIRTY_RELEASE_INPUTS|UNKNOWN_GIT_STATE) "
    r"Execution commit target: (?P<commit_target>[0-9a-f]{40}|not-supplied) "
    r"Canonical release binding: (?P<release_binding>VERIFIED|UNVERIFIED) "
    r"Canonical release basis: (?P<release_basis>TAG_PEELED_VIA_GITHUB_API|CI_THREE_WAY_IDENTITY|NO_CANONICAL_TAG_RECEIPT|NO_GIT_METADATA|COMMIT_BINDING_UNVERIFIED) "
    r"Canonical release target: (?P<release_target>[0-9a-f]{40}|not-supplied) "
    r"Canonical tag commit receipt: (?P<tag_commit>\S+) "
    r"Source archive SHA-256: (?P<archive>\S+) "
    r"Local git HEAD: (?P<head>\S+) "
    r"Relevant release-input state versus HEAD: (?P<state>\S+)$"
)
CERTIFICATE_RECEIPT_MARKER = "CERTIFICATE CHECKSUM CONSISTENT"
FULL_AUDIT_MARKER = "PASS all 16 release checks"
MASTER_VERDICT_MARKER = "MASTER NOTEBOOK VERDICT"
CERTIFICATE_FINGERPRINT_RE = re.compile(
    r"\bSHA\s*[-\N{HYPHEN}\N{NON-BREAKING HYPHEN}\N{EN DASH}\N{EM DASH}]?\s*256\b"
    r"\s*(?P<head>[0-9a-f]{16})\s*"
    r"(?:\N{HORIZONTAL ELLIPSIS}|\N{MIDLINE HORIZONTAL ELLIPSIS}|\.{3})\s*"
    r"(?P<tail>[0-9a-f]{8})\b",
    re.IGNORECASE,
)
CERTIFICATE_VERDICT_RE = re.compile(
    r"\bDeterministic certificate\s+"
    r"(?P<status>REPRODUCED|CHECKSUM ONLY)\b",
    re.IGNORECASE,
)
CELL_ID_RE = re.compile(r"^[A-Za-z0-9_-]{1,64}$")
REQUIRED_OUTPUT_MARKERS = (
    PROVENANCE_RECEIPT_MARKER,
    "RELEASE INPUT SHA-256",
    "Execution commit binding:",
    "Canonical release binding:",
    PINNED_COLAB_REF,
    "E6 extremal-incidence verification passed",
    "Independent R8 verification passed",
    FULL_AUDIT_MARKER,
    "CERTIFICATE CHECKSUM CONSISTENT",
    MASTER_VERDICT_MARKER,
)


def is_release_input_path(relative_path: str) -> bool:
    """Return whether a repository-relative path belongs to the release bundle."""

    path = PurePosixPath(relative_path)
    if path.is_absolute() or ".." in path.parts:
        return False
    normalized = path.as_posix()
    if normalized in RELEASE_INPUT_EXCLUDED_FILES:
        return False
    # Ignore only named desktop/build by-products, never arbitrary .gitignore
    # patterns: adding an ignore rule must not hide a changed source file.
    if path.name == ".DS_Store" or normalized in {
        "paper/paper.aux",
        "paper/paper.fdb_latexmk",
        "paper/paper.fls",
        "paper/paper.log",
        "paper/paper.out",
        "paper/paper.synctex.gz",
        "paper/paper.toc",
    }:
        return False
    if any(part in RELEASE_INPUT_EXCLUDED_DIRECTORY_NAMES for part in path.parts):
        return False
    if normalized in RELEASE_INPUT_ROOT_FILES:
        return True
    return any(
        path.parts[: len(root.parts)] == root.parts
        for root in map(PurePosixPath, RELEASE_INPUT_ROOT_DIRECTORIES)
    )


def release_input_files(repo_root: Path) -> list[tuple[str, Path]]:
    """Enumerate the explicit release-input allowlist deterministically."""

    selected: dict[str, Path] = {}

    def add_file(path: Path) -> None:
        relative = path.relative_to(repo_root).as_posix()
        if not is_release_input_path(relative):
            return
        if path.is_symlink():
            raise RuntimeError(f"release input must not be a symlink: {relative}")
        if not path.is_file():
            raise RuntimeError(f"release input is not a regular file: {relative}")
        selected[relative] = path

    def visit(directory: Path) -> None:
        relative = directory.relative_to(repo_root).as_posix()
        if directory.is_symlink():
            raise RuntimeError(f"release input directory must not be a symlink: {relative}")
        if not directory.is_dir():
            raise RuntimeError(f"required release-input directory is missing: {relative}")
        for child in sorted(directory.iterdir(), key=lambda item: item.name):
            child_relative = child.relative_to(repo_root).as_posix()
            if child_relative in RELEASE_INPUT_EXCLUDED_FILES:
                continue
            if child.is_dir() and child.name in RELEASE_INPUT_EXCLUDED_DIRECTORY_NAMES:
                continue
            if child.is_dir():
                visit(child)
            else:
                add_file(child)

    for relative in RELEASE_INPUT_ROOT_FILES:
        if relative in RELEASE_INPUT_EXCLUDED_FILES:
            continue
        path = repo_root / relative
        if not path.exists():
            raise RuntimeError(f"required release input is missing: {relative}")
        add_file(path)
    for relative in RELEASE_INPUT_ROOT_DIRECTORIES:
        visit(repo_root / relative)

    if not selected:
        raise RuntimeError("release-input allowlist selected no files")
    return sorted(selected.items())


def release_input_digest(repo_root: Path) -> str:
    """Hash release-input paths and bytes using a length-delimited manifest."""

    digest = sha256(RELEASE_INPUT_DIGEST_DOMAIN)
    for relative, path in release_input_files(repo_root):
        name = relative.encode("utf-8")
        content = path.read_bytes()
        digest.update(len(name).to_bytes(8, "big"))
        digest.update(name)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def valid_nonzero_hex(value: str, length: int) -> bool:
    """Recognize a lowercase, fixed-width, nonzero hexadecimal identifier."""

    return re.fullmatch(rf"[0-9a-f]{{{length}}}", value) is not None and int(value, 16) != 0


def normalize_optional_commit_sha(name: str, value: str | None) -> str | None:
    """Normalize an optional full commit SHA and reject malformed values."""

    if value is None or not value.strip():
        return None
    normalized = value.strip().lower()
    if not valid_nonzero_hex(normalized, 40):
        raise ValueError(f"{name} must be a nonzero, full 40-hex commit SHA")
    return normalized


def select_expected_commit(
    github_sha: str | None, expected_sha: str | None
) -> tuple[str | None, str]:
    """Select one trusted expected commit and identify its provenance basis."""

    github = normalize_optional_commit_sha("GITHUB_SHA", github_sha)
    expected = normalize_optional_commit_sha("EXPECTED_COMMIT_SHA", expected_sha)
    if github is not None and expected is not None:
        if github != expected:
            raise ValueError("GITHUB_SHA and EXPECTED_COMMIT_SHA disagree")
        return github, "HEAD_EQUALS_BOTH"
    if github is not None:
        return github, "HEAD_EQUALS_GITHUB_SHA"
    if expected is not None:
        return expected, "HEAD_EQUALS_EXPECTED_SHA"
    return None, "NO_EXPECTED_SHA"


def classify_commit_binding(
    *,
    mode: str,
    source_commit: str | None,
    local_head: str | None,
    relevant_state: str,
    github_sha: str | None,
    expected_sha: str | None,
) -> tuple[str, str, str]:
    """Classify execution-commit binding independently from release identity."""

    target, expected_basis = select_expected_commit(github_sha, expected_sha)
    target_value = target or "not-supplied"
    if mode == "colab-archive":
        commit = normalize_optional_commit_sha(
            "downloaded source commit", source_commit
        )
        if commit is None:
            raise ValueError("Colab execution has no downloaded source commit")
        if target is not None and target != commit:
            raise ValueError("expected commit differs from downloaded source commit")
        return "VERIFIED", "ARCHIVE_DOWNLOADED_BY_COMMIT_SHA", commit

    if mode == "local-tree":
        return "UNVERIFIED", "NO_GIT_METADATA", target_value
    if mode != "local-git":
        raise ValueError(f"unsupported source mode: {mode}")

    head = normalize_optional_commit_sha("local git HEAD", local_head)
    if head is None:
        raise ValueError("local-git mode has no usable HEAD")
    if target is not None and target != head:
        raise ValueError("expected commit differs from local git HEAD")
    if relevant_state == "DIRTY":
        return "UNVERIFIED", "DIRTY_RELEASE_INPUTS", target_value
    if relevant_state == "UNKNOWN":
        return "UNVERIFIED", "UNKNOWN_GIT_STATE", target_value
    if relevant_state != "CLEAN":
        raise ValueError(f"unsupported local release-input state: {relevant_state}")
    if target is None:
        return "UNVERIFIED", "NO_EXPECTED_SHA", "not-supplied"
    return "VERIFIED", expected_basis, target


def classify_canonical_release_binding(
    *,
    mode: str,
    resolved_tag_commit: str | None,
    identity_job_commit: str | None,
    commit_binding: str,
    commit_target: str,
) -> tuple[str, str, str]:
    """Classify canonical-tag identity separately from execution-commit binding."""

    if mode == "colab-archive":
        tag_commit = normalize_optional_commit_sha(
            "resolved release-tag commit", resolved_tag_commit
        )
        if tag_commit is None:
            raise ValueError("Colab execution has no resolved release-tag commit")
        if commit_binding != "VERIFIED" or commit_target != tag_commit:
            raise ValueError("Colab execution commit differs from resolved release tag")
        return "VERIFIED", "TAG_PEELED_VIA_GITHUB_API", tag_commit

    if mode == "local-tree":
        return "UNVERIFIED", "NO_GIT_METADATA", "not-supplied"
    if mode != "local-git":
        raise ValueError(f"unsupported source mode: {mode}")

    canonical = normalize_optional_commit_sha(
        "release-identity job commit", identity_job_commit
    )
    if canonical is None:
        return "UNVERIFIED", "NO_CANONICAL_TAG_RECEIPT", "not-supplied"
    if commit_binding != "VERIFIED":
        return "UNVERIFIED", "COMMIT_BINDING_UNVERIFIED", canonical
    if commit_target != canonical:
        raise ValueError(
            "execution commit differs from the release-identity job commit"
        )
    return "VERIFIED", "CI_THREE_WAY_IDENTITY", canonical


def peel_github_tag_payload(
    tag_name: str, ref_payload: object, tag_payload: object | None = None
) -> str:
    """Return the commit named by a validated lightweight or annotated tag."""

    expected_ref = f"refs/tags/{tag_name}"
    if not isinstance(ref_payload, dict) or ref_payload.get("ref") != expected_ref:
        raise ValueError("GitHub returned the wrong tag reference")
    ref_object = ref_payload.get("object")
    if not isinstance(ref_object, dict):
        raise ValueError("GitHub tag reference has no object")
    object_type = ref_object.get("type")
    object_sha = ref_object.get("sha")
    if not isinstance(object_sha, str) or not valid_nonzero_hex(object_sha, 40):
        raise ValueError("GitHub tag reference has an invalid object SHA")
    if object_type == "commit":
        return object_sha
    if object_type != "tag":
        raise ValueError("release tag does not target a commit or annotated tag")
    if not isinstance(tag_payload, dict) or tag_payload.get("sha") != object_sha:
        raise ValueError("GitHub returned the wrong annotated-tag object")
    target = tag_payload.get("object")
    if not isinstance(target, dict) or target.get("type") != "commit":
        raise ValueError("annotated release tag does not target a commit")
    commit = target.get("sha")
    if not isinstance(commit, str) or not valid_nonzero_hex(commit, 40):
        raise ValueError("annotated release tag has an invalid commit SHA")
    return commit


def git_repository_root(repo_root: Path) -> Path | None:
    """Return the Git top level only when it is exactly the supplied root."""

    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=repo_root,
            text=True,
            capture_output=True,
            check=False,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if result.returncode != 0:
        return None
    try:
        discovered = Path(result.stdout.strip()).resolve()
    except (OSError, RuntimeError):
        return None
    expected = repo_root.resolve()
    return discovered if discovered == expected else None


def local_git_head(repo_root: Path) -> str | None:
    """Return the full commit at local HEAD for provenance binding."""

    if git_repository_root(repo_root) is None:
        return None
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--verify", "HEAD^{commit}"],
            cwd=repo_root,
            text=True,
            capture_output=True,
            check=False,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    revision = result.stdout.strip().lower()
    return revision if result.returncode == 0 and valid_nonzero_hex(revision, 40) else None


def relevant_input_state(repo_root: Path) -> str:
    """Compare every allowlisted path and byte directly with the HEAD tree."""

    if local_git_head(repo_root) is None:
        return "UNKNOWN"
    try:
        result = subprocess.run(
            ["git", "ls-tree", "-r", "-z", "--full-tree", "HEAD"],
            cwd=repo_root,
            capture_output=True,
            check=False,
            timeout=20,
        )
    except (OSError, UnicodeDecodeError, subprocess.TimeoutExpired):
        return "UNKNOWN"
    if result.returncode != 0:
        return "UNKNOWN"

    head_blobs: dict[str, str] = {}
    for record in result.stdout.split(b"\0"):
        if not record:
            continue
        metadata, separator, raw_path = record.partition(b"\t")
        fields = metadata.split(b" ")
        if not separator or len(fields) != 3:
            return "UNKNOWN"
        relative = raw_path.decode("utf-8", errors="surrogateescape")
        if is_release_input_path(relative):
            if fields[1] != b"blob":
                return "UNKNOWN"
            try:
                object_id = fields[2].decode("ascii", errors="strict")
            except UnicodeDecodeError:
                return "UNKNOWN"
            head_blobs[relative] = object_id

    current_files = dict(release_input_files(repo_root))
    if set(current_files) != set(head_blobs):
        return "DIRTY"
    for relative, path in current_files.items():
        try:
            blob = subprocess.run(
                ["git", "cat-file", "blob", head_blobs[relative]],
                cwd=repo_root,
                capture_output=True,
                check=False,
                timeout=10,
            )
            if blob.returncode != 0:
                return "UNKNOWN"
            if path.is_symlink() or blob.stdout != path.read_bytes():
                return "DIRTY"
        except (OSError, subprocess.TimeoutExpired):
            return "UNKNOWN"
    return "CLEAN"


def format_provenance_receipt(
    *,
    mode: str,
    release_digest: str,
    commit_binding: str,
    commit_basis: str,
    commit_target: str,
    release_binding: str,
    release_basis: str,
    release_target: str,
    tag_commit: str,
    archive_digest: str,
    local_head: str,
    relevant_state: str,
) -> str:
    """Create the stable visible provenance receipt consumed by the checker."""

    return "\n".join(
        (
            PROVENANCE_RECEIPT_MARKER,
            f"Source mode: {mode}",
            f"Pinned Colab ref: {PINNED_COLAB_REF}",
            "Content binding: VERIFIED",
            f"RELEASE INPUT SHA-256: {release_digest}",
            f"Execution commit binding: {commit_binding}",
            f"Execution commit basis: {commit_basis}",
            f"Execution commit target: {commit_target}",
            f"Canonical release binding: {release_binding}",
            f"Canonical release basis: {release_basis}",
            f"Canonical release target: {release_target}",
            f"Canonical tag commit receipt: {tag_commit}",
            f"Source archive SHA-256: {archive_digest}",
            f"Local git HEAD: {local_head}",
            f"Relevant release-input state versus HEAD: {relevant_state}",
        )
    )


class SafeGitHubAPIRedirectHandler(HTTPRedirectHandler):
    """Accept only direct GitHub API responses; never forward bearer auth."""

    API_HOST = "api.github.com"
    API_AUTHORITIES = frozenset({API_HOST, f"{API_HOST}:443"})

    @classmethod
    def require_api_url(cls, url: str) -> None:
        if any(ord(character) < 32 or ord(character) == 127 for character in url):
            raise RuntimeError("Refusing an invalid GitHub API URL.")
        try:
            parsed = urlparse(url)
        except ValueError as error:
            raise RuntimeError("Refusing an invalid GitHub API URL.") from error
        if (
            parsed.scheme != "https"
            or parsed.netloc.lower() not in cls.API_AUTHORITIES
            or parsed.fragment
        ):
            raise RuntimeError("Refusing a non-GitHub API URL.")

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        self.require_api_url(req.full_url)
        raise RuntimeError(
            "GitHub API redirected unexpectedly; refusing to resend credentials."
        )


class SafeGitHubArchiveRedirectHandler(HTTPRedirectHandler):
    """Allow only GitHub's HTTPS archive redirect and public request headers."""

    ARCHIVE_HOST = "codeload.github.com"
    ARCHIVE_AUTHORITIES = frozenset({ARCHIVE_HOST, f"{ARCHIVE_HOST}:443"})
    REDIRECT_HEADER_ALLOWLIST = frozenset({"user-agent"})

    @classmethod
    def require_archive_url(cls, url: str) -> None:
        if any(ord(character) < 32 or ord(character) == 127 for character in url):
            raise RuntimeError("Refusing an invalid GitHub archive URL.")
        try:
            parsed = urlparse(url)
        except ValueError as error:
            raise RuntimeError("Refusing an invalid GitHub archive URL.") from error
        if (
            parsed.scheme != "https"
            or parsed.netloc.lower() not in cls.ARCHIVE_AUTHORITIES
            or parsed.fragment
        ):
            raise RuntimeError("Refusing an unexpected GitHub archive URL.")

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        SafeGitHubAPIRedirectHandler.require_api_url(req.full_url)
        self.require_archive_url(newurl)
        redirected = super().redirect_request(req, fp, code, msg, headers, newurl)
        if redirected is not None:
            for header_name in tuple(redirected.headers) + tuple(
                redirected.unredirected_hdrs
            ):
                if header_name.lower() not in self.REDIRECT_HEADER_ALLOWLIST:
                    redirected.remove_header(header_name)
        return redirected


class VisibleHTMLParser(HTMLParser):
    """Collect rendered text while excluding non-visible HTML element content."""

    NON_VISIBLE_ELEMENTS = frozenset({"head", "script", "style", "template"})
    VOID_ELEMENTS = frozenset(
        {
            "area",
            "base",
            "br",
            "col",
            "embed",
            "hr",
            "img",
            "input",
            "link",
            "meta",
            "param",
            "source",
            "track",
            "wbr",
        }
    )

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self._hidden_depth = 0

    @classmethod
    def _is_hidden(
        cls, tag: str, attrs: list[tuple[str, str | None]]
    ) -> bool:
        attributes = {name.lower(): value for name, value in attrs}
        style = "".join((attributes.get("style") or "").lower().split())
        return (
            tag in cls.NON_VISIBLE_ELEMENTS
            or "hidden" in attributes
            or attributes.get("aria-hidden", "").lower() == "true"
            or "display:none" in style
            or "visibility:hidden" in style
        )

    def handle_starttag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        tag = tag.lower()
        hidden = self._is_hidden(tag, attrs)
        if self._hidden_depth or hidden:
            if tag not in self.VOID_ELEMENTS:
                self._hidden_depth += 1
        elif tag in {"br", "hr"}:
            self.parts.append("\n")

    def handle_startendtag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        if self._hidden_depth:
            return
        tag = tag.lower()
        if not self._is_hidden(tag, attrs) and tag in {"br", "hr"}:
            self.parts.append("\n")

    def handle_endtag(self, tag: str) -> None:
        if self._hidden_depth:
            self._hidden_depth -= 1
        elif tag.lower() in {"div", "p", "table", "tr", "li"}:
            self.parts.append("\n")

    def handle_data(self, data: str) -> None:
        if not self._hidden_depth:
            self.parts.append(data)


def load(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def source_surface(notebook: dict) -> dict:
    """Retain authored content while discarding execution-only notebook state."""

    cells = []
    for cell in notebook.get("cells", []):
        source = cell.get("source", "")
        if isinstance(source, list):
            source = "".join(source)
        tags = cell.get("metadata", {}).get("tags", [])
        cells.append(
            {
                "cell_type": cell.get("cell_type"),
                "id": cell.get("id"),
                "source": source,
                "tags": tags,
            }
        )

    metadata = notebook.get("metadata", {})
    language = metadata.get("language_info", {})
    return {
        "cells": cells,
        "metadata": {
            "colab": metadata.get("colab", {}),
            "kernelspec": metadata.get("kernelspec", {}),
            "language_info": {
                "name": language.get("name"),
            },
        },
        "nbformat": notebook.get("nbformat"),
        "nbformat_minor": notebook.get("nbformat_minor"),
    }


def check_cell_ids(notebook: dict) -> list[str]:
    """Require stable, unique nbformat 4.5 cell identifiers."""

    identifiers = [cell.get("id") for cell in notebook.get("cells", [])]
    failures: list[str] = []
    invalid = [
        index
        for index, identifier in enumerate(identifiers, start=1)
        if not isinstance(identifier, str) or CELL_ID_RE.fullmatch(identifier) is None
    ]
    if invalid:
        failures.append(f"notebook cells have missing or invalid IDs: {invalid}")
    duplicates = sorted(
        {
            identifier
            for identifier in identifiers
            if isinstance(identifier, str) and identifiers.count(identifier) > 1
        }
    )
    if duplicates:
        failures.append("notebook cell IDs are not unique: " + ", ".join(duplicates))
    return failures


def output_value_text(value: object) -> str:
    """Flatten a notebook output value without depending on nbformat helpers."""

    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, list):
        return "".join(output_value_text(item) for item in value)
    if isinstance(value, dict):
        return "\n".join(output_value_text(item) for item in value.values())
    return str(value)


def output_text(output: dict) -> str:
    """Extract searchable text from stream and rich notebook outputs."""

    output_type = output.get("output_type")
    if output_type == "stream":
        return output_value_text(output.get("text"))
    if output_type not in {"display_data", "execute_result"}:
        return ""

    data = output.get("data", {})
    if not isinstance(data, dict):
        return output_value_text(data)

    text_parts = []
    for mime_type, value in data.items():
        if mime_type.startswith(("image/", "audio/", "video/")):
            continue
        text_parts.append(output_value_text(value))
    return "\n".join(text_parts)


def normalized_text(value: str) -> str:
    """Ignore presentation whitespace while retaining substantive output text."""

    return " ".join(value.split())


def visible_output_text(output: dict) -> str:
    """Extract visible text from one executed output, including rich HTML."""

    output_type = output.get("output_type")
    if output_type == "stream":
        return normalized_text(output_value_text(output.get("text")))
    if output_type not in {"display_data", "execute_result"}:
        return ""

    data = output.get("data", {})
    if not isinstance(data, dict):
        return normalized_text(output_value_text(data))

    # Jupyter normally stores a rich HTML representation together with a
    # ``text/plain`` fallback such as ``<IPython.core.display.HTML object>``.
    # Only one representation is rendered.  Prefer HTML when present so the
    # fallback cannot corrupt a strict receipt parse or count as extra visible
    # text.
    if "text/html" in data:
        parser = VisibleHTMLParser()
        parser.feed(output_value_text(data["text/html"]))
        parser.close()
        return normalized_text(" ".join(parser.parts))

    visible_parts: list[str] = []
    for mime_type, value in data.items():
        rendered = output_value_text(value)
        if mime_type.startswith("text/"):
            visible_parts.append(rendered)
    return normalized_text("\n".join(visible_parts))


def embedded_release_input_digest(notebook: dict) -> tuple[str | None, list[str]]:
    """Read the single literal EXPECTED_RELEASE_INPUT_SHA256 assignment."""

    values: list[object] = []
    for index, cell in enumerate(notebook.get("cells", []), start=1):
        if cell.get("cell_type") != "code":
            continue
        source = cell.get("source", "")
        if isinstance(source, list):
            source = "".join(source)
        try:
            tree = ast.parse(str(source), filename=f"notebook-cell-{index}")
        except SyntaxError:
            continue
        for statement in tree.body:
            if isinstance(statement, ast.Assign) and any(
                isinstance(target, ast.Name)
                and target.id == "EXPECTED_RELEASE_INPUT_SHA256"
                for target in statement.targets
            ):
                values.append(
                    statement.value.value
                    if isinstance(statement.value, ast.Constant)
                    else None
                )
            elif (
                isinstance(statement, ast.AnnAssign)
                and isinstance(statement.target, ast.Name)
                and statement.target.id == "EXPECTED_RELEASE_INPUT_SHA256"
            ):
                values.append(
                    statement.value.value
                    if isinstance(statement.value, ast.Constant)
                    else None
                )

    if len(values) != 1:
        return None, [
            "notebook must contain exactly one literal "
            f"EXPECTED_RELEASE_INPUT_SHA256 assignment; found {len(values)}"
        ]
    value = values[0]
    if not isinstance(value, str) or not valid_nonzero_hex(value, 64):
        return None, ["embedded release-input digest is not a nonzero 64-hex SHA-256"]
    return value, []


def check_release_input_provenance(
    notebook: dict,
    embedded_digest: str,
    fresh_digest: str,
    *,
    require_verified_commit: bool = False,
    require_verified_release: bool = False,
    expected_commit_sha: str | None = None,
    expected_release_sha: str | None = None,
    validator_root: Path = ROOT,
) -> list[str]:
    """Validate exactly one visible, content-bound provenance receipt."""

    receipt_outputs: list[str] = []
    marker_count = 0
    for cell in notebook.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for output in cell.get("outputs", []):
            rendered = visible_output_text(output)
            count = rendered.count(PROVENANCE_RECEIPT_MARKER)
            marker_count += count
            if count:
                receipt_outputs.append(rendered)
    if marker_count != 1 or len(receipt_outputs) != 1:
        return [
            "notebook must contain exactly one visible release-input provenance "
            f"receipt; found {marker_count}"
        ]

    match = PROVENANCE_RECEIPT_RE.fullmatch(receipt_outputs[0])
    if match is None:
        return ["release-input provenance receipt has an invalid structure"]

    fields = match.groupdict()
    failures: list[str] = []
    release_digest = fields["release"]
    if not valid_nonzero_hex(release_digest, 64):
        failures.append("receipt release-input digest is not a nonzero 64-hex SHA-256")
    if release_digest != embedded_digest:
        failures.append("receipt release-input digest differs from the embedded digest")
    if release_digest != fresh_digest:
        failures.append("receipt release-input digest differs from the current repository")
    if fields["ref"] != PINNED_COLAB_REF:
        failures.append(
            f"receipt Colab ref is {fields['ref']!r}, expected {PINNED_COLAB_REF!r}"
        )

    try:
        expected_commit = normalize_optional_commit_sha(
            "expected validator commit", expected_commit_sha
        )
    except ValueError as error:
        failures.append(str(error))
        expected_commit = None
    try:
        expected_release = normalize_optional_commit_sha(
            "expected canonical release commit", expected_release_sha
        )
    except ValueError as error:
        failures.append(str(error))
        expected_release = None

    commit_binding = fields["commit_binding"]
    commit_basis = fields["commit_basis"]
    commit_target = fields["commit_target"]
    release_binding = fields["release_binding"]
    release_basis = fields["release_basis"]
    release_target = fields["release_target"]
    tag_commit = fields["tag_commit"]

    if commit_target != "not-supplied" and not valid_nonzero_hex(
        commit_target, 40
    ):
        failures.append("receipt execution target is not a nonzero 40-hex SHA")
    if release_target != "not-supplied" and not valid_nonzero_hex(
        release_target, 40
    ):
        failures.append("receipt release target is not a nonzero 40-hex SHA")
    if expected_commit is not None and commit_target != expected_commit:
        failures.append("receipt execution target differs from validator expectation")
    if expected_release is not None and release_target != expected_release:
        failures.append("receipt release target differs from validator expectation")
    if require_verified_commit and commit_binding != "VERIFIED":
        failures.append("strict validation requires VERIFIED execution binding")
    if require_verified_release and release_binding != "VERIFIED":
        failures.append("strict validation requires VERIFIED canonical release binding")

    if require_verified_commit or require_verified_release:
        actual_head = local_git_head(validator_root)
        actual_state = relevant_input_state(validator_root)
        if require_verified_commit:
            if expected_commit is None:
                failures.append("strict execution validation has no expected commit")
            elif actual_head != expected_commit:
                failures.append("validator checkout HEAD differs from expected commit")
        if require_verified_release:
            if expected_release is None:
                failures.append("strict release validation has no canonical commit")
            elif actual_head != expected_release:
                failures.append(
                    "validator checkout HEAD differs from canonical release commit"
                )
        if actual_state != "CLEAN":
            failures.append(
                "validator release inputs are not byte-identical to HEAD"
            )
        if fields["mode"] == "local-git":
            if fields["head"] != actual_head:
                failures.append("receipt HEAD differs from validator checkout HEAD")
            if fields["state"] != actual_state:
                failures.append("receipt input state differs from validator state")

    if fields["mode"] == "colab-archive":
        if not valid_nonzero_hex(tag_commit, 40):
            failures.append("claimed resolved tag commit is not a nonzero 40-hex SHA")
        if not valid_nonzero_hex(fields["archive"], 64):
            failures.append("claimed archive digest is not a nonzero 64-hex SHA-256")
        if fields["head"] != "not-applicable":
            failures.append("Colab receipt must mark local HEAD not-applicable")
        if fields["state"] != "not-applicable":
            failures.append("Colab receipt must mark local input state not-applicable")
        if commit_binding != "VERIFIED":
            failures.append("Colab execution commit must be verified")
        if commit_basis != "ARCHIVE_DOWNLOADED_BY_COMMIT_SHA":
            failures.append("Colab receipt has the wrong execution-commit basis")
        if commit_target != tag_commit:
            failures.append("Colab execution target differs from resolved tag commit")
        if release_binding != "VERIFIED":
            failures.append("Colab canonical release must be verified")
        if release_basis != "TAG_PEELED_VIA_GITHUB_API":
            failures.append("Colab receipt has the wrong canonical-release basis")
        if release_target != tag_commit:
            failures.append("Colab release target differs from resolved tag commit")
    elif fields["mode"] == "local-git":
        if fields["archive"] != "not-applicable":
            failures.append("local receipt must mark archive digest not-applicable")
        if not valid_nonzero_hex(fields["head"], 40):
            failures.append("claimed local HEAD is not a nonzero 40-hex SHA")
        if fields["state"] not in {"CLEAN", "DIRTY", "UNKNOWN"}:
            failures.append("local receipt has an invalid relevant-input state")
        if commit_binding == "VERIFIED":
            if commit_basis not in {
                "HEAD_EQUALS_GITHUB_SHA",
                "HEAD_EQUALS_EXPECTED_SHA",
                "HEAD_EQUALS_BOTH",
            }:
                failures.append("verified local receipt has the wrong commit basis")
            if fields["state"] != "CLEAN":
                failures.append("verified local receipt has non-clean release inputs")
            if commit_target != fields["head"]:
                failures.append("verified execution target differs from local HEAD")
        elif commit_basis == "NO_EXPECTED_SHA":
            if commit_target != "not-supplied" or fields["state"] != "CLEAN":
                failures.append("NO_EXPECTED_SHA receipt has inconsistent fields")
        elif commit_basis == "DIRTY_RELEASE_INPUTS":
            if fields["state"] != "DIRTY":
                failures.append("DIRTY_RELEASE_INPUTS receipt is not dirty")
        elif commit_basis == "UNKNOWN_GIT_STATE":
            if fields["state"] != "UNKNOWN":
                failures.append("UNKNOWN_GIT_STATE receipt has a known state")
        else:
            failures.append("unverified local receipt has the wrong commit basis")

        if release_binding == "VERIFIED":
            if release_basis != "CI_THREE_WAY_IDENTITY":
                failures.append("verified release has the wrong identity basis")
            if not valid_nonzero_hex(tag_commit, 40):
                failures.append("verified release has no canonical tag commit receipt")
            if not (
                release_target
                == tag_commit
                == fields["head"]
                == commit_target
            ):
                failures.append("verified release identities do not resolve together")
            if commit_binding != "VERIFIED":
                failures.append("verified release has an unverified execution commit")
        elif release_basis == "NO_CANONICAL_TAG_RECEIPT":
            if release_target != "not-supplied" or tag_commit != "not-supplied":
                failures.append("missing-tag receipt contains a release target")
        elif release_basis == "COMMIT_BINDING_UNVERIFIED":
            if not valid_nonzero_hex(tag_commit, 40) or release_target != tag_commit:
                failures.append("unverified execution has an invalid tag receipt")
            if commit_binding == "VERIFIED":
                failures.append("verified execution uses an unverified-commit basis")
        else:
            failures.append("unverified local receipt has the wrong release basis")
    else:
        if tag_commit != "not-supplied":
            failures.append("local-tree receipt must have no tag commit receipt")
        if fields["archive"] != "not-applicable":
            failures.append("local-tree receipt must mark archive digest not-applicable")
        if fields["head"] != "unavailable":
            failures.append("local-tree receipt must mark local HEAD unavailable")
        if fields["state"] != "UNKNOWN":
            failures.append("local-tree receipt must mark input state UNKNOWN")
        if (
            commit_binding != "UNVERIFIED"
            or commit_basis != "NO_GIT_METADATA"
            or commit_target != "not-supplied"
        ):
            failures.append("local-tree receipt must have unverified execution binding")
        if (
            release_binding != "UNVERIFIED"
            or release_basis != "NO_GIT_METADATA"
            or release_target != "not-supplied"
        ):
            failures.append("local-tree receipt must have unverified release binding")
    return failures


def check_source_only_state(notebook: dict) -> list[str]:
    """Require the canonical/source notebook to contain no execution state."""

    failures: list[str] = []
    executed = []
    output_cells = []
    for index, cell in enumerate(notebook.get("cells", []), start=1):
        if cell.get("cell_type") != "code":
            continue
        if cell.get("execution_count") is not None:
            executed.append(index)
        if cell.get("outputs", []):
            output_cells.append(index)
    if executed:
        failures.append(f"source-only notebook has execution counts in cells: {executed}")
    if output_cells:
        failures.append(f"source-only notebook has outputs in cells: {output_cells}")
    return failures


def expected_certificate_fingerprint() -> str:
    """Return the notebook's 16-head/8-tail rendering of the certificate hash."""

    digest = sha256(CERTIFICATE.read_bytes()).hexdigest()
    return f"{digest[:16]}\N{HORIZONTAL ELLIPSIS}{digest[-8:]}"


def check_certificate_output_provenance(notebook: dict) -> list[str]:
    """Validate the visible certificate receipt against the current certificate."""

    receipt_texts = []
    for cell in notebook.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for output in cell.get("outputs", []):
            rendered = visible_output_text(output)
            if CERTIFICATE_RECEIPT_MARKER in rendered:
                receipt_texts.append(rendered)

    if not receipt_texts:
        return [
            "notebook has no visible CERTIFICATE CHECKSUM CONSISTENT "
            "receipt output"
        ]

    expected = expected_certificate_fingerprint()
    found = {
        f"{match.group('head').lower()}\N{HORIZONTAL ELLIPSIS}"
        f"{match.group('tail').lower()}"
        for rendered in receipt_texts
        for match in CERTIFICATE_FINGERPRINT_RE.finditer(rendered)
    }
    if not found:
        return [
            "notebook certificate receipt is missing its visible "
            "SHA-256 fingerprint"
        ]
    if len(found) > 1:
        return [
            "notebook certificate receipts contain conflicting "
            f"fingerprints: expected {expected}, found {', '.join(sorted(found))}"
        ]
    if found != {expected}:
        return [
            "notebook certificate fingerprint is stale: "
            f"expected {expected}, found {next(iter(found))}"
        ]
    return []


def check_certificate_verdict(notebook: dict) -> list[str]:
    """Ensure the final certificate label reflects whether regeneration passed."""

    rendered_outputs = [
        visible_output_text(output)
        for cell in notebook.get("cells", [])
        if cell.get("cell_type") == "code"
        for output in cell.get("outputs", [])
    ]
    audit_passed = any(FULL_AUDIT_MARKER in text for text in rendered_outputs)
    verdict_outputs = [
        text for text in rendered_outputs if MASTER_VERDICT_MARKER in text
    ]
    if not verdict_outputs:
        return ["notebook has no visible master-verdict output"]

    statuses = {
        match.group("status").upper()
        for rendered in verdict_outputs
        for match in CERTIFICATE_VERDICT_RE.finditer(rendered)
    }
    expected = "REPRODUCED" if audit_passed else "CHECKSUM ONLY"
    if not statuses:
        return [
            "master verdict has no deterministic-certificate provenance label"
        ]
    if statuses != {expected}:
        found = ", ".join(sorted(statuses))
        return [
            "master verdict misstates deterministic-certificate provenance: "
            f"expected {expected}, found {found}"
        ]
    return []


def check_output_integrity(
    notebook: dict,
    *,
    require_verified_commit: bool = False,
    require_verified_release: bool = False,
    expected_commit_sha: str | None = None,
    expected_release_sha: str | None = None,
) -> list[str]:
    """Return stable execution/output integrity failures for an executed notebook."""

    code_cells = [
        (index, cell)
        for index, cell in enumerate(notebook.get("cells", []), start=1)
        if cell.get("cell_type") == "code"
    ]
    if not code_cells:
        return ["notebook contains no code cells"]

    failures: list[str] = []
    execution_counts = [cell.get("execution_count") for _, cell in code_cells]
    expected_counts = list(range(1, len(code_cells) + 1))
    if (
        any(type(count) is not int for count in execution_counts)
        or execution_counts != expected_counts
    ):
        failures.append(
            "code-cell execution counts are not sequential and non-null: "
            f"expected {expected_counts}, found {execution_counts}"
        )

    missing_outputs = [
        index for index, cell in code_cells if not cell.get("outputs", [])
    ]
    if missing_outputs:
        failures.append(f"code cells have no outputs: {missing_outputs}")

    error_outputs = [
        index
        for index, cell in code_cells
        if any(
            output.get("output_type") == "error"
            for output in cell.get("outputs", [])
        )
    ]
    if error_outputs:
        failures.append(f"code cells contain error outputs: {error_outputs}")

    searchable_output = normalized_text(
        "\n".join(
            output_text(output)
            for _, cell in code_cells
            for output in cell.get("outputs", [])
        )
    )
    missing_markers = [
        marker
        for marker in REQUIRED_OUTPUT_MARKERS
        if normalized_text(marker) not in searchable_output
    ]
    if missing_markers:
        failures.append(
            "notebook outputs are missing substantive verdict markers: "
            + ", ".join(repr(marker) for marker in missing_markers)
        )

    embedded_digest, embedded_failures = embedded_release_input_digest(notebook)
    failures.extend(embedded_failures)
    if embedded_digest is not None:
        failures.extend(
            check_release_input_provenance(
                notebook,
                embedded_digest,
                release_input_digest(ROOT),
                require_verified_commit=require_verified_commit,
                require_verified_release=require_verified_release,
                expected_commit_sha=expected_commit_sha,
                expected_release_sha=expected_release_sha,
            )
        )
    failures.extend(check_certificate_output_provenance(notebook))
    failures.extend(check_certificate_verdict(notebook))

    return failures


def run_self_tests() -> int:
    """Run lightweight adversarial tests without executing the notebook."""

    def require_test(condition: bool, message: str) -> None:
        if not condition:
            raise RuntimeError(message)

    def require_bound_safe_opener(
        function: ast.FunctionDef,
        handler_name: str,
        label: str,
        *,
        allowed_call_counts: dict[str, int] | None = None,
    ) -> None:
        forbidden_syntax = (
            ast.AsyncFor,
            ast.ClassDef,
            ast.For,
            ast.Global,
            ast.Import,
            ast.ImportFrom,
            ast.Lambda,
            ast.Match,
            ast.NamedExpr,
            ast.Nonlocal,
            ast.While,
        )
        require_test(
            not any(
                node is not function and isinstance(node, forbidden_syntax)
                for node in ast.walk(function)
            ),
            f"generated {label} uses forbidden dynamic or rebinding syntax",
        )

        safe_assignments = [
            statement
            for statement in function.body
            if (
                isinstance(statement, ast.Assign)
                and len(statement.targets) == 1
                and isinstance(statement.targets[0], ast.Name)
                and isinstance(statement.value, ast.Call)
                and isinstance(statement.value.func, ast.Name)
                and statement.value.func.id == "build_opener"
                and len(statement.value.args) == 1
                and not statement.value.keywords
                and isinstance(statement.value.args[0], ast.Call)
                and isinstance(statement.value.args[0].func, ast.Name)
                and statement.value.args[0].func.id == handler_name
                and not statement.value.args[0].args
                and not statement.value.args[0].keywords
            )
        ]
        require_test(
            len(safe_assignments) == 1,
            f"generated {label} must construct exactly one {handler_name} opener",
        )
        safe_assignment = safe_assignments[0]
        opener_target = safe_assignment.targets[0]
        require_test(
            isinstance(opener_target, ast.Name),
            f"generated {label} has an invalid opener target",
        )
        opener_name = opener_target.id

        bindings: list[tuple[str, ast.AST]] = []
        for node in ast.walk(function):
            if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
                bindings.append((node.id, node))
            elif isinstance(node, ast.arg):
                bindings.append((node.arg, node))
            elif isinstance(node, ast.ExceptHandler) and node.name is not None:
                bindings.append((node.name, node))
        require_test(
            [node for name, node in bindings if name == opener_name]
            == [opener_target],
            f"generated {label} reassigns its validated opener",
        )
        require_test(
            not any(
                name in {"Request", "build_opener", handler_name}
                for name, _ in bindings
            ),
            f"generated {label} locally rebinds a trusted opener symbol",
        )
        require_test(
            not any(
                isinstance(node, (ast.Attribute, ast.Subscript))
                and isinstance(node.ctx, (ast.Store, ast.Del))
                for node in ast.walk(function)
            ),
            f"generated {label} mutates an object used by the request path",
        )

        calls = [node for node in ast.walk(function) if isinstance(node, ast.Call)]

        def static_call_path(callable_node: ast.expr) -> str | None:
            if isinstance(callable_node, ast.Name):
                return callable_node.id
            if not isinstance(callable_node, ast.Attribute):
                return None
            prefix = static_call_path(callable_node.value)
            if prefix is not None:
                return f"{prefix}.{callable_node.attr}"
            if (
                callable_node.attr == "hexdigest"
                and isinstance(callable_node.value, ast.Call)
                and isinstance(callable_node.value.func, ast.Name)
                and callable_node.value.func.id == "sha256"
            ):
                return "sha256(...).hexdigest"
            return None

        if allowed_call_counts is not None:
            actual_call_counts: dict[str, int] = {}
            dynamic_calls = 0
            for call in calls:
                path = static_call_path(call.func)
                if path is None:
                    dynamic_calls += 1
                    continue
                actual_call_counts[path] = actual_call_counts.get(path, 0) + 1
            require_test(
                dynamic_calls == 0 and actual_call_counts == allowed_call_counts,
                f"generated {label} changed its exact call surface",
            )
        require_test(
            not any(
                isinstance(call.func, ast.Name)
                and call.func.id
                in {
                    "__import__",
                    "compile",
                    "delattr",
                    "eval",
                    "exec",
                    "getattr",
                    "globals",
                    "locals",
                    "setattr",
                    "vars",
                }
                for call in calls
            ),
            f"generated {label} uses a dynamic dispatch primitive",
        )
        build_calls = [
            call
            for call in calls
            if isinstance(call.func, ast.Name) and call.func.id == "build_opener"
        ]
        require_test(
            build_calls == [safe_assignment.value],
            f"generated {label} constructs an additional or unbound opener",
        )
        handler_calls = [
            call
            for call in calls
            if isinstance(call.func, ast.Name) and call.func.id == handler_name
        ]
        require_test(
            handler_calls == [safe_assignment.value.args[0]],
            f"generated {label} constructs an unbound redirect handler",
        )
        opener_calls = [
            call
            for call in calls
            if (
                isinstance(call.func, ast.Attribute)
                and call.func.attr == "open"
            )
        ]
        require_test(
            len(opener_calls) == 1
            and isinstance(opener_calls[0].func.value, ast.Name)
            and opener_calls[0].func.value.id == opener_name,
            f"generated {label} does not perform its sole request through "
            f"the {handler_name} opener",
        )
        open_call = opener_calls[0]
        network_tries = [
            (position, statement)
            for position, statement in enumerate(function.body)
            if (
                isinstance(statement, ast.Try)
                and any(
                    isinstance(child, ast.With)
                    and any(item.context_expr is open_call for item in child.items)
                    for child in statement.body
                )
            )
        ]
        require_test(
            len(network_tries) == 1,
            f"generated {label} request is not a live top-level context manager",
        )
        require_test(
            function.body.index(safe_assignment) + 1 == network_tries[0][0],
            f"generated {label} does not use its opener immediately",
        )

    valid_opener_function = ast.parse(
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    try:\n"
        "        with opener.open(request) as response:\n"
        "            return response.read()\n"
        "    except RuntimeError:\n"
        "        raise\n"
    ).body[0]
    require_test(
        isinstance(valid_opener_function, ast.FunctionDef),
        "opener binding fixture is not a function",
    )
    fixture_call_counts = {
        "SafeHandler": 1,
        "build_opener": 1,
        "opener.open": 1,
        "response.read": 1,
    }
    require_bound_safe_opener(
        valid_opener_function,
        "SafeHandler",
        "fixture",
        allowed_call_counts=fixture_call_counts,
    )
    for unsafe_source in (
        "def probe(request):\n"
        "    safe = build_opener(SafeHandler())\n"
        "    unsafe = build_opener()\n"
        "    try:\n"
        "        with unsafe.open(request):\n"
        "            return None\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    opener = build_opener()\n"
        "    try:\n"
        "        with opener.open(request):\n"
        "            return None\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    try:\n"
        "        with opener.open(request) as first:\n"
        "            return opener.open(request)\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    opener: object = build_opener()\n"
        "    try:\n"
        "        with opener.open(request):\n"
        "            return None\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    opener.open = unsafe_open\n"
        "    try:\n"
        "        with opener.open(request):\n"
        "            return None\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    if False:\n"
        "        try:\n"
        "            with opener.open(request):\n"
        "                return None\n"
        "        except RuntimeError:\n"
        "            raise\n"
        "    return getattr(build_opener(), 'open')(request)\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    if (opener := build_opener()):\n"
        "        return None\n"
        "    try:\n"
        "        with opener.open(request):\n"
        "            return None\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    for opener in []:\n"
        "        pass\n"
        "    try:\n"
        "        with opener.open(request):\n"
        "            return None\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    build_opener = unsafe_factory\n"
        "    opener = build_opener(SafeHandler())\n"
        "    try:\n"
        "        with opener.open(request):\n"
        "            return None\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    SafeHandler = UnsafeHandler\n"
        "    opener = build_opener(SafeHandler())\n"
        "    try:\n"
        "        with opener.open(request):\n"
        "            return None\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    match request:\n"
        "        case opener:\n"
        "            pass\n"
        "    try:\n"
        "        with opener.open(request) as response:\n"
        "            return response.read()\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    object.__setattr__(opener, 'open', unsafe_open)\n"
        "    try:\n"
        "        with opener.open(request) as response:\n"
        "            return response.read()\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    opener.__dict__.update({'open': unsafe_open})\n"
        "    try:\n"
        "        with opener.open(request) as response:\n"
        "            return response.read()\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    Request = UnsafeRequest\n"
        "    opener = build_opener(SafeHandler())\n"
        "    try:\n"
        "        with opener.open(request) as response:\n"
        "            return response.read()\n"
        "    except RuntimeError:\n"
        "        raise\n",
        "def probe(request):\n"
        "    opener = build_opener(SafeHandler())\n"
        "    mutate(opener)\n"
        "    try:\n"
        "        with opener.open(request) as response:\n"
        "            return response.read()\n"
        "    except RuntimeError:\n"
        "        raise\n",
    ):
        unsafe_function = ast.parse(unsafe_source).body[0]
        require_test(
            isinstance(unsafe_function, ast.FunctionDef),
            "unsafe opener fixture is not a function",
        )
        try:
            require_bound_safe_opener(
                unsafe_function,
                "SafeHandler",
                "fixture",
                allowed_call_counts=fixture_call_counts,
            )
        except RuntimeError:
            pass
        else:
            raise RuntimeError("unsafe opener binding fixture passed")

    fresh = release_input_digest(ROOT)
    selected_paths = {relative for relative, _ in release_input_files(ROOT)}
    require_test(
        "notebooks/build_master_notebook.py" in selected_paths,
        "notebook builder is missing from the release-input digest",
    )
    require_test(
        "Cubic_Anomaly_Master_Verification.ipynb" not in selected_paths,
        "generated notebook creates a release-input digest cycle",
    )
    require_test(
        "docs/AUDIT.md" not in selected_paths,
        "audit hash register creates a release-input digest cycle",
    )
    with tempfile.TemporaryDirectory(prefix="release-input-test-") as tmp:
        copied = Path(tmp) / "repo"
        for relative, source in release_input_files(ROOT):
            target = copied / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
        require_test(release_input_digest(copied) == fresh, "copied bundle digest changed")
        copied_builder = copied / "notebooks" / "build_master_notebook.py"
        builder_bytes = copied_builder.read_bytes()
        copied_builder.write_bytes(builder_bytes + b"\n# digest mutation\n")
        require_test(
            release_input_digest(copied) != fresh,
            "notebook builder mutation was missed",
        )
        copied_builder.write_bytes(builder_bytes)
        require_test(
            release_input_digest(copied) == fresh,
            "restored notebook builder changed the digest",
        )
        for relative in RELEASE_INPUT_EXCLUDED_FILES:
            target = copied / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text("excluded\n", encoding="utf-8")
        for relative in ("docs/build/x", "formal/cache/x", "verification/.git/x"):
            target = copied / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text("excluded\n", encoding="utf-8")
        require_test(release_input_digest(copied) == fresh, "exclusion changed digest")
        for relative in (
            "docs/.DS_Store", "paper/.DS_Store", "paper/paper.aux",
            "paper/paper.fdb_latexmk", "paper/paper.fls", "paper/paper.log",
            "paper/paper.out", "paper/paper.synctex.gz", "paper/paper.toc",
        ):
            (copied / relative).write_bytes(b"local by-product\n")
        require_test(
            release_input_digest(copied) == fresh,
            "desktop or TeX by-product invalidated the source digest",
        )
        new_source = copied / "paper" / "paper.aux.tex"
        new_source.write_text("new source\n", encoding="utf-8")
        require_test(
            release_input_digest(copied) != fresh,
            "by-product exclusion hid a new TeX source file",
        )
        new_source.unlink()
        (copied / "README.md").write_text("included mutation\n", encoding="utf-8")
        require_test(release_input_digest(copied) != fresh, "included mutation was missed")

    def wrapped(receipt: str, copies: int = 1) -> dict:
        return {"cells": [{"cell_type": "code", "outputs": [
            {"output_type": "stream", "name": "stdout", "text": receipt}
            for _ in range(copies)
        ]}]}

    verified = classify_commit_binding(
        mode="local-git", source_commit=None, local_head="1" * 40,
        relevant_state="CLEAN", github_sha="1" * 40, expected_sha=None,
    )
    require_test(
        verified == ("VERIFIED", "HEAD_EQUALS_GITHUB_SHA", "1" * 40),
        "clean GitHub revision binding was not verified",
    )
    unverified = classify_commit_binding(
        mode="local-git", source_commit=None, local_head="1" * 40,
        relevant_state="CLEAN", github_sha=None, expected_sha=None,
    )
    require_test(
        unverified == ("UNVERIFIED", "NO_EXPECTED_SHA", "not-supplied"),
        "unanchored local revision was not marked unverified",
    )
    dirty = classify_commit_binding(
        mode="local-git", source_commit=None, local_head="1" * 40,
        relevant_state="DIRTY", github_sha=None, expected_sha="1" * 40,
    )
    require_test(
        dirty == ("UNVERIFIED", "DIRTY_RELEASE_INPUTS", "1" * 40),
        "dirty release inputs were not marked unverified",
    )
    try:
        classify_commit_binding(
            mode="local-git", source_commit=None, local_head="1" * 40,
            relevant_state="CLEAN", github_sha="2" * 40,
            expected_sha="1" * 40,
        )
    except ValueError:
        pass
    else:
        raise RuntimeError("conflicting expected commits were accepted")

    no_tag_receipt = classify_canonical_release_binding(
        mode="local-git", resolved_tag_commit=None, identity_job_commit=None,
        commit_binding="VERIFIED", commit_target="1" * 40,
    )
    require_test(
        no_tag_receipt
        == ("UNVERIFIED", "NO_CANONICAL_TAG_RECEIPT", "not-supplied"),
        "local commit binding was mistaken for canonical release identity",
    )
    ci_release = classify_canonical_release_binding(
        mode="local-git", resolved_tag_commit=None,
        identity_job_commit="1" * 40, commit_binding="VERIFIED",
        commit_target="1" * 40,
    )
    require_test(
        ci_release == ("VERIFIED", "CI_THREE_WAY_IDENTITY", "1" * 40),
        "matching CI release identity was not verified",
    )
    dirty_release = classify_canonical_release_binding(
        mode="local-git", resolved_tag_commit=None,
        identity_job_commit="1" * 40, commit_binding="UNVERIFIED",
        commit_target="1" * 40,
    )
    require_test(
        dirty_release
        == ("UNVERIFIED", "COMMIT_BINDING_UNVERIFIED", "1" * 40),
        "canonical tag receipt hid an unverified execution commit",
    )
    colab_release = classify_canonical_release_binding(
        mode="colab-archive", resolved_tag_commit="1" * 40,
        identity_job_commit=None, commit_binding="VERIFIED",
        commit_target="1" * 40,
    )
    require_test(
        colab_release == ("VERIFIED", "TAG_PEELED_VIA_GITHUB_API", "1" * 40),
        "Colab tag identity was not verified",
    )
    for label, arguments in (
        (
            "mismatched CI identity",
            {
                "mode": "local-git",
                "resolved_tag_commit": None,
                "identity_job_commit": "2" * 40,
                "commit_binding": "VERIFIED",
                "commit_target": "1" * 40,
            },
        ),
        (
            "missing Colab tag identity",
            {
                "mode": "colab-archive",
                "resolved_tag_commit": None,
                "identity_job_commit": None,
                "commit_binding": "VERIFIED",
                "commit_target": "1" * 40,
            },
        ),
    ):
        try:
            classify_canonical_release_binding(**arguments)
        except ValueError:
            pass
        else:
            raise RuntimeError(f"{label} was accepted")

    lightweight_ref = {
        "ref": f"refs/tags/{PINNED_COLAB_REF}",
        "object": {"type": "commit", "sha": "3" * 40},
    }
    require_test(
        peel_github_tag_payload(PINNED_COLAB_REF, lightweight_ref) == "3" * 40,
        "lightweight tag did not peel to its commit",
    )
    annotated_ref = {
        "ref": f"refs/tags/{PINNED_COLAB_REF}",
        "object": {"type": "tag", "sha": "4" * 40},
    }
    annotated_tag = {
        "sha": "4" * 40,
        "object": {"type": "commit", "sha": "5" * 40},
    }
    require_test(
        peel_github_tag_payload(
            PINNED_COLAB_REF, annotated_ref, annotated_tag
        ) == "5" * 40,
        "annotated tag did not peel to its commit",
    )
    bad_target = {**annotated_tag, "object": {"type": "tree", "sha": "5" * 40}}
    try:
        peel_github_tag_payload(PINNED_COLAB_REF, annotated_ref, bad_target)
    except ValueError:
        pass
    else:
        raise RuntimeError("non-commit annotated tag target was accepted")

    local = format_provenance_receipt(
        mode="local-git", release_digest=fresh,
        commit_binding="VERIFIED", commit_basis="HEAD_EQUALS_EXPECTED_SHA",
        commit_target="1" * 40,
        release_binding="UNVERIFIED",
        release_basis="NO_CANONICAL_TAG_RECEIPT",
        release_target="not-supplied", tag_commit="not-supplied",
        archive_digest="not-applicable",
        local_head="1" * 40, relevant_state="CLEAN",
    )
    require_test(not check_release_input_provenance(
        wrapped(local), fresh, fresh),
                 "valid local receipt failed")
    rich_local = {"cells": [{"cell_type": "code", "outputs": [{
        "output_type": "display_data",
        "data": {
            "text/html": f"<pre>{local}</pre>",
            "text/plain": "<IPython.core.display.HTML object>",
        },
        "metadata": {},
    }]}]}
    require_test(not check_release_input_provenance(
        rich_local, fresh, fresh),
        "valid rich Jupyter receipt failed")
    require_test(check_release_input_provenance(wrapped(local, 2), fresh, fresh),
                 "duplicate receipt passed")
    require_test(check_release_input_provenance(
        wrapped(local.replace(fresh, "0" * 64)), fresh, fresh),
        "zero content digest passed")
    require_test(check_release_input_provenance(
        wrapped(local), fresh, fresh, require_verified_release=True,
        expected_release_sha="1" * 40),
        "strict release validation accepted a missing canonical-tag receipt")
    ci_local = format_provenance_receipt(
        mode="local-git", release_digest=fresh,
        commit_binding="VERIFIED", commit_basis="HEAD_EQUALS_BOTH",
        commit_target="1" * 40,
        release_binding="VERIFIED", release_basis="CI_THREE_WAY_IDENTITY",
        release_target="1" * 40, tag_commit="1" * 40,
        archive_digest="not-applicable", local_head="1" * 40,
        relevant_state="CLEAN",
    )
    require_test(not check_release_input_provenance(
        wrapped(ci_local), fresh, fresh), "valid CI release receipt failed")
    require_test(check_release_input_provenance(
        wrapped(ci_local.replace(
            "Canonical release target: " + "1" * 40,
            "Canonical release target: " + "2" * 40,
        )), fresh, fresh), "mismatched canonical release target passed")
    colab = format_provenance_receipt(
        mode="colab-archive", release_digest=fresh,
        commit_binding="VERIFIED",
        commit_basis="ARCHIVE_DOWNLOADED_BY_COMMIT_SHA",
        commit_target="1" * 40,
        release_binding="VERIFIED", release_basis="TAG_PEELED_VIA_GITHUB_API",
        release_target="1" * 40, tag_commit="1" * 40,
        archive_digest="2" * 64,
        local_head="not-applicable", relevant_state="not-applicable",
    )
    require_test(not check_release_input_provenance(wrapped(colab), fresh, fresh),
                 "valid Colab receipt failed")
    require_test(check_release_input_provenance(
        wrapped(colab.replace("1" * 40, "0" * 40)), fresh, fresh),
        "zero commit passed")
    require_test(check_release_input_provenance(
        wrapped(colab.replace("2" * 64, "abcd")), fresh, fresh),
        "short archive digest passed")
    local_tree = format_provenance_receipt(
        mode="local-tree", release_digest=fresh,
        commit_binding="UNVERIFIED", commit_basis="NO_GIT_METADATA",
        commit_target="not-supplied",
        release_binding="UNVERIFIED", release_basis="NO_GIT_METADATA",
        release_target="not-supplied", tag_commit="not-supplied",
        archive_digest="not-applicable", local_head="unavailable",
        relevant_state="UNKNOWN",
    )
    require_test(not check_release_input_provenance(
        wrapped(local_tree), fresh, fresh), "valid exploratory tree receipt failed")
    require_test(check_release_input_provenance(
        wrapped(local_tree), fresh, fresh, require_verified_commit=True),
        "strict execution validation accepted unverified tree provenance")

    with tempfile.TemporaryDirectory(prefix="revision-binding-test-") as tmp:
        clean_repo = Path(tmp) / "repo"
        clean_repo.mkdir()
        for relative, source in release_input_files(ROOT):
            target = clean_repo / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
        clean_readme = clean_repo / "README.md"
        commands = (
            ["git", "-c", "init.templateDir=", "init", "-q"],
            ["git", "config", "commit.gpgSign", "true"],
            ["git", "config", "gpg.program", str(clean_repo / "missing-test-signer")],
            ["git", "add", "-f", "--", "."],
            [
                "git", "-c", "user.name=Notebook Test",
                "-c", "user.email=notebook-test@example.invalid",
                "-c", "commit.gpgSign=false", "-c", "core.hooksPath=/dev/null",
                "commit", "-qm", "initial",
            ],
        )
        for command in commands:
            result = subprocess.run(
                command, cwd=clean_repo, capture_output=True, text=True,
                check=False, timeout=20,
            )
            require_test(result.returncode == 0, result.stderr or str(command))
        clean_head = local_git_head(clean_repo)
        require_test(
            clean_head is not None and relevant_input_state(clean_repo) == "CLEAN",
            "committed release-input tree was not recognized as clean",
        )
        for relative in ("docs/.DS_Store", "paper/paper.aux", "paper/paper.log"):
            (clean_repo / relative).write_bytes(b"local by-product\n")
        require_test(
            relevant_input_state(clean_repo) == "CLEAN",
            "desktop or TeX by-product falsely dirtied the source tree",
        )
        nested = clean_repo / "nested"
        nested.mkdir()
        require_test(
            local_git_head(nested) is None,
            "nested source tree inherited an unrelated parent Git identity",
        )
        strict_local = format_provenance_receipt(
            mode="local-git", release_digest=fresh,
            commit_binding="VERIFIED",
            commit_basis="HEAD_EQUALS_EXPECTED_SHA",
            commit_target=clean_head,
            release_binding="VERIFIED", release_basis="CI_THREE_WAY_IDENTITY",
            release_target=clean_head, tag_commit=clean_head,
            archive_digest="not-applicable", local_head=clean_head,
            relevant_state="CLEAN",
        )
        require_test(not check_release_input_provenance(
            wrapped(strict_local), fresh, fresh, require_verified_commit=True,
            require_verified_release=True, expected_commit_sha=clean_head,
            expected_release_sha=clean_head, validator_root=clean_repo),
            "strict validation rejected a clean canonical-release receipt")
        clean_readme.write_text("mutated release input\n", encoding="utf-8")
        require_test(
            relevant_input_state(clean_repo) == "DIRTY",
            "byte-level HEAD comparison missed a release-input mutation",
        )
        require_test(check_release_input_provenance(
            wrapped(strict_local), fresh, fresh, require_verified_commit=True,
            require_verified_release=True, expected_commit_sha=clean_head,
            expected_release_sha=clean_head, validator_root=clean_repo),
            "strict validation trusted a forged CLEAN receipt",
        )

    api_handler = SafeGitHubAPIRedirectHandler()
    api_url = "https://api.github.com/repos/example/private/git/ref/tags/v0.1.0"
    api_request = Request(
        api_url,
        headers={"Authorization": "Bearer secret", "X-Test": "retained"},
    )
    for safe in (
        api_url,
        "https://api.github.com:443/repos/example/private",
        "HTTPS://API.GITHUB.COM/repos/example/private",
    ):
        SafeGitHubAPIRedirectHandler.require_api_url(safe)
    for unsafe in (
        "http://api.github.com/x",
        "https://example.com/x",
        "https://codeload.github.com/x",
        "https://api.github.com.evil.invalid/x",
        "https://api.github.com@evil.invalid/x",
        "https://evil.invalid@api.github.com/x",
        "https://api.github.com:0/x",
        "https://api.github.com:00/x",
        "https://api.github.com:/x",
        "https://api.github.com:444/x",
        "https://api.github.com:invalid/x",
        "https://api.github.com/x#fragment",
        "https://api.github.com/x\rheader",
        "https://api.github.com/x\nheader",
        "https://api.github.com/x\theader",
        "https://api.github.com/x\x00header",
    ):
        try:
            SafeGitHubAPIRedirectHandler.require_api_url(unsafe)
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"unsafe API URL passed: {unsafe}")
    for redirected_url in (
        "https://api.github.com/repositories/1",
        "https://example.com/capture",
    ):
        for status in (301, 302, 303, 307, 308):
            try:
                api_handler.redirect_request(
                    api_request, None, status, "Redirect", {}, redirected_url
                )
            except RuntimeError:
                pass
            else:
                raise RuntimeError(
                    f"authenticated API redirect passed: {status} {redirected_url}"
                )
    require_test(
        api_request.get_header("Authorization") == "Bearer secret",
        "API redirect test mutated the original authentication header",
    )
    require_test(api_request.full_url == api_url, "API redirect test mutated its URL")
    api_opener = build_opener(api_handler)
    redirect_handlers = [
        candidate
        for candidate in api_opener.handlers
        if isinstance(candidate, HTTPRedirectHandler)
    ]
    require_test(
        redirect_handlers == [api_handler],
        "API opener installed a permissive default redirect handler",
    )

    handler = SafeGitHubArchiveRedirectHandler()
    for safe in (
        "https://codeload.github.com/example/private/legacy.zip/" + "1" * 40,
        "https://codeload.github.com:443/example/private/legacy.zip/" + "1" * 40,
    ):
        SafeGitHubArchiveRedirectHandler.require_archive_url(safe)
    request = Request(
        "https://api.github.com/repos/example/private/zipball/" + "1" * 40,
        headers={
            "Authorization": "Bearer secret",
            "Proxy-Authorization": "Basic proxy-secret",
            "Cookie": "session=secret",
            "X-Test": "private",
            "User-Agent": "public-test-agent",
        },
    )
    request.add_unredirected_header("X-Unredirected-Secret", "private")
    for status in (301, 302, 303, 307, 308):
        redirected = handler.redirect_request(
            request, None, status, "Redirect", {},
            "https://codeload.github.com/example/private/legacy.zip/" + "1" * 40,
        )
        require_test(request.get_header("Authorization") == "Bearer secret",
                     "API authentication was removed")
        require_test(
            redirected is not None
            and {
                name.lower(): value for name, value in redirected.header_items()
            }
            == {"user-agent": "public-test-agent"},
            f"archive redirect {status} retained a non-allowlisted header",
        )
    for unsafe in (
        "https://api.github.com/x",
        "https://example.com/x",
        "http://codeload.github.com/x",
        "https://codeload.github.com:0/x",
        "https://codeload.github.com:00/x",
        "https://codeload.github.com:/x",
        "https://codeload.github.com:444/x",
        "https://codeload.github.com:invalid/x",
        "https://evil.invalid@codeload.github.com/x",
        "https://codeload.github.com@evil.invalid/x",
        "https://codeload.github.com/x#fragment",
        "https://codeload.github.com/x\rheader",
        "https://codeload.github.com/x\nheader",
        "https://codeload.github.com/x\theader",
        "https://codeload.github.com/x\x00header",
    ):
        try:
            handler.redirect_request(request, None, 302, "Found", {}, unsafe)
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"unsafe redirect passed: {unsafe}")

    with tempfile.TemporaryDirectory(prefix="notebook-generation-test-") as tmp:
        generated = Path(tmp) / "generated.ipynb"
        result = subprocess.run(
            [sys.executable, str(BUILDER), "--output", str(generated)],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        require_test(result.returncode == 0, result.stderr or "builder failed")
        generated_repeat = Path(tmp) / "generated-repeat.ipynb"
        repeated_result = subprocess.run(
            [sys.executable, str(BUILDER), "--output", str(generated_repeat)],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        require_test(
            repeated_result.returncode == 0,
            repeated_result.stderr or "repeated builder run failed",
        )
        require_test(
            generated.read_bytes() == generated_repeat.read_bytes(),
            "notebook builder is not byte-for-byte deterministic",
        )
        built = load(generated)
        require_test(not check_cell_ids(built), "generated notebook has invalid cell IDs")
        for mutation in ("missing", "duplicate", "malformed"):
            mutated = json.loads(json.dumps(built))
            if mutation == "missing":
                mutated["cells"][0].pop("id", None)
            elif mutation == "duplicate":
                mutated["cells"][1]["id"] = mutated["cells"][0]["id"]
            else:
                mutated["cells"][0]["id"] = "invalid cell id"
            require_test(
                bool(check_cell_ids(mutated)),
                f"generated notebook accepted a {mutation} cell ID",
            )
        altered_id = json.loads(json.dumps(built))
        altered_id["cells"][0]["id"] = "altered-overview"
        require_test(
            source_surface(altered_id) != source_surface(built),
            "source-surface comparison ignored an altered cell ID",
        )
        embedded, failures = embedded_release_input_digest(built)
        require_test(not failures and embedded == fresh, "wrong embedded digest")
        require_test(not check_source_only_state(built), "generated notebook has outputs")
        github_json_defs: list[ast.FunctionDef] = []
        archive_download_defs: list[ast.FunctionDef] = []
        redirect_setup_tree: ast.Module | None = None
        for index, cell in enumerate(built.get("cells", []), start=1):
            if cell.get("cell_type") != "code":
                continue
            source = cell.get("source", "")
            if isinstance(source, list):
                source = "".join(source)
            tree = ast.parse(str(source), filename=f"generated-cell-{index}")
            github_json_defs.extend(
                statement
                for statement in tree.body
                if isinstance(statement, ast.FunctionDef)
                and statement.name == "github_json"
            )
            archive_download_defs.extend(
                statement
                for statement in tree.body
                if isinstance(statement, ast.FunctionDef)
                and statement.name == "download_repo_for_colab"
            )
            redirect_class_names = {
                statement.name
                for statement in tree.body
                if isinstance(statement, ast.ClassDef)
                and statement.name
                in {
                    "SafeGitHubAPIRedirectHandler",
                    "SafeGitHubArchiveRedirectHandler",
                }
            }
            if redirect_class_names:
                require_test(
                    redirect_setup_tree is None,
                    "generated notebook defines redirect handlers in multiple cells",
                )
                require_test(
                    redirect_class_names
                    == {
                        "SafeGitHubAPIRedirectHandler",
                        "SafeGitHubArchiveRedirectHandler",
                    },
                    "generated notebook is missing a redirect handler",
                )
                redirect_setup_tree = tree
        require_test(
            len(github_json_defs) == 1,
            f"generated notebook has {len(github_json_defs)} github_json definitions",
        )
        github_json_calls = [
            node
            for node in ast.walk(github_json_defs[0])
            if isinstance(node, ast.Call)
        ]
        require_bound_safe_opener(
            github_json_defs[0],
            "SafeGitHubAPIRedirectHandler",
            "github_json",
            allowed_call_counts={
                "Request": 1,
                "RuntimeError": 3,
                "SafeGitHubAPIRedirectHandler": 1,
                "SafeGitHubAPIRedirectHandler.require_api_url": 2,
                "build_opener": 1,
                "json.loads": 1,
                "opener.open": 1,
                "response.geturl": 1,
                "response.read": 1,
            },
        )
        require_test(
            any(
                isinstance(call.func, ast.Name)
                and call.func.id == "build_opener"
                and any(
                    isinstance(argument, ast.Call)
                    and isinstance(argument.func, ast.Name)
                    and argument.func.id == "SafeGitHubAPIRedirectHandler"
                    for argument in call.args
                )
                for call in github_json_calls
            ),
            "generated github_json lacks the fail-closed redirect handler",
        )
        require_test(
            not any(
                isinstance(call.func, ast.Name) and call.func.id == "urlopen"
                for call in github_json_calls
            ),
            "generated github_json still uses unrestricted URL opening",
        )
        require_test(
            sum(
                isinstance(call.func, ast.Attribute)
                and isinstance(call.func.value, ast.Name)
                and call.func.value.id == "SafeGitHubAPIRedirectHandler"
                and call.func.attr == "require_api_url"
                for call in github_json_calls
            )
            >= 2,
            "generated github_json does not validate request and response URLs",
        )
        require_test(
            len(archive_download_defs) == 1,
            "generated notebook must have exactly one download_repo_for_colab definition",
        )
        archive_download_calls = [
            node
            for node in ast.walk(archive_download_defs[0])
            if isinstance(node, ast.Call)
        ]
        require_bound_safe_opener(
            archive_download_defs[0],
            "SafeGitHubArchiveRedirectHandler",
            "download_repo_for_colab",
            allowed_call_counts={
                "Path": 1,
                "Request": 1,
                "RuntimeError": 2,
                "SafeGitHubArchiveRedirectHandler": 1,
                "SafeGitHubArchiveRedirectHandler.require_archive_url": 1,
                "bool": 1,
                "build_opener": 1,
                "colab_secret": 1,
                "github_headers": 1,
                "opener.open": 1,
                "resolve_github_tag_commit": 1,
                "response.geturl": 1,
                "response.read": 1,
                "safe_extract": 1,
                "sha256": 1,
                "sha256(...).hexdigest": 1,
                "tempfile.mkdtemp": 1,
            },
        )
        require_test(
            any(
                isinstance(call.func, ast.Name)
                and call.func.id == "build_opener"
                and any(
                    isinstance(argument, ast.Call)
                    and isinstance(argument.func, ast.Name)
                    and argument.func.id == "SafeGitHubArchiveRedirectHandler"
                    for argument in call.args
                )
                for call in archive_download_calls
            ),
            "generated archive path lacks the restricted redirect handler",
        )
        require_test(
            any(
                isinstance(call.func, ast.Attribute)
                and isinstance(call.func.value, ast.Name)
                and call.func.value.id == "SafeGitHubArchiveRedirectHandler"
                and call.func.attr == "require_archive_url"
                for call in archive_download_calls
            ),
            "generated archive path does not validate its final response URL",
        )
        require_test(
            not any(
                isinstance(call.func, ast.Name) and call.func.id == "urlopen"
                for call in archive_download_calls
            ),
            "generated archive path still uses unrestricted URL opening",
        )

        require_test(
            redirect_setup_tree is not None,
            "generated notebook has no redirect-handler setup cell",
        )
        generated_redirect_namespace: dict[str, object] = {}
        generated_redirect_nodes = [
            node
            for node in redirect_setup_tree.body
            if (
                (
                    isinstance(node, ast.ImportFrom)
                    and node.module in {"urllib.parse", "urllib.request"}
                )
                or (
                    isinstance(node, ast.ClassDef)
                    and node.name
                    in {
                        "SafeGitHubAPIRedirectHandler",
                        "SafeGitHubArchiveRedirectHandler",
                    }
                )
            )
        ]
        exec(
            compile(
                ast.Module(body=generated_redirect_nodes, type_ignores=[]),
                filename="generated-redirect-runtime",
                mode="exec",
            ),
            generated_redirect_namespace,
        )
        generated_api_handler = generated_redirect_namespace[
            "SafeGitHubAPIRedirectHandler"
        ]
        generated_archive_handler = generated_redirect_namespace[
            "SafeGitHubArchiveRedirectHandler"
        ]
        generated_api_handler.require_api_url(api_url)
        generated_archive_handler.require_archive_url(
            "https://codeload.github.com/example/private/legacy.zip/" + "1" * 40
        )

        class FakeResponse:
            def __init__(self, url: str, body: bytes):
                self.url = url
                self.body = body

            def __enter__(self):
                return self

            def __exit__(self, exc_type, exc_value, traceback):
                return False

            def geturl(self) -> str:
                return self.url

            def read(self) -> bytes:
                return self.body

        class RecordingOpener:
            def __init__(self, handler, response: FakeResponse):
                self.handler = handler
                self.response = response
                self.calls: list[tuple[Request, int]] = []
                self.redirected_request = None

            def open(self, request: Request, *, timeout: int):
                self.calls.append((request, timeout))
                require_test(
                    len(self.calls) == 1,
                    "generated runtime attempted more than one direct request",
                )
                if isinstance(self.handler, generated_archive_handler):
                    self.redirected_request = self.handler.redirect_request(
                        request, None, 302, "Found", {}, self.response.url
                    )
                return self.response

        class RecordingOpenerFactory:
            def __init__(self, handler_type, response: FakeResponse):
                self.handler_type = handler_type
                self.response = response
                self.openers: list[RecordingOpener] = []

            def __call__(self, *handlers, **kwargs):
                require_test(
                    len(handlers) == 1
                    and not kwargs
                    and isinstance(handlers[0], self.handler_type),
                    "generated runtime constructed an unapproved opener",
                )
                opener = RecordingOpener(handlers[0], self.response)
                self.openers.append(opener)
                return opener

        class FakeTempfile:
            @staticmethod
            def mkdtemp(*, prefix: str, dir: str) -> str:
                require_test(
                    prefix == "cubic-anomaly-source-" and dir == "/content",
                    "generated archive runtime changed its temporary-directory scope",
                )
                return str(Path(tmp) / "colab-download")

        generated_redirect_namespace.update(
            {
                "HTTPError": HTTPError,
                "Path": Path,
                "REPO_SLUG": "example/private",
                "json": json,
                "sha256": sha256,
                "tempfile": FakeTempfile,
            }
        )
        exec(
            compile(
                ast.Module(
                    body=[github_json_defs[0], archive_download_defs[0]],
                    type_ignores=[],
                ),
                filename="generated-network-functions-runtime",
                mode="exec",
            ),
            generated_redirect_namespace,
        )

        api_response_url = "https://api.github.com/repos/example/private"
        api_factory = RecordingOpenerFactory(
            generated_api_handler,
            FakeResponse(api_response_url, b'{"ok": true}'),
        )
        generated_redirect_namespace["build_opener"] = api_factory
        api_result = generated_redirect_namespace["github_json"](
            api_response_url,
            {"Authorization": "Bearer owner-secret"},
            token_available=True,
            label="runtime test",
        )
        require_test(api_result == {"ok": True}, "generated github_json result changed")
        require_test(
            len(api_factory.openers) == 1
            and len(api_factory.openers[0].calls) == 1
            and api_factory.openers[0].calls[0][0].full_url == api_response_url
            and api_factory.openers[0].calls[0][0].get_header("Authorization")
            == "Bearer owner-secret"
            and api_factory.openers[0].calls[0][1] == 60,
            "generated github_json bypassed its controlled request path",
        )

        revision = "1" * 40
        archive_body = b"controlled archive payload"
        archive_url = (
            "https://codeload.github.com/example/private/legacy.zip/" + revision
        )
        archive_factory = RecordingOpenerFactory(
            generated_archive_handler,
            FakeResponse(archive_url, archive_body),
        )
        extraction_calls: list[tuple[bytes, Path]] = []
        extracted_path = Path(tmp) / "extracted"

        def fake_safe_extract(archive: bytes, destination: Path) -> Path:
            extraction_calls.append((archive, destination))
            return extracted_path

        generated_redirect_namespace.update(
            {
                "build_opener": archive_factory,
                "colab_secret": lambda name: "owner-secret",
                "github_headers": lambda token: {
                    "Authorization": f"Bearer {token}",
                    "User-Agent": "runtime-test-agent",
                },
                "resolve_github_tag_commit": (
                    lambda headers, *, token_available: revision
                ),
                "safe_extract": fake_safe_extract,
            }
        )
        archive_result = generated_redirect_namespace["download_repo_for_colab"]()
        require_test(
            archive_result
            == (extracted_path, revision, sha256(archive_body).hexdigest()),
            "generated archive runtime returned the wrong provenance tuple",
        )
        require_test(
            len(archive_factory.openers) == 1
            and len(archive_factory.openers[0].calls) == 1
            and archive_factory.openers[0].calls[0][0].full_url
            == f"https://api.github.com/repos/example/private/zipball/{revision}"
            and archive_factory.openers[0].calls[0][1] == 120,
            "generated archive runtime bypassed its controlled request path",
        )
        redirected_runtime_request = archive_factory.openers[0].redirected_request
        require_test(
            redirected_runtime_request is not None
            and {
                name.lower(): value
                for name, value in redirected_runtime_request.header_items()
            }
            == {"user-agent": "runtime-test-agent"},
            "generated archive runtime retained a private redirect header",
        )
        require_test(
            extraction_calls
            == [(archive_body, Path(tmp) / "colab-download")],
            "generated archive runtime did not pass exact bytes to safe extraction",
        )

    print(f"PASS release-input manifest tests ({len(release_input_files(ROOT))} files)")
    print("PASS commit/release classifiers, tag-peeling, and receipt mutation tests")
    print("PASS redirect/authentication tests")
    print("PASS temporary generation tests")
    return 0


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse the lightweight notebook-validation command line."""

    parser = argparse.ArgumentParser(
        description=(
            "Validate notebook source provenance and, by default, executed outputs."
        )
    )
    parser.add_argument(
        "--notebook",
        type=Path,
        default=CANONICAL,
        metavar="PATH",
        help="notebook to validate (default: the canonical repository notebook)",
    )
    parser.add_argument(
        "--source-only",
        action="store_true",
        help="check builder/source equivalence and assert hygiene; skip outputs",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run lightweight manifest, receipt, redirect, and generation tests",
    )
    parser.add_argument(
        "--require-verified-provenance",
        action="store_true",
        help=(
            "reject executed notebooks whose execution-commit binding is "
            "UNVERIFIED"
        ),
    )
    parser.add_argument(
        "--expected-commit-sha",
        metavar="SHA",
        help="full commit SHA expected in the executed notebook receipt",
    )
    parser.add_argument(
        "--require-canonical-release-provenance",
        action="store_true",
        help=(
            "reject executed notebooks whose canonical-release binding is "
            "UNVERIFIED"
        ),
    )
    parser.add_argument(
        "--expected-canonical-release-sha",
        metavar="SHA",
        help="full canonical release commit expected in the notebook receipt",
    )
    args = parser.parse_args(argv)
    if args.source_only and (
        args.require_verified_provenance
        or args.expected_commit_sha is not None
        or args.require_canonical_release_provenance
        or args.expected_canonical_release_sha is not None
    ):
        parser.error("provenance options cannot be used with --source-only")
    if args.require_verified_provenance and args.expected_commit_sha is None:
        parser.error("--require-verified-provenance requires --expected-commit-sha")
    if (
        args.require_canonical_release_provenance
        and args.expected_canonical_release_sha is None
    ):
        parser.error(
            "--require-canonical-release-provenance requires "
            "--expected-canonical-release-sha"
        )
    if args.expected_commit_sha is not None:
        try:
            args.expected_commit_sha = normalize_optional_commit_sha(
                "--expected-commit-sha", args.expected_commit_sha
            )
        except ValueError as error:
            parser.error(str(error))
    if args.expected_canonical_release_sha is not None:
        try:
            args.expected_canonical_release_sha = normalize_optional_commit_sha(
                "--expected-canonical-release-sha",
                args.expected_canonical_release_sha,
            )
        except ValueError as error:
            parser.error(str(error))
    if (
        args.expected_commit_sha is not None
        and args.expected_canonical_release_sha is not None
        and args.expected_commit_sha != args.expected_canonical_release_sha
    ):
        parser.error(
            "--expected-commit-sha and --expected-canonical-release-sha disagree"
        )
    return args


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.self_test:
        try:
            return run_self_tests()
        except (OSError, RuntimeError) as error:
            print(f"FAIL self-test: {error}")
            return 1
    if args.expected_commit_sha is not None:
        validator_head = local_git_head(ROOT)
        if validator_head != args.expected_commit_sha:
            print(
                "FAIL validator checkout HEAD differs from --expected-commit-sha: "
                f"expected {args.expected_commit_sha}, found {validator_head or 'unavailable'}"
            )
            return 1
    if args.expected_canonical_release_sha is not None:
        validator_head = local_git_head(ROOT)
        if validator_head != args.expected_canonical_release_sha:
            print(
                "FAIL validator checkout HEAD differs from "
                "--expected-canonical-release-sha: expected "
                f"{args.expected_canonical_release_sha}, found "
                f"{validator_head or 'unavailable'}"
            )
            return 1
    notebook_path = args.notebook
    try:
        notebook = load(notebook_path)
    except (OSError, json.JSONDecodeError) as error:
        print(f"FAIL  could not load notebook {notebook_path}: {error}")
        return 1

    cell_id_failures = check_cell_ids(notebook)
    if cell_id_failures:
        for failure in cell_id_failures:
            print(f"FAIL {failure}")
        return 1

    with tempfile.TemporaryDirectory(prefix="cubic-anomaly-notebook-") as tmp:
        generated = Path(tmp) / "generated.ipynb"
        result = subprocess.run(
            [sys.executable, str(BUILDER), "--output", str(generated)],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            print("FAIL  notebook builder could not run", file=sys.stderr)
            if result.stdout:
                print(result.stdout.rstrip(), file=sys.stderr)
            if result.stderr:
                print(result.stderr.rstrip(), file=sys.stderr)
            return result.returncode
        committed_surface = source_surface(notebook)
        generated_surface = source_surface(load(generated))

    if committed_surface != generated_surface:
        print(f"FAIL  notebook source differs from its builder: {notebook_path}")
        print("Run: python notebooks/build_master_notebook.py, then re-execute it.")
        return 1

    assertion_cells: list[int] = []
    for index, cell in enumerate(committed_surface["cells"], start=1):
        if cell["cell_type"] != "code":
            continue
        try:
            tree = ast.parse(cell["source"], filename=f"notebook-cell-{index}")
        except SyntaxError as error:
            print(f"FAIL  notebook code cell {index} does not parse: {error}")
            return 1
        if any(isinstance(node, ast.Assert) for node in ast.walk(tree)):
            assertion_cells.append(index)
    if assertion_cells:
        print(
            "FAIL  notebook verification cells use optimization-removable "
            f"assert statements: {assertion_cells}"
        )
        return 1

    print(f"PASS notebook source matches its builder: {notebook_path}")
    print("PASS notebook verification cells avoid removable assert statements")

    embedded_digest, embedded_failures = embedded_release_input_digest(notebook)
    if embedded_failures:
        for failure in embedded_failures:
            print(f"FAIL {failure}")
        return 1
    fresh_digest = release_input_digest(ROOT)
    if embedded_digest != fresh_digest:
        print(
            "FAIL embedded release-input digest differs from current repository: "
            f"expected {fresh_digest}, found {embedded_digest}"
        )
        return 1

    canonical_target = notebook_path.resolve() == CANONICAL.resolve()
    if canonical_target and (
        args.require_verified_provenance
        or args.expected_commit_sha is not None
        or args.require_canonical_release_provenance
        or args.expected_canonical_release_sha is not None
    ):
        print(
            "FAIL strict provenance validation requires a separate executed "
            "notebook artifact, not the canonical source-only notebook"
        )
        return 1
    if args.source_only or canonical_target:
        source_failures = check_source_only_state(notebook)
        if source_failures:
            for failure in source_failures:
                print(f"FAIL {failure}")
            return 1
        print("PASS notebook is source-only; output checks apply to CI artifacts")
        return 0

    output_failures = check_output_integrity(
        notebook,
        require_verified_commit=args.require_verified_provenance,
        require_verified_release=args.require_canonical_release_provenance,
        expected_commit_sha=args.expected_commit_sha,
        expected_release_sha=args.expected_canonical_release_sha,
    )
    if output_failures:
        for failure in output_failures:
            print(f"FAIL  {failure}")
        return 1

    if args.require_canonical_release_provenance:
        print(
            "PASS notebook outputs are complete, substantive, content-bound, "
            "execution-commit-bound, and canonical-release-bound"
        )
    elif args.require_verified_provenance:
        print(
            "PASS notebook outputs are complete, substantive, content-bound, "
            "and execution-commit-bound; canonical release binding is reported "
            "separately"
        )
    else:
        searchable = " ".join(
            visible_output_text(output)
            for cell in notebook.get("cells", [])
            for output in cell.get("outputs", [])
        )
        unverified = []
        if "Execution commit binding: UNVERIFIED" in searchable:
            unverified.append("execution commit")
        if "Canonical release binding: UNVERIFIED" in searchable:
            unverified.append("canonical release")
        if unverified:
            print(
                "WARNING notebook computation is content-bound but these "
                "provenance claims are UNVERIFIED: " + ", ".join(unverified)
            )
        else:
            print(
                "PASS notebook outputs are complete, substantive, content-bound, "
                "execution-commit-bound, and canonical-release-bound"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
