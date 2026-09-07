#!/usr/bin/env python3
"""Report source identity separately from the mathematical certificate.

Git exports the commit/tree identifiers into revision.json. For ZIP inputs we
recompute the entire Git tree (including paper, notebook and Lean sources),
restoring only that one export-substituted metadata file before hashing.
This checks snapshot consistency, not a publisher signature or authenticity.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import zipfile

REVISION_PATH = "verification/revision.json"
REVISION_TEMPLATE = b'{"commit": "$Format:%H$", "tree": "$Format:%T$"}\n'


def read_revision(raw: bytes) -> dict[str, str]:
    revision = json.loads(raw)
    if (not isinstance(revision, dict) or set(revision) != {"commit", "tree"}
            or any(not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value)
                   for value in revision.values())):
        raise ValueError("revision identifiers were not expanded by git archive")
    return revision


def git_object(kind: str, content: bytes) -> bytes:
    return hashlib.sha1(kind.encode() + b" " + str(len(content)).encode()
                        + b"\0" + content).digest()


def tree_hash(files: dict[str, tuple[int, bytes]]) -> str:
    """Git's recursive tree encoding, including paths and executable bits."""
    root = {}
    for name, value in files.items():
        parts = PurePosixPath(name).parts
        node = root
        for part in parts[:-1]:
            node = node.setdefault(part, {})
            if not isinstance(node, dict):
                raise ValueError("file/directory collision in snapshot")
        if parts[-1] in node:
            raise ValueError("duplicate path in snapshot")
        node[parts[-1]] = value

    def encode(node):
        entries = []
        for name, value in node.items():
            if isinstance(value, dict):
                mode, digest, order = b"40000", encode(value), name.encode() + b"/"
            else:
                permissions, raw = value
                mode = b"100755" if permissions & 0o111 else b"100644"
                digest, order = git_object("blob", raw), name.encode()
            entries.append((order, mode + b" " + name.encode() + b"\0" + digest))
        return git_object("tree", b"".join(value for _, value in sorted(entries)))

    return encode(root).hex()


def archive_revision(filename: Path) -> dict[str, object]:
    with zipfile.ZipFile(filename) as archive:
        entries = archive.infolist()
        if len(entries) > 5000 or sum(item.file_size for item in entries) > 100_000_000:
            raise ValueError("source archive exceeds the size limit")
        files = {}
        for item in entries:
            path = PurePosixPath(item.filename)
            mode = item.external_attr >> 16
            if (path.is_absolute() or ".." in path.parts or "\\" in item.filename
                    or stat.S_ISLNK(mode)):
                raise ValueError("unsafe archive path")
            if item.is_dir():
                continue
            if not path.parts or path.as_posix() != item.filename or item.filename in files:
                raise ValueError("duplicate or noncanonical archive path")
            if stat.S_IFMT(mode) not in (0, stat.S_IFREG):
                raise ValueError("archive contains a nonregular file")
            files[item.filename] = (mode, archive.read(item))
        candidates = [name[:-len(REVISION_PATH)] for name in files
                      if name == REVISION_PATH or name.endswith("/" + REVISION_PATH)]
        if len(candidates) != 1:
            raise ValueError("source ZIP lacks a unique revision record; download a current GitHub ZIP")
        prefix = candidates[0]
        if any(not name.startswith(prefix) for name in files):
            raise ValueError("files lie outside the source archive root")
        files = {name[len(prefix):]: value for name, value in files.items()}
        revision = read_revision(files[REVISION_PATH][1])
        if archive.comment and archive.comment != revision["commit"].encode():
            raise ValueError("ZIP comment and revision commit disagree")
        files[REVISION_PATH] = (files[REVISION_PATH][0], REVISION_TEMPLATE)
        actual_tree = tree_hash(files)
        if actual_tree != revision["tree"]:
            raise ValueError("ZIP contents differ from the recorded repository tree")
        return {**revision, "state": "complete ZIP tree verified", "files": len(files), "verified": True}


def checkout_revision(root: Path) -> dict[str, object]:
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=root, text=True).strip()
    commit, tree = git("rev-parse", "HEAD"), git("rev-parse", "HEAD^{tree}")
    dirty = bool(git("status", "--porcelain", "--untracked-files=normal"))
    # Filesystems without executable bits (Windows) make Git set core.fileMode
    # to false and take modes from the tree; mirror that so a clean checkout
    # hashes to the recorded tree there as well.
    trust_file_mode = git("config", "--type=bool", "--default=true", "core.fileMode") == "true"
    # Do not rely on the index: assume-unchanged/skip-worktree flags can hide
    # modified files from status. Hash every tracked file's actual bytes/mode.
    files = {}
    entries = subprocess.check_output(["git", "ls-tree", "-r", "-z", "HEAD"], cwd=root)
    for entry in entries.split(b"\0"):
        if not entry:
            continue
        header, encoded_name = entry.split(b"\t", 1)
        mode, kind, _ = header.split()
        name = encoded_name.decode("utf-8")
        path = root / name
        if (kind != b"blob" or mode not in (b"100644", b"100755")
                or not path.is_file() or path.is_symlink()
                or any((root / parent).is_symlink() for parent in path.relative_to(root).parents)):
            dirty = True
            continue
        files[name] = (path.stat().st_mode if trust_file_mode else int(mode, 8), path.read_bytes())
    dirty = dirty or tree_hash(files) != tree
    return {"commit": commit, "tree": tree,
            "verified": not dirty,
            "state": "locally modified (not the recorded tree)" if dirty else "clean Git checkout"}


def extracted_revision(root: Path) -> dict[str, object]:
    return {**read_revision((root / REVISION_PATH).read_bytes()), "verified": False,
            "state": "unverified extracted archive (set ARCHIVE_PATH to check the original ZIP)"}


def enforce_revision(revision: dict[str, object], requested: str) -> None:
    # Branch/tag names move; only a full commit identifier is a pin.
    if re.fullmatch(r"[0-9a-fA-F]{40}", requested):
        if revision["commit"] != requested.lower() or revision.get("verified") is not True:
            raise ValueError("sources do not match the requested clean commit")


def self_tests() -> int:
    import io
    import tempfile
    payload = {"README.md": (0o100644, b"example\n"),
               "paper/paper.tex": (0o100644, b"paper\n"),
               "run.py": (0o100755, b"pass\n"),
               REVISION_PATH: (0o100644, REVISION_TEMPLATE)}
    tree = tree_hash(payload)
    revision = {"commit": "a" * 40, "tree": tree}
    expanded = {**payload, REVISION_PATH: (0o100644, (json.dumps(revision) + "\n").encode())}

    def write_archive(files):
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, "w") as archive:
            for name, (mode, raw) in files.items():
                info = zipfile.ZipInfo("source/" + name)
                info.create_system = 3
                info.external_attr = mode << 16
                archive.writestr(info, raw)
        buffer.seek(0)
        return buffer

    good = archive_revision(write_archive(expanded))
    enforce_revision(good, "a" * 40)
    failures = []
    for name in payload:
        for mode, content in ((expanded[name][0], expanded[name][1] + b"changed"),
                              (0o100644 if expanded[name][0] & 0o111 else 0o100755, expanded[name][1])):
            failures.append({**expanded, name: (mode, content)})
        failures.append({key: value for key, value in expanded.items() if key != name})
    failures.extend(({**expanded, "extra.txt": (0o100644, b"extra")},
                     {**expanded, "../escape": (0o100644, b"unsafe")},
                     {**expanded, "link": (0o120777, b"README.md")}, payload))
    for files in failures:
        try:
            archive_revision(write_archive(files))
        except (ValueError, KeyError):
            continue
        raise ValueError("snapshot check accepted corrupted archive")
    for bad in ({**good, "commit": "b" * 40}, {**good, "verified": False}):
        try:
            enforce_revision(bad, "a" * 40)
        except ValueError:
            continue
        raise ValueError("commit pin accepted a mismatched snapshot")
    # Independent oracle for the implementation of the Git object format.
    if shutil.which("git") is None:
        return len(failures) + 2
    with tempfile.TemporaryDirectory(prefix="source-tree-test-") as directory:
        subprocess.run(["git", "init", "-q", directory], check=True, capture_output=True)
        for name, (mode, raw) in payload.items():
            path = Path(directory) / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
            path.chmod(mode & 0o777)
        subprocess.run(["git", "-c", "core.autocrlf=false", "add", "."], cwd=directory, check=True)
        for name, (mode, _) in payload.items():
            if mode & 0o111:  # record the bit even where the filesystem cannot
                subprocess.run(["git", "update-index", "--chmod=+x", name], cwd=directory, check=True)
        oracle = subprocess.check_output(["git", "write-tree"], cwd=directory, text=True).strip()
        if tree != oracle:
            raise ValueError("snapshot tree hash differs from Git")
        subprocess.run(["git", "-c", "user.name=Snapshot test", "-c", "user.email=test@example.invalid",
                        "-c", "commit.gpgsign=false", "commit", "-qm", "Snapshot oracle"],
                       cwd=directory, check=True, capture_output=True)
        clean = checkout_revision(Path(directory))
        if not clean["verified"]:
            raise ValueError("clean checkout did not match Git's tree")
        subprocess.run(["git", "update-index", "--assume-unchanged", "README.md"],
                       cwd=directory, check=True)
        (Path(directory) / "README.md").write_bytes(b"hidden local edit\n")
        if checkout_revision(Path(directory))["verified"]:
            raise ValueError("assume-unchanged flag concealed altered content")
    return len(failures) + 5


if __name__ == "__main__":
    print(f"PASS  {self_tests()} source-snapshot checks")
