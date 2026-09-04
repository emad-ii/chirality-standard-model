#!/usr/bin/env python3
"""Regenerate deterministic JSON, its digest, and the Lean data bridge."""

from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess
import sys


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
CERTIFICATE_DIR = REPO_ROOT / "verification" / "certificates"


def run(script: Path, *arguments: str) -> None:
    subprocess.run([sys.executable, str(script), *arguments], cwd=REPO_ROOT, check=True)


def main() -> None:
    exceptional = CERTIFICATE_DIR / "exceptional_rank_deficient_audit.json"
    certificate = CERTIFICATE_DIR / "e6_extrema_certificate.json"
    run(SCRIPT_DIR / "make_exceptional_rank_deficient_audit.py", "--output", str(exceptional))
    run(SCRIPT_DIR / "make_e6_extrema_certificate.py", "--output", str(certificate))
    digest = hashlib.sha256(certificate.read_bytes()).hexdigest()
    (CERTIFICATE_DIR / "e6_extrema_certificate.sha256").write_text(
        f"{digest}  {certificate.name}\n"
    )
    run(REPO_ROOT / "formal" / "scripts" / "generate_lean_data.py")
    print(f"regenerated certificate {digest}")


if __name__ == "__main__":
    main()
