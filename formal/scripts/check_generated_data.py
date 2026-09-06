#!/usr/bin/env python3
"""Fail if the committed Lean data module is not generated from the JSON."""

from __future__ import annotations

import difflib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


REPO_ROOT = Path(__file__).resolve().parents[2]
GENERATOR = REPO_ROOT / "formal" / "scripts" / "generate_lean_data.py"
COMMITTED = REPO_ROOT / "CubicAnomaly" / "E6" / "Data.lean"
CERTIFICATE = (
    REPO_ROOT / "verification" / "certificates" / "e6_extrema_certificate.json"
)


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="lean-data-check-") as temporary:
        generated = Path(temporary) / "Data.lean"
        subprocess.run(
            [sys.executable, str(GENERATOR), "--output", str(generated)],
            cwd=REPO_ROOT,
            check=True,
        )
        expected = COMMITTED.read_bytes()
        actual = generated.read_bytes()
        if expected != actual:
            print("Generated Lean data is stale. Run `python verification/python/regenerate.py`.", file=sys.stderr)
            print(
                "".join(
                    difflib.unified_diff(
                        expected.decode(errors="replace").splitlines(keepends=True),
                        actual.decode(errors="replace").splitlines(keepends=True),
                        fromfile=str(COMMITTED),
                        tofile="regenerated/Data.lean",
                    )
                ),
                file=sys.stderr,
            )
            return 1
    certificate_version = json.loads(CERTIFICATE.read_text())["certificate_version"]
    version_match = re.search(
        r"^def certificateVersion : Nat := ([0-9]+)$",
        COMMITTED.read_text(),
        re.MULTILINE,
    )
    if version_match is None or int(version_match.group(1)) != certificate_version:
        print(
            "Generated Lean data does not record the JSON certificate schema.",
            file=sys.stderr,
        )
        return 1
    print("PASS  generated Lean data matches the JSON certificate")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
