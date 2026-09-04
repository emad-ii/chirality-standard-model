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
        expected = COMMITTED.read_text()
        actual = generated.read_text()
        if expected != actual:
            print("Generated Lean data is stale. Run `make regenerate`.", file=sys.stderr)
            print(
                "".join(
                    difflib.unified_diff(
                        expected.splitlines(keepends=True),
                        actual.splitlines(keepends=True),
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
