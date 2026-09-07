#!/usr/bin/env python3
"""Regenerate the deterministic exceptional rank-deficient audit JSON."""

import argparse
import json
from pathlib import Path

import check_rank_deficient_exceptional as census

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
OUT = REPO_ROOT / "verification" / "certificates" / "exceptional_rank_deficient_audit.json"


def main(output: Path | None = None) -> None:
    census.check_index_normalization()
    data = census.run_census()
    out = output if output is not None else OUT
    out.write_bytes((json.dumps(data, indent=2, sort_keys=True) + "\n").encode("utf-8"))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    main(args.output)
