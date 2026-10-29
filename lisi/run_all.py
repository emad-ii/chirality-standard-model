#!/usr/bin/env python3
"""Run every Lisi-bridge check.  Standard library only."""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
CHECKS = ("e8.py", "check_e6_su3_bridge.py", "check_triality_d4d4.py", "check_common_refinement.py", "sm_charges.py", "check_dirac_weyl.py", "spin113.py", "match_e8_spin113.py", "check_frame_higgs.py", "match_e8_d7.py", "check_triality_su4.py", "check_magic_square.py", "check_distler_garibaldi.py", "check_lisi_theta.py")


def main() -> int:
    failed = 0
    start = time.time()
    for script in CHECKS:
        t0 = time.time()
        result = subprocess.run(
            [sys.executable, str(HERE / script)],
            cwd=HERE,
            text=True,
            capture_output=True,
            check=False,
        )
        print(result.stdout, end="")
        if result.returncode != 0:
            failed += 1
            print(f"FAIL  {script}\n{result.stderr}")
        else:
            print(f"      ({script}, {time.time() - t0:.2f}s)")
    print(("FAIL" if failed else "PASS") + f"  lisi bridge: {len(CHECKS) - failed}/{len(CHECKS)} checks  {time.time() - start:.2f}s")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
