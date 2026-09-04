# Independent Review Protocol

This repository is designed to be challenged. A useful review identifies the exact claim, the exact source location, the evidence surface being tested, and the consequence of any failure.

A published human referee report records the reviewer's permission, identity or requested anonymity, reviewed commit, scope, and provenance. Release-gate and model-audit results retain their own labels.

## Pin the object under review

The canonical release identity is the tag `v0.1.0` and the peeled,
40-character commit SHA to which it resolves. The separate
`release-v0.1.0` branch is a mutable launcher for Codespaces and manual CI; it
is not the reviewed object.

Record all four before beginning:

1. the `v0.1.0` tag and its peeled, full 40-character commit SHA;
2. the SHA-256 hashes of [`paper.tex`](../paper/paper.tex) and [`paper.pdf`](../paper/paper.pdf), as listed in [`AUDIT.md`](AUDIT.md);
3. the exact URL and head SHA of the tag-triggered Release CI run;
4. the final status of the identity job, all four content lanes, and the
   `release-gate` aggregator.

Verify that `main`, every checkout, the launcher-branch HEAD, both the notebook's
execution-commit and canonical-release receipt fields, and the CI run head SHA
equal the recorded commit. Confirm that the
run's exact three-way release-identity job passed. An archive alone establishes
its contents, not the tag-to-commit mapping; unless that mapping is checked
independently, label release provenance **UNVERIFIED**. These records expose a
report attached to the wrong revision, even if a tag is later moved.

## Follow the dependency order

1. **Manuscript proof.** Read the hypotheses and theorem in the [paper](../paper/paper.pdf), then inspect the structural reduction, full-rank exhaustiveness, both rank-deficient exclusions, invariant-theory argument, global subgroup integration, and branching argument.
2. **Claim map.** Use the [claim and evidence register](CLAIM_STATUS.md) and [paper / code / Lean crosswalk](PAPER_CROSSWALK.md) to locate the authority and supporting surface for every claim.
3. **Exact reconstruction.** Run the two independent $E_6$ routes and the complete Python gate at both normal and optimized interpreter settings. Check that regenerated certificates and expected outputs agree byte-for-byte and that no verification invariant is encoded as a removable Python `assert`.
4. **Bounded formal surface.** Read the named statements in [`Exceptional.lean`](../CubicAnomaly/Classification/Exceptional.lean) and [`Claims.lean`](../CubicAnomaly/E6/Claims.lean), then inspect the [proof allocation and trust model](FORMALIZATION_BOUNDARY.md). Verify which theorem starts from authored Cartan matrices, which path consumes generated certificate data, what Lean reconstructs, which bridges the manuscript proves, and what `native_decide` trusts.
5. **Physical interpretation.** Track the proved branching and index statements and the complete-matter assumption (M) under their stated labels.

For a clean local run:

```bash
make notebook-setup
make all
```

For release evidence, use the Actions run triggered by the `v0.1.0` tag. A
reviewer with repository write access can request a manual rerun from the
**Actions** page using **Run workflow** and selecting `release-v0.1.0`. In
either case, record the exact run URL and head SHA and confirm that the head SHA
equals the canonical release commit and that the three-way identity job passed.
The paper lane requires two fresh builds to be byte-identical and the committed
PDF to match their exact 288-dpi RGB renders, page-local searchable
prose/number fingerprints, stable metadata, and page count, with all fonts
embedded and active content rejected.

## Report a finding

Use the [structured mathematical-audit issue](https://github.com/emad-ii/cubic-anomaly-standard-model/issues/new?template=mathematical-audit.yml) or provide the same fields in a referee report:

- **Severity:** blocker, major, minor, or question.
- **Claim ID:** use `MP-*`, `E6-*`, `EX-*`, or `PH-*` from the register.
- **Exact location:** paper page and proposition/equation, or repository path and line.
- **Statement under review:** quote only the smallest necessary passage.
- **Evidence type:** manuscript proof (P), Lean checked (L), independently reproduced (C2), exactly computed (C1), or interpretive (I).
- **Reasoning:** give a counterexample, omitted case, failed implication, circular dependency, reproducibility failure, or overstatement.
- **Reproduction:** include the shortest command or derivation that exposes the problem.
- **Impact:** say which downstream claims fail if the finding is correct.

A mathematical finding identifies its source location and supplies an argument or reproducible failure.

## Publishing a human report

A report included in this repository should state the reviewer name or requested anonymity, date, release tag, peeled commit SHA, exact CI run URL and head SHA, provenance status, scope, conflicts of interest, and whether the author had a right of reply. Corrections made after the report should be linked to a commit and never silently folded into the original review.

The canonical [AI audit prompt](INDEPENDENT_MATH_AUDIT.md) generates adversarial questions and routes precise findings to human review. Its provenance label distinguishes it from a referee report or mathematical proof.
