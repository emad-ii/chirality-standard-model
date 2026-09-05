# Verification notes

The [master notebook](../Cubic_Anomaly_Master_Verification.ipynb) is the guided route. These notes give the individual commands and explain what each layer checks.

## Exact Python

From the repository root, with Python 3.10 or later:

```bash
python verification/python/run_all.py --jobs 2
```

The runner executes every mathematical verifier, compares 13 recorded outputs, independently regenerates both JSON certificates, checks the E6 certificate digest and cross-checks certificate arithmetic and the Lean data binding: 17 checks in total. They also work with Python optimization enabled:

```bash
python -O verification/python/run_all.py --jobs 2
```

All mathematical programs use the Python standard library. They cover:

- Two root-system realizations of the 38,880-triple E6 incidence space, its six Weyl cells, extrema and labelled containments.
- Two complete closed-subsystem censuses: 5,079 closed subsystems, of which 103 are maximal proper subsystems.
- Exceptional toral gradings, the Cartan cubic selector and the rank-deficient exceptional and classical checks.
- Context symmetry, stabilizers, central kernels, subgroup orderings and chiral dimensions.
- All 112 invariant mass-form rank strata on the restricted 81-dimensional module, including the 45-dimensional minimum kernel.

The [programs](python), [recorded outputs](expected) and [certificates](certificates) can also be inspected separately. Bounded classical arithmetic checks accompany the manuscript's all-rank proof; a finite sample is not substituted for that proof.

## Lean

[Lean 4](https://lean-lang.org/install/) is optional for running the Python notebook. The [toolchain](../lean-toolchain), [Mathlib revision](../lakefile.toml) and [dependency revisions](../lake-manifest.json) are pinned.

With Elan installed, run from the repository root:

```bash
lake exe cache get
python formal/scripts/check_generated_data.py
lake build
python formal/scripts/check_formal_hygiene.py
```

The first command downloads the upstream Mathlib build cache; it can be omitted if you prefer to build dependencies from their pinned sources. A first Lean run needs internet access, disk space for the toolchain and dependencies, and more time than the Python checks. The notebook offers the same sequence as an optional step.

### What Lean proves

The [exceptional classification module](../CubicAnomaly/Classification/Exceptional.lean) starts from authored Cartan matrices and integer symmetrizers for G2, F4, E6, E7 and E8. It reconstructs roots by reflection closure, exhausts root-lattice functionals modulo two and three up to Weyl action, checks the relevant component and grade-graph signatures, and evaluates the exact grade-one trace cubic on coroot spanning sets. This census is independent of the JSON certificate.

The [E6 checker](../CubicAnomaly/E6/Checker.lean) receives root coordinates, reflection permutations, a highest-root witness and six orbit seeds through the [generated data module](../CubicAnomaly/E6/Data.lean). It validates the witnesses against the fixed Cartan formulas and reconstructs the finite incidence calculation. It checks:

- Root closure, signs, squared lengths, reflection formulas and highest-root order.
- Closed subsystem masks with the rank/root-count signatures of D5, A5+A1 and A2³, in orbits of sizes 27, 36 and 40.
- A 38,880-element triple space covered by six disjoint simultaneous-reflection orbits.
- The six-cell intersection distribution and the two extrema.
- A closed irreducible six-root, rank-two component exactly in the two extremal cells.
- Common-subsystem multiplicities, context counts and 8,640 labelled containments.

Conventional root-system names use standard ADE classification. The theorem statements and expected counts are authored in Lean, not copied from JSON summary fields. The data-freshness check verifies the translation from JSON to Lean; Lean separately validates those witnesses. The [18 exported theorems](../formal/AxiomAudit.lean) include the principal theorem `CubicAnomaly.E6.finite_certificate_valid`.

### Trust model

The finite computations use `native_decide`. The axiom audit checks every exported theorem against this exact receipt:

```text
propext
Quot.sound
Lean.ofReduceBool
Lean.trustCompiler
```

The first two are foundational Lean axioms; the last two connect compiled evaluation to the theorem. The check also rejects unfinished proofs, project axioms, unsafe declarations and partial definitions. Compiler binaries and optional build caches come from their standard upstream distributions.

### Manuscript proofs

The paper supplies the compact-Lie structural reductions, completeness bridges, invariant-theory argument from the Cartan cubic to the ideal-valued radical, classical all-rank argument, global group integrations, branching, chiral index and invariant mass-kernel proof. Their finite computational parts have the support described above. The complete-matter interpretation (M) is the stated step from chiral index to physical family count.

## Local notebook

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements-notebook.txt
python -m jupyter nbconvert --execute --to notebook --output /tmp/chirality-verified.ipynb --ExecutePreprocessor.timeout=1800 Cubic_Anomaly_Master_Verification.ipynb
```

This writes an executed copy to `/tmp/chirality-verified.ipynb`. For interactive use, open the source notebook in your existing Jupyter editor. In Colab, a private repository ZIP can be uploaded at setup; no access token is required.

## Updating generated files

After an intentional change to the verification sources:

```bash
python verification/python/regenerate.py
```

Review changes to the mathematical certificate fields, update the notebook's setup checksum to the new certificate digest, then rerun the notebook. Edit the notebook in a notebook editor. Keep the distributed copy source-only so its results always come from the reader's run.

## LaTeX

The [PDF](../paper/paper.pdf) is supplied alongside its [self-contained LaTeX source](../paper/paper.tex). To rebuild it locally, open the source in your TeX editor or run `latexmk -pdf paper.tex` from the paper directory. Neither TeX nor a PDF build is needed to run the notebook.
