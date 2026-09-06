# Verification notes

The [master notebook](../Cubic_Anomaly_Master_Verification.ipynb) is the guided route. These notes give the individual commands and explain what each layer checks.

## Exact Python

From the repository root, with Python 3.10 or later:

```bash
python verification/python/run_all.py --jobs 2
```

The runner executes every mathematical verifier, compares 12 recorded outputs, independently regenerates both JSON certificates, checks the E6 certificate digest and cross-checks certificate arithmetic and the complete Lean data payload: 16 checks in total. Input consistency is checked first, so stale or malformed inputs fail before the longer searches. The checks also work with Python optimization enabled:

```bash
python -O verification/python/run_all.py --jobs 2
```

All mathematical programs use the Python standard library. They cover:

- Two root-system realizations of the 38,880-triple E6 incidence space. Both independently traverse all six Weyl orbits and compare each entire orbit with its cell; the R8 check also rejects incomplete, merged and overlapping partitions.
- Two complete closed-subsystem censuses using different algorithms: positive-simple-root enumeration in Cartan coordinates, and root-pair adjoining with additive closure in R8. Both recover 5,079 closed subsystems and 103 maximal proper subsystems. The R8 census reconstructs simple roots, exact ranks and Cartan/Dynkin diagrams for every subsystem; type names are not inferred from total root count.
- Exceptional toral gradings, the Cartan cubic selector and the rank-deficient exceptional and classical checks.
- Context symmetry, stabilizers, central kernels, subgroup orderings and chiral dimensions.
- The unique largest pairwise derived group on every triple, computed independently in both coordinate systems. Root count and rank-plus-root-count select the same pair, equivalent to the restricted chiral dimension being 15 or 16.

The ordering checks include all 2,466 distinct pair-parent root systems, invariance under simple reflections, relabelling of the pairs, and rejection of ties and malformed inputs. They also check counterexamples to substituting rank alone or maximum chiral dimension for the stated rule. The certificate records the dimensions, six-cell results and these alternative-selector counts.

Certificate regeneration compares all 5,079 actual subsystem sets and all 103 maximal sets across the two coordinate systems, not just their counts. The coordinate bridge is applied only after the two enumerations have finished independently.

The [programs](python), [recorded outputs](expected) and [certificates](certificates) can also be inspected separately. Bounded classical arithmetic checks accompany the manuscript's all-rank proof; a finite sample is not substituted for that proof.

### Verification-boundary tests

The Python gate regenerates the **entire** `Data.lean` translation in memory and compares bytes, without requiring Lean. The generator and its standalone freshness checker are included in the certificate's source-hash inventory. Thirty-one negative tests reject comment-only identity markers, missing or altered declarations, stale coordinates, matrices, reflections and seeds, non-integer payloads and duplicate JSON keys. These test payload freshness; the Lean build separately proves the finite claims about those data.

Source-snapshot tests also reject changed, missing or extra archived files, altered executable bits, unsafe paths and mismatched commit pins. When Git is installed, its own tree encoder provides an independent check of the archive verifier. Run the fast boundary tests separately with:

```bash
python verification/python/run_all.py --self-test
```

### Which revision was checked?

The notebook reports the repository commit/tree and the mathematical certificate digest **separately**. The certificate binds the computational inputs listed in its inventory; it is not a checksum of the paper, notebook or complete Lean project.

GitHub ZIPs and `git archive` exports carry [revision metadata](revision.json). The notebook recomputes the full archived Git tree, including the paper, notebook and proof sources, and compares it with that record. Only the export-substituted revision record is restored to its tracked template before hashing. This establishes internal snapshot consistency, not a publisher signature. Obtain the ZIP and any trusted revision identifier from the repository itself.

Set the notebook's `REPO_REF` to a full 40-character commit identifier to pin a run. Branch/tag names remain moving references. Downloads use fetch followed by detached checkout, so full commit identifiers work; an existing checkout is never silently switched. A pinned run rejects a different commit or a modified checkout. Unpinned local edits are reported explicitly.

For a local notebook, supply the pin through the `CHIRALITY_REPO_REF` environment variable before starting Jupyter; this avoids changing the tracked notebook merely to configure the run. Clean-checkout verification hashes the actual tracked file contents and modes, even when Git index flags hide edits from ordinary status. An already-extracted ZIP may run the mathematical checks with an explicit unverified-source label; supply its original ZIP through `ARCHIVE_PATH` to verify or pin that source snapshot. Rerunning setup clears imported project modules and prior verification results.

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
- The exact ranks and root counts of all three pair types, and strict D-A dominance by root count and by rank plus root count for every member of the triple universe.
- A closed irreducible six-root, rank-two component exactly in the two extremal cells.
- Common-subsystem multiplicities, context counts and 8,640 labelled containments.

Conventional root-system names use standard ADE classification. The theorem statements and expected counts are authored in Lean, not copied from JSON summary fields. The data-freshness check verifies the translation from JSON to Lean; Lean separately validates those witnesses. The [25 exported theorems](../formal/AxiomAudit.lean) include `CubicAnomaly.E6.finite_certificate_valid` and the separate intrinsic-ordering theorems. Pair ranks are calculated from the integer root coordinates. The paper proves that rank plus root count is the dimension of the corresponding semisimple Lie algebra, and that the structural selection is equivalent to the chiral-dimension characterization.

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

The paper supplies the compact-Lie structural reductions, the homogeneous realization of the algebraic pair, completeness bridges, the invariant-theory argument from the Cartan cubic to the ideal-valued radical, the classical all-rank argument, global group integrations, branching and chiral index. Their finite computational parts have the support described above. The chiral-index coefficient is a statement about the classified representation.

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
