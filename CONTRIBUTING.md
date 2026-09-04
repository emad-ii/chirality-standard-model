# Contributing

Changes should preserve the repository's authority boundaries.

1. Identify the affected claim or verification step. Update the paper when its mathematical statement or proof changes; code and documentation improvements can stand on their own.
2. Classify it in `docs/CLAIM_STATUS.md` as proved in the manuscript, Lean checked, independently reproduced, exactly computed, or interpretive.
3. Keep generated data free of expected theorem values whenever Lean can derive them.
4. Never introduce `sorry`, `admit`, project axioms, unsafe declarations, or partial definitions into the public Lean surface.
5. Regenerate deterministic artifacts only with `make regenerate`, review the diff, and run `make all`.
6. Do not broaden release wording beyond the status register.

Install the [local build prerequisites](docs/REPRODUCIBILITY.md#complete-local-gate)
and run `make notebook-setup` once. Before a cold Lean build, optionally run
`lake exe cache get`; `make lean` does not explicitly fetch the Mathlib cache.
For the strict paper-render comparison in `make all`, use the supplied Ubuntu
24.04 devcontainer or the matching CI TeX/Poppler environment.

`make notebook` and `make all` bind notebook execution to `HEAD` by default.
Regenerate affected artifacts and commit the release inputs before the final
gate: execution provenance still requires a clean input tree. For a `v0.1.0`
release checkout, explicitly use `make all NOTEBOOK_REF=refs/tags/v0.1.0`.
This checks execution against the local tag; canonical remote release identity
is established separately by CI or the Colab bootstrap.

For a new incidence claim, add the smallest executable predicate to
`Checker.lean`, state the exact proposition in `Claims.lean`, and expose a
named theorem. Add every public theorem to the axiom audit and claim register.

The root-level master notebook is generated from
`notebooks/build_master_notebook.py`; edit the builder rather than the notebook
JSON. Rebuild it and execute every cell in a clean kernel for validation. Keep
the canonical notebook source-only, with no outputs or execution counts;
executed notebooks belong in CI artifacts and must not be committed.
