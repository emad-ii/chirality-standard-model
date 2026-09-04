# Reproducibility

## Choose the right route

| Route | Best for | Scope |
| --- | --- | --- |
| [Master notebook](../Cubic_Anomaly_Master_Verification.ipynb) | Understanding and reproducing the finite calculation | Complete exact Python evidence, with Lean optional |
| [GitHub Codespaces](https://codespaces.new/emad-ii/cubic-anomaly-standard-model/tree/release-v0.1.0?quickstart=1) | One-click environment on the `release-v0.1.0` launcher branch | Notebook, Lean, TeX, and Poppler preconfigured |
| [GitHub Actions](https://github.com/emad-ii/cubic-anomaly-standard-model/actions/workflows/ci.yml?query=branch%3Arelease-v0.1.0+event%3Apush) | The clean, hosted push gate for the release launcher | Normal and optimized Python, notebook, Lean, and committed-PDF verification |
| `make all` | Complete local content gate | Workflow-contract guard, normal and optimized Python, notebook, Lean, and committed-PDF verification |

The notebook is the explanatory surface. `make all` reproduces every content
lane and validates the workflow contract locally. GitHub Actions adds the
remote-ref identity evidence that a local checkout cannot establish.

## Bind every route to the release commit

The canonical release object is the `v0.1.0` tag resolved to its peeled,
40-character commit SHA. The `release-v0.1.0` branch is only a launcher for
Codespaces and its branch-specific CI badge. Every non-PR Release CI run
fetches `main`, the annotated tag, and the launcher and rejects the run unless
all three, the checked-out HEAD, and the triggering SHA resolve to one commit.

Before a release review, record the result of:

```bash
git fetch --tags origin
git rev-parse 'origin/main^{commit}'
git rev-parse 'v0.1.0^{commit}'
git rev-parse 'origin/release-v0.1.0^{commit}'
git rev-parse 'HEAD^{commit}'
```

All four reported commits must agree in a release checkout or Codespace.
Record the exact Actions run URL and verify its head SHA is the same value. The
Colab provenance receipt records the tag-resolved commit used for its download.
An extracted source archive can reproduce the computation, but its tag-to-SHA
provenance remains **UNVERIFIED** unless that mapping is established through an
independent authenticated source.

## Complete local gate

Local prerequisites:

- Git, GNU Make, Bash, `curl`, and Python 3.12 with `venv` and `pip` support.
- Elan with `lake` on `PATH`, plus a native C/C++ build toolchain (Ubuntu's
  `build-essential`). Initial toolchain/dependency setup needs network access.
- TeX Live and `latexmk`. The Ubuntu 24.04 paper lane installs `latexmk`,
  `lmodern`, `texlive-fonts-recommended`, `texlive-latex-extra`, and
  `texlive-pictures`.
- Poppler's `pdfinfo`, `pdftotext`, `pdftoppm`, `pdffonts`, and `pdfdetach`
  (`poppler-utils` on Ubuntu).

The supplied [devcontainer](../.devcontainer/Dockerfile) provides the Ubuntu
24.04 environment used for the strict paper check. Other TeX/Poppler versions
may build a valid PDF but fail the exact rendering comparison in `make all`.

From a clean checkout with these prerequisites installed:

```bash
make notebook-setup
lake exe cache get # optional, recommended before the first local Lean build
make all
```

The Python verification layer uses only the standard library. The setup target
creates an isolated `.venv` for the notebook dependencies, and subsequent
`make` targets select it automatically. CI uses Python 3.12. Lean and Mathlib
versions and source revisions are pinned. Elan obtains the version-selected
toolchain on first use. `make lean` runs `lake build` and the formal checks;
it does not explicitly fetch the Mathlib cache. The optional `lake exe cache get`
step fetches the source-keyed cache before building. Without a usable cache,
a cold source build can take substantially longer; subsequent builds are
incremental.

For contributors, `make notebook` and `make all` default to `NOTEBOOK_REF=HEAD`.
The legacy `NOTEBOOK_RELEASE_TAG=v0.1.0` override remains supported when
`NOTEBOOK_REF` is unset.
Regenerate affected artifacts and commit the release inputs before the final
gate; notebook execution binding still requires those inputs to match HEAD.
For an explicit release audit, start from a clean worktree and select the tag:

```bash
git switch --detach refs/tags/v0.1.0
make all NOTEBOOK_REF=refs/tags/v0.1.0
```

The override selects the expected execution commit; it does not switch the
checkout or establish the remote tag's identity. The release-ref checks above
and the hosted CI receipt establish that separate claim.

These pins fix versions and source revisions, not every downloaded binary.
The hosted Lean lane uses the checksum-verified Elan installer plus the
standard upstream Lean toolchain and Mathlib cache. It reproduces and gates the
result under the trust model stated in
[`FORMALIZATION_BOUNDARY.md`](FORMALIZATION_BOUNDARY.md); it is not presented as
a hermetic, independently attested binary build.

## Notebook

The root-level [`Cubic_Anomaly_Master_Verification.ipynb`](../Cubic_Anomaly_Master_Verification.ipynb)
is the repository's single reader-facing notebook. The canonical notebook is
intentionally source-only, Colab-ready, and runs the complete Python release
gate by default. CI executes it top-to-bottom in a clean kernel and publishes
the fully validated executed notebook as a run artifact. From a local checkout:

```bash
make notebook-setup
make notebook
```

This binds execution to the current `HEAD`. In a clean `v0.1.0` release
checkout, use `make notebook NOTEBOOK_REF=refs/tags/v0.1.0` to explicitly bind
execution to the local release tag. Both routes write the executed artifact to
`build/notebook/Cubic_Anomaly_Master_Verification.executed.ipynb`.

The notebook reconstructs the roots and subsystem orbits, runs both independent
$E_6$ incidence implementations, validates the certificate digest, and invokes
all 16 Python release checks.
The receipt separates two questions: whether the computation ran from the
expected commit, and whether that commit is the canonical release selected by
the remote tag. The local commands above can verify the first against a clean
checkout, but they deliberately leave canonical-release binding **UNVERIFIED**;
a local tag is not independent evidence of its own remote identity. Outside
pull requests, CI waits for the three-way identity job, injects its canonical
commit receipt into the notebook, and strictly validates both bindings. Colab
instead resolves the annotated release tag through GitHub's API before
downloading that exact commit. An exploratory execution without an expected
commit may still run when its content digest matches, but its execution-commit
binding is also **UNVERIFIED**.
Set `RUN_COMPLETE_PYTHON_AUDIT = False` only for a
short exploratory pass; CI always runs the complete notebook unchanged.

### Colab and private access

Codespaces is the primary one-click route for collaborators on this private
repository. The supported Colab path is for the repository owner, who first
authorizes access to the private notebook, or downloads the `.ipynb` and
chooses **File → Upload notebook**. The owner must then create a fine-grained
GitHub token
restricted to this repository with **Contents: read-only**, add it through
Colab's key icon as the secret `GITHUB_TOKEN`, and permit the notebook to access
that secret. Never paste the token into a cell. The setup cell downloads the
source through GitHub's API without printing the credential.

GitHub fine-grained tokens do not currently support repository-collaborator
access to another user's private repository. This project does not recommend
the broader classic-token workaround. Collaborators should therefore use
Codespaces while this repository is private. No token is needed after public
release.

Lean is intentionally optional inside the notebook. Set
`RUN_LEAN_IF_AVAILABLE = True` only where the version-selected `lake` toolchain
is already installed. The dedicated CI lane remains the formal build authority.

## Paper

With TeX Live and `latexmk`:

```bash
make paper
```

The paper includes the primary Python implementation by a path relative to
`paper/`, so compile with `-cd` or from the `paper` directory. If `latexmk`
is installed outside `PATH`, pass its absolute path as
`LATEXMK=/path/to/latexmk make paper` (or on `make all`).

The target writes `paper/build/paper.pdf` and leaves the committed release PDF
untouched. It fixes `SOURCE_DATE_EPOCH` to the recorded manuscript build time
and suppresses pdfTeX's random trailer identifier. CI builds into two different
output directories and requires those two fresh PDFs to be byte-for-byte
equal. Because TeX engines from different distributions can encode identical
documents differently, the committed `paper/paper.pdf` is compared by exact
288-dpi RGB page renders, page-local searchable prose/number
fingerprints, stable metadata and document geometry, and page count. The
equivalent local check is:

```bash
make paper-release-check
```

The exact rendering check targets the Ubuntu 24.04 TeX Live/Poppler environment
in CI and the supplied devcontainer. Other versions may produce a valid PDF
while differing in font metrics or rasterization and failing this strict check.
Use the reference environment for release comparisons; `make paper` alone is
the local PDF build target.

That local target also rejects LaTeX warnings and overfull/underfull boxes and
requires 35 pages. It depends on Poppler's `pdfinfo`, `pdftotext`, `pdftoppm`,
`pdffonts`, and `pdfdetach` commands. The rendered-page check covers the visible equations
and layout; the text fingerprint separately checks searchable prose
words and multi-digit numerical claims on each page while tolerating
noncanonical math-font glyph maps. Stable title, author, subject, keywords,
page geometry, rotation, and encryption fields must agree, and every reported
font must be embedded. External URL annotations, document JavaScript, embedded
or associated files, PostScript XObjects, launch actions, and active-media
objects are rejected.

## Regenerating evidence

Normal verification never rewrites canonical artifacts. Maintainers can intentionally refresh them with:

```bash
make regenerate
```

That sequence regenerates the exceptional audit, regenerates the $E_6$ certificate, writes its SHA-256 receipt, and regenerates the Lean data module. Review every resulting diff. Then run `make all`.

## Determinism contract

- `PYTHONHASHSEED=42` is set for each verifier subprocess.
- Verification invariants use explicit runtime checks, and the release guard
  rejects any optimization-removable Python `assert` statement.
- The complete Python gate runs both normally and with `PYTHONOPTIMIZE=1`.
- Recorded text outputs are compared byte-for-byte.
- Both JSON artifacts are regenerated in temporary paths and compared byte-for-byte.
- The certificate digest must match its committed SHA-256 receipt.
- Generated Lean data must match the JSON conversion byte-for-byte.
- Lean independently validates the root coordinates and reflection tables.
- The exceptional Lean census starts from five authored Cartan matrices and
  imports neither the six-row table nor the cubic-index table.
- The canonical notebook's authored cells and stable metadata must match its builder.
- The notebook executes top-to-bottom in a clean kernel and reports separate
  execution-commit and canonical-release provenance bindings.
- The notebook's input digest excludes named desktop and TeX by-products;
  arbitrary Git ignore rules cannot hide changes to source inputs.
- The paper is rebuilt twice from source with fixed metadata; CI requires the
  two fresh builds to be byte-for-byte identical and requires the committed
  PDF to have the same exact 288-dpi RGB renders, page-local searchable
  prose/number fingerprints, stable metadata, and page count; all fonts must
  be embedded.

## CI gate

[`ci.yml`](../.github/workflows/ci.yml) has six jobs: one release-identity job,
four independent content jobs, and the final `release-gate` aggregator:

1. **Release identity** — outside pull requests, requires `main`, the annotated
   tag, the launcher, the event SHA, and checked-out HEAD to resolve to one
   commit.
2. **Python verification** — the workflow-contract mutation tests, all exact
   programs and deterministic artifacts, repeated with interpreter
   optimizations enabled.
3. **Notebook** — builder-freshness check followed by clean-kernel execution of
   the complete master notebook. Outside pull requests it depends on the
   release-identity job, receives that job's canonical commit output, and
   strictly validates both the execution commit and canonical release receipt.
4. **Lean** — version/source-pinned build under the disclosed upstream
   compiler/cache trust boundary, generated-data freshness, placeholder guard,
   and axiom receipt.
5. **Paper** — two clean, byte-identical LaTeX builds; exact 288-dpi RGB
   render, page-local searchable-fingerprint, stable-metadata, and page-count
   equality with the committed release PDF; embedded fonts; no active content;
   and warning-free, nonempty build logs.

6. **Release gate** — aggregates the four content results and, outside pull
   requests, requires the release-identity result as well.
The owner, or a collaborator with write access, can start the same clean run
from the repository's **Actions** page by opening **Release CI** and choosing
**Run workflow**. Manual dispatch requires write access to the repository.
Select `release-v0.1.0`,
then record the resulting run URL and confirm its head SHA against the peeled
`v0.1.0` commit before treating it as release evidence.
