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

The [all-rank structural theorem](../CubicAnomaly/Classification/AllRankComplex.lean)
now proves irreducibility, faithfulness, ambient simplicity, isotropy
semisimplicity and maximality for an effective proper compact pair with complex
commutant and a nonzero full cubic radical. It constructs a Hermitian matrix
realization of the complex half from the compact form and commutant, explicitly
intertwined with the entire adjoint complement. No separate realization witness
is assumed. The structural conclusions, the matrix bracket law and scalar
central action are proved. There is no rank bound. The same original
hypotheses now also give absolute simplicity of the ambient complexification,
nondegenerate complex Killing forms, a nonsymmetric complement, and the
actual complementary irreducible inequivalent dual halves.

The [canonical-half equivalence](../CubicAnomaly/Classification/CanonicalHalf.lean)
identifies the positive eigenspace with the exact matrix action used by the
anomaly. [Scalar extension](../CubicAnomaly/Classification/AnomalyComplexification.lean)
preserves and reflects the full radical. The
[Cartan proof](../CubicAnomaly/Classification/CartanCubic.lean) reduces it to
a finite tensor-matrix kernel, testing every mixed pair of Cartan basis
inputs. The [actual weight formula](../CubicAnomaly/Classification/CanonicalAnomaly.lean)
expresses that matrix as a sum of weight-coordinate products with actual
generalized weight multiplicities. No invariant-polynomial classification
or supplied eigenbasis is used. The all-rank endpoint constructs the Cartan
and the nonzero kernel vector from the original hypotheses.

The [coroot criterion](../CubicAnomaly/Classification/CanonicalCoroot.lean)
now reduces this further: the full radical is nonzero exactly when an actual
nonzero coroot annihilates every mixed pair of Cartan basis inputs in the
weight formula. [Coroot ideals](../CubicAnomaly/Classification/CorootComponents.lean)
are proved simple, and the entire radical is their sum over all coroots
passing those tests. These are actual Lie ideals, without supplied simple-type
labels. Identifying their weights and components with the authored finite
census remains necessary.

[Internal ideal tests](../CubicAnomaly/Classification/CubicIdealDecomposition.lean)
now recover the full radical as well: perfectness of semisimple ideals,
invariance and symmetry kill all mixed terms between complementary ideals.
Thus an ideal's internal cubic vanishes exactly when the entire ideal lies
in the full radical.

The [structural foundations](../CubicAnomaly/Classification/Structural.lean),
[ambient simplicity proof](../CubicAnomaly/Classification/CompactSimple.lean),
and [cubic radical proof](../CubicAnomaly/Classification/CubicRadical.lean) use
actual Mathlib Lie algebras, modules and ideals. The
[root-lattice module](../CubicAnomaly/Classification/RootSaturation.lean) proves
saturation for arbitrary finite crystallographic root pairings over
characteristic-zero integral domains, including actual complex Lie root
systems. The new
[all-rank intrinsic endpoint](../CubicAnomaly/Classification/IntrinsicToral.lean)
derives a dichotomy directly from the original hypotheses: the isotropy has
strictly smaller geometric abelian rank, or the actual ambient algebra has
a nonzero integer-root-lattice character into `ZMod 3`. Its grades are exactly
the complexified isotropy and the actual positive and negative complex halves;
they form an internal direct sum and satisfy the bracket degree law. On the
same constructed Cartan, the endpoint now also derives full rational rank
of the zero-grade roots, connected support graphs for both halves, exact
root-count/dimension identities and the grade-one root-cubic anomaly.

[Compact Cartans](../CubicAnomaly/Classification/CompactCartan.lean) constructs
the ambient common Cartan when the two geometric abelian ranks agree. Here
rank means the explicitly defined maximum dimension of an abelian subalgebra;
no identification with Mathlib's characteristic-polynomial rank is asserted.
[Common-Cartan geometry](../CubicAnomaly/Classification/CommonCartan.lean)
derives the closed contained-root subsystem and zero-grade identity.
[The actual dual halves](../CubicAnomaly/Classification/EqualRank.lean)
force three-class support, and nonsymmetry forces order three.
[Toral characters](../CubicAnomaly/Classification/ToralCharacter.lean) restricts
the degree map to the actual integer root lattice.
[The intrinsic basis](../CubicAnomaly/Classification/RootLatticeBasis.lean)
is now constructed: the actual lattice is finite free of rank `dim H`, and
has exactly `3^(dim H)` characters.
[Root coordinates](../CubicAnomaly/Classification/RootCharacterCoordinates.lean)
identify grade membership, root counts and graph edges with finite
coordinate predicates. No integer basis, grading-support or classification
witness is supplied to the all-rank endpoint.

[Full zero-root rank](../CubicAnomaly/Classification/FullRankRoots.lean)
follows from centrelessness and the actual root decomposition.
[Root support](../CubicAnomaly/Classification/RootSupportGraph.lean) is connected
because its component spans are invariant, and
[the converse](../CubicAnomaly/Classification/RootGraphCriterion.lean) uses
nonzero actual root brackets under the stated root-space hypotheses.
[Root dimensions](../CubicAnomaly/Classification/RootSupportDimension.lean)
give `dim h = dim H + #Ψ`, `dim V = #R₁`, and `#R₁ = #R₂`.

[The literal Cartan lift](../CubicAnomaly/Classification/ContainedCartan.lean)
identifies the common ambient Cartan with a Cartan of the actual isotropy
complexification, preserving inclusion. [The root trace formula](../CubicAnomaly/Classification/RootSupportTrace.lean)
proves the supported roots are exactly the module's weights, each of
multiplicity one. [The canonical transfer](../CubicAnomaly/Classification/CanonicalRootCubic.lean)
identifies the original anomaly action's cubic with
`Σ α∈R₁, α(x) α(y) α(z)`.
[The kernel equivalence](../CubicAnomaly/Classification/RootCubicKernel.lean)
then detects the original full radical using this actual root-cubic matrix
on the same Cartan. This discharges every mixed insertion; it is not only
a test of diagonal cubic values. Identification with authored root tables
and semantic completeness of their executable algorithms remain open.

[The intrinsic Cartan basis](../CubicAnomaly/Classification/IntrinsicCartanBasis.lean)
now makes every root evaluation literally its constructed integer coordinate.
[The coordinate cubic](../CubicAnomaly/Classification/CoordinateCubic.lean)
is therefore an exact integer matrix: sum the triple coordinate products
over actual roots whose coordinate dot product with the character is one
modulo three. [Kernel descent](../CubicAnomaly/Classification/RationalKernel.lean)
proves nonzero complex and rational kernels are equivalent for this matrix.
[The intrinsic anomaly theorem](../CubicAnomaly/Classification/IntrinsicAnomaly.lean)
connects that rational test to the original full radical. The all-rank
intrinsic endpoint derives a nonzero rational kernel vector on the same
constructed Cartan, without a supplied basis or coordinate witness.

A uniform [derivation argument](../CubicAnomaly/Classification/CyclicBracket.lean)
eliminates the symmetric branch without an equal-rank assumption.
[The involution obstruction](../CubicAnomaly/Classification/InvolutionObstruction.lean)
strengthens this: every involutive real Lie automorphism fixing the isotropy
pointwise is the identity, with no extra form-preservation hypothesis.
For the actual orthogonal ambient algebra,
[the defining module](../CubicAnomaly/Classification/OrthogonalDefining.lean)
is consequently proved irreducible over the reals and irreducible and
self-dual after complexification.
[Special-unitary irreducibility](../CubicAnomaly/Classification/UnitaryDefining.lean)
now follows from a traceless skew-Hermitian operator constructed from an
invariant projection, contradicting the zero ambient centralizer.
[Symplectic irreducibility](../CubicAnomaly/Classification/SymplecticDefining.lean)
follows by forcing the invariant projection to preserve the quaternionic
structure and then excluding its reflection involution.
[The actual alternating form](../CubicAnomaly/Classification/SymplecticForm.lean)
proves self-duality of that complexified defining module. These endpoints
use the original compact-pair hypotheses for the three concrete classical
constructions.

[Special-unitary isotropy simplicity](../CubicAnomaly/Classification/UnitarySimplicity.lean)
is now proved over both the reals and the actual complexification, in every
dimension. The assumed nonzero full cubic radical consequently equals the
whole isotropy, giving vanishing of every mixed cubic entry.
[The orthogonal and symplectic factor reduction](../CubicAnomaly/Classification/ClassicalIsotropyFactors.lean)
excludes three disjoint simple isotropy factors and leaves either simple
isotropy or exactly two atomic ideals whose sum is the whole algebra.
These arguments use actual nonzero products of ideal actions, proved tensor
irreducibility and Killing-form self-duality, and actual equivariant
complexification lifts. No tensor-factorization witness is an input.

[Evaluation](../CubicAnomaly/Classification/TensorEvaluation.lean) separately
constructs the two-factor defining tensor decomposition, with actual
irreducible faithful factor actions. [Coefficient forms](../CubicAnomaly/Classification/TensorFactorDuality.lean)
and [Schur scalarity](../CubicAnomaly/Classification/TensorFormFactorization.lean)
construct invariant nondegenerate factor forms and prove the original form
factors. The [actual adjoint trace pairings](../CubicAnomaly/Classification/AdjointTraceForms.lean)
give self-duality of the self-adjoint and traceless self-adjoint operator
modules. The final two-factor exclusion and highest-weight analysis remain
open.

The actual complexifications are also constructed:
[special-unitary to Mathlib `sl`](../CubicAnomaly/Classification/UnitaryComplexification.lean),
[orthogonal to Mathlib `so`](../CubicAnomaly/Classification/OrthogonalComplexification.lean),
and [symplectic to the preserver of the actual alternating form](../CubicAnomaly/Classification/SymplecticComplexification.lean).
The `sl` and `so` matrix constructions supply their own finite bases and
prove defining-action compatibility. This does not classify an arbitrary
simple compact ambient algebra into the concrete families.
[Quadratic restriction](../CubicAnomaly/Classification/QuadraticRestriction.lean)
proves the actual dimension equation and the Killing-form identity
`κ_g|h = κ_h + 2 Tr_V(ρ(x)ρ(y))`; normalized Dynkin-index integrality and
completeness of the integer sieve remain separate.

[Actual root dimensions](../CubicAnomaly/Classification/KillingDimension.lean)
and the original anomaly hypothesis now derive
[the exceptional search bounds](../CubicAnomaly/Classification/SieveBounds.lean):
ambient dimensions `52, 78, 133, 248` imply half-dimensions at most
`23, 36, 65, 121`, respectively. The
[rank-one obstruction](../CubicAnomaly/Classification/RankOneObstruction.lean)
also excludes strict rank deficiency for an actual even-dimensional ambient
algebra of geometric abelian rank two. No Lie-type labels are inferred from
those numerical hypotheses.

The
[classical arithmetic](../CubicAnomaly/Classification/Classical.lean) and
[Weyl products](../CubicAnomaly/Classification/ClassicalWeyl.lean) prove the
type-A cubic formula and both infinite D-type dimension gaps without bounded
sampling or assumed rational ratio identities in their final product theorems.
The [classical toral module](../CubicAnomaly/Classification/ClassicalToral.lean)
proves strict zero-grade rank drop for every nonzero order-three functional
on the explicit integral A, B, C and D root lattices, including the
lattice-to-coordinate extension argument, uniformly in rank.

The [formal scope document](../formal/README.md) gives exact hypotheses and
lists the remaining representation-theoretic and classification bridges.
**The full uniqueness theorem over all compact Lie-algebra pairs is not yet
formalized.**

The [exceptional classification module](../CubicAnomaly/Classification/Exceptional.lean) starts from authored Cartan matrices and integer symmetrizers for G2, F4, E6, E7 and E8. It reconstructs roots by reflection closure, exhausts root-lattice functionals modulo two and three up to Weyl action, checks the relevant component and grade-graph signatures, and evaluates the exact grade-one trace cubic on coroot spanning sets. This census is independent of the JSON certificate.

The [selection module](../CubicAnomaly/Classification/Selection.lean) turns
that checked cubic table into a universal uniqueness theorem, its converse,
and an `∃!` statement inside the explicitly stated exceptional finite census.

The [E6 checker](../CubicAnomaly/E6/Checker.lean) receives root coordinates, reflection permutations, a highest-root witness and six orbit seeds through the [generated data module](../CubicAnomaly/E6/Data.lean). It validates the witnesses against the fixed Cartan formulas and reconstructs the finite incidence calculation. It checks:

- Root closure, signs, squared lengths, reflection formulas and highest-root order.
- Closed subsystem masks with the rank/root-count signatures of D5, A5+A1 and A2³, in orbits of sizes 27, 36 and 40.
- A 38,880-element triple space covered by six disjoint simultaneous-reflection orbits.
- The six-cell intersection distribution and the two extrema.
- The exact ranks and root counts of all three pair types, and strict D-A dominance by root count and by rank plus root count for every member of the triple universe.
- A closed irreducible six-root, rank-two component exactly in the two extremal cells.
- Common-subsystem multiplicities, context counts and 8,640 labelled containments.

Conventional root-system names use standard ADE classification. The theorem statements and expected counts are authored in Lean, not copied from JSON summary fields. The data-freshness check verifies the translation from JSON to Lean; Lean separately validates those witnesses. The [exported theorem audit](../formal/AxiomAudit.lean) includes `CubicAnomaly.E6.finite_certificate_valid` and the separate intrinsic-ordering theorems, together with the new structural and classical results. Pair ranks are calculated from the integer root coordinates. The paper proves that rank plus root count is the dimension of the corresponding semisimple Lie algebra, and that the structural selection is equivalent to the chiral-dimension characterization.

### Trust model

The finite computations use `native_decide`. The axiom audit checks the original
finite theorems and the selection results derived from them against this exact receipt:

```text
propext
Quot.sound
Lean.ofReduceBool
Lean.trustCompiler
```

The first two are foundational Lean axioms; the last two connect compiled evaluation to the theorem.
The manifest contains **666 public theorem exports**: **637 deductive** and
**29 finite/native-derived**. The deductive structural, root-lattice and
classical theorems use only a
subset of `propext`, `Classical.choice`, and `Quot.sound`; compiler-evaluation
axioms are rejected for that class. Every receipt is matched to its fully
qualified theorem name. Self-tests reject missing, duplicate, unknown or
mislabeled receipts and compiler dependencies in deductive proofs.
The check also rejects unfinished proofs, project axioms, unsafe declarations
and partial definitions. Compiler binaries and optional build caches come
from their standard upstream distributions.

### Manuscript proofs

The paper supplies the homogeneous realization of the algebraic pair, the
remaining classification/completeness and representation-theoretic bridges,
identification of the classified actual weights and ideals with the finite
census, global group integrations, branching and chiral index. The Lean
modules discharge the real and complex structural reduction, the actual
dual-pair construction, the geometric rank-deficient-or-intrinsic-toral-data
dichotomy, same-Cartan root-cubic detection and reconstruction of the full
radical from actual simple ideals, the defining-module irreducibility step
for all three concrete compact classical constructions, actual complexification
bridges, dimension and quadratic restriction identities, derived exceptional
search bounds, root-lattice saturation, classical order-three exclusion and
unbounded classical arithmetic described above.
They do not replace the remaining classification argument. The chiral-index
coefficient is a statement about the classified representation.

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
