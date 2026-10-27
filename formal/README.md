# Formal proof scope

The Lean development contains a rank-independent structural reduction for
actual compact real Lie algebras and their complexifications, a direct
Cartan-matrix criterion for the full anomaly radical, uniform root-lattice
and classical arithmetic theorems, and an explicit uniqueness theorem inside
the finite exceptional census. **The manuscript's global uniqueness theorem over all compact
Lie-algebra embeddings is not yet a Lean theorem.** The remaining bridges are
listed below.

The toolchain remains Lean 4.28.0 with the exact Mathlib revision in
`lake-manifest.json`. No project axioms or unfinished proofs are used.

## The structural reduction

The original real structural entry point is

```lean
CubicAnomaly.Classification.HermitianRealization.all_rank_structural_reduction_of_commutant
```

Its conclusion is the conjunction

```lean
LieModule.IsIrreducible ℝ h (orthogonalComplement B h) ∧
  LieModule.IsFaithful ℝ h (orthogonalComplement B h) ∧
  LieAlgebra.IsSimple ℝ g ∧
  LieAlgebra.IsSemisimple ℝ h ∧
  IsCoatom h
```

These are Mathlib's Lie-module, simple-Lie-algebra, semisimple-Lie-algebra,
and maximal-proper-element notions. They are not Boolean flags attached to
an enumerated candidate.

The hypotheses are:

1. A finite-dimensional real Lie algebra `g` with `CompactForm g`: a symmetric,
   positive definite, ad-invariant real bilinear form.
2. A proper Lie subalgebra `h` and `Effective h`: every ambient ideal contained
   in `h` is zero.
3. An actual real-algebra equivalence between the endomorphisms commuting with
   the action on the entire orthogonal complement and `ℂ`.
4. Nonvanishing of the full trace-cubic radical of the complex half constructed
   from that commutant equivalence.

There is no upper bound on rank, dimension, or matrix size. The complex-half
record contains no faithfulness, irreducibility, simplicity, semisimplicity,
maximality, scalar-centre, or classification field. Even its matrix commutator
law is derived from the Lie action rather than assumed.

The theorem constructs its Hermitian realization automatically. The definition
`hermitianHalfOfCommutant B h e` supplies the complex coordinates, Hermitian
generators, and intertwining equation `ρ(x) = I • T(x)`. The auxiliary theorem
`AllRank.all_rank_structural_reduction` is also available for an explicitly
supplied realization. Neither version assumes any of its structural conclusions.

Writing `V := hermitianHalfOfCommutant B h e`, the exact cubic hypothesis is
`V.cubicRadical ≠ ⊥`. Membership in this genuine Lie ideal means
`∀ y z, (1/2) * trace (T(x) * (T(y) * T(z) + T(z) * T(y))) = 0`.

### What the structural proof does

`HermitianRealization.lean` transports complex scalar multiplication through
the commutant equivalence and proves that the Lie action is complex-linear.
If `J` is multiplication by `I`, the positive real form is symmetrized to
`S(x,y) = B(x,y) + B(Jx,Jy)`. The formula
`H(x,y) = S(x,y) + I * S(Jx,y)` defines a positive invariant Hermitian form
with Mathlib's conjugate-linear first-slot convention. An orthonormal complex
basis gives matrices `T = -I * ρ`; invariance proves they are Hermitian.
The construction uses the entire adjoint complement.

`Structural.lean` constructs invariant orthogonal complements. For any
invariant submodule, its orthogonal projection belongs to the commutant.
Transporting this idempotent to `ℂ` makes it zero or one, proving
irreducibility. Intermediate subalgebras would give invariant submodules,
which proves maximality. The annihilator of an invariant complement is
constructed as an ambient ideal; effectivity makes it zero and proves
faithfulness.

The same file transports multiplication by `I` to an equivariant complex
structure. An irreducible real module with such a structure has no nonzero
fixed vector. Projecting the ambient centre to the complement therefore
places it inside `h`, and effectivity kills it. Positive definiteness also
proves that every abelian ambient ideal is central and that a compact
centre-free algebra is semisimple.

`CompactSimple.lean` proves ambient simplicity without assuming a
classification or a direct-sum decomposition into classified simple factors.
Every nonzero ambient ideal projects onto the irreducible complement. If two
nonzero complementary ideals existed, effectivity would make either
projection an isomorphism. The transported complex structure would lie in
the centroid of a compact ideal. The invariant positive form then forces
that ideal to be abelian, contradicting the vanishing centre.

`CubicRadical.lean` defines the full radical of an invariant trilinear form
as a genuine Lie ideal. Its membership condition quantifies over **both**
remaining inputs. For Hermitian matrix generators, an equivariant operator
has a real eigenvalue. Irreducibility makes its eigenspace the entire module,
which proves scalar action of central generators. The mixed insertion
`c(x,z,x)` becomes a scalar times `trace (T(x) * T(x))`; the Hermitian
trace-square theorem and faithfulness force `x = 0`. Thus a nonzero radical
forces the centre of `h` to vanish. Restricting the compact form to `h` then
proves its semisimplicity.

`quotientComplementEquiv` in `Structural.lean` is an actual equivariant
isomorphism between the literal quotient `g ⧸ h.toLieSubmodule` and the
chosen invariant complement. The use of the orthogonal complement is
therefore connected formally to the quotient formulation.

### Actual complexification and the completed structural endpoint

The stronger combined entry point is

```lean
CubicAnomaly.Classification.AllRankComplex.all_rank_complex_structural_reduction
```

It takes exactly the compact form, effective proper subalgebra, complex
commutant equivalence, and nonzero full cubic radical above. In addition to
the five real conclusions, it proves:

- `LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g)`.
- `LieAlgebra.IsKilling` for both `ℂ ⊗[ℝ] g` and `ℂ ⊗[ℝ] h`.
- A nonsymmetric complement: some `x,y ∈ q` have `[x,y] ∉ h`.
- A complementary pair of actual submodules of `ℂ ⊗[ℝ] q`, the `I` and `-I`
  eigenspaces of the extended commutant complex structure. Both are
  irreducible for `ℂ ⊗[ℝ] h`; the negative half is equivariantly isomorphic
  to the dual of the positive half, and the two halves are inequivalent.

`CompactKilling.lean` identifies the real Killing kernel with the centre
using the trace square of skew-adjoint adjoint operators. `Complexification.lean`
proves the real/imaginary decomposition of every tensor, reflection of real
subspace membership, and scalar extension of the Killing form itself.
`AbsoluteSimplicity.lean` rules out a proper complex ideal by transferring
multiplication by `I` through its real projection: this would produce the
already excluded complex centroid of a compact real simple algebra.

`ComplexHalf.lean` constructs the positive half from
`m ↦ 1 ⊗ m - I ⊗ Jm`, with the real projection as inverse. This proves its
irreducibility directly from real irreducibility; applying `-J` handles the
negative half. `ComplexDuality.lean` proves that the extended positive form
is a nondegenerate invariant complex bilinear form, that both halves are
isotropic, and that the mixed pairing identifies them as dual modules.
Transporting an opposite-half intertwiner back to the real module makes it
both commute and anticommute with `J`, hence vanish. No duality or
inequivalence witness is an input.

`AmbientComplexification.lean` embeds these halves into the actual ambient
`ℂ ⊗[ℝ] g`, identifies their sum with `q.baseChange ℂ`, preserves the
complementary isotropy subspace, and transports irreducibility. The canonical
Hermitian coordinates are proved compatible with `J` in
`HermitianRealization.lean`; `CanonicalHalf.lean` identifies the actual
positive half with the complex matrix representation used for the anomaly.

### Uniform elimination of the symmetric branch

`CyclicBracket.lean` eliminates the entire involutive branch by one argument.
The commutant complex structure is proved skew-adjoint for the original
positive invariant form. If `[q,q] ⊆ h`, extending `J` by zero on `h` gives
a derivation of `g`. The nondegenerate Killing form makes it inner. Its
generator centralizes `h`, but the ambient centralizer is zero when `h` is
centreless and the complement is irreducible of complex type. This
contradicts `J² = -1` on the nonzero complement.

Thus `symmetric_complex_complement_cubic_radical_eq_bot` holds in the
original real domain, without an equal-rank assumption or a classification
of symmetric pairs.

### The full anomaly radical is detected on a Cartan subalgebra

`CartanCubic.lean` proves Cartan restriction directly for invariant symmetric
trilinear forms on finite-dimensional Killing Lie algebras. Invariance kills
root pairs whose weights do not sum to zero. Opposite roots are handled by
invariance with one root vector and one Cartan input. Consequently a Cartan
element is in the full mixed radical exactly when all its Cartan insertions
vanish. An additional root-space argument proves that an ideal is determined
by its intersection with the Cartan.

For a Cartan basis `b`, define the rectangular matrix

\[
M_{(j,k),i}=c(b_i,b_j,b_k).
\]

The theorem `radical_ne_bot_iff_cartan_matrix_kernel` proves that the full
Lie-ideal radical is nonzero exactly when this finite matrix has a nonzero
kernel vector. This needs neither a simple-factor decomposition nor a
classification of invariant polynomials. `CartanTrace.lean` proves the
required invariance and full symmetry for the actual matrix trace cubic.

`AnomalyComplexification.lean` constructs the genuine representation
`ρ = I • T` from the Hermitian convention and extends it to `ℂ ⊗[ℝ] h`.
On real inputs its cubic is `-I` times the Hermitian cubic. Hermitian
symmetry makes the latter real, so a complex vector lies in the complex
radical exactly when both its real and imaginary coordinates lie in the
original radical. In particular, as actual subspaces,

\[
\operatorname{Rad}(c_{\rho_{\mathbb C}})
=\mathbb C\otimes_{\mathbb R}\operatorname{Rad}(c_T).
\]

`hermitian_radical_ne_bot_iff_cartan_matrix_kernel` therefore applies to the
original anomaly condition. The endpoint
`AllRankComplex.all_rank_nonzero_cartan_anomaly_kernel` constructs an actual
Cartan subalgebra and its finite basis and derives a nonzero kernel vector
directly from the original compact-pair hypotheses.

`WeightCubic.lean` proves the trace of every product of commuting action
operators is the corresponding sum of actual weights with generalized
weight-space multiplicities. Nilpotent parts disappear from the trace, so a
diagonal eigenbasis is not assumed. `MatrixCubic.lean` proves trace-cubic
invariance under an actual intertwining coordinate equivalence.
`CanonicalAnomaly.lean` combines these with the canonical positive half:

\[
M_{(j,k),i}
=\sum_{\chi\in\operatorname{Wt}(V)}
  \dim(V_\chi)\,\chi(b_i)\chi(b_j)\chi(b_k).
\]

`canonical_anomaly_iff_cartan_weight_kernel` is an equivalence for the
original full radical. `AllRankComplex.all_rank_nonzero_cartan_weight_kernel`
constructs a Cartan and a nonzero vector in this actual weight matrix's
kernel from the original hypotheses. Identifying the resulting actual
weights with an authored finite root table remains part of the
classification-to-census bridge.

## Root-lattice reduction and finite uniqueness

`RootReduction.lean` proves saturation over `ℝ`.
`RootSaturation.lean` strengthens this to every finite crystallographic
Mathlib `RootPairing` over a characteristic-zero integral domain, including
the actual complex Lie root systems: a closed subsystem satisfies

\[
\Phi\cap\langle\Psi\rangle_{\mathbb Z}=\Psi.
\]

The stronger proof pairs an integral expression for a root with its own
coroot. The integer pairings sum to `2`, so one is positive; root subtraction
shortens the expression. This avoids imposing an order on complex scalars.
The Lie wrappers use Mathlib's actual roots as functions on the Cartan,
with the same integer-span carrier as the grading construction.

`RootGrading.lean` groups actual generalized weight spaces by additive
degree. The components are independent, span the module, and satisfy the
bracket degree law. Irreducibility makes all weights congruent modulo the
integer span of the acting algebra's roots. Saturation identifies the zero
grade of the quotient by a closed subsystem lattice with the common
Cartan plus the subsystem root spaces.

If actual root support is contained in `0,c,-c`, properness of the zero grade
forces `c ≠ 0`. If `c` did not have order three, every bracket of off-zero
components would lie in grade zero, including the order-two case. The
uniform nonsymmetry theorem excludes this. The compact-pair endpoint
`compact_pair_cyclic_root_grading` constructs an internal `ZMod 3` grading
and its bracket law. It requires the common-Cartan support and the
identifications of the zero/off-zero components with the given pair; those
geometric identifications are explicitly retained as hypotheses.

`RootSimple.lean` proves that an ideal's Cartan intersection is invariant
under coroot reflections using actual root `sl₂` triples. With Cartan
detection of ideals, this proves the converse to Mathlib's
simple-algebra-to-irreducible-root-system implication. Thus simplicity is
equivalent to irreducibility of the actual root system over algebraically
closed fields of characteristic zero, without a simple-type list.

`Selection.lean` derives universal uniqueness, existence, an iff
characterization, and an `∃!` theorem from the existing exceptional cubic
table. The exact endpoint is

```lean
CubicAnomaly.Classification.Selection.finite_cubic_selection_exists_unique
```

Its universe is explicitly the five authored exceptional Cartan data and
the rows produced by their finite order-three censuses. A nonempty null
component list selects exactly the `E8` record with 78 grade-zero roots,
81 grade-one roots, component signatures `#[(6,2),(72,6)]`, and null
component signature `#[(72,6)]`. This does not assume that every compact
pair already belongs to that finite universe.

## Classical arguments without a rank cutoff

`ClassicalToral.lean` proves the classical order-three exclusion directly on
the integral root lattices of A, B, C and D. For every nonzero `ℤ`-linear
functional from one of these root lattices to `ZMod 3`, the rational span of
the zero-grade roots has strictly smaller dimension than the ambient root
span. The four final `typeA/B/C/D_order_three_rank_drop` theorems quantify
over all ranks; no bounded table of classical cases is used.

The passage from lattice functionals to coordinate gradings is also proved.
For B, C and D, the roots generate each doubled coordinate vector and two
is invertible modulo three. For A, differences from a fixed coordinate
generate its sum-zero lattice. Lifting residues to `{-1,0,1}` puts every
zero-grade root in a proper rational hyperplane. The comparison with the
ambient root span handles A's sum-zero realization without confusing its
rank with the number of coordinates. Connecting an arbitrary classical Lie
algebra to these explicit root lattices remains a classification bridge.

`Classical.lean` proves the entire finite sum for the type-A support cubic,
not merely an identity for two unspecified coordinates:

\[
C_3=-6a(2a+N-2i)\ne0
\quad(a>0,\ 1\le i,\ 2i<N).
\]

It also proves uniform rational inequalities and exterior-square dimension
gaps, a binomial lower bound, and the four stated exceptional arithmetic
gaps. The arithmetic of the four authored exceptional dimensions does not
by itself establish their representation-theoretic interpretation.

`ClassicalWeyl.lean` goes further for the infinite D-type families. It
defines the full products over the positive roots `e_k-e_l` and `e_k+e_l`,
proves the product recurrences, derives both displayed rational ratio
identities, and proves the dimension lower bounds. Its two final theorems

```lean
Classical.typeD_weyl_exterior_gap_one
Classical.typeD_weyl_exterior_gap_two
```

have only `r : ℕ` and `5 ≤ r` as hypotheses. The Weyl-ratio identities and
dimension bounds are not assumptions in those final results. They apply
even beyond the odd ranks needed by the manuscript. Identifying these
explicit root products with dimensions of actual highest-weight modules
still requires the representation-theoretic Weyl dimension theorem.

## Remaining work for global uniqueness

The following implications are not supplied by a successful build of the
current project:

| Remaining bridge | What must be established |
| --- | --- |
| Common-Cartan geometry and support | For the equal-rank branch, construct a common Cartan and its closed subsystem and identify the actual pair with the zero/off-zero root-lattice components; compose the proved weight-coset and grading results through these identifications |
| Classification and census interpretation | Exhaustive reduction of actual simple Lie algebras to classical or exceptional root data, with isomorphisms respecting the subalgebra and representation; identification of the classical root lattices with the explicit realizations in `ClassicalToral.lean` |
| Exceptional rank-deficient branch | Formalization and completeness of the Weyl-dimension/Dynkin-index sieve currently implemented in Python |
| Classical representation branch | Irreducibility of the defining module, simplicity of the subalgebra in that branch, the canonical highest-weight constituents and support classification, and the Weyl-dimension and cubic-index interpretations |
| Census-to-Lie interpretation | Identify the authored finite root coordinates, module weights, coroot spans and component labels with the actual classified Lie algebra and representation; the full-radical-to-Cartan-kernel theorem is already proved |
| Existence and identification | Construction of the compact `E8 ⊃ E6 + A2` inclusion and identification of its complex half with `27 ⊠ 3` |

There is deliberately no theorem that hides these bridges in a field called
"classification" or assumes that an arbitrary pair lies in the six-row
table. The finite selection theorem and the structural theorem are both
proved, but they are not yet connected by the full classification argument.

## Verification and trust

Run from the repository root:

```sh
lake exe cache get
lake build
python3 formal/scripts/check_generated_data.py
python3 formal/scripts/check_formal_hygiene.py
python3 formal/scripts/check_formal_hygiene.py --self-test
```

The hygiene checker keeps an explicit export manifest and matches every
`#print axioms` receipt to its fully qualified theorem name. It rejects
missing, duplicate, unknown, and mislabeled receipts as well as unfinished
proofs and project axioms.

The original finite computational theorems and the selection theorems
derived from them retain the exact receipt

```text
propext
Quot.sound
Lean.ofReduceBool
Lean.trustCompiler
```

The new deductive structural, root-lattice and classical proofs are checked
separately. Their permitted dependencies are only

```text
propext
Classical.choice
Quot.sound
```

A deductive theorem that acquires `Lean.trustCompiler`, `Lean.ofReduceBool`,
`sorryAx`, or any other additional axiom fails the audit. Axiom-free proofs
are also accepted in this class. The stricter native receipt is preserved
for the existing finite surface rather than applying one enlarged whitelist
to all theorems.
