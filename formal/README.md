# Formal proof scope

For every finite-dimensional compact real Lie-algebra pair with effective
proper isotropy and a chosen complex commutant equivalence on its entire
adjoint complement, the canonical half has nonzero full mixed cubic radical
if and only if the oriented pair is isomorphic to the constructed compact
E₈ pair. The same real ambient isomorphism carries the isotropy and its
radical onto the fixed isotropy and radical. Its complexification identifies
the two matter eigenspaces with their orientations preserved.

```lean
CubicAnomaly.Fixed.GlobalClassification.anomaly_iff_fixed_pair
CubicAnomaly.Fixed.GlobalClassification.compact_pair_classification
```

The structural reduction produces simple complex ambient type and an
irreducible dual-pair complement. Nested Cartans and root-system
classification give the classical and exceptional alternatives. The
exceptional index and dimension tests force full Cartan rank. The compact
classical models all have zero full cubic radical under the other
hypotheses. The equal-rank classification and the constructed fixed pair
give the forward and reverse implications.
[Global theorem](../CubicAnomaly/Fixed/GlobalClassification.lean) ·
[Ambient alternatives](../CubicAnomaly/Fixed/AmbientClassification.lean) ·
[Equal-rank pair](../CubicAnomaly/Fixed/E8EqualRankRealPair.lean).

The toolchain remains Lean 4.28.0 with the exact Mathlib revision in
`lake-manifest.json`. No project axioms or unfinished proofs are used.

## The constructive fixed target

The new [fixed-candidate scope](FixedCandidate.md) describes a second,
constructive route that does not require excluding every other Lie pair.
The [fixed package](../CubicAnomaly/Fixed.lean) constructs and matches actual
exceptional objects and Standard Model modules:

- The 240 exceptional coordinate roots define an irreducible complex
  `RootPairing` with an explicit simple base and `E8` Cartan matrix. The
  resulting Geck matrix Lie algebra is identified with its adjoint module
  and proved simple of complex dimension 248. An explicit positive metric
  yields a compact real form, a complexification Lie equivalence, and real
  simplicity and dimension 248.
- The root-coordinate grading modulo three becomes an actual Lie-algebra
  grading with dimensions `86 + 81 + 81`. Explicit commuting matrix-unit
  systems embed `sl(5,ℂ) × sl(3,ℂ)` faithfully in its degree-zero subalgebra.
  Restricting the first factor embeds the actual Standard Model plus family
  algebra. A signed basis equivalence identifies the actual degree-one
  adjoint subspace with `Matter81` and intertwines that entire action.
- The actual degree-one module is irreducible under the entire zero-grade
  algebra. Compact conjugation constructs the 86-dimensional real isotropy
  and its full 162-dimensional real orthogonal complement. A polynomial
  in one compact family generator recovers multiplication by `i`, forcing
  the full real commutant to be exactly `ℂ`.
- The actual unitary block group is the quotient of
  `SU(3) × SU(2) × U(1)` by an explicitly proved central cyclic kernel of
  order six. Its charge congruence and representation descent criterion
  are proved algebraically. Actual group representations on the same
  matter spaces have the derived circle powers and a trivial kernel
  action; differentiation compatibility with the Lie actions remains open.
- The five family charge blocks are derived from alternating tensors and
  the dual defining module. The actual 81-dimensional module splits
  equivariantly under the Standard Model algebra as three families and a
  self-dual 36-dimensional remainder.
  A nonzero fifth trace proves the family and full module are not self-dual.
- The actual Standard Model action on the 27-dimensional module has zero
  linear trace and full symmetric cubic. Coupling the actual defining
  family `sl(3,ℂ)` action gives an 81-dimensional representation whose full
  cubic radical is exactly the Standard Model ideal. The explicit action
  match transfers this result to the actual exceptional subspace under
  the embedded gauge and family algebra.
- The cubic radical under the **entire** 86-dimensional zero-grade algebra
  is exactly the explicit span of six coroots and 72 root vectors, of
  dimension 78. Complex-linear coordinates identify the actual degree-one
  module with the canonical Hermitian half of the compact pair and
  transfer its full mixed cubic. Thus the canonical half has nonzero
  radical, and the constructed pair satisfies every original algebraic
  hypothesis of the all-rank structural theorem.

The six-coroot, 72-root span is Lie-isomorphic to the simple E₆ root-lattice
algebra. Its centralizer is the embedded family sl₃. On the degree-one
space this gives three copies of one irreducible 27 with first fundamental
highest weight, with the defining family action on the copy index. The
canonical compact radical has real dimension 78 and complexifies to this
E₆ ideal. Exceptional group integration and differentiation of the group
actions remain open. [Proofs and conventions](FixedCandidate.md#the-e₆-ideal-and-its-local-27).

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

`InvolutionObstruction.lean` strengthens this to every invariant complement
and every involution fixing `h` pointwise. Its endpoint
`all_rank_anomalous_involution_eq_refl` takes the original hypotheses and
proves that such an involution is the identity. Preservation of the chosen
compact form is not an additional assumption. Maximality first identifies
the fixed algebra of a nonidentity involution with `h`; its negative
eigenspace would then be a symmetric invariant complement, which the
transported complex structure excludes.

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
kernel from the original hypotheses. For a common Cartan, the subsequent
root-system and cubic transport identify the grade-one weights and their
integer contractions with the census coordinates.
[Cubic transport](../CubicAnomaly/Classification/RootClassificationCubic.lean).

### The radical is a sum of actual simple coroot ideals

`CartanCoroot.lean` makes the Cartan test finite in its first input as well.
For a finite-dimensional Killing Lie algebra over an algebraically closed
field of characteristic zero, every nonzero ideal contains an actual
nonzero coroot. Ideals are determined by the coroots they contain. For a
Cartan basis `b` and a symmetric invariant cubic `c`, this gives

\[
\operatorname{Rad}(c)\ne0
\quad\Longleftrightarrow\quad
\exists\alpha\in\Phi,\quad
\forall i,j,\ c(h_\alpha,b_i,b_j)=0.
\]

All mixed pairs of basis inputs are tested. The test is not restricted to
the diagonal values `c(hα,hα,hα)`. Nonzero root-coroot pairing propagates
membership in an ideal, and hence cubic nullness, along connected roots.

`CorootComponents.lean` proves that the ideal generated by any actual
coroot is simple. Its proof uses complementary ideals and the actual root
`sl₂` triple, without a list of simple Lie types. Every ideal is the sum
of the coroot ideals it contains. In particular,

\[
\operatorname{Rad}(c)
=\sum_{\substack{\alpha\in\Phi\\
                  \forall i,j,\ c(h_\alpha,b_i,b_j)=0}}
  \langle h_\alpha\rangle_{\mathrm{Lie\ ideal}}.
\]

`CanonicalCoroot.lean` transports this statement to the actual positive
half used in the original anomaly condition. The tested expression is

\[
C(\alpha;i,j)
=\sum_{\chi\in\operatorname{Wt}(V)}
  \dim(V_\chi)\,\chi(h_\alpha)\chi(b_i)\chi(b_j).
\]

`canonical_anomaly_iff_null_coroot` is the corresponding equivalence, and
`canonical_complex_radical_eq_iSup_null_corootIdeals` reconstructs the
entire complex radical as a sum of actual simple ideals.
`all_rank_exists_null_coroot` constructs the Cartan of `h_C` and a nonzero
actual coroot satisfying every mixed test from the original compact-pair
hypotheses. The common-Cartan selection later uses the actual root and
cubic identifications with the exceptional census.
[Common-Cartan selection](../CubicAnomaly/Classification/RootClassificationSelection.lean).

`CubicIdealDecomposition.lean` also proves that internal component tests
detect the **full** radical. Every ideal of a semisimple Lie algebra is
perfect. Invariance and symmetry then kill cubic terms involving both an
ideal and its complementary ideal. Consequently

\[
c|_{I^3}=0\quad\Longleftrightarrow\quad I\subseteq\operatorname{Rad}(c).
\]

The entire radical is therefore the sum of the actual simple coroot ideals
whose internal cubic vanishes. The quantification over both remaining
ambient inputs is discharged by proof; it is not dropped from the anomaly
condition.

## The all-rank geometric branch reduction

The initial endpoint is

```lean
CubicAnomaly.Classification.AllRankGrading.all_rank_rank_deficient_or_cyclic_grading
```

It takes exactly the compact form, effective proper subalgebra, complex
commutant equivalence and nonzero full radical of the original structural
theorem. Its conclusion is

```lean
abelianRank ℝ h < abelianRank ℝ g ∨ CanonicalCyclicGrading B h e
```

Here `CompactCartan.abelianRank` is explicitly the maximum dimension of an
actual abelian Lie subalgebra. The definition uses a natural-number supremum;
finite dimensionality supplies its bound and proves that the maximum is
attained. Monotonicity under injective Lie maps gives the dichotomy between
strict inequality and equality. This development does not identify this
definition with Mathlib's separate characteristic-polynomial `LieAlgebra.rank`.

For a compact algebra, a maximum-dimensional abelian subalgebra is proved
to be Cartan: invariance and positivity make its normalizer centralize it,
and any extra centralizing vector would enlarge the abelian subalgebra.
When the two abelian ranks agree, a maximizing subalgebra of `h` is also
maximal-dimensional in `g`. Its actual image under complexification is an
ambient Cartan contained in the actual complexified isotropy. The proof
reflects normalizer membership through real and imaginary parts.

`CanonicalCyclicGrading` is a transparent conclusion predicate. It contains
an actual ambient Cartan `H`, with

\[
H\subseteq\mathfrak h_{\mathbb C},\qquad
\dim_{\mathbb C}H=\operatorname{abelianRank}_{\mathbb R}(\mathfrak g),
\]

and a nonzero additive character of the actual integer root lattice

\[
\chi:Q(\mathfrak g_{\mathbb C},H)\longrightarrow\mathbb Z/3.
\]

The resulting root grades form an internal direct sum, satisfy the bracket
degree law, and are exactly

\[
\mathfrak g_0=\mathfrak h_{\mathbb C},\qquad
\mathfrak g_1=V,\qquad
\mathfrak g_{-1}=V_-\cong V^*.
\]

The last two equalities use the actual embedded `I` and `-I` eigenspaces
of the extended commutant complex structure. No Cartan, closed subsystem,
three-class support, grade identification, character or classification
witness is an input to this reduction. The global theorem eliminates the
rank-deficient alternative using the classical exclusions and the exceptional
factor tests. [Global classification](../CubicAnomaly/Fixed/GlobalClassification.lean).

### Intrinsic finite data and the same-Cartan anomaly

The strengthened endpoint is

```lean
CubicAnomaly.Classification.IntrinsicToral.all_rank_rank_deficient_or_intrinsic_toral_data
```

It has the same original hypotheses and the conclusion

```lean
abelianRank ℝ h < abelianRank ℝ g ∨ IntrinsicToralData B h e
```

`IntrinsicToralData` extends the constructed cyclic grading with conclusions
on that **same** ambient Cartan:

- The actual zero-grade root forms span the complex dual of the Cartan and
  have rational span of dimension `dim H`.
- The actual positive- and negative-half support graphs are connected.
  Their edges are exactly root differences lying in the zero-grade roots.
- `dim h = dim H + #Ψ`, `dim V = #R₁`, and `#R₁ = #R₂`.
- The actual integer root lattice is finite free of rank `dim H`, has a
  constructed integral basis, and has exactly `3^(dim H)` characters into
  `ZMod 3`. The selected character is a nonzero coordinate assignment.
- A nonzero Cartan vector annihilates the actual grade-one root cubic
  against every remaining pair of Cartan inputs.
- The finite integer matrix formed from the grade-one roots' intrinsic
  coordinate triple products has a nonzero rational kernel.

`FullRankRoots.lean` proves the spanning claim by showing that a Cartan
vector annihilating the contained roots centralizes the whole isotropy.
Centrelessness kills it. The rational-rank statement uses both scalar
extension and the crystallographic root-span rank theorem; it is not
inferred merely from complex spanning.

`RootSupportGraph.lean` proves that a connected component's root-space sum
is an invariant submodule. Irreducibility makes it the entire half.
`RootGraphCriterion.lean` proves the converse using actual nonzero root
brackets. Its equivalence concerns ambient root-space modules disjoint
from the Cartan and requires negation-closed acting roots, or the actual
invariant-form criterion deriving that property. It does not assert such
a criterion for arbitrary weight modules with multiplicities.

`RootSupportDimension.lean` uses independent one-dimensional ambient root
spaces to prove the dimension formulas. `RootCharacterCoordinates.lean`
identifies actual grade membership, counts and graph edges with finite
coordinate dot-product and difference predicates in the constructed basis.

`ContainedCartan.lean` proves that the literal inverse image of the common
ambient Cartan under the actual complexified isotropy inclusion is itself
a Cartan. Its equivalence and lift preserve that inclusion exactly.
`RootSupportTrace.lean` identifies the weights of a supported root-space
module with its actual contained roots and proves every multiplicity is one.
`CanonicalRootCubic.lean` then proves, for the canonical anomaly action,

\[
c_{\rho}(x,y,z)=\sum_{\alpha\in R_1}\alpha(x)\alpha(y)\alpha(z).
\]

`CommonCartanAnomaly.lean` and `RootCubicKernel.lean` prove that the original
full radical is nonzero exactly when this root-cubic matrix on the same
Cartan has a nonzero kernel. All mixed insertions are retained. No Cartan conjugacy witness,
weight table or guessed multiplicity is an input.

`IntrinsicCartanBasis.lean` constructs the Cartan basis dual to the
constructed integral root basis. Actual roots evaluate on it to their
integer coordinates. `CoordinateCubic.lean` consequently identifies the
actual root-cubic matrix with the scalar cast of the integer matrix

\[
A_{(j,k),i}(a)=
\sum_{\substack{\alpha\in\Phi\\
                 \sum_\ell\alpha_\ell a_\ell=1\;\mathrm{mod}\;3}}
\alpha_i\alpha_j\alpha_k\in\mathbb Z.
\]

`RationalKernel.lean` proves that any rational matrix has a nonzero kernel
after field extension exactly when it already has one over the rationals.
To descend a complex vector, choose a rational linear functional on
`ℂ` sending a nonzero coordinate to one, then apply it to every coordinate
and row equation. `IntrinsicAnomaly.lean` composes the bridges into
`canonical_anomaly_iff_intrinsic_rational_kernel`. In particular the
original-hypothesis `IntrinsicToralData` conclusion includes a nonzero
rational vector annihilated by the exact integer matrix above.

These finite parametrizations are related to the exceptional tables by an
actual root bijection preserving the integral coordinates, the three grades
and the cubic contractions. [Root bijection](../CubicAnomaly/Classification/RootClassificationExceptional.lean) ·
[Cubic transport](../CubicAnomaly/Classification/RootClassificationCubic.lean).

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

`CommonCartan.lean` now derives the geometric hypotheses required by the
earlier conditional grading theorem. A subalgebra containing an actual
ambient Cartan is the sum of that Cartan and the root spaces it contains.
`RootBracket.lean` uses actual root strings to prove nonzero brackets when
the sum of two roots is a root, giving additive closure of the contained
roots. Nondegeneracy of the extended compact form on the actual complexified
subalgebra gives closure under negation. Saturation then identifies the
zero lattice grade with that subalgebra.

`CompactGeometry.lean` provides the actual complexified inclusion, the
equivalence between tensor complexification and its ambient image, and
nondegeneracy of the extended form on every complexified real subspace.
`EqualRank.lean` transports the actual irreducible dual halves through this
equivalence. The zero grade acts on every degree, so each irreducible half
is homogeneous. Duality makes their degrees opposite. Together with the
ambient direct sum this derives the support `0,c,-c`.

Properness forces `c ≠ 0`. If `c` did not have order three, every bracket
of off-zero components would lie in grade zero, including the order-two
case. Uniform nonsymmetry excludes this. Thus
`compact_common_cartan_cyclic_grading` derives the actual cyclic grading
with only the ambient common Cartan still supplied; `AllRankGrading.lean`
constructs that Cartan in the equal-abelian-rank branch.

The initial quotient is the additive group of all functions `H → ℂ` modulo
the integer span of the contained roots; the entire quotient is not asserted to be
cyclic. `ToralCharacter.lean` restricts its degree map to the actual integer
root lattice and proves that its image lies in the cyclic subgroup just
constructed. Inverting the injective map from `ZMod 3` gives the nonzero
actual character and preserves all three grade identities.
`RootLatticeBasis.lean` identifies this lattice with Mathlib's actual
integer root span and constructs an integral basis of rank `dim H`.
`intrinsicRootCharacterEquiv` parametrizes its characters by the basis
values, proves the coordinate evaluation formula, and counts exactly
`3^(dim H)` characters. On the common Cartan, the root bijection built
from the classified simple-root matrix matches the actual root system
to the authored coordinates used in the exceptional enumeration.
[Root classification](../CubicAnomaly/Classification/RootClassificationDynkin.lean).

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

### Defining modules and restriction identities

`SelfDualAbsorption.lean` proves that a direct sum of two inequivalent
irreducible dual modules has exactly four submodules. Its self-dual
submodules are only zero and the whole sum. Consequently an equivariant
map from an irreducible self-dual module into the actual ambient algebra
has image in the complexified isotropy. A nondegenerate invariant bilinear
form supplies the required self-duality; it need not be symmetric.

For the actual real algebra of skew-adjoint operators on a finite-dimensional
inner-product space `W`, `OrthogonalDefining.lean` derives irreducibility
of the restricted real defining module from the original compact-pair
hypotheses. A proper invariant subspace would give an orthogonal reflection
whose conjugation is a nonidentity involution fixing `h` pointwise,
contradicting `InvolutionObstruction.lean`.

The same file excludes a commuting complex structure on `W` by separating
its skew-adjoint and self-adjoint parts and using the zero ambient centralizer
and positivity. `AbsoluteIrreducibility.lean` proves a general descent
lemma: a real irreducible Lie module with no commuting complex structure
has irreducible complexification. It does not require a finite-dimensional
division-algebra classification. The endpoint
`all_rank_orthogonal_defining_irreducible_self_dual` therefore gives both
irreducibility and equivariant self-duality of the actual defining module
`W_C` under `h_C`.

`UnitaryGeometry.lean` and `UnitaryDefining.lean` complete the defining-module
step for the actual special-unitary algebra of traceless skew-Hermitian
operators. A proper invariant complex subspace `U` gives a commuting
orthogonal projection `P`. The operator

\[
i\bigl(\dim(W)P-\dim(U)\operatorname{id}\bigr)
\]

is a nonzero traceless skew-Hermitian element of the ambient centralizer,
contradicting the derived zero centralizer. `ComplexDefining.lean`
constructs the action of the actual complexified isotropy on the same
complex defining space and proves irreducibility transfers to it.

`SymplecticGeometry.lean` constructs the actual compact symplectic algebra
from an antiunitary quaternionic structure `J`, with `J² = -1`.
`SymplecticDefining.lean` proves that every self-adjoint operator commuting
with the isotropy also commutes with `J`: otherwise its difference from
its quaternionic conjugate gives a nonzero symplectic centralizer element.
An invariant projection must therefore preserve `J`. A proper invariant
subspace would then give a nonidentity reflection involution fixing the
isotropy, which the existing involution obstruction excludes.
`SymplecticForm.lean` constructs the actual nondegenerate alternating
bilinear form `ω(u,v) = ⟨Ju,v⟩`, proves its invariance under the actual
complexified action, and derives equivariant self-duality.

Thus defining-module irreducibility is proved for all three concrete compact
classical constructions, with self-duality for the orthogonal and symplectic
defining modules. Isotropy simplicity is now proved in all three cases,
over the reals and the actual complexification, without a rank bound.

### Isotropy simplicity and the intermediate factor reduction

`LieDensity.lean` proves that the associative algebra generated by an actual
finite-dimensional irreducible Lie action over an algebraically closed field
is the entire endomorphism algebra. The proof uses Mathlib's Schur and
Jacobson-density theorems. It assumes neither faithfulness nor semisimplicity
of the Lie algebra.

`ExternalTensor.lean` uses this density result to prove irreducibility of the
actual tensor of two disjoint simple ideals under the ambient diagonal
action. `IdealTensorExtensions.lean` proves the analogous three-ideal result
and a more general asymmetric tensor lemma. The proofs isolate the two
factor actions and use rank-one endomorphisms to extract tensor coefficients.
`IdealTensorDuality.lean` constructs self-duality from the restrictions of
the actual ambient Killing form to the atomic ideals and proves the tensor
dual identification equivariant.

`IdealActionProducts.lean`, `IdealProductRepresentation.lean`, and
`IdealTripleProduct.lean` construct nonzero equivariant maps by multiplying
actual defining action operators. Perfectness forces every equivariant map
from two disjoint ideal factors to the adjoint module into both ideals, so
it must vanish. The same obstruction applies to three factors. Consequently
the nonzero operator-product image cannot lie in the original action image.
These product and range obstructions need no supplied tensor factorization.

`UnitarySimplicity.lean` combines these results with the actual trace-zero
complexification and self-dual absorption. Its original-hypothesis endpoints
are

```lean
all_rank_special_unitary_complexified_isotropy_simple
all_rank_special_unitary_isotropy_simple
all_rank_special_unitary_cubic_radical_eq_top
all_rank_special_unitary_cubic_trace_zero
```

The two-ideal product is traceless because the ideals commute and are
perfect. Its irreducible self-dual source forces its ambient image into the
isotropy, contradicting the range obstruction. Therefore the actual isotropy
is simple, over both the reals and the complex numbers. Its assumed nonzero
full mixed radical is then the whole isotropy, so every mixed cubic trace
of the canonical Hermitian half is zero.

In the orthogonal and symplectic cases, three commuting skew operators have
skew product for the actual complex bilinear defining form. The corresponding
triple tensor is irreducible and self-dual, giving the same contradiction.
`ClassicalIsotropyFactors.lean` proves

```lean
all_rank_orthogonal_isotropy_simple_or_two_atoms
all_rank_symplectic_isotropy_simple_or_two_atoms
```

Each conclusion is simplicity of the actual complexified isotropy or the
existence of two disjoint atomic ideals whose supremum is the whole algebra.
`SimpleIdealStructure.lean` derives these alternatives from the actual atomic
ideal lattice. The atoms are simple Lie algebras by semisimplicity. This
intermediate two-factor alternative is excluded by the operator argument
below.

### Constructed tensor factors and forms

`TensorEvaluation.lean` constructs

\[
U\otimes\operatorname{Hom}_{I}(U,W)\longrightarrow W,
\qquad u\otimes f\longmapsto f(u).
\]

For finite irreducible `U`, density proves injectivity by extracting every
coefficient of a kernel tensor. If two commuting ideals span the ambient
algebra and `W` is irreducible, any nonzero evaluation image is the whole
module. Choosing an actual atomic restricted submodule therefore constructs
the tensor factorization. The multiplicity space has an actual commuting
ideal action, and its irreducibility, finite dimension and faithfulness are
proved. `TensorFactorActions.lean` constructs the ideal projections and
upgrades evaluation to an equivalence for the full ambient Lie action.

`TensorFactorDuality.lean` extracts a nonzero coefficient form from an
invariant tensor form. Irreducibility makes that coefficient nondegenerate
and hence constructs actual factor self-duality. `TensorFormFactorization.lean`
uses Schur scalarity to prove equality of the original tensor form with a
tensor product of derived invariant nondegenerate factor forms; it also
derives reflexivity of invariant forms on finite irreducible modules.

`AdjointTraceForms.lean` constructs the actual bilinear adjoint and proves
nondegeneracy and invariance of the trace pairing on self-adjoint operators
and on their traceless subspace. This derives their equivariant self-duality.
`TensorEndomorphisms.lean` proves that the canonical endomorphism tensor
identification is equivariant, that its trace pairing factors, and that
skew/self-adjoint parity gives form-preserving tensor operators.

`TwoIdealTensorForms.lean` combines the evaluation and form constructions
into one package derived from the original faithful irreducible module and
its actual form. `ClassicalTwoFactorReduction.lean` applies it to the
original orthogonal and symplectic pairs: the two-factor alternative now
includes an actual atomic restricted submodule, its actual equivariant-map
multiplicity space, faithful irreducible factor actions, the literal
evaluation equivalence, and invariant nondegenerate reflexive factor forms
whose tensor product is the pullback of the original defining form.

`TensorParityBlocks.lean` constructs the two actual equivariant operator
blocks `I ⊗ P⁰` and `P⁰ ⊗ J`. It proves their pure-tensor formulas,
injectivity from faithful factor action, nonvanishing when the source
factors are nonzero, membership in the actual tensor form preserver, and
self-duality of the sources from the derived Killing and trace pairings.

### Complete exclusion of two classical isotropy factors

`CompactOperatorModel.lean` constructs exact models of the original
orthogonal and symplectic ambient complexifications. Each model records
its injective actual operator map, its exact form-preserving range, and
its literal isotropy inclusion. `EquivariantOperatorTransport.lean`
transports operators through the constructed tensor evaluation and its
exact form equality. The models are proved from the concrete
complexification equivalences; they are not additional hypotheses of the
original-pair theorems.

`TensorParitySeparation.lean` uses actual partial traces and a partial
bilinear adjoint to separate both parity blocks from the full factor
operator sum, hence from the actual diagonal isotropy action.
`SelfDualQuotientObstruction.lean` identifies the kernel of the actual
complexified complement projection with scalar-extended isotropy. A
nonzero self-dual module injecting into the complex-type quotient fills
that quotient. `CompactTensorParity.lean` applies this to show that both
traceless self-adjoint factor spaces cannot be nonzero.

The stronger final argument only needs one surviving block. In
`CompactTensorSaturation.lean`, a nonzero block `I ⊗ P⁰` is identified
bijectively with the actual complexified complement. It has no `I`-fixed
vectors: `I` is centerless in its adjoint action and acts trivially on the
other factor. An extra form-preserving operator in that other factor has
an `I`-fixed quotient class, so its class is zero. Partial trace then forces
the other factor's actual action to be its full form-preserving algebra.
No maximality implication is used.

`DualPairSkew.lean` and `CompactQuotientSkew.lean` construct the actual
quotient's nonzero equivariant sign operator. It is skew for every
invariant bilinear form. `TensorEndomorphismDescent.lean` uses density and
rank-one coefficient extraction to descend that operator through the
irreducible adjoint ideal factor. The result is a nonzero equivariant
endomorphism of the actual `P⁰`, skew for its ordinary trace pairing.

`TraceZeroEndKilling.lean` proves the explicit Killing formula on actual
trace-zero endomorphisms and its nondegeneracy. `TraceZeroSymmetricPair.lean`
derives the actual symmetric decomposition into skew and traceless
self-adjoint operators. Its equivariant trace-skew endomorphism extends
by zero on the skew subalgebra to a derivation. The inner-derivation theorem,
Schur scalarity for the original defining action, and trace zero force
this derivation to vanish. This contradicts the descended nonzero sign
operator. The argument does not assume irreducibility of `P⁰` or a
highest-weight description of it.

Thus both traceless self-adjoint spaces vanish. `ScalarAdjointDensity.lean`
then makes scalars plus each factor action all of its endomorphism
algebra: commutators lie in the action and anticommutators are scalar.
`TensorScalarSkew.lean` projects the actual endomorphism tensor decomposition
onto its skew part; every ambient form-preserving operator lies in the
diagonal isotropy action. The actual model and scalar-extension membership
reflection give `h = ⊤`, contradicting original properness. No identification
of a two-dimensional symplectic factor is needed.

`CompactTensorExclusion.lean` assembles this contradiction.
`ClassicalTensorPackageExclusion.lean` extracts every required action,
faithfulness, irreducibility, tensor, and form from the previously
constructed actual package, retaining the original factor actions.
`ClassicalSimplicity.lean` closes the original-hypothesis endpoints:

```lean
all_rank_orthogonal_complexified_isotropy_simple
all_rank_orthogonal_isotropy_simple
all_rank_orthogonal_cubic_radical_eq_top
all_rank_orthogonal_cubic_trace_zero
all_rank_symplectic_complexified_isotropy_simple
all_rank_symplectic_isotropy_simple
all_rank_symplectic_cubic_radical_eq_top
all_rank_symplectic_cubic_trace_zero
```

Together with `UnitarySimplicity.lean`, these complete defining-module
irreducibility and isotropy simplicity for all three concrete compact
classical constructions in every dimension. The final orthogonal exclusion
uses the possible highest-weight supports of the defining module. The
special-unitary exclusion uses tensor interchange.
[Orthogonal exclusion](../CubicAnomaly/Classification/ClassicalConstituentOrthogonalExclusion.lean).

### Complete special-unitary exclusion by tensor interchange

`UnitaryNoGo.lean` proves

```lean
all_rank_special_unitary_cubic_radical_eq_bot
```

Its inputs are the original compact form `B`, actual subalgebra
`h : LieSubalgebra ℝ (specialUnitaryAlgebra W)`, effectiveness, properness,
and the actual real complement commutant equivalence with `ℂ`. Its conclusion is

```lean
(hermitianHalfOfCommutant B h e).cubicRadical = ⊥
```

There is no rank restriction. Nontriviality, defining irreducibility,
isotropy simplicity, and every required decomposition are derived in the
contradictory branch assuming a nonzero radical.

`UnitaryEndDecomposition.lean` constructs the actual equivariant scalar,
isotropy, and complement inclusions and projections. Normalized trace
removes the scalar part, the actual special-unitary complexification lifts
the traceless part, and the original compact orthogonal projections split
that lift. Their literal retractions and sum identity give

\[
\operatorname{End}_{\mathbb C}(W)
 =\mathbb C\,1\oplus\mathfrak h_{\mathbb C}\oplus V\oplus V^*.
\]

`ScalarModule.lean` proves the scalar summand is irreducible, self-dual,
and inequivalent to the actual simple adjoint summand.
`UnitarySkewLine.lean` proves that two such self-dual irreducibles and one
inequivalent irreducible dual pair have exactly one nonzero line of
equivariant operators skew for the invariant nondegenerate symmetric
trace pairing. Vanishing cross maps, orthogonality, and nondegeneracy on
the summands are derived. The line is generated by the sign operator on
`V ⊕ V*`, extended by zero on scalars and isotropy.

`TraceReshuffle.lean` constructs the actual canonical linear equivalence

\[
\operatorname{End}_{\mathfrak h_{\mathbb C}}
  (\operatorname{End}_{\mathbb C}W)
\cong
\operatorname{End}_{\mathfrak h_{\mathbb C}}(W\otimes W).
\]

The construction uses the ordinary operator trace pairing and the actual
tensor endomorphism equivalence. It proves that trace-skew operators
correspond exactly to operators anticommuting with the literal tensor
flip `F`. Therefore the actual tensor commutant would have one nonzero
line of operators `T` satisfying `F * T = -(T * F)`.

`TensorUnitary.lean` derives adjoint closure of this commutant from the
original skew-Hermitian defining generators, and proves that the actual
tensor flip is equivariant, self-adjoint, and involutive.
`FlipOddObstruction.lean` excludes the proposed line in any complex
star-closed subalgebra. If `F * T = c • T`, involutivity gives `c = ±1`.
The nonzero adjoint `T†` is in the same line, but taking adjoints reverses
that eigenvalue. This is a contradiction.

`UnitaryTraceSkewObstruction.lean` assembles the actual reshuffle and
adjoint argument. `UnitaryNoGo.lean` then derives the line from the
original hypotheses and applies that obstruction. This closes the
special-unitary no-go branch without a highest-weight constituent,
Weyl-dimension formula, or decomposition of `W ⊗ W` into irreducibles.

The separate `UnitarySelfDualExclusion.lean` also proves that the actual
defining module cannot be equivariantly self-dual under the original
nonzero-radical hypotheses. `SelfDualInvariantForm.lean` constructs the
literal invariant nondegenerate form from self-duality; the trace-zero
self-adjoint block and symmetric-pair derivation argument exclude it.
`ScalarTraceZeroDensity.lean` handles its zero-block case by removing the
scalar term through the actual trace. This remains an independently
proved structural result; the tensor-interchange no-go does not require it.

### Actual classical complexifications

`UnitaryComplexification.lean` constructs the actual equivalence from
`ℂ ⊗ su(W)` to the complex trace-zero endomorphisms. Surjectivity is the
explicit decomposition of an operator into its skew-Hermitian real and
imaginary parts. `OrthogonalComplexification.lean` similarly identifies
`ℂ ⊗ so(W)` with the endomorphisms preserving the complexified real inner
product, acting on the actual `ℂ ⊗ W`. Its intrinsic equivalence does not
require finite dimensionality.

Choosing actual finite bases gives `standardSpecialUnitaryMatrixEquiv`
and `standardOrthogonalMatrixEquiv` to Mathlib's matrix `sl` and `so`.
The choices are constructed, and the full defining-action compatibility
is proved. `SymplecticComplexification.lean` identifies `ℂ ⊗ sp(W,J)`
with the complex endomorphisms preserving the actual alternating form
constructed above. In the standard orthonormal quaternionic coordinates
on two copies of `ℂⁿ`, its Gram matrix is `-J`. The complexification maps
isomorphically onto Mathlib's symplectic matrix algebra and scalar conjugation
becomes negative conjugate transpose. Multiplication by `J` injects the
Hamiltonian matrices into the symmetric matrices and bounds their dimension
by `n(2n+1)`. [Symplectic compact model](../CubicAnomaly/Classification/SymplecticCompactModel.lean)
and [matrix dimension](../CubicAnomaly/Classification/SymplecticMatrixDimension.lean).

`UnitaryModuleBridge.lean` and `ClassicalModuleBridge.lean` additionally make
these identifications equivariant for the actual complexified isotropy
action. They prove faithfulness, agreement with the literal isotropy
inclusions, and equivariant lifting of trace-zero or form-preserving
endomorphism maps to the original ambient complexifications. Thus the
isotropy-factor results above do not assume an intertwining witness.

### Derived exceptional search bounds

`QuadraticRestriction.lean` proves two necessary identities for the actual
canonical positive half and actual complexified inclusion, directly from
the complementary dual-module decomposition:

\[
\dim_{\mathbb R}\mathfrak g
=\dim_{\mathbb R}\mathfrak h+2\dim_{\mathbb C}V,
\]

\[
\kappa_{\mathfrak g_{\mathbb C}}(\iota x,\iota y)
=\kappa_{\mathfrak h_{\mathbb C}}(x,y)
 +2\operatorname{Tr}_V(\rho(x)\rho(y)).
\]

The latter uses invariance of trace forms under actual module equivalences,
their equality on dual modules, and additivity over complementary submodules.
The factor-index theorem then evaluates the restriction on an actual long
simple coroot and obtains the divisibility test used for each constituent.
[Factor-index formula](../CubicAnomaly/Classification/ExceptionalSieveFactorIndex.lean) ·
[Ambient divisibility](../CubicAnomaly/Classification/ExceptionalSieve.lean).

`KillingDimension.lean` derives
`dim L = dim H + 2 #positiveRoots` and `dim L ≥ 3 dim H` from the actual
root-system base. A nonzero Killing algebra has dimension at least three;
if its dimension is even, it has dimension at least six.
`SieveBounds.lean` derives nonzero isotropy from the original anomaly
hypothesis and obtains

\[
2\dim V+3\le\dim\mathfrak g,
\qquad
2\dim V+6\le\dim\mathfrak g\quad(\dim\mathfrak g\text{ even}).
\]

The dimensions `52, 78, 133, 248` therefore imply the search bounds
`23, 36, 65, 121`, respectively, without a supplied search-bound witness.
The theorem states these as dimension implications; it does not assign
exceptional type names to an arbitrary ambient algebra.
`RankOneObstruction.lean` proves that an actual compact centreless
rank-one algebra has dimension three. From the original hypotheses it
then excludes strict rank deficiency whenever the ambient geometric
abelian rank is two and its dimension is even. The rank-one isotropy obstruction now applies in every ambient rank.
For odd ambient dimension it forces isotropy rank at least three and
sharpens the 133-dimensional ambient search to half-dimension at most 62.
The general highest-weight and index interpretation is discussed below.

### Root lattices and dimension inequalities

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
rank with the number of coordinates. The signed-coordinate reflection proof
also works on the simple roots of an actual Cartan with a classical matrix.

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
even beyond the odd ranks needed by the manuscript. The all-rank
classification obtains its dimension bounds on the actual modules from
weight strings, Weyl orbits and the product of constituent dimensions.
[Simple-root strings](../CubicAnomaly/Classification/ExceptionalSieveSimpleStrings.lean) ·
[Factor products](../CubicAnomaly/Classification/ExceptionalSieveFactorProduct.lean) ·
[Orthogonal exclusion](../CubicAnomaly/Classification/ClassicalConstituentOrthogonalExclusion.lean).

## Selection from an actual common Cartan

The simple roots of the ambient complexification give a positive-definite,
indecomposable crystallographic Cartan matrix. A finite Cartan classification
on the pinned toolchain gives a reindexing to A, B, C, D, E, F or G. For each
exceptional matrix, reflection closure and descent identify the actual roots
with the entire authored root table. The same bijection transports the integer
root lattice, character grades and cubic contraction matrix.
[Dynkin classification](../CubicAnomaly/Classification/RootClassificationDynkin.lean)
and [cubic transport](../CubicAnomaly/Classification/RootClassificationCubic.lean).

For each classical matrix, lift the character values on simple roots to
integers. The lifts have values between −2 and 2 on every root, as do their
simple reflections. A zero residue then has integer value zero. If its roots
span the Cartan dual, the functional vanishes identically. This contradicts
the nontrivial character supplied by the compact pair.
[All-rank classical obstruction](../CubicAnomaly/Classification/RootClassificationClassical.lean).

In the remaining five root systems, the original hypotheses give full
zero-root span and a nonzero rational kernel for the grade-one cubic
matrix. Checking the characters selects E₈, with 78 roots of grade zero
and 81 of grade one. Thus at equal abelian rank the rank is 8 and the
actual ambient, isotropy and complex-half dimensions are 248, 86 and 81.
The selected character lies in the Weyl orbit of the seventh-coordinate
character in the fixed construction.
[Equal-rank selection](../CubicAnomaly/Classification/EqualRankSelection.lean)
and [Weyl orbit](../CubicAnomaly/Classification/RootClassificationOrbit.lean).

The character comparison lifts to a Lie algebra isomorphism. Matched
positive and negative simple-root generators in a product generate a
subalgebra surjecting onto each simple factor. Its intersection with
height zero is contained in the diagonal Cartan. The subalgebra is proper,
so it is the graph of a Lie equivalence. Compact-normalized root triples
let the equivalence descend to the real form while preserving both
grades. The fixed Geck algebra and isotropy have an explicit common
Cartan with real origin. Consequently the equal-rank conclusion is an
isomorphism to the actual fixed pair. Its scalar extension carries the
two oriented matter halves with it.
[Lie algebra recognition](../CubicAnomaly/Classification/ChevalleyRecognition.lean),
[real descent](../CubicAnomaly/Classification/CompactEqualRankPair.lean),
and [fixed-pair theorem](../CubicAnomaly/Fixed/E8EqualRankRealPair.lean).

In the compact symplectic case the square of a highest vector gives a
rank-one operator in the isotropy. Its quaternionic partner gives a second
such operator on a nonorthogonal line. The generated operators span the
whole symplectic algebra, contradicting properness. The theorem applies
in every dimension to the original concrete compact symplectic pair.
[Symplectic exclusion](../CubicAnomaly/Classification/ClassicalConstituentSymplecticExclusion.lean).

For an ambient compact Lie algebra whose Cartan matrix is of type A, the
proof constructs a complex equivalence to trace-zero matrices and descends
it to a real special-unitary equivalence. Transport along this equivalence
proves that the full cubic radical is zero for the original pair, at every
isotropy rank. [Type-A recognition](../CubicAnomaly/Classification/TypeACompactRecognition.lean)
and [exclusion](../CubicAnomaly/Classification/TypeACompactExclusion.lean).

In ambient dimension 52 the original compact-pair hypotheses and a nonzero
radical force the isotropy to have abelian rank at least four. For semisimple
isotropy of rank at most eight, failure of Weyl negation forces a connected
simple-root component of type A of rank at least two, odd D, or E₆. In the
orthogonal defining algebra the highest-weight support satisfies the
opposition-orbit constraints, including the bounds on exchanged nodes.
[Dimension 52](../CubicAnomaly/Classification/ExceptionalSieveF4.lean),
[semisimple opposition](../CubicAnomaly/Classification/WeylComponentObstruction.lean),
and [orthogonal support](../CubicAnomaly/Classification/ClassicalConstituentOrthogonal.lean).

The exceptional sieve proves the Freudenthal recurrence on actual weight
spaces and Weyl-word invariance of their multiplicities. The dimension of an
irreducible module over the direct sum of its acting simple ideals is the product
of the dimensions of the corresponding irreducible constituents. The Killing-trace
restriction on each constituent gives the tested quadratic-index divisibility.
[Freudenthal recurrence](../CubicAnomaly/Classification/ExceptionalSieveFreudenthal.lean),
[Weyl invariance](../CubicAnomaly/Classification/ExceptionalSieveWeightOrbit.lean),
[factor dimensions](../CubicAnomaly/Classification/ExceptionalSieveFactorProduct.lean),
and [factor index](../CubicAnomaly/Classification/ExceptionalSieve.lean).

The type-C recognition proof constructs all `2r²` signed roots from an actual
Cartan of type C. The resulting dimension bound and the standard symplectic
simple-root matrices give a complex Lie isomorphism. Normalized compact
conjugation descends it to a real isomorphism, so the cubic radical vanishes
for any compact ambient algebra of this type. In real dimensions 14 and 52,
combining the rank bounds with equal-rank uniqueness also forces a zero
radical. [Type C](../CubicAnomaly/Classification/TypeCCompactRecognition.lean)
and [small exceptional dimensions](../CubicAnomaly/Fixed/SmallExceptionalExclusion.lean).

For general simple factors the positive-string and opposition checks are now
connected to actual faithful modules. The `A₂` dimension-35 case contradicts
the required vanishing cubic. The type-A matrix-unit calculation relates the
actual highest vector to the centered cubic in its coordinates. A separate
minuscule dimension bound counts weights in a supplied minuscule orbit.
[A₂ cubic](../CubicAnomaly/Classification/ExceptionalSieveA2Cubic.lean),
[type-A highest-weight coordinates](../CubicAnomaly/Classification/TypeACubicHighestWeight.lean),
and [minuscule weights](../CubicAnomaly/Classification/MinusculeDimension.lean).

## Global uniqueness for the oriented compact pair

For G₂, F₄, E₆, E₇ and E₈ the exceptional rank bound applies to the
nested Cartans of the original pair. Each simple factor contributes an
actual highest label, its trace-index test and a lower bound from
simple-root strings. The constituent dimensions multiply to the half
dimension. A non-self-dual half supplies a label moved by opposition.
The surviving F₄ and E₇ rows require an A₂ constituent of dimension 10,
which divides neither 22 nor 52. The E₆ rank-two case contradicts the
quadratic trace congruence forced by its vanishing mixed cubic.
[Exceptional assembly](../CubicAnomaly/Classification/ExceptionalSieveAssembly.lean) ·
[E₆ obstruction](../CubicAnomaly/Classification/ExceptionalSieveE6Singleton.lean).

For classical ambient types, real-form recognition identifies a concrete
special-unitary, compact orthogonal or compact symplectic model. The
orthogonal exclusion uses opposition on the defining highest weight,
the type-A cubic and the remaining type-D and E₆ support cases.
Transport brings the vanishing full radical back to the original pair.
[Orthogonal recognition](../CubicAnomaly/Classification/ClassicalOrthogonalRecognition.lean) ·
[Orthogonal exclusion](../CubicAnomaly/Classification/ClassicalConstituentOrthogonalExclusion.lean) ·
[Ambient alternatives](../CubicAnomaly/Fixed/AmbientClassification.lean).

Every survivor therefore reaches the constructed compact E₈ pair.
The commutant equivalence fixes the labels of the two matter halves.
The forward implication carries each eigenspace to the corresponding
fixed eigenspace. The converse transports nonvanishing of the fixed
canonical radical back to the original pair. The stronger equivalence
identifies the full 78-dimensional radical under the very same map on
the isotropy algebra.
[Global classification](../CubicAnomaly/Fixed/GlobalClassification.lean) ·
[Radical transport](../CubicAnomaly/Fixed/OrientedPairRadical.lean).

Integration of the exceptional Lie algebra inclusions and compatibility
of the constructed group and Lie actions under differentiation remain open.
[Fixed construction and physical scope](FixedCandidate.md#remaining-identification-and-physical-scope).

## Verification and trust

Run from the repository root:

```sh
lake exe cache get
lake build
python3 formal/scripts/check_generated_data.py
python3 formal/scripts/check_formal_hygiene.py
python3 formal/scripts/check_formal_hygiene.py --self-test
```

The audit covers **1889 public theorem exports**: **1441 deductive**,
**30 finite/native-profile**, and **418 certificate-derived**. The hygiene checker keeps an explicit export
manifest and matches every
`#print axioms` receipt to its fully qualified theorem name. It rejects
missing, duplicate, unknown, and mislabeled receipts as well as unfinished
proofs and project axioms.

Every theorem in the finite/native-profile class has the exact receipt

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

The certificate-derived class includes the exceptional construction, the matching
theorems and the global compact-pair classification. Its **exact** receipt is

```text
propext
Classical.choice
Quot.sound
Lean.ofReduceBool
Lean.trustCompiler
```

This class records ordinary structural deductions that inherit the finite
root and compatibility certificates, including the coordinate certificate's
own use of choice.
It does not change either of the previous trust profiles. Adversarial receipt
tests remove each required dependency and inject an unfinished-proof or
project-classification axiom; each mutation must be rejected. The standalone
group, charge, matter, chirality and anomaly proofs remain in the deductive
class. Their transfer to the actual exceptional subspace inherits the
explicitly audited finite certificates.
