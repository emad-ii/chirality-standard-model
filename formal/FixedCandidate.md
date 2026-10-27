# Constructing the fixed candidate

The constructive goal is to build one specified structure and prove its
consequences. It does not require first excluding every other compact Lie
pair. The new [fixed-construction modules](../CubicAnomaly/Fixed.lean) therefore
develop the exceptional root model and the Standard Model sector directly.

The exceptional and matter constructions are now matched at the level of
actual complex Lie-algebra actions. The constructed exceptional matrix algebra
has dimension 248, is simple, and has an explicit compact real form. One actual
81-dimensional homogeneous adjoint subspace is identified with the constructed
Standard Model and family representation through a faithful, explicitly
specified embedding. The actual compact pair now satisfies the original
complex-commutant and nonzero canonical cubic-radical hypotheses. The entire
complex zero-grade radical is identified with an explicit 78-dimensional
span. The abstract `E6` factor and irreducible `27` identification and the
exceptional group integrations remain separate obligations.

## Actual exceptional root, adjoint and compact objects

[E8Coordinates](../CubicAnomaly/Fixed/E8Coordinates.lean) uses the unchanged
[shared root generator](../CubicAnomaly/Classification/ExceptionalRoots.lean)
from the exceptional census. Its finite certificate checks 240 distinct integer
vectors, squared length two, closure under every root reflection, the eight
simple coordinate vectors, and positivity or negativity in that simple basis.
The generator was separated from the census to keep construction imports small;
its definitions and the census algorithms were preserved verbatim.

[E8RootPairing](../CubicAnomaly/Fixed/E8RootPairing.lean),
[E8Base](../CubicAnomaly/Fixed/E8Base.lean), and
[E8Irreducible](../CubicAnomaly/Fixed/E8Irreducible.lean) construct an actual
reduced, crystallographic, irreducible complex root pairing with its explicit
simple base and `E8` Cartan matrix. [E8Geck](../CubicAnomaly/Fixed/E8Geck.lean)
constructs the actual matrix Lie algebra and its irreducible defining module.

[E8Adjoint](../CubicAnomaly/Fixed/E8Adjoint.lean) identifies that defining module
with the **actual adjoint representation**. Its consequences include

\[
 \dim_{\mathbb C}\mathfrak g=248,
 \qquad \mathfrak g\text{ is simple}.
\]

This is the dimension of the generated Lie algebra itself. The identification
uses a bilinear bracket table bound to the reconstructed roots, verified
simple-generator images, and all 1,476,096 simple-generator derivation identities.
It does not assume a Jacobi certificate or an exceptional classification theorem.

[E8Metric](../CubicAnomaly/Fixed/E8Metric.lean) proves positivity of
`J = diag(4I − C, I₂₄₀)` using an exact rational factor and inverse.
[E8Adjoints](../CubicAnomaly/Fixed/E8Adjoints.lean) proves
`eᵢ* J = J fᵢ` and `hᵢ* J = J hᵢ` for the actual generators.
[E8Compact](../CubicAnomaly/Fixed/E8Compact.lean) then constructs the actual real
subalgebra of skew-adjoint operators, the positive invariant form
`−Re(trace(XY))`, and a complexification Lie equivalence back to `g`.
[E8Structure](../CubicAnomaly/Fixed/E8Structure.lean) proves that this compact
real algebra is simple and has real dimension 248. These are algebraic compact
real-form statements; integration to a compact Lie group is a further step.

## Actual grading and classical embeddings

[E8Grading](../CubicAnomaly/Fixed/E8Grading.lean) realizes the seventh root
coordinate modulo three as an actual grading

\[
 \mathfrak g=\mathfrak g_0\oplus\mathfrak g_1\oplus\mathfrak g_2,
 \qquad (\dim\mathfrak g_0,\dim\mathfrak g_1,\dim\mathfrak g_2)
 =(86,81,81).
\]

The bracket respects addition of degrees. The zero piece is an actual Lie
subalgebra, and the other two pieces are actual modules for it. The finite
root data also checks that the 78 zero-degree roots split into orthogonal
sets of 72 and 6, with the displayed `E6` Cartan submatrix and `A2` Gram matrix.
A Lie-algebra identification of the entire 78-dimensional factor is not
inferred from these root counts alone.

[E8A4](../CubicAnomaly/Fixed/E8A4.lean) and
[E8A2](../CubicAnomaly/Fixed/E8A2.lean) construct actual embeddings of
`sl(5,ℂ)` and the family `sl(3,ℂ)`. The first uses the simple-root chain with
zero-based indices `[1,3,4,5]`. The family factor uses the negative highest
root followed by the last simple root, fixing the defining-family orientation.
All 25 and 9 projected matrix units have explicit integral sparse witnesses,
with denominators cleared by 5 and 3. Their checked commutators give Lie
homomorphisms on arbitrary matrices. Coordinate recovery proves injectivity
on trace-zero matrices.

[E8ClassicalEmbedding](../CubicAnomaly/Fixed/E8ClassicalEmbedding.lean) proves
that the two images commute and that their product embedding is faithful.
Restricting the first factor to the existing colour/weak block algebra gives
an actual faithful inclusion

\[
 \mathfrak g_{\mathrm{SM},\mathbb C}\oplus\mathfrak{sl}_3(\mathbb C)
 \hookrightarrow\mathfrak g_0.
\]

## The exceptional half and matter are matched

[E8MatterData](../CubicAnomaly/Fixed/E8MatterData.lean) supplies a signed basis
bijection between the 81 degree-one roots and the existing three-copy matter
labels. It checks the action of every projected classical and family matrix
unit on that same basis. [E8MatterRealization](../CubicAnomaly/Fixed/E8MatterRealization.lean)
turns those checks into identities on arbitrary complex vectors.

[E8MatterMatching](../CubicAnomaly/Fixed/E8MatterMatching.lean) constructs an
explicit linear equivalence from the original `Matter81` to the actual
`gradeModule 1` and proves that it intertwines the full embedded gauge and
family action. Thus the fixed exceptional half has three copies of

\[
 \mathbf{10}\oplus\overline{\mathbf5}\oplus\mathbf5
 \oplus\overline{\mathbf5}\oplus\mathbf1\oplus\mathbf1
\]

under the selected classical restriction, with the displayed defining family
mixing. The multiplicity in this restricted representation is established by
the explicit exceptional basis match. Naming the entire local 27 as an
irreducible module for the full `E6` factor is still a separate identification.

[E8Matter](../CubicAnomaly/Fixed/E8Matter.lean) constructs the representation
from the **actual commutator action on the actual degree-one Lie submodule**.
In the proved coordinates, it equals the existing coupled matter matrix
representation. Consequently the local anomaly and radical results below
now apply to this actual exceptional subspace under the specified embedding.
The same module bundles the Standard Model restriction as an actual
`LieModuleEquiv`, transfers the three-family splitting and self-dual remainder,
and proves that the actual degree-one module is not Standard Model self-dual.

## The original compact-pair hypotheses

[E8CompactGrading](../CubicAnomaly/Fixed/E8CompactGrading.lean) proves that
the actual compact conjugation `σ(X) = −X*` reverses the three grades.
[E8CompactPair](../CubicAnomaly/Fixed/E8CompactPair.lean) constructs

\[
 \mathfrak h=\mathfrak k\cap\mathfrak g_0,
 \qquad
 q=\mathfrak k\cap(\mathfrak g_1\oplus\mathfrak g_2),
 \qquad
 (\dim_{\mathbb R}\mathfrak k,\dim_{\mathbb R}\mathfrak h,
   \dim_{\mathbb R}q)=(248,86,162).
\]

The complexification of `h` is the actual zero-grade algebra. The map
`v ↦ v + σ(v)` identifies the real underlying degree-one module with `q`
and intertwines the compact isotropy action.
[E8CompactOrthogonal](../CubicAnomaly/Fixed/E8CompactOrthogonal.lean)
identifies this `q` with the exact orthogonal complement used by the all-rank
structural theorem, and proves properness and effectivity of the pair.

[DiagonalTreeIrreducible](../CubicAnomaly/Fixed/DiagonalTreeIrreducible.lean)
proves a general irreducibility criterion: an injective diagonal spectrum
isolates coordinates by polynomials in one operator, and reversible action
edges along a spanning tree propagate any nonzero coordinate to all the
others. [E8MatterIrreducible](../CubicAnomaly/Fixed/E8MatterIrreducible.lean)
binds two finite checks to the actual inherited action and proves

\[
 \mathfrak g_1\text{ is irreducible under the entire }\mathfrak g_0.
\]

The complex-type proof uses one actual family operator. On the three family
coordinates, `T = i diag(1,1,−2)` has eigenvalues `i,i,−2i`, so

\[
 J=i\,\mathrm{id}=\tfrac32T+\tfrac12T^3.
\]

[E8FamilyComplexStructure](../CubicAnomaly/Fixed/E8FamilyComplexStructure.lean)
proves this identity for the actual exceptional action and proves that its
generator is compact. Thus every real intertwiner commutes with `J` and is
complex linear. The compact isotropy complexly spans `g₀`, so complex
irreducibility and Schur's lemma give exactly the complex scalars.
[PolynomialComplexStructure](../CubicAnomaly/Fixed/PolynomialComplexStructure.lean)
proves this implication generally, and
[E8PairComplexType](../CubicAnomaly/Fixed/E8PairComplexType.lean) transports
it to the actual real complement:

\[
 \operatorname{End}_{\mathfrak h,\mathbb R}(q)\cong_{\mathbb R}\mathbb C.
\]

The inverse of the chosen algebra equivalence sends `i` to the existing
degree-one complex structure.
[E8CanonicalPair](../CubicAnomaly/Fixed/E8CanonicalPair.lean)
therefore constructs a complex-linear coordinate equivalence with the
canonical Hermitian half in `HermitianRealization.lean`. It transports the
full cubic tensor, including the `i³ = −i` normalization, and proves that
each of the six compact coroots `i h₀,…,i h₅` belongs to its radical.
Their nonzero witnesses establish the original nonzero-radical hypothesis.

The endpoint `e8_original_pair_hypotheses` has no additional hypothesis:
it establishes effectivity, properness, the full real complex commutant,
and a nonzero full cubic radical for this exact canonical Hermitian half.
Applying the existing all-rank theorem yields real irreducibility and
faithfulness of the full complement, ambient simplicity, isotropy
semisimplicity, and maximality in
`e8_canonical_pair_structural_conclusions`.

## Actual Standard Model group and charge lattice

[StandardModelGroup](../CubicAnomaly/Fixed/StandardModelGroup.lean) defines
`S(U(3) × U(2))` as the kernel of the product of the determinants of actual
unitary matrix groups. It constructs the homomorphism

\[
 ((A,B),z)\longmapsto(z^{-2}A,z^3B).
\]

The proof establishes all of the following:

- The map is surjective onto the determinant-one block subgroup.
- Its kernel consists precisely of the elements
  `((z² I₃, z⁻³ I₂), z)` with `z⁶ = 1`.
- Projection to the phase is a group isomorphism from that kernel to the
  sixth roots of unity in the complex numbers.
- The kernel is central, cyclic and has exactly six elements.
- The quotient by the actual kernel is isomorphic to the actual block group.
- The block group embeds faithfully in the special unitary group on the
  five-dimensional colour-plus-weak space.
- The central-circle map with exponents `(-2,3)` is injective.

The central-character calculation proves

\[
 \text{triviality on the kernel}
 \quad\Longleftrightarrow\quad
 6\mid q+2t+3s.
\]

Here `q` is integer hypercharge, and `t,s` are integer representatives of
the colour and weak central characters. The module also proves the actual
homomorphism descent criterion: a representation with the specified central
character descends to the constructed gauge group exactly when this
congruence holds. The character action is an explicit hypothesis of that
general representation theorem; the charge congruence and descent are its
conclusions.

These are algebraic group and representation statements. A topological
covering-map theorem or integration of the exceptional inclusion is not
silently inferred from them.

[MatterGroupAction](../CubicAnomaly/Fixed/MatterGroupAction.lean) constructs
actual group homomorphisms into the linear automorphism groups of the same
`Five`, `Ten`, `AntiFive`, `Matter27` and `Matter81` spaces used below. The
alternating action is literal congruence `X ↦ gXgᵀ`; the dual action is
inverse precomposition. The central circle acts with powers `(-2,3)` on
the defining five, `(-4,1,6)` on alternating blocks, and `(2,-3)` on dual
coordinates. The computed six-element covering kernel acts trivially on
the actual matter representation, which therefore descends to the block
group. This direct construction does not require the general descent
theorem's central-character hypothesis. Compatibility by differentiation
between these group actions and the constructed Lie actions remains a
separate, unproved statement.

## Actual matter modules and threefold chiral content

The [alternating tensor construction](../CubicAnomaly/Fixed/MatterAlternating.lean)
realizes the ten by alternating five-by-five matrices with literal action
`A·X = AX + XAᵀ`. Its block decomposition, the three-dimensional dual
identification and the two-dimensional determinant identification are proved
in [MatterBlocks](../CubicAnomaly/Fixed/MatterBlocks.lean),
[MatterSmall](../CubicAnomaly/Fixed/MatterSmall.lean), and
[MatterBranching](../CubicAnomaly/Fixed/MatterBranching.lean).

Together with the actual dual defining five, the family module has the
five literal colour, weak and hypercharge actions

\[
 (\mathbf3,\mathbf2)_1,
 \quad(\overline{\mathbf3},\mathbf1)_{-4},
 \quad(\mathbf1,\mathbf1)_6,
 \quad(\overline{\mathbf3},\mathbf1)_2,
 \quad(\mathbf1,\mathbf2)_{-3}.
\]

The subscripts are integer charges `q = 6Y`. These action formulas are
derived by explicit coordinate equivalences, not installed as a branching
table assumption.

[MatterLieAlgebra](../CubicAnomaly/Fixed/MatterLieAlgebra.lean) defines the
actual complex Standard Model Lie algebra as the block-diagonal subalgebra
of traceless five-by-five matrices. Every one of its elements is proved to
be `diag(A−2q I₃, B+3q I₂)` for traceless colour and weak matrices `A,B`.
Thus the action and anomaly identities cover the entire constructed algebra.

[MatterSpectrum](../CubicAnomaly/Fixed/MatterSpectrum.lean) constructs the
15-dimensional family, its extension by a defining/dual pair and two
trivial lines to a 27-dimensional module, and three copies of that module.
The dimensions 15, 27 and 81 are proved for the actual vector spaces.

[MatterChirality](../CubicAnomaly/Fixed/MatterChirality.lean) constructs a
Standard Model equivariant splitting

\[
 V_{81}\simeq 3F_{15}\oplus E_{36},
 \qquad E_{36}\simeq E_{36}^{*}.
\]

The self-duality of the remainder is an actual Standard Model equivariant
isomorphism; it is a statement after restriction to the gauge algebra.
The corresponding cancellation in the usual additive chiral quotient is
a mathematical consequence of this splitting; no separate formal
Grothendieck-group package is claimed.

[MatterNonSelfDual](../CubicAnomaly/Fixed/MatterNonSelfDual.lean) proves that
the family and the full 81-dimensional module are not equivariantly
self-dual. For the actual hypercharge element `H`,

\[
 \operatorname{Tr}_{F_{15}}(H^5)=4320,
 \qquad \operatorname{Tr}_{V_{81}}(H^5)=12960.
\]

An actual self-duality would negate an odd trace while preserving it by
conjugation, forcing zero. The nonzero fifth trace therefore detects
chirality even though the linear and cubic traces vanish.

## Full local anomaly and family-factor theorem

[MatterAnomaly](../CubicAnomaly/Fixed/MatterAnomaly.lean) proves zero linear
trace and zero full symmetric cubic for the constructed 27-dimensional
module under the entire actual Standard Model Lie algebra. The proof uses
the derived family actions, actual vectorlike cancellation, and polarization.
It does not assume an anomaly theorem for an exceptional representation.

[TensorAnomaly](../CubicAnomaly/Fixed/TensorAnomaly.lean) constructs external
tensor matrix representations. For traceless factors it proves the complete
trilinear identity

\[
 c_{\rho\boxtimes\sigma}
 =\dim(N)c_\rho+\dim(M)c_\sigma,
\]

and identifies the full radical with the product of the two factor radicals.
[FamilyAnomaly](../CubicAnomaly/Fixed/FamilyAnomaly.lean) proves that the
literal defining `sl(3,ℂ)` representation has zero full cubic radical by
elementary-matrix tests.

The combined endpoint in
[MatterFamilyAnomaly](../CubicAnomaly/Fixed/MatterFamilyAnomaly.lean) is an
actual representation of
`StandardModelAlgebra × sl(3,ℂ)` on an 81-dimensional space, with

\[
 \operatorname{Rad}(c_{81})=\mathfrak g_{\mathrm{SM},\mathbb C}\times0,
 \qquad
 c_{81}(x,y,z)=27c_{\mathbf3}(x_M,y_M,z_M).
\]

There are no remaining anomaly-vanishing hypotheses in this endpoint.
Every cubic insertion from the gauge ideal vanishes, including arbitrary
mixed family insertions. Hypercharge witnesses that the radical is nonzero.
The family matrix `diag(1,1,−2)` has cubic `−6`, and its actual action on the
coupled module has cubic `−162`.

An explicit coordinate equivalence intertwines the gauge restriction of
this coupled action with the already constructed three-copy `Matter81`.
The family factor retains a nonzero cubic anomaly; this construction does
not make it an anomaly-free gauge factor.

## The cubic radical on the entire zero-grade algebra

[E8FullCubic](../CubicAnomaly/Fixed/E8FullCubic.lean) constructs the matrix
representation from the inherited action of every element of `g₀` on
the actual `g₁`. Its restriction agrees with the already matched
gauge-plus-family representation. The Cartan cubic is computed on the
actual 81 root weights. On the eight simple-coroot coordinates it is

\[
 c(t,t,t)=6t_6^3-27t_6^2t_7+27t_6t_7^2.
\]

Here the convention is
`c(A,B,C) = trace(A(BC + CB))/2`, so `c(A,A,A) = trace(A³)`.
The finite tensor calculation checks all first-slot contractions with
the six coroots `h₀,…,h₅`, including arbitrary pairs of the eight Cartan
directions.
[FiniteToralCubic](../CubicAnomaly/Classification/FiniteToralCubic.lean)
upgrades this to the full mixed radical using proved spanning, weight and
opposite-root bracket identities. This argument does not assume a Lie
classification or a nondegenerate Killing form.

The radical is a Lie ideal. Bracketing the six coroots with the 72 supported
root vectors places all of those vectors in the radical. Their independent
coordinates give a 78-dimensional subspace `e6Span`. The embedded faithful
family `sl₃` has dimension eight and intersects the full radical trivially,
by the already proved family anomaly. Since `dim g₀ = 86`, the dimension
bound forces

\[
 \operatorname{Rad}(c_{\mathfrak g_1})=\texttt{e6Span},
 \qquad \dim_{\mathbb C}\operatorname{Rad}(c_{\mathfrak g_1})=78.
\]

These are full-algebra results: the other two cubic inputs range over all
of `g₀`. The radical is both nonzero and proper. Naming its explicit
78-dimensional Lie ideal as an abstract standard `E6` model remains a
separate identification; the radical computation itself no longer depends
on completing that identification.

## Remaining identification and physical scope

The main remaining exceptional identifications are the explicit
78-dimensional radical with the required abstract `E6` algebra, its local
27-dimensional irreducible module, and the relevant compact group
integrations. The complete original compact-pair hypotheses and the full
zero-grade cubic radical are now proved. The existing selected Standard
Model embedding and its matter action do not establish uniqueness of the
Standard Model algebra among all subalgebras of the radical.

The universal orthogonal/symplectic exclusions and exceptional sieve
completeness are not prerequisites for this constructive target. They remain
part of the stronger global uniqueness program. The manuscript's universal
uniqueness theorem is not yet an exported Lean theorem.

The fifth trace is a representation-theoretic chirality witness. The anomaly
results are local trace identities; global gauge-anomaly cancellation requires
its own theorem. The construction concerns internal groups and representations.
Masses, decoupling of the additional matter, a vacuum, interactions and their
parameters are not derived by these statements.

## The proof reduction that closes the adjoint bridge

[AdjointRecognition](../CubicAnomaly/Fixed/AdjointRecognition.lean) proves a
general result for a generated matrix Lie algebra acting irreducibly on `M`.
Given a candidate linear map `B : M → End(M)`, it is enough to verify

\[
 B(sv)=[s,B(v)]
\]

for its generating matrices, together with a nonzero image in the generated
algebra and preimages for every generator. The kernel of `B` is invariant,
so irreducibility and the nonzero witness make `B` injective. The preimage
of the generated algebra is also invariant and nonzero, so every image of
`B` lies in that algebra. Equivariance then makes the image a Lie subalgebra
containing all generators, and hence the whole generated algebra.

For the checked bilinear operation `β`, the map is `B(v)(w) = β(v,w)`.
Its resulting commutator identity transfers the actual matrix bracket to
`β`. This supplies the adjoint identification and its dimension without
first checking every triple in a Jacobi table.

The subsequent matter match uses a second reduction: explicit matrix units
and a signed basis intertwiner replace an appeal to a full exceptional
branching classification for the restricted gauge and family representation.

## Trust boundary

The standalone group, charge, matter, chirality and anomaly calculations are
deductive Lean proofs. The generic adjoint-recognition and matrix-unit
extension arguments are deductive as well. Their named receipts use only
subsets of `propext`, `Classical.choice` and `Quot.sound`.

The exceptional coordinate, sparse compatibility, matrix-unit and matter
matching certificates use `native_decide`. Structural and matching theorems
that depend on those certificates inherit their compiler-evaluation
dependencies; those dependencies are disclosed and audited by name. The
audit retains the original exact finite-computation profile, keeps compiler
dependencies forbidden in the deductive class, and adds an exact profile
for certificate-derived structural proofs using `Classical.choice`.
No unproved classification or exceptional-branching assumption is admitted.
