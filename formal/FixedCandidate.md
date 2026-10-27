# Constructing the fixed candidate

The constructive goal is to build one specified structure and prove its
consequences. It does not require first excluding every other compact Lie
pair. The new [fixed-construction modules](../CubicAnomaly/Fixed.lean) therefore
develop the exceptional root model and the Standard Model sector directly.

There are two distinct constructions. The exceptional side starts from the
reconstructed `E8` coordinates and builds actual root and matrix objects.
The Standard Model side constructs actual matrix groups and matter modules,
then proves their charges, chirality and local anomaly identities. **The
identification of these two constructions through the compact exceptional
inclusion is still open.**

## Actual exceptional root and matrix objects

[E8Coordinates](../CubicAnomaly/Fixed/E8Coordinates.lean) reconstructs the roots
using the existing exceptional Cartan-data generator. One finite certificate
checks the 240 distinct materialized integer vectors, squared length two,
closure under every root reflection, the eight simple coordinate vectors,
and positivity or negativity in that simple basis. Explicit integral inverse
witnesses avoid expensive determinant expansions.

[E8RootPairing](../CubicAnomaly/Fixed/E8RootPairing.lean) transports those facts
to an actual complex `RootPairing`: roots and coroots span the full
eight-dimensional space, the pairing is perfect, and the system is
crystallographic and reduced. The reflection permutation is constructed.
[E8Base](../CubicAnomaly/Fixed/E8Base.lean) builds the explicit simple base and
identifies its Cartan matrix. [E8Irreducible](../CubicAnomaly/Fixed/E8Irreducible.lean)
proves irreducibility by propagating reflection-invariant subspaces through
the connected simple-root graph.

[E8Geck](../CubicAnomaly/Fixed/E8Geck.lean) applies Mathlib's Geck construction
to these actual objects. The generated algebra is a finite-dimensional
complex matrix Lie algebra with trivial solvable radical. Its defining
representation is irreducible and has dimension 248.

The last dimension statement concerns the **defining representation**.
It does not yet prove that the generated Lie algebra itself has dimension
248 or that its defining module is its adjoint representation. A compact
real form, the actual `E6 + A2` inclusion, and the identification of its
adjoint-complement half with `27 ⊠ 3` are also still required.

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

[MatterChirality](../CubicAnomaly/Fixed/MatterChirality.lean) constructs an
equivariant splitting

\[
 V_{81}\simeq 3F_{15}\oplus E_{36},
 \qquad E_{36}\simeq E_{36}^{*}.
\]

The self-duality of the remainder is an actual equivariant isomorphism.
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

## Remaining identification and physical scope

The remaining exceptional task is to construct and identify one actual
compact inclusion

\[
 \mathfrak e_8\supset\mathfrak e_6\oplus\mathfrak{su}(3)_M
\]

and prove that its actual complex half restricts to the constructed matter
module. This includes the exceptional subgroup chain, the actual
`27 ⊠ 3` identification, and the relevant compact group integrations.
The separate matrix constructions above do not assume this bridge.

The restricted Standard Model representation is reducible. Its proved
properties do not establish the original irreducible-complement hypotheses
for an exceptional pair. Likewise, the Standard Model radical theorem is a
theorem about the restricted gauge algebra, not yet the full exceptional
identity `Rad(c_V) = e6`.

The universal orthogonal/symplectic exclusions and exceptional sieve
completeness are not prerequisites for this constructive target. They remain
part of the stronger global uniqueness program.

Three copies are an explicit input of the downstream construction. Deriving
that multiplicity from the exceptional inclusion remains part of the
`27 ⊠ 3` identification. The fifth trace is a representation-theoretic
chirality witness, not an additional physical gauge-anomaly claim.

The anomaly results are local trace identities; a global gauge-anomaly
theorem is not supplied by them. The construction concerns internal groups
and representations. Masses,
decoupling of the additional matter, a vacuum and interaction parameters
are not derived by these theorems.

## Next construction route

The explicit Geck matrices suggest a compact-form construction that can be
attempted before proving the generated Lie algebra's dimension or invoking
classification. This is a proposed proof route, not an exported theorem.
For the explicit Cartan matrix `C`, set `S = 4I − C` and put the block
Hermitian matrix `J = diag(S, I₂₄₀)` on the defining space. The required
generator identities are `eᵢ* J = J fᵢ` and `hᵢ* J = J hᵢ`.

An exact positive-definiteness proof for `S`, followed by those identities,
would make `σ(X) = −J⁻¹ X* J` a conjugate-linear Lie involution preserving
the generated algebra. Its fixed real subalgebra and the form
`−Re(trace(XY))` would then supply the algebraic compactness object used
elsewhere in this project. This route still requires implementation and
does not by itself integrate a compact Lie group.

The separate adjoint bridge must identify the generated algebra with the
intended 248-dimensional module, for example through an explicit root-operator
basis with proved closure and independence. Merely splitting the defining
space into dimensions `86 + 81 + 81` would not prove the required
adjoint-complement statement. The actual subsystem generators and the
`27 ⊠ 3` identification remain essential.

## Trust boundary

The group, charge, matter, chirality and anomaly theorems are deductive Lean
proofs. Their named receipts use only subsets of `propext`, `Classical.choice`
and `Quot.sound`.

The exceptional coordinate certificate uses `native_decide`. Structural
theorems that depend on that certificate inherit its compiler-evaluation
dependencies; those dependencies are disclosed and audited by name. The
audit retains the original exact finite-computation profile, keeps compiler
dependencies forbidden in the deductive class, and adds an exact profile
for certificate-derived structural proofs using `Classical.choice`.
No unproved classification or exceptional-branching assumption is admitted.
