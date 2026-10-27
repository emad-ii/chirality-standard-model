import CubicAnomaly.Classification.CompactSimple
import CubicAnomaly.Classification.CubicRadical

/-!
# The all-rank structural reduction

This is the structural lemma for actual finite-dimensional compact real
Lie-algebra pairs.  Effectivity, properness, the complex commutant, and the
nonzero full cubic radical imply irreducibility, faithfulness, simplicity of
the ambient algebra, semisimplicity of the isotropy algebra, and maximality.

The complex half is supplied in a Hermitian basis, by `HermitianHalf`.  Its
real underlying module is explicitly identified with the entire adjoint
complement, and its action is required to intertwine that complement's Lie
action.  This is representation data, not a structural or classification
conclusion.  The bracket identity, faithfulness, and scalar-centre conclusion
are derived rather than fields of the input.

`HermitianRealization.lean` constructs this data from the compact form and
complex commutant and exports the main theorem without a separate
realization-witness input.

No bound on the rank or dimension is present.  This module does not prove
that the resulting simple/maximal/semisimple pair reaches the finite
exceptional census.  In particular it is not the global uniqueness theorem.
-/

namespace CubicAnomaly.Classification.AllRank

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.CompactSimple
open CubicAnomaly.Classification.CubicRadical
open Matrix

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- A chosen complex half and Hermitian basis for the complete real complement.

The relation `ρ(x) = I • T(x)` fixes the Hermitian-generator convention.
There is no faithfulness, irreducibility, scalar-centre, or classification
assumption in this structure.
-/
structure HermitianHalf (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g) where
  dimension : ℕ
  coordinates : q ≃ₗ[ℝ] (Fin dimension → ℂ)
  generators : h →ₗ[ℝ] Matrix (Fin dimension) (Fin dimension) ℂ
  action : ∀ x m, coordinates ⁅x, m⁆ =
    Complex.I • (generators x *ᵥ coordinates m)
  hermitian : ∀ x, (generators x).IsHermitian

/-- The full mixed cubic radical of the specified complex half, as a Lie ideal. -/
noncomputable def HermitianHalf.cubicRadical
    {h : LieSubalgebra ℝ g} {q : LieSubmodule ℝ h g} (V : HermitianHalf h q) :
    LieIdeal ℝ h :=
  generatorRadical V.generators Complex.I
    (scaled_commutator_of_action V.coordinates V.generators V.action)

/-- Membership in this radical quantifies over both remaining isotropy inputs. -/
theorem hermitian_half_cubic_radical_membership
    {h : LieSubalgebra ℝ g} {q : LieSubmodule ℝ h g}
    (V : HermitianHalf h q) (x : h) :
    x ∈ V.cubicRadical ↔
      ∀ y z, matrixTraceCubic (V.generators x) (V.generators y) (V.generators z) = 0 :=
  mem_radical_iff (traceCubicForm V.generators)
    (trace_cubic_form_invariant_of_scaled_commutator V.generators Complex.I
      (scaled_commutator_of_action V.coordinates V.generators V.action)) x

/-- The complete structural reduction, uniformly in every rank and dimension.

The input is a compact effective proper pair with complex commutant and a
chosen Hermitian realization of its complex half whose full cubic radical
is nonzero.  None of the five conclusions is assumed in an input field.
-/
theorem all_rank_structural_reduction [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (V : HermitianHalf h (orthogonalComplement B h))
    (hradical : V.cubicRadical ≠ ⊥) :
    LieModule.IsIrreducible ℝ h (orthogonalComplement B h) ∧
      LieModule.IsFaithful ℝ h (orthogonalComplement B h) ∧
      LieAlgebra.IsSimple ℝ g ∧ LieAlgebra.IsSemisimple ℝ h ∧ IsCoatom h := by
  let q := orthogonalComplement B h
  have hc := compact_orthogonal_complement_isCompl B h
  have hqne : q ≠ ⊥ := by
    intro hq
    have hq' : q.toSubmodule = ⊥ := congrArg LieSubmodule.toSubmodule hq
    have htop := hc.sup_eq_top
    rw [hq', sup_bot_eq] at htop
    exact hproper ((LieSubalgebra.toSubmodule_eq_top h).mp htop)
  letI : Nontrivial q := (LieSubmodule.nontrivial_iff_ne_bot ℝ h g).mpr hqne
  letI : LieModule.IsIrreducible ℝ h q := compact_complex_commutant_irreducible B h q e
  letI : LieModule.IsFaithful ℝ h q :=
    effective_invariant_complement_faithful h q heff hc.sup_eq_top
  have hfaithful : Function.Injective V.generators := by
    intro x y hxy
    apply LieModule.ext_of_isFaithful (R := ℝ) (L := h) q
    intro m
    apply V.coordinates.injective
    rw [V.action, V.action, hxy]
  have hradical' : ∃ x : h, x ≠ 0 ∧
      ∀ y z, matrixTraceCubic (V.generators x) (V.generators y) (V.generators z) = 0 := by
    have hsub : V.cubicRadical.toSubmodule ≠ ⊥ := by
      intro hz
      exact hradical ((LieSubmodule.toSubmodule_eq_bot V.cubicRadical).mp hz)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsub
    exact ⟨x, hx0, (hermitian_half_cubic_radical_membership V x).mp hx⟩
  have hcenter := center_eq_bot_of_irreducible_hermitian_realization
    V.coordinates V.generators V.action hfaithful V.hermitian hradical'
  exact ⟨inferInstance, inferInstance, compact_pair_ambient_simple B h heff hproper e,
    compact_semisimple_of_center_eq_bot (B.restrict h) hcenter,
    maximal_of_irreducible_complement h q hc hproper⟩

end CubicAnomaly.Classification.AllRank
