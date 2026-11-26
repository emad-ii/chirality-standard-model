import CubicAnomaly.Classification.ClassicalConstituentHighest
import CubicAnomaly.Classification.CompactOperatorModel
import CubicAnomaly.Classification.DualPairSkew

/-!
# Highest weights of the three actual ambient constituents

The projections onto the compact isotropy and its two quotient halves
bound the number of highest weights in the form-preserving algebra.
All three weights come from the original constituents.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentCompact

open LieAlgebra LieModule Module LieAlgebra.IsKilling Submodule
open CubicAnomaly.Classification
open ClassicalConstituentHighest ClassicalConstituentWeights
open Structural ComplexDuality Complexification CompactGeometry SelfDualQuotientObstruction
open CompactOperatorModel DualPairSkew
open scoped TensorProduct

section Transport

variable {L M N : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  {b : (rootSystem H).Base} {μ : H → ℂ}
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule L N] [LieModule ℂ L N]

omit [LieModule ℂ L M] [LieModule ℂ L N] in
/-- A nonzero equivariant image of a highest vector has the same highest weight. -/
theorem highest_map (f : M →ₗ⁅ℂ,L⁆ N) {v : M}
    (hv : IsHighestVector H b μ v) (hne : f v ≠ 0) :
    IsHighestVector H b μ (f v) := by
  refine ⟨hne, ?_, ?_⟩
  · intro x
    exact (f.map_lie (x : L) v).symm.trans (by rw [show ⁅(x : L), v⁆ = _ from hv.2.1 x, map_smul])
  · intro α hα x hx
    exact (f.map_lie x v).symm.trans (by rw [hv.2.2 α hα x hx, map_zero])

omit [LieModule ℂ L M] [LieModule ℂ L N] in
/-- An injective equivariant map reflects the highest-vector conditions. -/
theorem highest_preimage (f : M →ₗ⁅ℂ,L⁆ N) (hinj : Function.Injective f)
    {v : M} (hv : IsHighestVector H b μ (f v)) : IsHighestVector H b μ v := by
  refine ⟨fun hz => hv.1 (by rw [hz, map_zero]), ?_, ?_⟩
  · intro x
    apply hinj
    exact (f.map_lie (x : L) v).trans ((hv.2.1 x).trans (map_smul f _ _).symm)
  · intro α hα x hx
    apply hinj
    rw [f.map_lie, hv.2.2 α hα x hx, map_zero]

private theorem exists_unique_weight [FiniteDimensional ℂ M] [IsIrreducible ℂ L M]
    (b : (rootSystem H).Base) :
    ∃ χ : H → ℂ, (∃ v : M, IsHighestVector H b χ v) ∧
      ∀ (μ : H → ℂ) (w : M), IsHighestVector H b μ w → μ = χ := by
  letI : Nontrivial M := nontrivial_of_isIrreducible ℂ L M
  obtain ⟨χ, v, _, hv, hc, hpos, _⟩ :=
    ExceptionalSieveWeights.exists_bounded_dominant_highest_weight (M := M) H b
  have h := show IsHighestVector H b χ v from ⟨hv, hc, hpos⟩
  exact ⟨χ, ⟨v, h⟩, fun _ _ hw => (irreducible_highest_weight_unique H b hw h).2⟩

omit [LieModule ℂ L M] in
private theorem highest_summand (P Q : LieSubmodule ℂ L M) (hc : IsCompl P Q)
    {z : M} (hz : IsHighestVector H b μ z) :
    (∃ v : P, IsHighestVector H b μ v) ∨ ∃ v : Q, IsHighestVector H b μ v := by
  let pp := invariantSummandProjection P Q hc
  let pq := invariantSummandProjection Q P hc.symm
  by_cases hpp : pp z = 0
  · have hmem : z ∈ Q :=
      (LieSubmodule.isCompl_toSubmodule.mpr hc).projection_apply_eq_zero_iff.mp
        (congrArg Subtype.val hpp)
    have hpq : pq z ≠ 0 := by
      intro hn
      have hmem' : z ∈ P :=
        (LieSubmodule.isCompl_toSubmodule.mpr hc.symm).projection_apply_eq_zero_iff.mp
          (congrArg Subtype.val hn)
      exact hz.1 (hc.disjoint.le_bot (show z ∈ P ⊓ Q from ⟨hmem', hmem⟩))
    exact Or.inr ⟨_, highest_map H pq hz hpq⟩
  · exact Or.inl ⟨_, highest_map H pp hz hpp⟩

end Transport

section Compact

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)] [LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    (b : (rootSystem H).Base)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [LieRingModule (ℂ ⊗[ℝ] h) W]
    [LieModule ℂ (ℂ ⊗[ℝ] h) W] {β : LinearMap.BilinForm ℂ W}

include hp in
/-- For an actual compact operator model with simple complexified isotropy,
every highest weight belongs to the actual adjoint or to one of the two
irreducible quotient halves. -/
theorem compact_model_highest_weights (A : Model h β) :
    let J := complexifiedEnd (commutantComplexStructure e)
    ∃ θ p q : H → ℂ, (∃ z : ℂ ⊗[ℝ] h, IsHighestVector H b θ z) ∧
      (∃ z : invariantEigenspace J Complex.I, IsHighestVector H b p z) ∧
      (∃ z : invariantEigenspace J (-Complex.I), IsHighestVector H b q z) ∧
      ∀ μ : H → ℂ, HasSkewHighestWeight H b β μ → μ = θ ∨ μ = p ∨ μ = q := by
  let P := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let Q := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I)
  obtain ⟨hc, hP, hQ, _, _⟩ := compact_complement_complex_type_decomposition B h hp e
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) P := hP
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) Q := hQ
  obtain ⟨θ, hθ, hθu⟩ := exists_unique_weight (M := ℂ ⊗[ℝ] h) H b
  obtain ⟨p, hpw, hpu⟩ := exists_unique_weight (M := P) H b
  obtain ⟨q, hqw, hqu⟩ := exists_unique_weight (M := Q) H b
  refine ⟨θ, p, q, hθ, hpw, hqw, ?_⟩
  intro μ hμ
  obtain ⟨T, hT, hne, hw, hkill⟩ := hμ
  obtain ⟨z, rfl⟩ := (A.range_iff T).mpr hT
  have hz := highest_preimage H A.operatorMap A.injective
    (show IsHighestVector H b μ (A.operatorMap z) from ⟨hne, hw, hkill⟩)
  let π := complexifiedComplementProjection B h
  by_cases hπ : π z = 0
  · have hmem := (complexified_complement_projection_eq_zero_iff B h z).mp hπ
    change z ∈ (complexifiedHom h.toLieSubmodule.incl).range at hmem
    obtain ⟨y, hy⟩ := hmem
    have hinj : Function.Injective (complexifiedHom h.toLieSubmodule.incl) :=
      complexification_linearMap_injective h.toLieSubmodule.incl.toLinearMap Subtype.val_injective
    exact Or.inl (hθu μ y (highest_preimage H _ hinj (hy ▸ hz)))
  · have hz' := highest_map H π hz hπ
    rcases highest_summand H P Q hc hz' with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact Or.inr (Or.inl (hpu _ w hw))
    · exact Or.inr (Or.inr (hqu _ w hw))

end Compact

end CubicAnomaly.Classification.ClassicalConstituentCompact
