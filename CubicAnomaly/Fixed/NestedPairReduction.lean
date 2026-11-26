import CubicAnomaly.Classification.ExceptionalSieveIndex
import CubicAnomaly.Fixed.E8EqualRankRealPair

/-! An original compact pair either has a strictly smaller nested isotropy
Cartan or is equivalent to the oriented fixed pair. The nested Cartans
record their real origins for both the classical and exceptional reductions. -/

namespace CubicAnomaly.Fixed.NestedPairReduction

open LieAlgebra LieModule Module
open Classification.Structural Classification.HermitianRealization Classification.CompactGeometry
open Classification.CompactCartan Classification.CompactEqualRankPair Classification.ExceptionalSieveIndex
open E8Compact E8CompactPair E8CanonicalPair E8PairComplexType E8FixedCommonCartan E8EqualRankRealPair
open scoped TensorProduct

attribute [local instance] E8Compact.e8_compact_real_finiteDimensional

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]

/-- The deficient branch supplies a nested pair of scalar-extended real
Cartans with a strict inequality of their actual complex dimensions. -/
theorem fixed_or_strict_nested_cartans (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    IsOrientedFixedPair B h e ∨ ∃ (T : LieSubalgebra ℝ h) (D : LieSubalgebra ℝ g),
      (complexifiedSubalgebra T).IsCartanSubalgebra ∧ (complexifiedSubalgebra D).IsCartanSubalgebra ∧
      finrank ℂ (complexifiedSubalgebra T) < finrank ℂ (complexifiedSubalgebra D) ∧
      ∀ x : complexifiedSubalgebra T, complexifiedLieHom h.incl x ∈ complexifiedSubalgebra D := by
  obtain ⟨T, D, hTab, hTC, hDab, hDC, _, hle, hnest⟩ := compact_pair_nested_real_cartans B h
  letI := hTab
  letI := hTC
  letI := hDab
  letI := hDC
  letI := complexified_abelian_cartan T
  letI := complexified_abelian_cartan D
  by_cases hDh : D ≤ h
  · left
    letI : (complexifiedSubalgebra fixedRealCartan).IsCartanSubalgebra :=
      complexified_fixedRealCartan_eq.symm ▸ fixedCartan_isCartanSubalgebra
    exact compact_common_cartan_pairs_real_equiv B h ha hp e hr D hDh compactForm compactZero
      e8_compact_pair_effective e8_compactZero_ne_top pairCommutantEquivComplex
      e8_canonical_half_cubicRadical_ne_bot fixedRealCartan fixedRealCartan_le_compactZero
  · refine Or.inr ⟨T, D, inferInstance, inferInstance, ?_, hnest⟩
    let F := h.incl.comp T.incl
    let E := LieEquiv.ofInjective F (Subtype.val_injective.comp Subtype.val_injective)
    have strict : F.range.toSubmodule < D.toSubmodule := lt_of_le_of_ne hle (fun he => hDh (by
      intro x hx
      have hx' : x ∈ F.range.toSubmodule := he ▸ hx
      obtain ⟨u, rfl⟩ := (F.mem_range _).mp hx'
      exact u.val.property))
    change finrank ℂ (T.toSubmodule.baseChange ℂ) < finrank ℂ (D.toSubmodule.baseChange ℂ)
    rw [Classification.Complexification.complexification_submodule_finrank,
      Classification.Complexification.complexification_submodule_finrank]
    exact E.toLinearEquiv.finrank_eq.trans_lt (Submodule.finrank_lt_finrank_of_lt strict)

end CubicAnomaly.Fixed.NestedPairReduction
