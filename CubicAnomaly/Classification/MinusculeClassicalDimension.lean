import CubicAnomaly.Classification.MinusculeDimension
import CubicAnomaly.Classification.MinusculeIntegralWeights
import CubicAnomaly.Classification.RootClassificationClassicalCD

/-!
# Dimension bounds for the defining D weight and the middle A₃ weight

The defining D weights are indexed by the positive and negative coordinate
vectors. The six weights of the A₃ middle fundamental representation are
indexed by pairs of the four defining coordinates.
-/

namespace CubicAnomaly.Classification.MinusculeClassicalDimension

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentHighest
open RootClassificationClassicalCD MinusculeIntegralWeights MinusculeDimension

private def middleLabel : Fin 6 → Fin 3 → ℤ :=
  ![![0,1,0], ![1,-1,1], ![1,0,-1], ![-1,0,1], ![-1,1,-1], ![0,-1,0]]

private theorem middleStep : ∀ u i, ∃ v, ∀ j,
    middleLabel v j = middleLabel u j - CartanMatrix.A 3 i j * middleLabel u i := by decide

private theorem middleBounds : ∀ u i, -1 ≤ middleLabel u i ∧ middleLabel u i ≤ 1 := by decide

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
    [IsIrreducible ℂ L M] {χ : Weight ℂ H M} {v : M} (hv : IsHighestVector H b χ v)

include hv in
/-- An irreducible module of actual D type with first fundamental highest
weight has at most twice the rank many dimensions. -/
theorem typeD_vector_finrank_le {n : ℕ} (hn : 3 ≤ n) (s : Fin n ≃ b.support)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.D n i j)
    (hχ : ∀ i, χ (coroot (s i).val.val) = if i.val = 0 then 1 else 0) :
    finrank ℂ M ≤ 2*n := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+2 := ⟨n-2,by omega⟩
  have ha (j : Fin (m+2)) :
      χ (coroot (s j).val.val) = (vectorLabel m (0,false) j : ℂ) := by
    rw [hχ, vectorLabel_highest _ (by omega)]
    split_ifs <;> simp
  obtain ⟨S,hb,hs,hm,hcard⟩ := minuscule_finset_of_integral_labels H b s _ hC
    (vectorLabel m) (0,false) (vectorLabel_reflect m) (vectorLabel_bounds m) χ ha hv
  exact (finrank_le_card_of_minuscule_orbit H b hv S hb hs hm).trans
    (by simpa [Nat.mul_comm] using hcard)

include hv in
/-- An irreducible module of actual A₃ type with highest weight ω₂ has
at most six dimensions. -/
theorem typeA_three_middle_finrank_le (s : Fin 3 ≃ b.support)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.A 3 i j)
    (hχ : ∀ i, χ (coroot (s i).val.val) = if i.val = 1 then 1 else 0) :
    finrank ℂ M ≤ 6 := by
  have ha (j : Fin 3) : χ (coroot (s j).val.val) = (middleLabel 0 j : ℂ) := by
    rw [hχ]
    fin_cases j <;> norm_num [middleLabel]
  obtain ⟨S,hb,hs,hm,hcard⟩ := minuscule_finset_of_integral_labels H b s _ hC
    middleLabel 0 middleStep middleBounds χ ha hv
  exact (finrank_le_card_of_minuscule_orbit H b hv S hb hs hm).trans (by simpa using hcard)

end CubicAnomaly.Classification.MinusculeClassicalDimension
