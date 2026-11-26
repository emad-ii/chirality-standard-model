import CubicAnomaly.Classification.ExceptionalSieveF4
import CubicAnomaly.Fixed.E8EqualRankRealPair

/-! The original pair hypotheses preclude a nonzero mixed radical in
dimensions fourteen and fifty-two, in both possible rank branches. -/

namespace CubicAnomaly.Fixed.SmallExceptionalExclusion

open LieAlgebra LieModule LieAlgebra.IsKilling Module
open Classification.Structural Classification.CompactCartan Classification.CompactGeometry
open Classification.Complexification Classification.HermitianRealization Classification.AllRankComplex
open Classification.ExceptionalSieveRankOne Classification.ExceptionalSieveF4
open Classification.ExceptionalF4Dimension E8EqualRankRealPair
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]

/-- In dimensions fourteen and fifty-two every effective proper compact
pair with complex commutant has zero canonical mixed cubic radical. -/
theorem small_exceptional_radical_eq_bot (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hd : finrank ℝ g = 14 ∨ finrank ℝ g = 52) : (hermitianHalfOfCommutant B h e).cubicRadical = ⊥ := by
  by_contra hr
  have hstr := all_rank_complex_structural_reduction B h ha hp e hr
  letI : IsKilling ℂ (ℂ ⊗[ℝ] g) := hstr.2.2.1
  letI : IsSimple ℂ (ℂ ⊗[ℝ] g) := hstr.2.1
  obtain ⟨A, haA, hdim⟩ := exists_abelian_finrank_eq_abelianRank ℝ g
  letI := haA
  letI : A.IsCartanSubalgebra := compact_maximum_abelian_isCartan B A hdim
  let H := complexifiedSubalgebra A
  letI : H.IsCartanSubalgebra := complexified_abelian_cartan A
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  have hdim' : finrank ℂ H = abelianRank ℝ g := by
    change finrank ℂ (A.toSubmodule.baseChange ℂ) = _
    rw [complexification_submodule_finrank]
    exact hdim
  rcases all_rank_deficient_or_fixed_pair B h ha hp e hr with hlt | ⟨f, _, _⟩
  · rcases hd with h14 | h52
    · have hle := dim14_cartan_finrank_le_two H b (by rwa [finrank_baseChange])
      have hlo := all_rank_isotropy_rank_ge_two B h ha hp e hr
      omega
    · obtain ⟨s, _⟩ := dim52_matching_F4 H b (by rwa [finrank_baseChange])
      have h4 : finrank ℂ H = 4 :=
        (finrank_eq_card_basis (b.toCoweightBasis.reindex s.symm)).trans (Fintype.card_fin _)
      have hlo := compact_pair_dimension_52_rank_ge_four B h ha hp e hr h52
      omega
  · have h248 := f.toLinearEquiv.finrank_eq.trans E8Structure.e8_compact_finrank
    omega

end CubicAnomaly.Fixed.SmallExceptionalExclusion
