import CubicAnomaly.Classification.AllRankComplex
import CubicAnomaly.Classification.RootClassificationClassical
import CubicAnomaly.Classification.RootClassificationSelection
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! At equal rank, the original compact-pair hypotheses select the E₈
Cartan matrix and determine the dimensions of the actual three spaces. -/

namespace CubicAnomaly.Classification.EqualRankSelection

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open RootClassificationExceptional RootClassificationClassical Exceptional
open CompactCartan FullRankRoots ToralCharacter Structural HermitianRealization
open Complexification CompactGeometry AllRankComplex
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- A common Cartan in an actual anomalous compact pair has the E₈ Cartan
matrix. The ambient, isotropy and one complex half have dimensions 248, 86
and 81. No identification with classified data is an input. -/
theorem compact_common_cartan_forces_eight
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] g)] (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
    [H.IsCartanSubalgebra] (hH : H ≤ complexifiedSubalgebra h) (b : (rootSystem H).Base) :
    (∃ s : Index e8Datum ≃ b.support,
      ∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j) ∧
      finrank ℝ g = 248 ∧ finrank ℝ h = 86 ∧
      finrank ℂ (invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I) = 81 := by
  classical
  letI : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g) :=
    (all_rank_complex_structural_reduction B h heff hp e hr).2.1
  rcases simple_lie_classical_or_exceptional_census H b with hc | ⟨d, hd, s, hm, _⟩
  · obtain ⟨χ, hn, _, hz, _⟩ := compact_common_cartan_root_character B h heff hp e hr H hH
    exact (hn (classical_cartan_character_span_obstruction H b hc χ
      (complexifiedSubalgebra h) hz.symm
      (compact_common_cartan_root_forms_span_eq_top B h heff hp e hr H hH))).elim
  · obtain ⟨rfl, hdim⟩ := exceptional_common_cartan_selection B h heff hp e hr H hH hd b s hm
    exact ⟨⟨s, hm⟩, hdim⟩

/-- Every pair satisfying the original hypotheses has strict rank deficiency
or an ambient rank of eight and dimensions 248, 86 and 81. -/
theorem all_rank_deficient_or_eight_dimensions
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    abelianRank ℝ h < abelianRank ℝ g ∨
      abelianRank ℝ g = 8 ∧ finrank ℝ g = 248 ∧ finrank ℝ h = 86 ∧
      finrank ℂ (invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I) = 81 := by
  classical
  rcases (abelianRank_subalgebra_le ℝ g h).lt_or_eq with hl | he
  · exact Or.inl hl
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) :=
    (all_rank_complex_structural_reduction B h heff hp e hr).2.2.1
  obtain ⟨H, hCartan, hH, hdimH⟩ := compact_equal_abelianRank_exists_complex_cartan B h he
  letI := hCartan
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  obtain ⟨⟨s, _⟩, hdim⟩ := compact_common_cartan_forces_eight B h heff hp e hr H hH b
  refine Or.inr ⟨?_, hdim⟩
  rw [← hdimH, ← (Subspace.dual_finrank_eq : finrank ℂ (Dual ℂ H) = finrank ℂ H),
    finrank_eq_card_basis (b.toWeightBasis.reindex s.symm), Fintype.card_fin]
  rfl

end CubicAnomaly.Classification.EqualRankSelection
