import CubicAnomaly.Classification.EqualRankOrbit
import CubicAnomaly.Classification.RootClassificationConjugacy

/-! # Lie conjugacy of the equal-rank compact pair's complex grading

A single automorphism of the complexified ambient algebra carries the original
complexified isotropy and both oriented halves to the corresponding grades
of the canonical E₈ character.
-/

namespace CubicAnomaly.Classification.EqualRankConjugacy

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open RootClassificationExceptional RootClassificationOrbit Exceptional RootClassificationConjugacy
open Structural HermitianRealization Complexification CompactGeometry RootGrading
open ToralCharacter CommonCartan Selection
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The complexified isotropy, positive half, and negative half are
simultaneously sent to the fixed character's grades by a Lie automorphism. -/
theorem compact_common_cartan_canonical_lie_conjugacy
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] g)] (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
    [H.IsCartanSubalgebra] (hH : H ≤ complexifiedSubalgebra h) (b : (rootSystem H).Base) :
    ∃ s : Index e8Datum ≃ b.support,
      (∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j) ∧
      ∃ σ : (ℂ ⊗[ℝ] g) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] g),
        let ψ := (simpleCharacterEquiv H b s).symm canonical
        let q := orthogonalComplement B h
        let J := commutantComplexStructure e
        (∀ x, σ x ∈ H ↔ x ∈ H) ∧
        (h.toSubmodule.baseChange ℂ).map σ.toLinearMap = rootCharacterGrade H ψ 0 ∧
        (ambientComplexifiedHalf q J Complex.I).toSubmodule.map σ.toLinearMap =
          rootCharacterGrade H ψ 1 ∧
        (ambientComplexifiedHalf q J (-Complex.I)).toSubmodule.map σ.toLinearMap =
          rootCharacterGrade H ψ (-1) := by
  obtain ⟨s, hs, w, _, _, hzero, hpos, hneg, _⟩ :=
    EqualRankOrbit.compact_common_cartan_canonical_grading B h heff hp e hr H hH b
  obtain ⟨σ, hHσ, hσ⟩ := map_character_grades_of_word_preserving_cartan H b s w _
    ((simpleCharacterEquiv H b s).symm canonical) rfl
  refine ⟨s, hs, σ, ?_⟩
  dsimp only
  exact ⟨hHσ, hzero ▸ hσ 0, hpos ▸ hσ 1, hneg ▸ hσ (-1)⟩

end CubicAnomaly.Classification.EqualRankConjugacy
