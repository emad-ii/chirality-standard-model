import CubicAnomaly.Classification.EqualRankSelection
import CubicAnomaly.Classification.RootClassificationOrbit

/-!
# The canonical E₈ grading for a compact pair with a common Cartan

The selected isotropy has dimension 86 and the common Cartan has dimension
eight. Its 78 remaining root directions place the actual character in the
Weyl orbit of the fixed seventh-coordinate character. Pulling that character
back by the resulting reflection word gives all three original spaces.
-/

namespace CubicAnomaly.Classification.EqualRankOrbit

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open RootClassificationExceptional RootClassificationOrbit EqualRankSelection Exceptional
open Structural HermitianRealization Complexification CompactGeometry RootGrading
open ToralCharacter CommonCartan RootSupportDimension Selection
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- For every choice of simple base, a labeling by the E₈ Cartan matrix
and a word in its actual Weyl reflections carry the seventh-coordinate
character to the grading of the isotropy and the two oriented halves. -/
theorem compact_common_cartan_canonical_grading
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] g)] (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
    [H.IsCartanSubalgebra] (hH : H ≤ complexifiedSubalgebra h) (b : (rootSystem H).Base) :
    ∃ s : Index e8Datum ≃ b.support,
      (∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j) ∧
      ∃ w : List (Fin 8),
        let χ := ((simpleCharacterEquiv H b s).symm canonical).comp
          (latticeWord H b s w).toAddMonoidHom
        let q := orthogonalComplement B h
        let J := commutantComplexStructure e
        χ ≠ 0 ∧ DirectSum.IsInternal (rootCharacterGrade H χ) ∧
        rootCharacterGrade H χ 0 = h.toSubmodule.baseChange ℂ ∧
        rootCharacterGrade H χ 1 = (ambientComplexifiedHalf q J Complex.I).toSubmodule ∧
        rootCharacterGrade H χ (-1) = (ambientComplexifiedHalf q J (-Complex.I)).toSubmodule ∧
        ∀ (i j : ZMod 3) (x y : ℂ ⊗[ℝ] g),
          x ∈ rootCharacterGrade H χ i → y ∈ rootCharacterGrade H χ j →
          ⁅x,y⁆ ∈ rootCharacterGrade H χ (i+j) := by
  classical
  obtain ⟨⟨s, hC⟩, _, h86, _⟩ := compact_common_cartan_forces_eight B h heff hp e hr H hH b
  obtain ⟨χ, hn, hsum, hzero, hpos, hneg, hbr⟩ :=
    compact_common_cartan_root_character B h heff hp e hr H hH
  have rankH : finrank ℂ H = 8 := by
    rw [← (Subspace.dual_finrank_eq : finrank ℂ (Dual ℂ H) = finrank ℂ H),
      finrank_eq_card_basis (b.toWeightBasis.reindex s.symm), Fintype.card_fin]
    rfl
  obtain ⟨f, _⟩ := exists_grade_support_equiv H b s
    (d := e8Datum) (by simp [IsExceptionalCensusDatum]) hC χ 0
  have hc : (containedRoots H (rootCharacterGrade H χ 0)).ncard =
      (gradeTable e8Datum (simpleCharacterEquiv H b s χ) 0).card := by
    simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe] using
      (Nat.card_congr f).symm
  have hdim := (compact_common_cartan_root_count_formulas B h heff hp e H hH).1
  rw [h86, rankH, ← hzero, hc] at hdim
  obtain ⟨w, hw⟩ := e8_actual_character_weyl_word H b s hC χ (by omega)
  refine ⟨s, hC, w, ?_⟩
  dsimp only
  rw [← hw]
  exact ⟨hn, hsum, hzero, hpos, hneg, hbr⟩

end CubicAnomaly.Classification.EqualRankOrbit
