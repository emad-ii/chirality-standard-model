import CubicAnomaly.Classification.RootClassificationSieve
import CubicAnomaly.Classification.RootClassificationCubic
import CubicAnomaly.Classification.QuadraticRestriction

/-!
# Selection for an actual compact pair with an exceptional common Cartan

Starting from the original algebraic hypotheses, the common Cartan supplies
a nonzero root-lattice character. Its actual grade-zero roots span the dual
and its grade-one root cubic has nonzero kernel. Once the simple Cartan
matrix matches one of the five exceptional data, these conditions select
the E8 matrix and force the dimensions of the ambient algebra, isotropy and
complex half.
-/

namespace CubicAnomaly.Classification.RootClassificationExceptional

open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.Selection
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.FullRankRoots
open CubicAnomaly.Classification.ToralCharacter
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.RootSupportDimension
open CubicAnomaly.Classification.QuadraticRestriction
open LieAlgebra LieModule Module LieAlgebra.IsKilling
open scoped TensorProduct Matrix

/-- An identified exceptional common Cartan in an actual anomalous compact
pair forces the E8 datum, 248-dimensional ambient algebra, 86-dimensional
isotropy, and 81-dimensional canonical positive eigenspace. -/
theorem exceptional_common_cartan_selection
    {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hrad : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra] (hH : H ≤ complexifiedSubalgebra h)
    {d : RootDatum} (hd : IsExceptionalCensusDatum d)
    (b : (rootSystem H).Base) (s : Index d ≃ b.support)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j) :
    d = e8Datum ∧ finrank ℝ g = 248 ∧ finrank ℝ h = 86 ∧
      finrank ℂ (invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I) = 81 := by
  classical
  obtain ⟨χ, hχ, _, hzero, hone, _, _⟩ := compact_common_cartan_root_character B h heff hproper e hrad H hH
  let a := simpleCharacterEquiv H b s χ
  have ha : a ≠ 0 := by
    intro hz
    apply hχ
    apply (simpleCharacterEquiv H b s).injective
    rw [show simpleCharacterEquiv H b s χ = 0 from hz]
    ext i
    simp
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hrad).2.2.2.1
  have hk := (canonical_anomaly_iff_census_kernel B h heff hproper e (LieAlgebra.center_eq_bot ℝ h)
    H hH b s hd hC χ hone).mp hrad
  have hs := compact_common_cartan_root_forms_span_eq_top B h heff hproper e hrad H hH
  obtain ⟨hd8, h0, h1⟩ := exceptional_assignment_selection hd a ha
    (zero_grade_separates_census_coordinates H b s hd hC χ (complexifiedSubalgebra h) hzero.symm hs) hk
  have rankH : finrank ℂ H = 8 := by
    rw [← (Subspace.dual_finrank_eq : finrank ℂ (Dual ℂ H) = finrank ℂ H), finrank_eq_card_basis (b.toWeightBasis.reindex s.symm),
      Fintype.card_fin, hd8]
    rfl
  have count (k : ZMod 3) : (containedRoots H (rootCharacterGrade H χ k)).ncard =
      (gradeTable d a k).card := by
    obtain ⟨f, -⟩ := exists_grade_support_equiv H b s hd hC χ k
    simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe] using
      (Nat.card_congr f).symm
  obtain ⟨hdimh, hdimP, _, _⟩ := compact_common_cartan_root_count_formulas B h heff hproper e H hH
  rw [← hzero, count, h0, rankH] at hdimh
  rw [← hone, count, h1] at hdimP
  have hV := (ambientHalfEquiv (orthogonalComplement B h) (commutantComplexStructure e)
    Complex.I).toLinearEquiv.finrank_eq.trans hdimP
  have hdim := compact_pair_dimension_equation B h hproper e
  exact ⟨hd8, by omega, hdimh, hV⟩

end CubicAnomaly.Classification.RootClassificationExceptional
