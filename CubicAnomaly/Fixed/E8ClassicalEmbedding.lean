import CubicAnomaly.Fixed.E8A2
import CubicAnomaly.Fixed.MatterLabels
import CubicAnomaly.Fixed.MatterFamilyAnomaly

/-!
# Concrete gauge and family subalgebras of the exceptional construction

The two checked matrix-unit systems commute. Their coordinate recovery maps
prove that their direct-product inclusion is faithful. Restricting the first
factor gives the already constructed Standard Model algebra, with its exact
colour/weak ordering and hypercharge convention.
-/

namespace CubicAnomaly.Fixed.E8ClassicalEmbedding

open Matrix
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.TensorAnomaly
open CubicAnomaly.Fixed.MatterLieAlgebra
open CubicAnomaly.Fixed.MatterFamilyAnomaly

noncomputable section

private theorem a4_support (i j : Fin 5) :
    ∀ p ∈ E8A4Data.unitData i j, p.1 ∈ basisList := by
  simpa only [supported, List.all_eq_true, List.contains_iff_mem] using
    (E8A4Data.e8_a4_unit_support_certificate i j).1

private theorem a2_support (i j : Fin 3) :
    ∀ p ∈ E8A2Data.familyUnitData i j, p.1 ∈ basisList := by
  simpa only [supported, List.all_eq_true, List.contains_iff_mem] using
    (E8A2Data.e8_a2_unit_support_certificate i j).1

theorem e8_a4_a2_units_commute (i j : Fin 5) (k l : Fin 3) :
    ⁅E8A4.unitImage i j, E8A2.unitImage k l⁆ = 0 := by
  have hc : candidateBracket (realize (E8A4Data.unitData i j))
      (realize (E8A2Data.familyUnitData k l)) = 0 := by
    rw [e8_candidateBracket_realize _ _ (a4_support i j) (a2_support k l)]
    exact e8_realize_eq_of_sparseEq _ _
      (E8A2Data.e8_a4_a2_commuting_certificate i j k l)
  unfold E8A4.unitImage E8A2.unitImage
  rw [← e8_adjointEquiv_bracket]
  simp [E8A4.unitVector, E8A2.unitVector, hc]

theorem e8_a4_a2_matrices_commute (A : E8A4.Matrix5) (B : E8A2.Matrix3) :
    ⁅E8A4.gl5Hom A, E8A2.gl3Hom B⁆ = 0 := by
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A A' hA hA' => simp [add_lie, hA, hA']
  | h_std_basis i j a =>
    induction B using Matrix.induction_on' with
    | h_zero => simp
    | h_add B B' hB hB' => simp [lie_add, hB, hB']
    | h_std_basis k l b =>
      have ha : Matrix.single i j a = a • Matrix.single i j (1 : ℂ) := by simp
      have hb : Matrix.single k l b = b • Matrix.single k l (1 : ℂ) := by simp
      rw [ha, hb, map_smul, map_smul, smul_lie, lie_smul,
        E8A4.e8_a4_gl5Hom_unit, E8A2.e8_a2_gl3Hom_unit, e8_a4_a2_units_commute]
      simp

theorem e8_family_recovery_a4_unit (i j : Fin 5) :
    E8A2.recovery (E8A4.unitVector i j) = 0 := by
  unfold E8A4.unitVector
  rw [map_smul]
  ext a b
  change (1 / 5 : ℂ) * E8A2.recovery (realize (E8A4Data.unitData i j)) a b = 0
  rw [E8A2.e8_a2_recovery_sparse _ (a4_support i j),
    E8A2Data.e8_a2_recovery_vanishes_on_a4_certificate]
  simp

theorem e8_family_recovery_a4 (A : E8A4.Matrix5) :
    E8A2.recovery (adjointEquiv.symm (E8A4.gl5Hom A)) = 0 := by
  let T := E8A2.recovery.comp
    (adjointEquiv.symm.toLinearEquiv.toLinearMap.comp E8A4.gl5Hom.toLinearMap)
  have hT : T = 0 := by
    apply (Matrix.stdBasis ℂ (Fin 5) (Fin 5)).ext
    rintro ⟨i, j⟩
    rw [Matrix.stdBasis_eq_single]
    change E8A2.recovery (adjointEquiv.symm
      (E8A4.gl5Hom (Matrix.single i j 1))) = 0
    rw [E8A4.e8_a4_gl5Hom_unit]
    change E8A2.recovery (adjointEquiv.symm (adjointEquiv (E8A4.unitVector i j))) = 0
    rw [adjointEquiv.symm_apply_apply, e8_family_recovery_a4_unit]
  exact LinearMap.congr_fun hT A

abbrev ClassicalPair := ProductLie E8A4.sl5 E8A2.sl3

/-- The actual commuting special-linear product inside the exceptional algebra. -/
def classicalEmbedding : ClassicalPair →ₗ⁅ℂ⁆ E8Geck.lieAlgebra where
  toFun x := E8A4.sl5Embedding x.1 + E8A2.sl3Embedding x.2
  map_add' x y := by
    change E8A4.sl5Embedding (x.1 + y.1) + E8A2.sl3Embedding (x.2 + y.2) =
      (E8A4.sl5Embedding x.1 + E8A2.sl3Embedding x.2) +
        (E8A4.sl5Embedding y.1 + E8A2.sl3Embedding y.2)
    simp only [map_add]
    abel
  map_smul' c x := by
    change E8A4.sl5Embedding (c • x.1) + E8A2.sl3Embedding (c • x.2) =
      c • (E8A4.sl5Embedding x.1 + E8A2.sl3Embedding x.2)
    simp only [map_smul, smul_add]
  map_lie' {x y} := by
    have hc (a : E8A4.sl5) (b : E8A2.sl3) :
        ⁅E8A4.sl5Embedding a, E8A2.sl3Embedding b⁆ = 0 :=
      e8_a4_a2_matrices_commute a.val b.val
    have hc' (a : E8A4.sl5) (b : E8A2.sl3) :
        ⁅E8A2.sl3Embedding b, E8A4.sl5Embedding a⁆ = 0 := by
      rw [← lie_skew, hc, neg_zero]
    change E8A4.sl5Embedding ⁅x.1, y.1⁆ + E8A2.sl3Embedding ⁅x.2, y.2⁆ = _
    simp [add_lie, lie_add, hc, hc']

theorem e8_classicalEmbedding_injective : Function.Injective classicalEmbedding := by
  intro x y h
  have hr := congrArg
    (fun z : E8Geck.lieAlgebra => E8A2.recovery (adjointEquiv.symm z)) h
  have hs (a : E8A4.sl5) :
      E8A2.recovery (adjointEquiv.symm (E8A4.sl5Embedding a)) = 0 :=
    e8_family_recovery_a4 a.val
  change E8A2.recovery (adjointEquiv.symm
      (E8A4.sl5Embedding x.1 + E8A2.sl3Embedding x.2)) =
    E8A2.recovery (adjointEquiv.symm
      (E8A4.sl5Embedding y.1 + E8A2.sl3Embedding y.2)) at hr
  simp only [map_add, hs, E8A2.e8_a2_recovery_sl3, zero_add] at hr
  have hy : x.2 = y.2 := Subtype.ext hr
  have hx : x.1 = y.1 := by
    apply E8A4.e8_a4_sl5Embedding_injective
    change E8A4.sl5Embedding x.1 + E8A2.sl3Embedding x.2 =
      E8A4.sl5Embedding y.1 + E8A2.sl3Embedding y.2 at h
    rw [hy] at h
    exact add_right_cancel h
  exact Prod.ext hx hy

/-- Reindex the actual block Standard Model algebra in the selected A4 chain. -/
def gaugeMatrixHom : StandardModelAlgebra →ₗ⁅ℂ⁆ E8A4.Matrix5 :=
  ((Matrix.reindexAlgEquiv ℂ ℂ MatterLabels.fiveIndexEquiv).toAlgHom.toLieHom).comp
    standardModelLieSubalgebra.incl

private theorem gauge_trace_zero (x : StandardModelAlgebra) :
    Matrix.trace (gaugeMatrixHom x) = 0 := by
  have ht : Matrix.trace (gaugeMatrixHom x) = Matrix.trace x.val := by
    exact MatterLabels.fiveIndexEquiv.symm.sum_comp (fun i => x.val i i)
  exact ht.trans x.property.2

def gaugeSl5Embedding : StandardModelAlgebra →ₗ⁅ℂ⁆ E8A4.sl5 where
  __ := gaugeMatrixHom.toLinearMap.codRestrict E8A4.sl5.toSubmodule gauge_trace_zero
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact gaugeMatrixHom.map_lie x y

theorem e8_gaugeSl5Embedding_injective : Function.Injective gaugeSl5Embedding := by
  intro x y h
  apply Subtype.ext
  apply (Matrix.reindexAlgEquiv ℂ ℂ MatterLabels.fiveIndexEquiv).injective
  exact congrArg Subtype.val h

/-- The already constructed gauge-plus-family algebra embedded in the actual E8 algebra. -/
def gaugeFamilyEmbedding : GaugeFamilyAlgebra →ₗ⁅ℂ⁆ E8Geck.lieAlgebra :=
  classicalEmbedding.comp
    { toFun := fun x => (gaugeSl5Embedding x.1, x.2)
      map_add' x y := Prod.ext (map_add gaugeSl5Embedding x.1 y.1) rfl
      map_smul' c x := Prod.ext (map_smul gaugeSl5Embedding c x.1) rfl
      map_lie' {x y} := Prod.ext (gaugeSl5Embedding.map_lie x.1 y.1) rfl }

theorem e8_gaugeFamilyEmbedding_injective : Function.Injective gaugeFamilyEmbedding := by
  intro x y h
  have hp := e8_classicalEmbedding_injective h
  change (gaugeSl5Embedding x.1, x.2) = (gaugeSl5Embedding y.1, y.2) at hp
  exact Prod.ext
    (e8_gaugeSl5Embedding_injective (congrArg (fun p : ClassicalPair => p.1) hp))
    (congrArg (fun p : ClassicalPair => p.2) hp)

theorem e8_gaugeFamilyEmbedding_mem_zero (x : GaugeFamilyAlgebra) :
    gaugeFamilyEmbedding x ∈ zeroSubalgebra :=
  zeroSubalgebra.add_mem
    (E8A4.e8_a4_sl5Embedding_mem_zero (gaugeSl5Embedding x.1))
    (E8A2.e8_a2_sl3Embedding_mem_zero x.2)

/-- The same faithful gauge and family inclusion with its actual graded codomain. -/
def gaugeFamilyZeroEmbedding : GaugeFamilyAlgebra →ₗ⁅ℂ⁆ zeroSubalgebra where
  __ := gaugeFamilyEmbedding.toLinearMap.codRestrict zeroSubalgebra.toSubmodule
    e8_gaugeFamilyEmbedding_mem_zero
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact gaugeFamilyEmbedding.map_lie x y

theorem e8_gaugeFamilyZeroEmbedding_injective :
    Function.Injective gaugeFamilyZeroEmbedding := by
  intro x y h
  exact e8_gaugeFamilyEmbedding_injective (congrArg Subtype.val h)

end

end CubicAnomaly.Fixed.E8ClassicalEmbedding
