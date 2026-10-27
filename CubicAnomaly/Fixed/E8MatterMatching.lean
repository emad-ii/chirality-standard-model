import CubicAnomaly.Fixed.E8ClassicalEmbedding
import CubicAnomaly.Fixed.E8MatterRealization
import CubicAnomaly.Fixed.MatterFamilyCoordinates

/-!
# Matching the actual exceptional half with the constructed matter module

The signed coordinate map is an explicit bijection onto the actual degree-one
adjoint subspace. Both matrix-unit identities extend by linearity to the full
gauge and family action. Thus the earlier matter construction and the fixed
exceptional construction describe the same restricted representation.
-/

namespace CubicAnomaly.Fixed.E8MatterMatching

open Matrix
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8MatterRealization
open CubicAnomaly.Fixed.E8ClassicalEmbedding
open CubicAnomaly.Fixed.MatterSpectrum
open CubicAnomaly.Fixed.MatterLieAlgebra
open CubicAnomaly.Fixed.MatterCoordinates
open CubicAnomaly.Fixed.MatterFamilyCoordinates
open CubicAnomaly.Fixed.MatterFamilyAnomaly

noncomputable section

def matterToDefining : Matter81 →ₗ[ℂ] DefiningSpace :=
  matterCoordinateMap.comp matter81ExplicitCoordinates.toLinearMap

/-- The explicit matter basis embedded as actual exceptional matrices. -/
def matterToAdjoint : Matter81 →ₗ[ℂ] E8Geck.lieAlgebra :=
  adjointEquiv.toLinearEquiv.toLinearMap.comp matterToDefining

private def projectedFiveMap : E8A4.Matrix5 →ₗ[ℂ] MatrixFive :=
  (Matrix.reindexAlgEquiv ℂ ℂ MatterLabels.fiveIndexEquiv).symm.toLinearMap.comp
    E8A4.tracelessProjection

private theorem projectedFiveMap_unit (p q : Fin 5) :
    projectedFiveMap (Matrix.single p q 1) =
      (1 / 5 : ℂ) • unitMatrix (MatterLabels.fiveIndexEquiv.symm p)
        (MatterLabels.fiveIndexEquiv.symm q) := by
  have hs : (Matrix.reindexAlgEquiv ℂ ℂ MatterLabels.fiveIndexEquiv).symm
      (Matrix.single p q (1 : ℂ)) =
      Matrix.single (MatterLabels.fiveIndexEquiv.symm p)
        (MatterLabels.fiveIndexEquiv.symm q) 1 := by
    exact Matrix.submatrix_single_equiv _ _ _ _ _
  change (Matrix.reindexAlgEquiv ℂ ℂ MatterLabels.fiveIndexEquiv).symm
    (E8A4.tracelessProjection (Matrix.single p q 1)) = _
  rw [E8A4.e8_a4_tracelessProjection_apply, map_sub, map_smul, map_one, hs]
  by_cases hpq : p = q
  · subst q
    simp [unitMatrix, MatterLabels.delta, smul_sub, smul_smul]
  · have hsym : MatterLabels.fiveIndexEquiv.symm p ≠
        MatterLabels.fiveIndexEquiv.symm q :=
      fun h => hpq (MatterLabels.fiveIndexEquiv.symm.injective h)
    simp [unitMatrix, MatterLabels.delta, hpq, hsym,
      Matrix.trace_single_eq_of_ne p q 1 hpq, smul_smul]

private theorem five_vector_unit_action (p q : Fin 5) (v : Matter81) :
    candidateBracket (E8A4.unitVector p q) (matterToDefining v) =
      matterToDefining ⁅projectedFiveMap (Matrix.single p q 1), v⁆ := by
  have h := e8_matter_a4_unit_action p q (matter81ExplicitCoordinates v)
  have ha := matter81_unit_action p q v
  change candidateBracket (realize (E8A4Data.unitData p q))
      (matterCoordinateMap (matter81ExplicitCoordinates v)) =
    matterCoordinateMap (matterUnitMatrix p q *ᵥ matter81ExplicitCoordinates v) at h
  rw [← ha] at h
  rw [projectedFiveMap_unit]
  simpa only [E8A4.unitVector, matterToDefining, LinearMap.comp_apply,
    map_smul, LinearMap.smul_apply, smul_lie] using
    congrArg (fun w : DefiningSpace => (1 / 5 : ℂ) • w) h

theorem e8_five_vector_action (A : E8A4.Matrix5) (v : Matter81) :
    candidateBracket (adjointEquiv.symm (E8A4.gl5Hom A)) (matterToDefining v) =
      matterToDefining ⁅projectedFiveMap A, v⁆ := by
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A B hA hB => simp [map_add, add_lie, LinearMap.add_apply, hA, hB]
  | h_std_basis p q c =>
      rw [show Matrix.single p q c = c • Matrix.single p q (1 : ℂ) by simp]
      simp only [map_smul, LinearMap.smul_apply, smul_lie]
      rw [E8A4.e8_a4_gl5Hom_unit]
      change c • candidateBracket (adjointEquiv.symm
        (adjointEquiv (E8A4.unitVector p q))) (matterToDefining v) = _
      rw [adjointEquiv.symm_apply_apply, five_vector_unit_action]

private theorem projectedFiveMap_gauge (x : StandardModelAlgebra) :
    projectedFiveMap (gaugeMatrixHom x) = x.val := by
  have ht : Matrix.trace (gaugeMatrixHom x) = 0 := (gaugeSl5Embedding x).property
  change (Matrix.reindexAlgEquiv ℂ ℂ MatterLabels.fiveIndexEquiv).symm
    (E8A4.tracelessProjection (gaugeMatrixHom x)) = x.val
  rw [E8A4.e8_a4_tracelessProjection_apply, ht]
  simp [gaugeMatrixHom]

theorem e8_matter_gauge_action (x : StandardModelAlgebra) (v : Matter81) :
    ⁅E8A4.sl5Embedding (gaugeSl5Embedding x), matterToAdjoint v⁆ =
      matterToAdjoint ⁅x, v⁆ := by
  have h := congrArg adjointEquiv (e8_five_vector_action (gaugeMatrixHom x) v)
  rw [e8_adjointEquiv_bracket, adjointEquiv.apply_symm_apply,
    projectedFiveMap_gauge] at h
  exact h

private theorem family_projection_unit (p q : Fin 3) :
    E8A2.tracelessProjection (Matrix.single p q 1) =
      (1 / 3 : ℂ) • familyUnitMatrix p q := by
  rw [E8A2.e8_a2_tracelessProjection_apply]
  by_cases hpq : p = q
  · subst q
    simp [familyUnitMatrix, MatterLabels.delta, smul_sub, smul_smul]
  · simp [familyUnitMatrix, MatterLabels.delta, hpq,
      Matrix.trace_single_eq_of_ne p q 1 hpq, smul_smul]

private theorem family_vector_unit_action (p q : Fin 3) (v : Matter81) :
    candidateBracket (E8A2.unitVector p q) (matterToDefining v) =
      matterToDefining (familyCopyActionMap
        (E8A2.tracelessProjection (Matrix.single p q 1)) v) := by
  have h := e8_matter_family_unit_action p q (matter81ExplicitCoordinates v)
  have ha := matter81_family_unit_action p q v
  change candidateBracket (realize (E8A2Data.familyUnitData p q))
      (matterCoordinateMap (matter81ExplicitCoordinates v)) =
    matterCoordinateMap (familyMatterUnitMatrix p q *ᵥ matter81ExplicitCoordinates v) at h
  rw [← ha] at h
  rw [family_projection_unit]
  simpa only [E8A2.unitVector, matterToDefining, LinearMap.comp_apply,
    map_smul, LinearMap.smul_apply, family_copy_action_map_apply, familyUnitElement] using
    congrArg (fun w : DefiningSpace => (1 / 3 : ℂ) • w) h

theorem e8_family_vector_action (F : E8A2.Matrix3) (v : Matter81) :
    candidateBracket (adjointEquiv.symm (E8A2.gl3Hom F)) (matterToDefining v) =
      matterToDefining (familyCopyActionMap (E8A2.tracelessProjection F) v) := by
  induction F using Matrix.induction_on' with
  | h_zero => simp
  | h_add F G hF hG => simp [map_add, LinearMap.add_apply, hF, hG]
  | h_std_basis p q c =>
      rw [show Matrix.single p q c = c • Matrix.single p q (1 : ℂ) by simp]
      simp only [map_smul, LinearMap.smul_apply]
      rw [E8A2.e8_a2_gl3Hom_unit]
      change c • candidateBracket (adjointEquiv.symm
        (adjointEquiv (E8A2.unitVector p q))) (matterToDefining v) = _
      rw [adjointEquiv.symm_apply_apply, family_vector_unit_action]

theorem e8_matter_family_action (F : E8A2.sl3) (v : Matter81) :
    ⁅E8A2.sl3Embedding F, matterToAdjoint v⁆ =
      matterToAdjoint (familyCopyAction F.val v) := by
  have h := congrArg adjointEquiv (e8_family_vector_action F.val v)
  have ht : Matrix.trace F.val = 0 := F.property
  rw [e8_adjointEquiv_bracket, adjointEquiv.apply_symm_apply,
    E8A2.e8_a2_tracelessProjection_apply, ht] at h
  simpa using h

/-- The original coupled gauge/family action, transported to the original matter space. -/
def coupledAction (x : GaugeFamilyAlgebra) : Module.End ℂ Matter81 :=
  coupledMatterCoordinates.symm.conj (coupledMatter81Representation x).toLin'

theorem e8_coupledAction_coordinates (x : GaugeFamilyAlgebra) (v : Matter81) :
    coupledMatterCoordinates (coupledAction x v) =
      coupledMatter81Representation x *ᵥ coupledMatterCoordinates v := by
  simp [coupledAction, LinearEquiv.conj_apply, Matrix.toLin'_apply]

private theorem coupledAction_decomposition (x : GaugeFamilyAlgebra) (v : Matter81) :
    coupledAction x v = ⁅x.1, v⁆ + familyCopyAction x.2.val v := by
  apply coupledMatterCoordinates.injective
  rw [e8_coupledAction_coordinates, map_add,
    coupled_matter81_gauge_action, coupled_family_copy_action]
  have hx : x = (x.1, 0) + (0, x.2) := by
    exact Prod.ext (add_zero x.1).symm (zero_add x.2).symm
  conv_lhs => rw [hx, map_add, Matrix.add_mulVec]

theorem e8_matter_full_action (x : GaugeFamilyAlgebra) (v : Matter81) :
    matterToAdjoint (coupledAction x v) =
      ⁅gaugeFamilyEmbedding x, matterToAdjoint v⁆ := by
  rw [coupledAction_decomposition, map_add]
  change _ = ⁅E8A4.sl5Embedding (gaugeSl5Embedding x.1) +
    E8A2.sl3Embedding x.2, matterToAdjoint v⁆
  rw [add_lie, e8_matter_gauge_action, e8_matter_family_action]

/-- The actual homogeneous adjoint module, with its inherited degree-zero action. -/
abbrev ActualMatter := gradeModule 1

private theorem matterToAdjoint_homogeneous (v : Matter81) :
    matterToAdjoint v ∈ (gradeModule 1).toSubmodule :=
  ⟨matterToDefining v, e8_matterCoordinateMap_homogeneous _, rfl⟩

def matterToActualGrade : Matter81 →ₗ[ℂ] ActualMatter :=
  matterToAdjoint.codRestrict (gradeModule 1).toSubmodule matterToAdjoint_homogeneous

/-- The explicit signed basis map identifies the entire actual exceptional half. -/
def actualMatterEquiv : Matter81 ≃ₗ[ℂ] ActualMatter :=
  matterToActualGrade.linearEquivOfInjective
    (by
      intro v w h
      have hv : matterToAdjoint v = matterToAdjoint w :=
        congrArg (fun z : ActualMatter => z.val) h
      change adjointEquiv (matterToDefining v) = adjointEquiv (matterToDefining w) at hv
      have hv' := adjointEquiv.injective hv
      exact matter81ExplicitCoordinates.injective (e8_matterCoordinateMap_injective hv'))
    (by rw [matter81_finrank, e8_complementary_module_dimensions.1])

theorem e8_actualMatterEquiv_val (v : Matter81) :
    (actualMatterEquiv v).val = matterToAdjoint v := rfl

theorem e8_actualMatterEquiv_action (x : GaugeFamilyAlgebra) (v : Matter81) :
    actualMatterEquiv (coupledAction x v) =
      ⁅gaugeFamilyZeroEmbedding x, actualMatterEquiv v⁆ := by
  apply Subtype.ext
  exact e8_matter_full_action x v

/-- Exact action matching in the same coordinates as the existing anomaly theorem. -/
theorem e8_actual_matter_coordinates_action (x : GaugeFamilyAlgebra) (w : ActualMatter) :
    coupledMatterCoordinates (actualMatterEquiv.symm ⁅gaugeFamilyZeroEmbedding x, w⁆) =
      coupledMatter81Representation x *ᵥ
        coupledMatterCoordinates (actualMatterEquiv.symm w) := by
  have h := congrArg actualMatterEquiv.symm
    (e8_actualMatterEquiv_action x (actualMatterEquiv.symm w))
  simp only [actualMatterEquiv.symm_apply_apply, actualMatterEquiv.apply_symm_apply] at h
  exact (congrArg coupledMatterCoordinates h.symm).trans
    (e8_coupledAction_coordinates x (actualMatterEquiv.symm w))

end

end CubicAnomaly.Fixed.E8MatterMatching
