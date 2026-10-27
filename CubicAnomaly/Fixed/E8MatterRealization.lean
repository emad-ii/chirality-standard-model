import CubicAnomaly.Fixed.E8MatterData
import CubicAnomaly.Fixed.E8Grading

/-!
# Realizing the simultaneous classical and family matter witness

The signed finite table defines an explicit linear map into the existing
exceptional module. Its image is the entire degree-one space, and both
collections of matrix-unit actions intertwine on arbitrary vectors.
-/

namespace CubicAnomaly.Fixed.E8MatterRealization

open Matrix
open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8MatterData
open CubicAnomaly.Fixed.E8A4Data
open CubicAnomaly.Fixed.E8A2Data
open scoped BigOperators

noncomputable section

abbrev MatterCoordinateSpace := MatterLabels.Index → ℂ

/-- The literal signed-basis map, before restriction to its homogeneous image. -/
def matterCoordinateMap : MatterCoordinateSpace →ₗ[ℂ] E8Geck.DefiningSpace :=
  Fintype.linearCombination ℂ (fun i => realize (basisData i))

theorem e8_matterCoordinateMap_single (i : MatterLabels.Index) :
    matterCoordinateMap (Pi.single i (1 : ℂ)) = realize (basisData i) := by
  simp [matterCoordinateMap, Fintype.linearCombination_apply_single]

private theorem basisData_supported (i : MatterLabels.Index) :
    ∀ p ∈ basisData i, p.1 ∈ basisList := by
  simp [basisData, E8BracketData.singleton, e8_matter_label_mem_basis]

private theorem basisData_apply (i : MatterLabels.Index) (j : E8Geck.Index) :
    realize (basisData i) j =
      if dataIndex j = rootLabel i then (signOfLabel i : ℂ) else 0 := by
  classical
  by_cases h : dataIndex j = rootLabel i
  · simp [e8_realize_apply, basisData, E8BracketData.singleton, coefficient, h]
  · simp [e8_realize_apply, basisData, E8BracketData.singleton, coefficient, h, Ne.symm h]

theorem e8_matterCoordinateMap_apply (v : MatterCoordinateSpace)
    (i : MatterLabels.Index) (j : E8Geck.Index) (hj : dataIndex j = rootLabel i) :
    matterCoordinateMap v j = v i * (signOfLabel i : ℂ) := by
  classical
  simp [matterCoordinateMap, Fintype.linearCombination_apply, Finset.sum_apply,
    basisData_apply, hj, e8_matter_rootLabel_injective.eq_iff]

private theorem basis_sign_ne_zero (i : MatterLabels.Index) :
    (signOfLabel i : ℂ) ≠ 0 := by
  have h : (signOfLabel i : ℂ) * (signOfLabel i : ℂ) = 1 := by
    exact_mod_cast e8_matter_basis_sign_sq i
  intro hi
  simp [hi] at h

theorem e8_matterCoordinateMap_injective : Function.Injective matterCoordinateMap := by
  intro v w h
  funext i
  obtain ⟨j, hj⟩ := (e8_mem_basisList_iff _).mp (e8_matter_label_mem_basis i)
  have he := congrFun h j
  rw [e8_matterCoordinateMap_apply v i j hj,
    e8_matterCoordinateMap_apply w i j hj] at he
  exact mul_right_cancel₀ (basis_sign_ne_zero i) he

theorem e8_matterCoordinateMap_homogeneous (v : MatterCoordinateSpace) :
    matterCoordinateMap v ∈ gradeSpace 1 := by
  classical
  rw [matterCoordinateMap, Fintype.linearCombination_apply]
  apply (gradeSpace 1).sum_mem
  intro i _
  apply (gradeSpace 1).smul_mem
  apply e8_realize_homogeneous
  simp [basisData, E8BracketData.singleton, e8_matter_label_grade]

/-- The same explicit map with its proved degree-one codomain. -/
def matterCoordinateMapGrade : MatterCoordinateSpace →ₗ[ℂ] gradeSpace 1 :=
  matterCoordinateMap.codRestrict (gradeSpace 1) e8_matterCoordinateMap_homogeneous

/-- Every degree-one vector is represented by exactly one matter coordinate vector. -/
def matterCoordinateEquiv : MatterCoordinateSpace ≃ₗ[ℂ] gradeSpace 1 :=
  matterCoordinateMapGrade.linearEquivOfInjective
    (fun _ _ h => e8_matterCoordinateMap_injective (congrArg Subtype.val h))
    (by rw [Module.finrank_fintype_fun_eq_card, MatterLabels.matter_label_card,
      e8_gradeSpace_dimensions.2.1])

theorem e8_matterCoordinateEquiv_val (v : MatterCoordinateSpace) :
    (matterCoordinateEquiv v).val = matterCoordinateMap v := rfl

private theorem realize_filtered_columns (c : MatterLabels.Index → ℤ)
    (xs : List MatterLabels.Index) :
    realize (xs.filterMap fun r =>
      if c r = 0 then none else some (rootLabel r, c r * signOfLabel r)) =
        (xs.map fun r => (c r : ℂ) • realize (basisData r)).sum := by
  induction xs with
  | nil => simp [realize, SparseRealization.realize]
  | cons r xs ih =>
      by_cases hr : c r = 0
      · simp [hr, ih]
      · simp only [List.filterMap_cons, if_neg hr, List.map_cons, List.sum_cons]
        change (c r * signOfLabel r) • basisVector (rootLabel r) +
            realize (xs.filterMap fun r =>
              if c r = 0 then none else some (rootLabel r, c r * signOfLabel r)) = _
        rw [ih]
        simp only [basisData, e8_realize_singleton, Int.cast_smul_eq_zsmul, SemigroupAction.mul_smul]

theorem e8_matrixColumnData_realize (c : MatterLabels.Index → ℤ) :
    realize (matrixColumnData c) = matterCoordinateMap (fun i => (c i : ℂ)) := by
  classical
  rw [matrixColumnData, realize_filtered_columns, matterCoordinateMap,
    Fintype.linearCombination_apply]
  simpa only [e8_matter_labelList_toFinset] using
    (List.sum_toFinset (fun r => (c r : ℂ) • realize (basisData r))
      e8_matter_labelList_nodup).symm

/-- The checked integral A4 column identity holds in the actual exceptional space. -/
theorem e8_matter_a4_basis_action (p q : Fin 5) (s : MatterLabels.Index) :
    candidateBracket (realize (unitData p q))
        (matterCoordinateMap (Pi.single s (1 : ℂ))) =
      matterCoordinateMap
        ((fun r t => (MatterLabels.unitCoefficient p q r t : ℂ)) *ᵥ Pi.single s 1) := by
  classical
  rw [e8_matterCoordinateMap_single, Matrix.mulVec_single_one]
  have hu : ∀ x ∈ unitData p q, x.1 ∈ basisList := by
    simpa only [supported, List.all_eq_true, List.contains_iff_mem] using
      (e8_a4_unit_support_certificate p q).1
  calc
    candidateBracket (realize (unitData p q)) (realize (basisData s)) =
        realize (sparseBracket (unitData p q) (basisData s)) :=
      e8_candidateBracket_realize _ _ hu (basisData_supported s)
    _ = realize (matrixColumnData (fun r => MatterLabels.unitCoefficient p q r s)) :=
      e8_realize_eq_of_sparseEq _ _ (e8_matter_a4_unit_match_certificate p q s)
    _ = _ := e8_matrixColumnData_realize _

/-- The checked integral family column identity holds in the same actual space. -/
theorem e8_matter_family_basis_action (p q : Fin 3) (s : MatterLabels.Index) :
    candidateBracket (realize (familyUnitData p q))
        (matterCoordinateMap (Pi.single s (1 : ℂ))) =
      matterCoordinateMap
        ((fun r t => (MatterLabels.familyUnitCoefficient p q r t : ℂ)) *ᵥ
          Pi.single s 1) := by
  classical
  rw [e8_matterCoordinateMap_single, Matrix.mulVec_single_one]
  have hu : ∀ x ∈ familyUnitData p q, x.1 ∈ basisList := by
    simpa only [supported, List.all_eq_true, List.contains_iff_mem] using
      (e8_a2_unit_support_certificate p q).1
  calc
    candidateBracket (realize (familyUnitData p q)) (realize (basisData s)) =
        realize (sparseBracket (familyUnitData p q) (basisData s)) :=
      e8_candidateBracket_realize _ _ hu (basisData_supported s)
    _ = realize (matrixColumnData (fun r => MatterLabels.familyUnitCoefficient p q r s)) :=
      e8_realize_eq_of_sparseEq _ _ (e8_matter_family_unit_match_certificate p q s)
    _ = _ := e8_matrixColumnData_realize _

private theorem extend_basis_action (u : E8Geck.DefiningSpace)
    (A : Matrix MatterLabels.Index MatterLabels.Index ℂ)
    (h : ∀ i, candidateBracket u (matterCoordinateMap (Pi.single i (1 : ℂ))) =
      matterCoordinateMap (A *ᵥ Pi.single i 1)) (v : MatterCoordinateSpace) :
    candidateBracket u (matterCoordinateMap v) = matterCoordinateMap (A *ᵥ v) := by
  classical
  have he : (candidateBracket u).comp matterCoordinateMap =
      matterCoordinateMap.comp (Matrix.toLin' A) := by
    apply LinearMap.pi_ext
    intro i c
    have hs : (Pi.single i c : MatterCoordinateSpace) =
        c • (Pi.single i (1 : ℂ) : MatterCoordinateSpace) := by
      ext j
      by_cases hij : i = j
      · subst j
        simp
      · simp [Ne.symm hij]
    rw [hs]
    simpa only [map_smul, LinearMap.comp_apply, Matrix.toLin'_apply] using
      congrArg (fun z : E8Geck.DefiningSpace => c • z) (h i)
  exact LinearMap.congr_fun he v

/-- The entire A4 action is matched, not only its dimension or weight multiset. -/
theorem e8_matter_a4_unit_action (p q : Fin 5) (v : MatterCoordinateSpace) :
    candidateBracket (realize (unitData p q)) (matterCoordinateMap v) =
      matterCoordinateMap ((fun r s => (MatterLabels.unitCoefficient p q r s : ℂ)) *ᵥ v) :=
  extend_basis_action _ _ (e8_matter_a4_basis_action p q) v

/-- The commuting family action is matched on the same signed basis. -/
theorem e8_matter_family_unit_action (p q : Fin 3) (v : MatterCoordinateSpace) :
    candidateBracket (realize (familyUnitData p q)) (matterCoordinateMap v) =
      matterCoordinateMap
        ((fun r s => (MatterLabels.familyUnitCoefficient p q r s : ℂ)) *ᵥ v) :=
  extend_basis_action _ _ (e8_matter_family_basis_action p q) v

end

end CubicAnomaly.Fixed.E8MatterRealization
