import CubicAnomaly.Fixed.DiagonalTreeIrreducible
import CubicAnomaly.Fixed.E8MatterIrreducibleData
import CubicAnomaly.Fixed.E8MatterRealization

/-!
# Irreducibility of the actual exceptional degree-one module

An explicit degree-zero Cartan element separates all eighty-one basis lines.
The checked root-action tree joins those lines using actual degree-zero
matrices. Polynomial coordinate isolation and tree propagation therefore
prove irreducibility for the full actual zero-grade Lie algebra.
-/

namespace CubicAnomaly.Fixed.E8MatterIrreducible

open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8A4Data
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8MatterData
open CubicAnomaly.Fixed.E8MatterRealization
open CubicAnomaly.Fixed.E8MatterIrreducibleData

noncomputable section

/-- The literal signed coordinates, now in the actual homogeneous adjoint module. -/
def actualCoordinateMap : MatterCoordinateSpace →ₗ[ℂ] gradeModule 1 :=
  (adjointEquiv.toLinearEquiv.toLinearMap.comp matterCoordinateMap).codRestrict
    (gradeModule 1).toSubmodule
    (fun v => ⟨matterCoordinateMap v, e8_matterCoordinateMap_homogeneous v, rfl⟩)

private theorem actualCoordinateMap_injective : Function.Injective actualCoordinateMap := by
  intro v w h
  have hv : adjointEquiv (matterCoordinateMap v) = adjointEquiv (matterCoordinateMap w) :=
    congrArg (fun z : gradeModule 1 => z.val) h
  exact e8_matterCoordinateMap_injective (adjointEquiv.injective hv)

def actualCoordinateEquiv : MatterCoordinateSpace ≃ₗ[ℂ] gradeModule 1 :=
  actualCoordinateMap.linearEquivOfInjective actualCoordinateMap_injective
    (by rw [Module.finrank_fintype_fun_eq_card, MatterLabels.matter_label_card,
      e8_complementary_module_dimensions.1])

theorem e8_irreducible_coordinates_val (v : MatterCoordinateSpace) :
    (actualCoordinateEquiv v).val = adjointEquiv (matterCoordinateMap v) := rfl

private theorem coordinate_basis_val (i : MatterLabels.Index) :
    (actualCoordinateEquiv (Pi.single i (1 : ℂ))).val =
      adjointEquiv (realize (basisData i)) := by
  rw [e8_irreducible_coordinates_val, e8_matterCoordinateMap_single]

private theorem basis_supported (i : MatterLabels.Index) :
    ∀ p ∈ basisData i, p.1 ∈ basisList := by
  simp [basisData, E8BracketData.singleton, e8_matter_label_mem_basis]

private theorem supported_entries (xs : Sparse) (hs : supported xs = true) :
    ∀ p ∈ xs, p.1 ∈ basisList := by
  simpa only [supported, List.all_eq_true, List.contains_iff_mem] using hs

/-- Any checked degree-zero sparse vector defines an actual zero-grade element. -/
def zeroElement (xs : Sparse) (hz : xs.all (fun p => grade p.1 == 0) = true) :
    zeroSubalgebra :=
  ⟨adjointEquiv (realize xs), ⟨realize xs,
    e8_realize_homogeneous xs 0 (fun p hp => eq_of_beq ((List.all_eq_true.mp hz) p hp)),
    rfl⟩⟩

private theorem sparse_scalar_action (xs : Sparse)
    (hs : supported xs = true) (hz : xs.all (fun p => grade p.1 == 0) = true)
    (i j : MatterLabels.Index) (c : ℤ)
    (ha : sparseEq (sparseBracket xs (basisData i)) (scale c (basisData j)) = true) :
    ⁅zeroElement xs hz, actualCoordinateEquiv (Pi.single i (1 : ℂ))⁆ =
      (c : ℂ) • actualCoordinateEquiv (Pi.single j (1 : ℂ)) := by
  apply Subtype.ext
  change ⁅adjointEquiv (realize xs),
      (actualCoordinateEquiv (Pi.single i (1 : ℂ))).val⁆ =
    (c : ℂ) • (actualCoordinateEquiv (Pi.single j (1 : ℂ))).val
  rw [coordinate_basis_val, coordinate_basis_val, ← e8_adjointEquiv_bracket,
    e8_candidateBracket_realize _ _ (supported_entries xs hs) (basis_supported i)]
  have hh := e8_realize_eq_of_sparseEq _ _ ha
  unfold sparseBracket at hh
  rw [hh, e8_realize_scale, map_zsmul, Int.cast_smul_eq_zsmul]

private def diagonalOperator : Module.End ℂ MatterCoordinateSpace where
  toFun v i := (eigenvalue i : ℂ) * v i
  map_add' v w := by ext i; exact mul_add _ _ _
  map_smul' c v := by
    ext i
    change (eigenvalue i : ℂ) * (c * v i) = c * ((eigenvalue i : ℂ) * v i)
    ring

private theorem diagonalOperator_single (i : MatterLabels.Index) :
    diagonalOperator (Pi.single i (1 : ℂ)) =
      (eigenvalue i : ℂ) • (Pi.single i (1 : ℂ) : MatterCoordinateSpace) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [diagonalOperator]
  · simp [diagonalOperator, hj]

private theorem diagonal_actual_action (v : MatterCoordinateSpace) :
    ⁅zeroElement diagonalData e8_matter_separating_diagonal_certificate.2.1,
      actualCoordinateEquiv v⁆ = actualCoordinateEquiv (diagonalOperator v) := by
  let H := zeroElement diagonalData e8_matter_separating_diagonal_certificate.2.1
  have he : (LieModule.toEnd ℂ zeroSubalgebra (gradeModule 1) H).comp
      actualCoordinateEquiv.toLinearMap =
      actualCoordinateEquiv.toLinearMap.comp diagonalOperator := by
    apply (Pi.basisFun ℂ MatterLabels.Index).ext
    intro i
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, Pi.basisFun_apply,
      LinearEquiv.coe_coe, diagonalOperator_single, map_smul]
    exact sparse_scalar_action diagonalData e8_matter_separating_diagonal_certificate.1
      e8_matter_separating_diagonal_certificate.2.1 i i (eigenvalue i)
      (e8_matter_separating_diagonal_certificate.2.2.2 i)
  exact LinearMap.congr_fun he v

set_option maxHeartbeats 800000 in
/-- Every nonzero submodule for the actual zero-grade algebra is the entire
actual degree-one module. -/
theorem e8_actualMatter_submodule_eq_top
    (U : LieSubmodule ℂ zeroSubalgebra (gradeModule 1)) (hU : U ≠ ⊥) : U = ⊤ := by
  classical
  let W : Submodule ℂ MatterCoordinateSpace :=
    U.toSubmodule.comap actualCoordinateEquiv.toLinearMap
  have hD : ∀ v ∈ W, (fun i => (eigenvalue i : ℂ) * v i) ∈ W := by
    intro v hv
    have hm : actualCoordinateEquiv v ∈ U := hv
    have hh : ⁅zeroElement diagonalData e8_matter_separating_diagonal_certificate.2.1,
        actualCoordinateEquiv v⁆ ∈ U := U.lie_mem hm
    rw [diagonal_actual_action] at hh
    exact hh
  have hstep : ∀ i, i ≠ baseLabel →
      (Pi.single (parent i) (1 : ℂ) ∈ W ↔ Pi.single i (1 : ℂ) ∈ W) := by
    intro i hi
    rcases e8_matter_action_tree_certificate i hi with
      ⟨_, hsf, hsr, hzf, hzr, hcf, hcr, haf, har⟩
    constructor
    · intro hp
      have hm : actualCoordinateEquiv (Pi.single (parent i) (1 : ℂ)) ∈ U := hp
      have hh : ⁅zeroElement (forwardData i) hzf,
          actualCoordinateEquiv (Pi.single (parent i) (1 : ℂ))⁆ ∈ U := U.lie_mem hm
      rw [sparse_scalar_action (forwardData i) hsf hzf (parent i) i
        (forwardCoefficient i) haf] at hh
      have hc : (forwardCoefficient i : ℂ) ≠ 0 := by exact_mod_cast hcf
      exact (U.toSubmodule.smul_mem_iff hc).mp hh
    · intro hp
      have hm : actualCoordinateEquiv (Pi.single i (1 : ℂ)) ∈ U := hp
      have hh : ⁅zeroElement (reverseData i) hzr,
          actualCoordinateEquiv (Pi.single i (1 : ℂ))⁆ ∈ U := U.lie_mem hm
      rw [sparse_scalar_action (reverseData i) hsr hzr i (parent i)
        (reverseCoefficient i) har] at hh
      have hc : (reverseCoefficient i : ℂ) ≠ 0 := by exact_mod_cast hcr
      exact (U.toSubmodule.smul_mem_iff hc).mp hh
  have hW : W ≠ ⊥ := by
    intro hw
    apply hU
    apply (LieSubmodule.eq_bot_iff U).mpr
    intro v hv
    have hh : actualCoordinateEquiv.symm v ∈ W := by
      change actualCoordinateEquiv (actualCoordinateEquiv.symm v) ∈ U
      simpa using hv
    rw [hw, Submodule.mem_bot] at hh
    have he := congrArg actualCoordinateEquiv hh
    simpa using he
  have heigen : Function.Injective (fun i => (eigenvalue i : ℂ)) := by
    intro i j hij
    exact e8_matter_separating_diagonal_certificate.2.2.1 (Int.cast_injective hij)
  have ht : W = ⊤ := DiagonalTreeIrreducible.eq_top_of_diagonal_and_tree W
    (fun i => (eigenvalue i : ℂ)) heigen hD baseLabel parent rank
    (fun i hi => (e8_matter_action_tree_certificate i hi).1) hstep hW
  apply top_unique
  intro v _
  have hh : actualCoordinateEquiv.symm v ∈ W := by rw [ht]; trivial
  change actualCoordinateEquiv (actualCoordinateEquiv.symm v) ∈ U at hh
  simpa using hh

/-- The full actual zero-grade Lie algebra acts irreducibly on the actual
81-dimensional complementary half. -/
theorem e8_actualMatter_isIrreducible :
    LieModule.IsIrreducible ℂ zeroSubalgebra (gradeModule 1) := by
  letI : Nontrivial (gradeModule 1) := actualCoordinateEquiv.toEquiv.symm.nontrivial
  exact LieModule.IsIrreducible.mk e8_actualMatter_submodule_eq_top

end

end CubicAnomaly.Fixed.E8MatterIrreducible
