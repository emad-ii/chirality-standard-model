import CubicAnomaly.Fixed.E8Matter
import CubicAnomaly.Fixed.E8Compact
import CubicAnomaly.Fixed.PolynomialComplexStructure

/-!
# The actual family action determines the complex structure

The embedded family element `i * diag(1,1,-2)` is skew-adjoint in the
constructed compact metric. On the actual exceptional matter half its
action `T` satisfies `i = (3/2) T + (1/2) T^3`. Thus a real intertwiner
for the compact isotropy cannot introduce an antilinear component.
-/

namespace CubicAnomaly.Fixed.E8FamilyComplexStructure

open Matrix
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8A2Data
open CubicAnomaly.Fixed.E8A2
open CubicAnomaly.Fixed.E8Compact
open CubicAnomaly.Fixed.E8MatterMatching
open CubicAnomaly.Fixed.E8Matter
open CubicAnomaly.Fixed.MatterSpectrum
open CubicAnomaly.Fixed.MatterFamilyCoordinates
open CubicAnomaly.Fixed.FamilyAnomaly
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 800000

/-- A specified family element with purely imaginary eigenvalues. -/
def imaginaryFamilyWitness : FamilyLie := Complex.I • familyWitness

private def coordinateOperator :
    E8Geck.DefiningSpace →ₗ[ℂ] Module.End ℂ E8Compact.DefiningSpace :=
  operatorEquiv.toLinearMap.comp bracketMatrixMap

private theorem cartan_operator_selfAdjoint (i : Fin 8) :
    (coordinateOperator (basisVector (.inl i))).adjoint =
      coordinateOperator (basisVector (.inl i)) := by
  change (operatorEquiv (bracketMatrixMap (basisVector (.inl i)))).adjoint =
    operatorEquiv (bracketMatrixMap (basisVector (.inl i)))
  rw [e8_h_bracketMatrixMap_image, map_zsmul, map_zsmul]
  have hh : (operatorEquiv (RootPairing.GeckConstruction.h
      (E8RootPairing.simpleIndex i))).adjoint =
      operatorEquiv (RootPairing.GeckConstruction.h (E8RootPairing.simpleIndex i)) :=
    MatrixCompactForm.metric_matrix_adjoint _ _ _ _
      (E8Adjoints.geck_cartan_weighted_adjoint _)
  rw [hh]

private theorem cartan_sparse_operator_selfAdjoint (xs : Sparse)
    (hxs : ∀ p ∈ xs, ∃ k : Fin 8, p.1 = .inl k) :
    (coordinateOperator (realize xs)).adjoint = coordinateOperator (realize xs) := by
  induction xs with
  | nil => simp [realize, SparseRealization.realize]
  | cons p xs ih =>
      change (coordinateOperator (p.2 • basisVector p.1 + realize xs)).adjoint =
        coordinateOperator (p.2 • basisVector p.1 + realize xs)
      rw [map_add, map_zsmul, map_add, map_zsmul]
      obtain ⟨k, hk⟩ := hxs p List.mem_cons_self
      rw [hk, cartan_operator_selfAdjoint,
        ih (fun q hq => hxs q (List.mem_cons_of_mem p hq))]

private theorem diagonal_unit_selfAdjoint (i : Fin 3) :
    (operatorEquiv (unitImage i i).val).adjoint = operatorEquiv (unitImage i i).val := by
  have hx : ∀ p ∈ familyUnitData i i, ∃ k : Fin 8, p.1 = .inl k := by
    unfold familyUnitData
    rw [if_pos rfl]
    intro p hp
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
    exact ⟨k, rfl⟩
  change (coordinateOperator ((1 / 3 : ℂ) • realize (familyUnitData i i))).adjoint =
    coordinateOperator ((1 / 3 : ℂ) • realize (familyUnitData i i))
  rw [map_smul, map_smulₛₗ, cartan_sparse_operator_selfAdjoint _ hx]
  norm_num [map_ofNat]

private theorem family_witness_matrix_units :
    familyWitness.val = Matrix.single 0 0 1 + Matrix.single 1 1 1 -
      (2 : ℂ) • Matrix.single 2 2 1 := by
  change Matrix.diagonal ![1, 1, -2] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.single_apply, Matrix.diagonal, Fin.ext_iff]

/-- The actual embedded family witness is Hermitian for the constructed metric. -/
theorem e8_family_witness_selfAdjoint :
    (operatorEquiv (sl3Embedding familyWitness).val).adjoint =
      operatorEquiv (sl3Embedding familyWitness).val := by
  have he : sl3Embedding familyWitness = unitImage 0 0 + unitImage 1 1 -
      (2 : ℂ) • unitImage 2 2 := by
    change gl3Hom familyWitness.val = _
    rw [family_witness_matrix_units, map_sub, map_add, map_smul,
      e8_a2_gl3Hom_unit, e8_a2_gl3Hom_unit, e8_a2_gl3Hom_unit]
  rw [he]
  change (operatorEquiv ((unitImage 0 0).val + (unitImage 1 1).val -
      (2 : ℂ) • (unitImage 2 2).val)).adjoint =
    operatorEquiv ((unitImage 0 0).val + (unitImage 1 1).val -
      (2 : ℂ) • (unitImage 2 2).val)
  simp only [map_sub, map_add, map_smul, map_smulₛₗ,
    diagonal_unit_selfAdjoint, map_ofNat]

/-- Multiplying that actual Hermitian family generator by `i` gives an
actual compact skew-adjoint generator. -/
theorem e8_imaginary_family_witness_skewAdjoint :
    (operatorEquiv (sl3Embedding imaginaryFamilyWitness).val).adjoint =
      -operatorEquiv (sl3Embedding imaginaryFamilyWitness).val := by
  unfold imaginaryFamilyWitness
  rw [map_smul]
  change (operatorEquiv (Complex.I • (sl3Embedding familyWitness).val)).adjoint = _
  rw [map_smul, map_smulₛₗ, e8_family_witness_selfAdjoint]
  simp

/-- The family element acts on the actual homogeneous adjoint space. -/
def familyOperator (F : FamilyLie) : Module.End ℂ ActualMatter :=
  LieModule.toEnd ℂ zeroSubalgebra ActualMatter (sl3ZeroEmbedding F)

theorem e8_familyOperator_matching (F : FamilyLie) (v : Matter81) :
    familyOperator F (actualMatterEquiv v) =
      actualMatterEquiv (familyCopyAction F.val v) := by
  apply Subtype.ext
  exact e8_matter_family_action F v

private theorem imaginary_family_copy_action (v : Matter81) (i : Fin 3) :
    familyCopyAction imaginaryFamilyWitness.val v i =
      (Complex.I * ![1, 1, -2] i) • v i := by
  change familyCopyAction (Complex.I • Matrix.diagonal ![1, 1, -2]) v i = _
  simp [familyCopyAction, Matrix.diagonal_apply, mul_ite, ite_smul]

private theorem family_copy_polynomial (v : Matter81) :
    Complex.I • v =
      (3 / 2 : ℝ) • familyCopyAction imaginaryFamilyWitness.val v +
      (1 / 2 : ℝ) • familyCopyAction imaginaryFamilyWitness.val
        (familyCopyAction imaginaryFamilyWitness.val
          (familyCopyAction imaginaryFamilyWitness.val v)) := by
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, imaginary_family_copy_action]
  have hreal (r : ℝ) (w : Matter27) : (r : ℂ) • w = r • w :=
    IsScalarTower.algebraMap_smul ℂ r w
  rw [← hreal (3 / 2), ← hreal (1 / 2)]
  have hc : Complex.I = ((3 / 2 : ℝ) : ℂ) * (Complex.I * ![1, 1, -2] i) +
      ((1 / 2 : ℝ) : ℂ) * (Complex.I * ![1, 1, -2] i *
        (Complex.I * ![1, 1, -2] i * (Complex.I * ![1, 1, -2] i))) := by
    fin_cases i <;> norm_num <;> ring_nf <;>
      norm_num [pow_succ, Complex.I_mul_I] <;> ring
  simpa only [smul_smul, ← add_smul] using congrArg (fun c : ℂ => c • v i) hc

/-- On the actual exceptional half, the complex structure is a cubic
real polynomial in one actual compact family action. -/
theorem e8_family_operator_complex_structure (v : ActualMatter) :
    Complex.I • v =
      (3 / 2 : ℝ) • familyOperator imaginaryFamilyWitness v +
      (1 / 2 : ℝ) • familyOperator imaginaryFamilyWitness
        (familyOperator imaginaryFamilyWitness
          (familyOperator imaginaryFamilyWitness v)) := by
  obtain ⟨w, rfl⟩ := actualMatterEquiv.surjective v
  have h := congrArg actualMatterEquiv (family_copy_polynomial w)
  have hr (r : ℝ) (u : Matter81) :
      actualMatterEquiv (r • u) = r • actualMatterEquiv u :=
    (actualMatterEquiv.restrictScalars ℝ).map_smul r u
  simpa only [map_add, map_smul, hr,
    ← e8_familyOperator_matching] using h

end

end CubicAnomaly.Fixed.E8FamilyComplexStructure
