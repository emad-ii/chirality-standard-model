import CubicAnomaly.Fixed.E8A2Data
import CubicAnomaly.Fixed.E8A4
import CubicAnomaly.Fixed.E8Grading
import CubicAnomaly.Fixed.MatrixUnitHom
import Mathlib.Algebra.Lie.Classical

/-!
# A faithful special-linear algebra inside the actual exceptional algebra

The checked sparse matrix units yield an actual homomorphism from three by
three matrices into the constructed exceptional Lie algebra. A concrete
coordinate recovery map proves that its kernel on traceless matrices is
zero. Every image lies in the actual degree-zero subalgebra.
-/

namespace CubicAnomaly.Fixed.E8A2

open Matrix
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8A2Data
open CubicAnomaly.Fixed.E8A4Data (sparseBracket)

noncomputable section

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev sl3 := LieAlgebra.SpecialLinear.sl (Fin 3) ℂ

private theorem unit_supported (i j : Fin 3) :
    ∀ p ∈ familyUnitData i j, p.1 ∈ basisList := by
  simpa only [supported, List.all_eq_true, List.contains_iff_mem] using
    (e8_a2_unit_support_certificate i j).1

private theorem unit_grade_zero (i j : Fin 3) :
    ∀ p ∈ familyUnitData i j, grade p.1 = 0 := by
  rintro ⟨d, c⟩ hp
  have hh := List.all_eq_true.mp (e8_a2_unit_support_certificate i j).2 (d, c) hp
  cases d with
  | inl k => rfl
  | inr v =>
      have hv : v[6] % 3 = 0 := eq_of_beq hh
      change (v[6] : ZMod 3) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero hv)

/-- The denominator-cleared finite witnesses normalized in the actual module. -/
def unitVector (i j : Fin 3) : DefiningSpace := (1 / 3 : ℂ) • realize (familyUnitData i j)

/-- Actual exceptional matrices corresponding to projected elementary matrices. -/
def unitImage (i j : Fin 3) : E8Geck.lieAlgebra := adjointEquiv (unitVector i j)

theorem e8_a2_unitVector_bracket (i j k l : Fin 3) :
    candidateBracket (unitVector i j) (unitVector k l) =
      (if j = k then unitVector i l else 0) - (if l = i then unitVector k j else 0) := by
  unfold unitVector
  simp only [map_smul, LinearMap.smul_apply]
  rw [e8_candidateBracket_realize _ _ (unit_supported i j) (unit_supported k l)]
  have hc := e8_realize_eq_of_sparseEq _ _ (e8_a2_unit_bracket_certificate i j k l)
  unfold sparseBracket at hc
  rw [hc, e8_realize_scale, e8_realize_append, e8_realize_scale]
  have hz : realize ([] : Sparse) = 0 := rfl
  split_ifs <;>
    norm_num [hz, ← Int.cast_smul_eq_zsmul ℂ, smul_add, smul_smul] <;> module

theorem e8_a2_unitImage_bracket (i j k l : Fin 3) :
    ⁅unitImage i j, unitImage k l⁆ =
      (if j = k then unitImage i l else 0) - (if l = i then unitImage k j else 0) := by
  unfold unitImage
  rw [← e8_adjointEquiv_bracket, e8_a2_unitVector_bracket]
  split_ifs <;> simp

/-- An actual Lie homomorphism from all three by three matrices. -/
def gl3Hom : Matrix3 →ₗ⁅ℂ⁆ E8Geck.lieAlgebra :=
  MatrixUnitHom.lieHom unitImage e8_a2_unitImage_bracket

theorem e8_a2_gl3Hom_unit (i j : Fin 3) :
    gl3Hom (Matrix.single i j (1 : ℂ)) = unitImage i j :=
  MatrixUnitHom.matrix_unit_lieHom_single unitImage e8_a2_unitImage_bracket i j

/-- Linear extraction of the displayed matrix coefficients from the full
248-dimensional coordinate space. -/
def recovery : DefiningSpace →ₗ[ℂ] Matrix3 :=
  (1 / 2 : ℂ) • ((Pi.basisFun ℂ Index).constr ℂ fun k a b =>
    (familyRecoverCoefficient a b (dataIndex k) : ℂ))

private theorem recovery_basis (d : DataIndex) (hd : d ∈ basisList) (a b : Fin 3) :
    recovery (basisVector d) a b = (1 / 2 : ℂ) * (familyRecoverCoefficient a b d : ℂ) := by
  obtain ⟨k, rfl⟩ := (e8_mem_basisList_iff d).mp hd
  rw [e8_basisVector_dataIndex, ← Pi.basisFun_apply ℂ Index k]
  change (1 / 2 : ℂ) *
    (((Pi.basisFun ℂ Index).constr ℂ fun k a b =>
      (familyRecoverCoefficient a b (dataIndex k) : ℂ))
      ((Pi.basisFun ℂ Index) k)) a b = _
  rw [Module.Basis.constr_basis]

theorem e8_a2_recovery_sparse (xs : Sparse)
    (hxs : ∀ p ∈ xs, p.1 ∈ basisList) (a b : Fin 3) :
    recovery (realize xs) a b = (1 / 2 : ℂ) * (familyRecoverSparse xs a b : ℂ) := by
  induction xs with
  | nil => simp [realize, SparseRealization.realize, familyRecoverSparse]
  | cons p xs ih =>
      change recovery (p.2 • basisVector p.1 + realize xs) a b =
        (1 / 2 : ℂ) * ((p.2 * familyRecoverCoefficient a b p.1 + familyRecoverSparse xs a b : ℤ) : ℂ)
      rw [map_add, map_zsmul]
      change p.2 • recovery (basisVector p.1) a b + recovery (realize xs) a b = _
      rw [recovery_basis _ (hxs p List.mem_cons_self),
        ih (fun q hq => hxs q (List.mem_cons_of_mem p hq))]
      simp only [Int.cast_add, Int.cast_mul, zsmul_eq_mul]
      ring

/-- The explicit traceless projection of a three by three matrix. -/
def tracelessProjection : Matrix3 →ₗ[ℂ] Matrix3 :=
  LinearMap.id - (Matrix.traceLinearMap (Fin 3) ℂ ℂ).smulRight
    ((1 / 3 : ℂ) • (1 : Matrix3))

theorem e8_a2_tracelessProjection_apply (A : Matrix3) :
    tracelessProjection A = A - (Matrix.trace A / 3) • (1 : Matrix3) := by
  simp [tracelessProjection, div_eq_mul_inv, smul_smul]

theorem e8_a2_recovery_unitVector (i j : Fin 3) :
    recovery (unitVector i j) = tracelessProjection (Matrix.single i j 1) := by
  rw [unitVector, map_smul, e8_a2_tracelessProjection_apply]
  have ht : Matrix.trace (Matrix.single i j (1 : ℂ)) = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  ext a b
  change (1 / 3 : ℂ) * recovery (realize (familyUnitData i j)) a b = _
  rw [e8_a2_recovery_sparse _ (unit_supported i j), e8_a2_unit_recovery_certificate]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply,
    Matrix.one_apply, ht, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_ite,
    Int.cast_one, Int.cast_zero]
  simp only [show (i = a ∧ j = b) ↔ (a = i ∧ b = j) from
    ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩]
  have hdiag : (if i = j ∧ a = b then (1 : ℂ) else 0) =
      (if i = j then (1 : ℂ) else 0) * (if a = b then (1 : ℂ) else 0) := by
    by_cases hij : i = j <;> by_cases hab : a = b <;> simp [hij, hab]
  rw [hdiag]
  ring

/-- Recovery of the actual matrix-algebra image is exactly the traceless
projection, proved on matrix units and then extended linearly. -/
theorem e8_a2_recovery_gl3Hom (A : Matrix3) :
    recovery (adjointEquiv.symm (gl3Hom A)) = tracelessProjection A := by
  let T : Matrix3 →ₗ[ℂ] Matrix3 :=
    recovery.comp (adjointEquiv.symm.toLinearEquiv.toLinearMap.comp gl3Hom.toLinearMap)
  have hT : T = tracelessProjection := by
    apply (Matrix.stdBasis ℂ (Fin 3) (Fin 3)).ext
    rintro ⟨i, j⟩
    rw [Matrix.stdBasis_eq_single]
    change recovery (adjointEquiv.symm (gl3Hom (Matrix.single i j 1))) = _
    rw [e8_a2_gl3Hom_unit]
    change recovery (adjointEquiv.symm (adjointEquiv (unitVector i j))) = _
    rw [adjointEquiv.symm_apply_apply, e8_a2_recovery_unitVector]
  exact LinearMap.congr_fun hT A

/-- The actual special-linear embedding obtained by restricting the matrix
homomorphism to trace zero. -/
def sl3Embedding : sl3 →ₗ⁅ℂ⁆ E8Geck.lieAlgebra := gl3Hom.comp sl3.incl

theorem e8_a2_recovery_sl3 (A : sl3) :
    recovery (adjointEquiv.symm (sl3Embedding A)) = A.val := by
  change recovery (adjointEquiv.symm (gl3Hom A.val)) = A.val
  rw [e8_a2_recovery_gl3Hom, e8_a2_tracelessProjection_apply]
  have ht : Matrix.trace A.val = 0 := A.property
  simp [ht]

theorem e8_a2_sl3Embedding_injective : Function.Injective sl3Embedding := by
  intro A B h
  apply Subtype.ext
  have hr := congrArg (fun x : E8Geck.lieAlgebra => recovery (adjointEquiv.symm x)) h
  simpa only [e8_a2_recovery_sl3] using hr

theorem e8_a2_unitImage_mem_zero (i j : Fin 3) : unitImage i j ∈ zeroSubalgebra := by
  refine ⟨unitVector i j, ?_, rfl⟩
  exact (gradeSpace 0).smul_mem _ (e8_realize_homogeneous _ _ (unit_grade_zero i j))

theorem e8_a2_gl3Hom_mem_zero (A : Matrix3) : gl3Hom A ∈ zeroSubalgebra := by
  change MatrixUnitHom.linearMap unitImage A ∈ zeroSubalgebra
  rw [MatrixUnitHom.matrix_unit_linearMap_apply]
  apply zeroSubalgebra.toSubmodule.sum_mem
  intro i _
  apply zeroSubalgebra.toSubmodule.sum_mem
  intro j _
  exact zeroSubalgebra.smul_mem _ (e8_a2_unitImage_mem_zero i j)

theorem e8_a2_sl3Embedding_mem_zero (A : sl3) : sl3Embedding A ∈ zeroSubalgebra :=
  e8_a2_gl3Hom_mem_zero A.val

/-- The same faithful copy lies inside the actual degree-zero Lie algebra. -/
def sl3ZeroEmbedding : sl3 →ₗ⁅ℂ⁆ zeroSubalgebra where
  __ := sl3Embedding.toLinearMap.codRestrict zeroSubalgebra.toSubmodule
    e8_a2_sl3Embedding_mem_zero
  map_lie' := by
    intro A B
    apply Subtype.ext
    exact sl3Embedding.map_lie A B

theorem e8_a2_sl3ZeroEmbedding_injective : Function.Injective sl3ZeroEmbedding := by
  intro A B h
  apply e8_a2_sl3Embedding_injective
  exact congrArg Subtype.val h

end

end CubicAnomaly.Fixed.E8A2
