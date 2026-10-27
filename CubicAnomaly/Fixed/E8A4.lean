import CubicAnomaly.Fixed.E8A4Data
import CubicAnomaly.Fixed.E8Grading
import CubicAnomaly.Fixed.MatrixUnitHom
import Mathlib.Algebra.Lie.Classical

/-!
# A faithful special-linear algebra inside the actual exceptional algebra

The checked sparse matrix units yield an actual homomorphism from five by
five matrices into the constructed exceptional Lie algebra. A concrete
coordinate recovery map proves that its kernel on traceless matrices is
zero. Every image lies in the actual degree-zero subalgebra.
-/

namespace CubicAnomaly.Fixed.E8A4

open Matrix
open CubicAnomaly.Fixed.E8RootPairing
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8A4Data
open RootPairing.GeckConstruction

noncomputable section

abbrev Matrix5 := Matrix (Fin 5) (Fin 5) ℂ
abbrev sl5 := LieAlgebra.SpecialLinear.sl (Fin 5) ℂ

private theorem unit_supported (i j : Fin 5) :
    ∀ p ∈ unitData i j, p.1 ∈ basisList := by
  simpa only [supported, List.all_eq_true, List.contains_iff_mem] using
    (e8_a4_unit_support_certificate i j).1

private theorem unit_grade_zero (i j : Fin 5) :
    ∀ p ∈ unitData i j, grade p.1 = 0 := by
  rintro ⟨d, c⟩ hp
  have hh := List.all_eq_true.mp (e8_a4_unit_support_certificate i j).2 (d, c) hp
  cases d with
  | inl k => rfl
  | inr v =>
      have hv : v[6] = 0 := eq_of_beq hh
      simp [grade, hv]

/-- The denominator-cleared finite witnesses normalized in the actual module. -/
def unitVector (i j : Fin 5) : DefiningSpace := (1 / 5 : ℂ) • realize (unitData i j)

/-- Actual exceptional matrices corresponding to projected elementary matrices. -/
def unitImage (i j : Fin 5) : E8Geck.lieAlgebra := adjointEquiv (unitVector i j)

theorem e8_a4_unitVector_bracket (i j k l : Fin 5) :
    candidateBracket (unitVector i j) (unitVector k l) =
      (if j = k then unitVector i l else 0) - (if l = i then unitVector k j else 0) := by
  unfold unitVector
  simp only [map_smul, LinearMap.smul_apply]
  rw [e8_candidateBracket_realize _ _ (unit_supported i j) (unit_supported k l)]
  have hc := e8_realize_eq_of_sparseEq _ _ (e8_a4_unit_bracket_certificate i j k l)
  unfold sparseBracket at hc
  rw [hc, e8_realize_scale, e8_realize_append, e8_realize_scale]
  have hz : realize ([] : Sparse) = 0 := rfl
  split_ifs <;>
    norm_num [hz, ← Int.cast_smul_eq_zsmul ℂ, smul_add, smul_smul] <;> module

theorem e8_a4_unitImage_bracket (i j k l : Fin 5) :
    ⁅unitImage i j, unitImage k l⁆ =
      (if j = k then unitImage i l else 0) - (if l = i then unitImage k j else 0) := by
  unfold unitImage
  rw [← e8_adjointEquiv_bracket, e8_a4_unitVector_bracket]
  split_ifs <;> simp

/-- An actual Lie homomorphism from all five by five matrices. -/
def gl5Hom : Matrix5 →ₗ⁅ℂ⁆ E8Geck.lieAlgebra :=
  MatrixUnitHom.lieHom unitImage e8_a4_unitImage_bracket

theorem e8_a4_gl5Hom_unit (i j : Fin 5) :
    gl5Hom (Matrix.single i j (1 : ℂ)) = unitImage i j :=
  MatrixUnitHom.matrix_unit_lieHom_single unitImage e8_a4_unitImage_bracket i j

theorem e8_a4_gl5Hom_upper_simple (p : Fin 4) :
    (gl5Hom (Matrix.single (⟨p.val, by omega⟩ : Fin 5)
      (⟨p.val + 1, by omega⟩ : Fin 5) 1) : Matrix Index Index ℂ) =
      e (simpleIndex (chain p)) := by
  rw [e8_a4_gl5Hom_unit]
  change bracketMatrixMap (unitVector _ _) = _
  rw [unitVector, map_smul, (e8_a4_simple_unit_certificate p).1,
    e8_realize_singleton, map_zsmul, e8_e_bracketMatrixMap_image]
  fin_cases p <;>
    norm_num [chain, diagramSign, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]

theorem e8_a4_gl5Hom_lower_simple (p : Fin 4) :
    (gl5Hom (Matrix.single (⟨p.val + 1, by omega⟩ : Fin 5)
      (⟨p.val, by omega⟩ : Fin 5) 1) : Matrix Index Index ℂ) =
      f (simpleIndex (chain p)) := by
  rw [e8_a4_gl5Hom_unit]
  change bracketMatrixMap (unitVector _ _) = _
  rw [unitVector, map_smul, (e8_a4_simple_unit_certificate p).2,
    e8_realize_singleton, map_zsmul, e8_f_bracketMatrixMap_image]
  fin_cases p <;>
    norm_num [chain, diagramSign, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]

/-- Linear extraction of the displayed matrix coefficients from the full
248-dimensional coordinate space. -/
def recovery : DefiningSpace →ₗ[ℂ] Matrix5 :=
  (Pi.basisFun ℂ Index).constr ℂ fun k a b =>
    (recoverCoefficient a b (dataIndex k) : ℂ)

private theorem recovery_basis (d : DataIndex) (hd : d ∈ basisList) (a b : Fin 5) :
    recovery (basisVector d) a b = (recoverCoefficient a b d : ℂ) := by
  obtain ⟨k, rfl⟩ := (e8_mem_basisList_iff d).mp hd
  rw [e8_basisVector_dataIndex, ← Pi.basisFun_apply ℂ Index k]
  simp [recovery]

theorem e8_a4_recovery_sparse (xs : Sparse)
    (hxs : ∀ p ∈ xs, p.1 ∈ basisList) (a b : Fin 5) :
    recovery (realize xs) a b = (recoverSparse xs a b : ℂ) := by
  induction xs with
  | nil => simp [realize, SparseRealization.realize, recoverSparse]
  | cons p xs ih =>
      change recovery (p.2 • basisVector p.1 + realize xs) a b =
        ((p.2 * recoverCoefficient a b p.1 + recoverSparse xs a b : ℤ) : ℂ)
      rw [map_add, map_zsmul]
      change p.2 • recovery (basisVector p.1) a b + recovery (realize xs) a b = _
      rw [recovery_basis _ (hxs p List.mem_cons_self),
        ih (fun q hq => hxs q (List.mem_cons_of_mem p hq))]
      simp [Int.cast_add, Int.cast_mul, zsmul_eq_mul]

/-- The explicit traceless projection of a five by five matrix. -/
def tracelessProjection : Matrix5 →ₗ[ℂ] Matrix5 :=
  LinearMap.id - (Matrix.traceLinearMap (Fin 5) ℂ ℂ).smulRight
    ((1 / 5 : ℂ) • (1 : Matrix5))

theorem e8_a4_tracelessProjection_apply (A : Matrix5) :
    tracelessProjection A = A - (Matrix.trace A / 5) • (1 : Matrix5) := by
  simp [tracelessProjection, div_eq_mul_inv, smul_smul]

theorem e8_a4_recovery_unitVector (i j : Fin 5) :
    recovery (unitVector i j) = tracelessProjection (Matrix.single i j 1) := by
  rw [unitVector, map_smul, e8_a4_tracelessProjection_apply]
  have ht : Matrix.trace (Matrix.single i j (1 : ℂ)) = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  ext a b
  change (1 / 5 : ℂ) * recovery (realize (unitData i j)) a b = _
  rw [e8_a4_recovery_sparse _ (unit_supported i j), e8_a4_unit_recovery_certificate]
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
theorem e8_a4_recovery_gl5Hom (A : Matrix5) :
    recovery (adjointEquiv.symm (gl5Hom A)) = tracelessProjection A := by
  let T : Matrix5 →ₗ[ℂ] Matrix5 :=
    recovery.comp (adjointEquiv.symm.toLinearEquiv.toLinearMap.comp gl5Hom.toLinearMap)
  have hT : T = tracelessProjection := by
    apply (Matrix.stdBasis ℂ (Fin 5) (Fin 5)).ext
    rintro ⟨i, j⟩
    rw [Matrix.stdBasis_eq_single]
    change recovery (adjointEquiv.symm (gl5Hom (Matrix.single i j 1))) = _
    rw [e8_a4_gl5Hom_unit]
    change recovery (adjointEquiv.symm (adjointEquiv (unitVector i j))) = _
    rw [adjointEquiv.symm_apply_apply, e8_a4_recovery_unitVector]
  exact LinearMap.congr_fun hT A

/-- The actual special-linear embedding obtained by restricting the matrix
homomorphism to trace zero. -/
def sl5Embedding : sl5 →ₗ⁅ℂ⁆ E8Geck.lieAlgebra := gl5Hom.comp sl5.incl

theorem e8_a4_recovery_sl5 (A : sl5) :
    recovery (adjointEquiv.symm (sl5Embedding A)) = A.val := by
  change recovery (adjointEquiv.symm (gl5Hom A.val)) = A.val
  rw [e8_a4_recovery_gl5Hom, e8_a4_tracelessProjection_apply]
  have ht : Matrix.trace A.val = 0 := A.property
  simp [ht]

theorem e8_a4_sl5Embedding_injective : Function.Injective sl5Embedding := by
  intro A B h
  apply Subtype.ext
  have hr := congrArg (fun x : E8Geck.lieAlgebra => recovery (adjointEquiv.symm x)) h
  simpa only [e8_a4_recovery_sl5] using hr

theorem e8_a4_unitImage_mem_zero (i j : Fin 5) : unitImage i j ∈ zeroSubalgebra := by
  refine ⟨unitVector i j, ?_, rfl⟩
  exact (gradeSpace 0).smul_mem _ (e8_realize_homogeneous _ _ (unit_grade_zero i j))

theorem e8_a4_gl5Hom_mem_zero (A : Matrix5) : gl5Hom A ∈ zeroSubalgebra := by
  change MatrixUnitHom.linearMap unitImage A ∈ zeroSubalgebra
  rw [MatrixUnitHom.matrix_unit_linearMap_apply]
  apply zeroSubalgebra.toSubmodule.sum_mem
  intro i _
  apply zeroSubalgebra.toSubmodule.sum_mem
  intro j _
  exact zeroSubalgebra.smul_mem _ (e8_a4_unitImage_mem_zero i j)

theorem e8_a4_sl5Embedding_mem_zero (A : sl5) : sl5Embedding A ∈ zeroSubalgebra :=
  e8_a4_gl5Hom_mem_zero A.val

/-- The same faithful copy lies inside the actual degree-zero Lie algebra. -/
def sl5ZeroEmbedding : sl5 →ₗ⁅ℂ⁆ zeroSubalgebra where
  __ := sl5Embedding.toLinearMap.codRestrict zeroSubalgebra.toSubmodule
    e8_a4_sl5Embedding_mem_zero
  map_lie' := by
    intro A B
    apply Subtype.ext
    exact sl5Embedding.map_lie A B

theorem e8_a4_sl5ZeroEmbedding_injective : Function.Injective sl5ZeroEmbedding := by
  intro A B h
  apply e8_a4_sl5Embedding_injective
  exact congrArg Subtype.val h

end

end CubicAnomaly.Fixed.E8A4
