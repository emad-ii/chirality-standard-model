import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis

/-!
# Recognizing a matrix Lie homomorphism from matrix-unit images

Checking the elementary commutator rule is sufficient to construct an actual
Lie homomorphism on every matrix. This lets finite sparse witnesses be used
without assuming a presentation theorem for the generated Lie algebra.
-/

namespace CubicAnomaly.Fixed.MatrixUnitHom

open Matrix

variable {R n L : Type*} [CommRing R] [Fintype n] [DecidableEq n]
  [LieRing L] [LieAlgebra R L]

noncomputable section

/-- Extend the chosen images of matrix units by linearity. -/
def linearMap (v : n → n → L) : Matrix n n R →ₗ[R] L :=
  Matrix.liftLinear R fun i j => (LinearMap.id : R →ₗ[R] R).smulRight (v i j)

theorem matrix_unit_linearMap_single (v : n → n → L) (i j : n) (a : R) :
    linearMap v (Matrix.single i j a) = a • v i j := by
  simp [linearMap]

theorem matrix_unit_linearMap_apply (v : n → n → L) (A : Matrix n n R) :
    linearMap v A = ∑ i, ∑ j, A i j • v i j := by
  simp [linearMap, Matrix.liftLinear_apply]

private theorem single_lie_single (i j k l : n) :
    ⁅Matrix.single i j (1 : R), Matrix.single k l (1 : R)⁆ =
      (if j = k then Matrix.single i l 1 else 0) -
        (if l = i then Matrix.single k j 1 else 0) := by
  rw [Ring.lie_def]
  congr 1
  · by_cases h : j = k
    · subst k
      simp
    · simp [h, Matrix.single_mul_single_of_ne]
  · by_cases h : l = i
    · subst i
      simp
    · simp [h, Matrix.single_mul_single_of_ne]

/-- The usual elementary commutator relations imply the full Lie identity. -/
theorem matrix_unit_linearMap_lie (v : n → n → L)
    (hv : ∀ i j k l, ⁅v i j, v k l⁆ =
      (if j = k then v i l else 0) - (if l = i then v k j else 0))
    (A B : Matrix n n R) : linearMap v ⁅A, B⁆ = ⁅linearMap v A, linearMap v B⁆ := by
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A A' hA hA' => simp [add_lie, hA, hA']
  | h_std_basis i j a =>
    induction B using Matrix.induction_on' with
    | h_zero => simp
    | h_add B B' hB hB' => simp [lie_add, hB, hB']
    | h_std_basis k l b =>
      have ha : Matrix.single i j a = a • Matrix.single i j (1 : R) := by simp
      have hb : Matrix.single k l b = b • Matrix.single k l (1 : R) := by simp
      rw [ha, hb, smul_lie, lie_smul, map_smul, map_smul,
        map_smul, map_smul, smul_lie, lie_smul, single_lie_single,
        map_sub, matrix_unit_linearMap_single, matrix_unit_linearMap_single,
        one_smul, one_smul, hv]
      congr 2
      split_ifs <;> simp [matrix_unit_linearMap_single]

/-- The actual matrix Lie homomorphism specified by the checked unit images. -/
def lieHom (v : n → n → L)
    (hv : ∀ i j k l, ⁅v i j, v k l⁆ =
      (if j = k then v i l else 0) - (if l = i then v k j else 0)) :
    Matrix n n R →ₗ⁅R⁆ L where
  __ := linearMap v
  map_lie' {A B} := matrix_unit_linearMap_lie v hv A B

theorem matrix_unit_lieHom_single (v : n → n → L)
    (hv : ∀ i j k l, ⁅v i j, v k l⁆ =
      (if j = k then v i l else 0) - (if l = i then v k j else 0))
    (i j : n) : lieHom v hv (Matrix.single i j (1 : R)) = v i j := by
  simpa [lieHom] using matrix_unit_linearMap_single v i j (1 : R)

end

end CubicAnomaly.Fixed.MatrixUnitHom
