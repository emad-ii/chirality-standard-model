import CubicAnomaly.Fixed.MatterLieAlgebra
import CubicAnomaly.Fixed.FamilyAnomaly
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Local anomalies of the constructed Standard Model matter modules

The actual block action on the constructed family is used to compute its
linear and cubic traces. The calculation applies to arbitrary traceless
colour and weak matrices and every hypercharge generator, not merely a
diagonal charge list. Polarization recovers all mixed cubic insertions.
-/

namespace CubicAnomaly.Fixed.MatterAnomaly

open Matrix Module
open scoped Kronecker
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Fixed.TensorAnomaly
open CubicAnomaly.Fixed.MatterBranching
open CubicAnomaly.Fixed.MatterDual
open CubicAnomaly.Fixed.MatterSpectrum
open CubicAnomaly.Fixed.MatterLieAlgebra

noncomputable section

private theorem trace_cube_scalar_shift {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (q : ℂ) :
    trace ((A + q • 1) ^ 3) = trace (A ^ 3) +
      3 * q * trace (A ^ 2) + 3 * q ^ 2 * trace A + (Fintype.card n : ℂ) * q ^ 3 := by
  simp only [pow_succ, pow_zero, mul_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.smul_mul, Matrix.mul_smul, one_mul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  ring

private theorem trace_cube_tensor_action {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    trace ((tensorAction A B) ^ 3) =
      (Fintype.card n : ℂ) * trace (A ^ 3) +
        (Fintype.card m : ℂ) * trace (B ^ 3) +
        3 * trace (A ^ 2) * trace B + 3 * trace A * trace (B ^ 2) := by
  simp only [pow_succ, pow_zero, mul_one, tensorAction, Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, one_mul, Matrix.trace_add, Matrix.trace_kronecker,
    Matrix.trace_one]
  ring

private theorem trace_square_tensor_action {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    trace ((tensorAction A B) ^ 2) =
      (Fintype.card n : ℂ) * trace (A ^ 2) +
        (Fintype.card m : ℂ) * trace (B ^ 2) + 2 * trace A * trace B := by
  simp only [pow_two, tensorAction, Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, one_mul, mul_one, Matrix.trace_add,
    Matrix.trace_kronecker, Matrix.trace_one]
  ring

private theorem trace_cube_neg_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (q : ℂ) :
    trace ((-Aᵀ + q • 1) ^ 3) = -trace (A ^ 3) +
      3 * q * trace (A ^ 2) - 3 * q ^ 2 * trace A + (Fintype.card n : ℂ) * q ^ 3 := by
  rw [trace_cube_scalar_shift]
  simp only [pow_succ, pow_zero, Matrix.one_mul,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← Matrix.transpose_mul,
    Matrix.trace_neg, Matrix.trace_transpose, Matrix.mul_assoc]
  ring

/-- Every traceless `2 × 2` matrix has zero cubic trace. -/
theorem weak_traceless_cube_trace (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : trace B = 0) : trace (B ^ 3) = 0 := by
  have hdiag : B 1 1 = -B 0 0 := by
    have h : B 0 0 + B 1 1 = 0 := by
      simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_succ] using hB
    linear_combination h
  simp [pow_succ, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_succ, hdiag]
  ring

private def rectangularAction (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) :
    Module.End ℂ (Matrix (Fin 3) (Fin 2) ℂ) where
  toFun X := A * X + X * Bᵀ + q • X
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, smul_add]; abel
  map_smul' c X := by simp [smul_add, smul_smul, mul_comm]

private def rectangularCoordinates :
    Matrix (Fin 3) (Fin 2) ℂ ≃ₗ[ℂ] ((Fin 2 × Fin 3) → ℂ) where
  toFun := Matrix.vec
  invFun f i j := f (j, i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rectangular_operator_coordinates
    (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) :
    rectangularCoordinates.conj (rectangularAction A B q) =
      (tensorAction B A + q • 1).toLin' := by
  apply LinearMap.ext
  intro v
  let X := rectangularCoordinates.symm v
  have hX : Matrix.vec X = v := rectangularCoordinates.apply_symm_apply v
  have hleft := Matrix.kronecker_mulVec_vec A X (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have hright := Matrix.kronecker_mulVec_vec (1 : Matrix (Fin 3) (Fin 3) ℂ) X B
  simp only [transpose_one, Matrix.mul_one, Matrix.one_mul] at hleft hright
  change Matrix.vec (A * X + X * Bᵀ + q • X) =
    (tensorAction B A + q • 1) *ᵥ v
  rw [← hX]
  simp only [tensorAction, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hleft, hright, Matrix.vec_add, Matrix.vec_smul]
  abel

private theorem trace_cube_conjugate {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (e : M ≃ₗ[ℂ] N) (f : Module.End ℂ M) :
    LinearMap.trace ℂ N ((e.conj f) ^ 3) = LinearMap.trace ℂ M (f ^ 3) := by
  have hp : (e.conj f) ^ 3 = e.conj (f ^ 3) := (map_pow e.conjRingEquiv f 3).symm
  rw [hp, LinearMap.trace_conj']

private theorem trace_cube_prod {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    (f : Module.End ℂ M) (g : Module.End ℂ N) :
    LinearMap.trace ℂ (M × N) ((f.prodMap g) ^ 3) =
      LinearMap.trace ℂ M (f ^ 3) + LinearMap.trace ℂ N (g ^ 3) := by
  rw [show (f.prodMap g) ^ 3 = (f ^ 3).prodMap (g ^ 3) by rfl,
    LinearMap.trace_prodMap']

private theorem rectangular_action_cube_trace
    (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : trace A = 0) (hB : trace B = 0) :
    LinearMap.trace ℂ _ ((rectangularAction A B q) ^ 3) =
      2 * trace (A ^ 3) + 3 * trace (B ^ 3) +
        6 * q * trace (A ^ 2) + 9 * q * trace (B ^ 2) + 6 * q ^ 3 := by
  rw [← trace_cube_conjugate rectangularCoordinates, rectangular_operator_coordinates,
    ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq, trace_cube_scalar_shift,
    trace_cube_tensor_action, trace_square_tensor_action, tensor_action_trace]
  simp only [hA, hB, Fintype.card_fin, Fintype.card_prod, Nat.cast_ofNat,
    Nat.cast_mul, mul_zero, zero_mul, add_zero]
  ring

private def familyBlockOperator (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) :
    Module.End ℂ (((Fin 3 → ℂ) × (Matrix (Fin 3) (Fin 2) ℂ × ℂ)) ×
      ((Fin 3 → ℂ) × (Fin 2 → ℂ))) :=
  ((-Aᵀ + (-4 * q) • 1).toLin'.prodMap
    ((rectangularAction A B q).prodMap ((6 * q) • 1))).prodMap
      ((-Aᵀ + (2 * q) • 1).toLin'.prodMap (B + (-3 * q) • 1).toLin')

private theorem family_operator_coordinates
    (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : trace A = 0) (hB : trace B = 0) :
    familyCoordinates.conj
      (LieModule.toEnd ℂ MatrixFive Family (standardModelGenerator A B q)) =
      familyBlockOperator A B q := by
  apply LinearMap.ext
  intro v
  change familyCoordinates ⁅standardModelGenerator A B q, familyCoordinates.symm v⁆ = _
  rw [family_standard_model_action A B q hA hB, familyCoordinates.apply_symm_apply]
  simp only [familyBlockOperator, LinearMap.prodMap_apply, Matrix.toLin'_apply,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, rectangularAction,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Module.End.one_apply,
    smul_eq_mul]

private theorem scalar_cube_trace (a : ℂ) :
    LinearMap.trace ℂ ℂ ((a • (1 : Module.End ℂ ℂ)) ^ 3) = a ^ 3 := by
  have hp : (a • (1 : Module.End ℂ ℂ)) ^ 3 = (a ^ 3) • 1 := by
    apply LinearMap.ext
    intro x
    simp [pow_succ, smul_eq_mul]
    ring
  rw [hp, map_smul, LinearMap.trace_one]
  simp

/-- The actual fifteen-dimensional Standard Model family has vanishing
cubic trace for every colour, weak and hypercharge insertion. -/
theorem family_standard_model_cube_trace
    (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : trace A = 0) (hB : trace B = 0) :
    LinearMap.trace ℂ Family
      ((LieModule.toEnd ℂ MatrixFive Family (standardModelGenerator A B q)) ^ 3) = 0 := by
  rw [← trace_cube_conjugate familyCoordinates, family_operator_coordinates A B q hA hB]
  simp only [familyBlockOperator, trace_cube_prod]
  rw [rectangular_action_cube_trace A B q hA hB, scalar_cube_trace]
  simp only [← Matrix.toLin'_pow, Matrix.trace_toLin'_eq]
  rw [trace_cube_neg_transpose, trace_cube_neg_transpose, trace_cube_scalar_shift,
    weak_traceless_cube_trace B hB]
  simp only [hA, hB, Fintype.card_fin, Nat.cast_ofNat, mul_zero, add_zero, zero_add]
  ring

private theorem rectangular_action_trace
    (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) :
    LinearMap.trace ℂ _ (rectangularAction A B q) =
      2 * trace A + 3 * trace B + 6 * q := by
  rw [← LinearMap.trace_conj' _ rectangularCoordinates, rectangular_operator_coordinates,
    Matrix.trace_toLin'_eq, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    tensor_action_trace]
  simp only [Fintype.card_fin, Fintype.card_prod, Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul]
  ring

/-- The same actual family has zero linear trace, the coefficient used
for the mixed gauge-gravitational local anomaly. -/
theorem family_standard_model_linear_trace
    (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : trace A = 0) (hB : trace B = 0) :
    LinearMap.trace ℂ Family
      (LieModule.toEnd ℂ MatrixFive Family (standardModelGenerator A B q)) = 0 := by
  rw [← LinearMap.trace_conj' _ familyCoordinates, family_operator_coordinates A B q hA hB]
  simp only [familyBlockOperator, LinearMap.trace_prodMap', Matrix.trace_toLin'_eq,
    rectangular_action_trace, map_smul, LinearMap.trace_one, Module.finrank_self,
    Matrix.trace_add, Matrix.trace_neg, Matrix.trace_transpose, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, Nat.cast_one, smul_eq_mul,
    mul_one, hA, hB]
  ring


private theorem dual_operator_coordinates (A : MatrixFive) :
    (dualCoordinates FiveIndex).conj (LieModule.toEnd ℂ MatrixFive AntiFive A) =
      (-Aᵀ).toLin' := by
  apply LinearMap.ext
  intro v
  change dualCoordinates FiveIndex ⁅A, (dualCoordinates FiveIndex).symm v⁆ = _
  rw [dual_matrix_action, (dualCoordinates FiveIndex).apply_symm_apply]
  rfl

private theorem vectorlike_cube_trace (A : MatrixFive) :
    LinearMap.trace ℂ VectorlikePair
      ((LieModule.toEnd ℂ MatrixFive VectorlikePair A) ^ 3) = 0 := by
  change LinearMap.trace ℂ (Five × AntiFive)
    ((A.toLin'.prodMap (LieModule.toEnd ℂ MatrixFive AntiFive A)) ^ 3) = 0
  rw [trace_cube_prod, ← trace_cube_conjugate (dualCoordinates FiveIndex),
    dual_operator_coordinates]
  simp only [← Matrix.toLin'_pow, Matrix.trace_toLin'_eq]
  have h := trace_cube_neg_transpose A 0
  simp only [zero_smul, add_zero, mul_zero, zero_mul, zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), sub_zero] at h
  rw [h]
  ring

private theorem vectorlike_linear_trace (A : MatrixFive) :
    LinearMap.trace ℂ VectorlikePair
      (LieModule.toEnd ℂ MatrixFive VectorlikePair A) = 0 := by
  change LinearMap.trace ℂ (Five × AntiFive)
    (A.toLin'.prodMap (LieModule.toEnd ℂ MatrixFive AntiFive A)) = 0
  rw [LinearMap.trace_prodMap', ← LinearMap.trace_conj' _ (dualCoordinates FiveIndex),
    dual_operator_coordinates]
  simp only [Matrix.trace_toLin'_eq, Matrix.trace_neg, Matrix.trace_transpose]
  ring

private theorem singlet_operator_zero (A : MatrixFive) :
    LieModule.toEnd ℂ MatrixFive TwoSinglets A = 0 := by
  apply LinearMap.ext
  intro v
  rfl

private theorem matter27_parameter_cube_trace
    (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : trace A = 0) (hB : trace B = 0) :
    LinearMap.trace ℂ Matter27
      ((LieModule.toEnd ℂ MatrixFive Matter27 (standardModelGenerator A B q)) ^ 3) = 0 := by
  let G := standardModelGenerator A B q
  change LinearMap.trace ℂ Matter27
    (((LieModule.toEnd ℂ MatrixFive Family G).prodMap
      ((LieModule.toEnd ℂ MatrixFive VectorlikePair G).prodMap
        (LieModule.toEnd ℂ MatrixFive TwoSinglets G))) ^ 3) = 0
  rw [trace_cube_prod, trace_cube_prod, family_standard_model_cube_trace A B q hA hB,
    vectorlike_cube_trace, singlet_operator_zero]
  simp

private theorem matter27_parameter_linear_trace
    (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : trace A = 0) (hB : trace B = 0) :
    LinearMap.trace ℂ Matter27
      (LieModule.toEnd ℂ MatrixFive Matter27 (standardModelGenerator A B q)) = 0 := by
  let G := standardModelGenerator A B q
  change LinearMap.trace ℂ Matter27
    ((LieModule.toEnd ℂ MatrixFive Family G).prodMap
      ((LieModule.toEnd ℂ MatrixFive VectorlikePair G).prodMap
        (LieModule.toEnd ℂ MatrixFive TwoSinglets G))) = 0
  rw [LinearMap.trace_prodMap', LinearMap.trace_prodMap',
    family_standard_model_linear_trace A B q hA hB,
    vectorlike_linear_trace, singlet_operator_zero]
  simp

/-- Every generator of the actual Standard Model Lie subalgebra has
zero linear trace on the complete constructed twenty-seven. -/
theorem matter27_standard_model_linear_trace (x : StandardModelAlgebra) :
    LinearMap.trace ℂ Matter27 (LieModule.toEnd ℂ StandardModelAlgebra Matter27 x) = 0 := by
  obtain ⟨A, B, q, hA, hB, hG⟩ := standard_model_element_parameters x
  change LinearMap.trace ℂ Matter27 (LieModule.toEnd ℂ MatrixFive Matter27 x.val) = 0
  rw [← hG]
  exact matter27_parameter_linear_trace A B q hA hB

/-- The actual Standard Model Lie subalgebra has zero cubic trace on
the complete constructed twenty-seven, including all extra matter. -/
theorem matter27_standard_model_cube_trace (x : StandardModelAlgebra) :
    LinearMap.trace ℂ Matter27
      ((LieModule.toEnd ℂ StandardModelAlgebra Matter27 x) ^ 3) = 0 := by
  obtain ⟨A, B, q, hA, hB, hG⟩ := standard_model_element_parameters x
  change LinearMap.trace ℂ Matter27 ((LieModule.toEnd ℂ MatrixFive Matter27 x.val) ^ 3) = 0
  rw [← hG]
  exact matter27_parameter_cube_trace A B q hA hB

/-- Actual twenty-seven-dimensional coordinates, obtained from its proved
dimension rather than a supplied branching or representation certificate. -/
def matter27Coordinates : Matter27 ≃ₗ[ℂ] (Fin 27 → ℂ) :=
  (Module.finBasisOfFinrankEq ℂ Matter27 matter27_finrank).equivFun

/-- The literal action of the actual Standard Model Lie algebra in those
coordinates. It is a Lie homomorphism by transport of the constructed module. -/
def matter27MatrixRepresentation :
    StandardModelAlgebra →ₗ⁅ℂ⁆ Matrix (Fin 27) (Fin 27) ℂ :=
  lieEquivMatrix'.toLieHom.comp (matter27Coordinates.lieConj.toLieHom.comp
    (LieModule.toEnd ℂ StandardModelAlgebra Matter27))

/-- Matrix coordinates intertwine the actual module endomorphism. -/
theorem matter27_matrix_operator (x : StandardModelAlgebra) :
    (matter27MatrixRepresentation x).toLin' =
      matter27Coordinates.conj (LieModule.toEnd ℂ StandardModelAlgebra Matter27 x) := by
  simp [matter27MatrixRepresentation, LinearEquiv.lieConj_apply]

/-- The constructed actual matrix representation is traceless. -/
theorem matter27_matrix_trace (x : StandardModelAlgebra) :
    trace (matter27MatrixRepresentation x) = 0 := by
  rw [← Matrix.trace_toLin'_eq, matter27_matrix_operator, LinearMap.trace_conj']
  exact matter27_standard_model_linear_trace x

private theorem matter27_matrix_cube_trace (x : StandardModelAlgebra) :
    trace ((matter27MatrixRepresentation x) ^ 3) = 0 := by
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow, matter27_matrix_operator,
    trace_cube_conjugate]
  exact matter27_standard_model_cube_trace x

private theorem symmetric_trilinear_zero_of_diagonal
    {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (c : TrilinearForm (R := ℂ) (L := L) (S := ℂ))
    (hs : CubicAnomaly.Classification.CartanCubic.IsSymmetric c)
    (hc : ∀ x, c x x x = 0) (x y z : L) : c x y z = 0 := by
  have hxyz := hc (x + y + z)
  have hxy := hc (x + y)
  have hxz := hc (x + z)
  have hyz := hc (y + z)
  have hx := hc x
  have hy := hc y
  have hz := hc z
  simp only [map_add, LinearMap.add_apply] at hxyz hxy hxz hyz
  have h1 : c x z y = c x y z := hs.2 x z y
  have h2 : c y x z = c x y z := hs.1 y x z
  have h3 : c y z x = c x y z := (hs.2 y z x).trans h2
  have h4 : c z x y = c x y z := (hs.1 z x y).trans h1
  have h5 : c z y x = c x y z := (hs.1 z y x).trans h3
  rw [h1, h2, h3, h4, h5] at hxyz
  linear_combination (hxyz - hxy - hxz - hyz + hx + hy + hz) / 6

/-- The full cubic of the actual complete twenty-seven vanishes on the
actual Standard Model Lie algebra, including arbitrary mixed insertions. -/
theorem matter27_standard_model_full_cubic (x y z : StandardModelAlgebra) :
    matrixTraceCubic (matter27MatrixRepresentation x)
      (matter27MatrixRepresentation y) (matter27MatrixRepresentation z) = 0 := by
  apply symmetric_trilinear_zero_of_diagonal
    (complexTraceCubicForm matter27MatrixRepresentation.toLinearMap)
    (complex_trace_cubic_symmetric matter27MatrixRepresentation.toLinearMap) _ x y z
  intro a
  change matrixTraceCubic (matter27MatrixRepresentation a)
    (matter27MatrixRepresentation a) (matter27MatrixRepresentation a) = 0
  have h := matter27_matrix_cube_trace a
  simpa [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add, pow_succ,
    Matrix.mul_assoc] using h


end

end CubicAnomaly.Fixed.MatterAnomaly
