import CubicAnomaly.Fixed.MatterAlternating

/-!
# The small alternating representations in the Standard Model restriction

Explicit coordinate isomorphisms identify the alternating tensors in
dimension three with the determinant-twisted dual representation, and
those in dimension two with the determinant representation. These are
proved for arbitrary matrices; tracelessness gives the familiar dual
colour module and trivial weak module.
-/

namespace CubicAnomaly.Fixed.MatterSmall

open Matrix
open CubicAnomaly.Fixed.MatterAlternating

noncomputable section

private theorem alternating_diag_zero {n : Type*} [Fintype n] [DecidableEq n]
    (X : AlternatingTensor n) (i : n) : X.val i i = 0 := by
  have h := congrArg (fun A : Matrix n n ℂ => A i i) X.property
  change X.val i i = -X.val i i at h
  linear_combination (1 / 2 : ℂ) * h

private theorem alternating_swap {n : Type*} [Fintype n] [DecidableEq n]
    (X : AlternatingTensor n) (i j : n) : X.val j i = -X.val i j :=
  congrArg (fun A : Matrix n n ℂ => A i j) X.property

private def alternatingThreeFromVector (v : Fin 3 → ℂ) : AlternatingTensor (Fin 3) :=
  ⟨!![0, v 2, -v 1; -v 2, 0, v 0; v 1, -v 0, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

/-- An explicit volume-form identification in dimension three. -/
def alternatingThreeEquiv : AlternatingTensor (Fin 3) ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun X := ![X.val 1 2, -X.val 0 2, X.val 0 1]
  invFun := alternatingThreeFromVector
  left_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alternatingThreeFromVector, alternating_diag_zero,
        alternating_swap X 0 1, alternating_swap X 0 2, alternating_swap X 1 2]
  right_inv v := by
    ext i
    fin_cases i <;> simp [alternatingThreeFromVector]
  map_add' X Y := by
    ext i
    fin_cases i
    all_goals simp
    abel
  map_smul' c X := by ext i; fin_cases i <;> simp

/-- The alternating three-dimensional module is the dual twisted by trace. -/
theorem alternating_three_action (A : Matrix (Fin 3) (Fin 3) ℂ)
    (X : AlternatingTensor (Fin 3)) :
    alternatingThreeEquiv ⁅A, X⁆ =
      Matrix.trace A • alternatingThreeEquiv X - Aᵀ *ᵥ alternatingThreeEquiv X := by
  obtain ⟨v, rfl⟩ := alternatingThreeEquiv.symm.surjective X
  ext i
  fin_cases i <;>
    simp [alternatingThreeEquiv, alternatingThreeFromVector, alternating_action_val,
      Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.trace,
      Fin.sum_univ_succ] <;> ring

/-- Restriction to traceless colour matrices is the literal dual action. -/
theorem alternating_three_traceless_action (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : Matrix.trace A = 0) (X : AlternatingTensor (Fin 3)) :
    alternatingThreeEquiv ⁅A, X⁆ = -Aᵀ *ᵥ alternatingThreeEquiv X := by
  rw [alternating_three_action, hA, zero_smul, zero_sub, Matrix.neg_mulVec]

private def alternatingTwoFromScalar (z : ℂ) : AlternatingTensor (Fin 2) :=
  ⟨!![0, z; -z, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

/-- The alternating square of the two-dimensional weak space is a line. -/
def alternatingTwoEquiv : AlternatingTensor (Fin 2) ≃ₗ[ℂ] ℂ where
  toFun X := X.val 0 1
  invFun := alternatingTwoFromScalar
  left_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alternatingTwoFromScalar, alternating_diag_zero, alternating_swap X 0 1]
  right_inv z := rfl
  map_add' X Y := rfl
  map_smul' c X := rfl

/-- The actual action on the alternating weak line is multiplication by trace. -/
theorem alternating_two_action (A : Matrix (Fin 2) (Fin 2) ℂ)
    (X : AlternatingTensor (Fin 2)) :
    alternatingTwoEquiv ⁅A, X⁆ = Matrix.trace A * alternatingTwoEquiv X := by
  obtain ⟨z, rfl⟩ := alternatingTwoEquiv.symm.surjective X
  simp [alternatingTwoEquiv, alternatingTwoFromScalar, alternating_action_val,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_succ]
  ring

/-- Traceless weak matrices act trivially on their alternating square. -/
theorem alternating_two_traceless_action (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Matrix.trace A = 0) (X : AlternatingTensor (Fin 2)) :
    ⁅A, X⁆ = 0 := by
  apply alternatingTwoEquiv.injective
  rw [alternating_two_action, hA, zero_mul, map_zero]

end

end CubicAnomaly.Fixed.MatterSmall
