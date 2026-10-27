import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# A concrete alternating-tensor matter module

The ten-dimensional module used in the `SU(5)` restriction is constructed
as skew-transpose matrices. Its action is the literal tensor action
`X ↦ A * X + X * Aᵀ`. Thus the representation and its diagonal weights
are proved from matrices, rather than supplied as branching data.

This construction is downstream of the exceptional inclusion: identifying
it with a summand of the actual `E6` twenty-seven remains a separate bridge.
-/

namespace CubicAnomaly.Fixed.MatterAlternating

open Matrix

noncomputable section

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Alternating two-tensors represented by skew-transpose matrices. -/
def alternatingSubmodule : Submodule ℂ (Matrix n n ℂ) where
  carrier := {X | Xᵀ = -X}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    simp only [transpose_add, hX, hY, neg_add_rev]
    abel
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    simp [hX]

/-- The actual alternating tensor space. -/
abbrev AlternatingTensor := alternatingSubmodule n

omit [DecidableEq n] in
private theorem action_mem (A : Matrix n n ℂ) (X : AlternatingTensor n) :
    A * X.val + X.val * Aᵀ ∈ alternatingSubmodule n := by
  change (A * X.val + X.val * Aᵀ)ᵀ = -(A * X.val + X.val * Aᵀ)
  rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, X.property]
  simp only [neg_mul, mul_neg, neg_add_rev]

instance : LieRingModule (Matrix n n ℂ) (AlternatingTensor n) where
  bracket A X := ⟨A * X.val + X.val * Aᵀ, action_mem n A X⟩
  add_lie A B X := by
    apply Subtype.ext
    change (A + B) * X.val + X.val * (A + B)ᵀ =
      (A * X.val + X.val * Aᵀ) + (B * X.val + X.val * Bᵀ)
    simp only [transpose_add, add_mul, mul_add]
    abel
  lie_add A X Y := by
    apply Subtype.ext
    change A * (X.val + Y.val) + (X.val + Y.val) * Aᵀ =
      (A * X.val + X.val * Aᵀ) + (A * Y.val + Y.val * Aᵀ)
    simp only [add_mul, mul_add]
    abel
  leibniz_lie A B X := by
    apply Subtype.ext
    change A * (B * X.val + X.val * Bᵀ) + (B * X.val + X.val * Bᵀ) * Aᵀ =
      ((A * B - B * A) * X.val + X.val * (A * B - B * A)ᵀ) +
        (B * (A * X.val + X.val * Aᵀ) + (A * X.val + X.val * Aᵀ) * Bᵀ)
    simp only [transpose_sub, transpose_mul, add_mul, mul_add, sub_mul, mul_sub, mul_assoc]
    abel

instance : LieModule ℂ (Matrix n n ℂ) (AlternatingTensor n) where
  smul_lie c A X := by
    apply Subtype.ext
    change (c • A) * X.val + X.val * (c • A)ᵀ =
      c • (A * X.val + X.val * Aᵀ)
    simp [smul_add]
  lie_smul c A X := by
    apply Subtype.ext
    change A * (c • X.val) + (c • X.val) * Aᵀ =
      c • (A * X.val + X.val * Aᵀ)
    simp [smul_add]

/-- The constructed Lie action is the usual alternating tensor action. -/
@[simp] theorem alternating_action_val (A : Matrix n n ℂ) (X : AlternatingTensor n) :
    (⁅A, X⁆ : AlternatingTensor n).val = A * X.val + X.val * Aᵀ := rfl

/-- A diagonal generator acts with the sum of the two fundamental weights. -/
theorem alternating_diagonal_action (d : n → ℂ) (X : AlternatingTensor n) (i j : n) :
    (⁅Matrix.diagonal d, X⁆ : AlternatingTensor n).val i j =
      (d i + d j) * X.val i j := by
  simp only [alternating_action_val, Matrix.add_apply, Matrix.diagonal_mul,
    Matrix.diagonal_transpose, Matrix.mul_diagonal]
  ring

end

noncomputable section Coordinates

variable (n : Type*) [Fintype n] [LinearOrder n]

/-- The independent coordinates of an alternating tensor. -/
abbrev PairIndex := {p : n × n // p.1 < p.2}

private def alternatingFromCoordinates (f : PairIndex n → ℂ) : AlternatingTensor n :=
  ⟨fun i j => if h : i < j then f ⟨(i, j), h⟩
    else if h : j < i then -f ⟨(j, i), h⟩ else 0, by
    change (fun i j => if h : j < i then f ⟨(j, i), h⟩
      else if h : i < j then -f ⟨(i, j), h⟩ else 0) = _
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, not_lt_of_gt hij]
    · simp
    · simp [hji, not_lt_of_gt hji]⟩

/-- Every alternating tensor is determined by its upper-triangular entries. -/
def alternatingCoordinates : AlternatingTensor n ≃ₗ[ℂ] (PairIndex n → ℂ) where
  toFun X p := X.val p.val.1 p.val.2
  invFun := alternatingFromCoordinates n
  left_inv X := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [alternatingFromCoordinates, hij]
    · have hx := congrArg (fun A : Matrix n n ℂ => A i i) X.property
      have hz : X.val i i = 0 := by
        change X.val i i = -X.val i i at hx
        linear_combination (1 / 2 : ℂ) * hx
      simp [alternatingFromCoordinates, hz]
    · have hx := congrArg (fun A : Matrix n n ℂ => A j i) X.property
      change X.val i j = -X.val j i at hx
      simp [alternatingFromCoordinates, hji, not_lt_of_gt hji, hx]
  right_inv f := by
    funext p
    simp [alternatingFromCoordinates, p.property]
  map_add' X Y := by rfl
  map_smul' c X := by rfl

/-- The independent coordinates are genuine eigenvectors for a diagonal action. -/
theorem alternating_coordinates_diagonal (d : n → ℂ) (X : AlternatingTensor n)
    (p : PairIndex n) :
    alternatingCoordinates n ⁅Matrix.diagonal d, X⁆ p =
      (d p.val.1 + d p.val.2) * alternatingCoordinates n X p :=
  alternating_diagonal_action n d X p.val.1 p.val.2

instance : FiniteDimensional ℂ (AlternatingTensor n) :=
  (alternatingCoordinates n).symm.finiteDimensional

/-- The alternating-tensor dimension is the number of unordered pairs. -/
theorem alternating_finrank :
    Module.finrank ℂ (AlternatingTensor n) = Fintype.card (PairIndex n) := by
  rw [(alternatingCoordinates n).finrank_eq]
  exact Module.finrank_pi _

end Coordinates

end CubicAnomaly.Fixed.MatterAlternating
