import CubicAnomaly.Classification.OddOrthogonalMatrixGenerators

/-!
# Compact adjoints in the odd orthogonal Witt model

The Hermitian metric gives the middle coordinate squared length two.
Its adjoint exchanges every paired split matrix unit with the unit of
opposite indices, including the short terminal simple-root generator.
-/

namespace CubicAnomaly.Classification.TypeBCompactAdjoint

open OddOrthogonalMatrixGenerators Matrix
open scoped Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [DecidableEq ι] [Fintype ι] in
private theorem scale_nz (i : Index ι) : scale i ≠ 0 := by
  cases i <;> norm_num [scale]

omit [DecidableEq ι] [Fintype ι] in
private theorem scale_star (i : Index ι) : star (scale i) = scale i := by
  cases i <;> simp [scale]

private theorem weighted_single (i j : Index ι) (c : ℂ) :
    Matrix.diagonal (fun x : Index ι => (scale x)⁻¹) * single i j c * Matrix.diagonal scale =
      single i j ((scale i)⁻¹ * c * scale j) := by
  ext x y
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.single_apply]
  split_ifs with he
  · obtain ⟨rfl,rfl⟩ := he
    rfl
  · simp

private theorem weighted_unit (i j : Index ι) :
    Matrix.diagonal (fun x : Index ι => (scale x)⁻¹) * (unit i j).valᴴ * Matrix.diagonal scale =
      (unit j i).val := by
  simp only [unit, Matrix.conjTranspose_sub, Matrix.conjTranspose_single, scale_star,
    mul_sub, sub_mul, weighted_single, scale_flip, inv_mul_cancel₀ (scale_nz _), one_mul]

/-- The split simple generators have the compact Hermitian adjoint
determined by the middle coordinate of squared length two. -/
theorem raising_weighted_adjoint {n : ℕ} (i : Fin (n+1)) :
    Matrix.diagonal (fun x : Index (Fin (n+1)) => (scale x)⁻¹) *
      (raising i).valᴴ * Matrix.diagonal scale = (lowering i).val := by
  induction i using Fin.lastCases with
  | last => simpa only [raising, lowering, Fin.lastCases_last] using weighted_unit (pos (Fin.last n)) mid
  | cast j => simpa only [raising, lowering, Fin.lastCases_castSucc] using weighted_unit (pos j.castSucc) (pos j.succ)

omit [Fintype ι] in
private theorem block_scale (c : ℂ) :
    Matrix.fromBlocks (c • (1 : Matrix Unit Unit ℂ)) 0 0 (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) =
      Matrix.diagonal (Sum.elim (fun _ : Unit => c) (fun _ : ι ⊕ ι => (1 : ℂ))) := by
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, ← Matrix.diagonal_one, Matrix.fromBlocks_diagonal]
  congr 1
  funext x
  cases x <;> simp

/-- The adjoint formula in the two matrix blocks used to descend the
odd orthogonal Witt model to the compact real form. -/
theorem raising_block_adjoint {n : ℕ} (i : Fin (n+1)) :
    Matrix.fromBlocks ((2 : ℂ)⁻¹ • (1 : Matrix Unit Unit ℂ)) 0 0 1 *
      (raising i).valᴴ * Matrix.fromBlocks ((2 : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 1 =
        (lowering i).val := by
  rw [block_scale, block_scale]
  have h : Sum.elim (fun _ : Unit => (2 : ℂ)⁻¹) (fun _ : Fin (n+1) ⊕ Fin (n+1) => (1 : ℂ)) =
      fun x => (scale x)⁻¹ := by
    funext x
    cases x <;> simp [scale]
  rw [h]
  exact raising_weighted_adjoint i

end CubicAnomaly.Classification.TypeBCompactAdjoint
