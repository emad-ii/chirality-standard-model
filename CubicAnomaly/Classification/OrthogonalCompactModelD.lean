import CubicAnomaly.Classification.OrthogonalComplexification
import CubicAnomaly.Classification.CompactChevalleyConjugation
import Mathlib.Algebra.Lie.Classical

/-! Compact conjugation in split orthogonal matrix coordinates. -/
namespace CubicAnomaly.Classification.OrthogonalCompactModel

open LieAlgebra Matrix OrthogonalDefining OrthogonalComplexification CompactChevalleyConjugation
open scoped Matrix ComplexConjugate TensorProduct

noncomputable section

variable {W ι : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fintype ι] [DecidableEq ι]

private theorem matrix_tmul_entry (b : OrthonormalBasis ι ℝ W) (a : ℂ)
    (x : orthogonalAlgebra W) (i j : ι) :
    (orthogonalMatrixEquiv b (a ⊗ₜ[ℝ] x)).val i j = a * (LinearMap.toMatrix b.toBasis b.toBasis x.val i j : ℝ) := by
  change LinearMap.toMatrix (b.toBasis.baseChange ℂ) (b.toBasis.baseChange ℂ)
    (orthogonalComplexificationHom (a ⊗ₜ[ℝ] x)).val i j = _
  simp [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply, orthogonal_complexification_action_tmul,
    Module.Basis.baseChange_repr_tmul, mul_comm]

/-- Compact scalar conjugation acts by negative conjugate transpose in a real orthonormal basis. -/
theorem orthogonal_matrix_scalar_conjugation (b : OrthonormalBasis ι ℝ W) (z : ℂ ⊗[ℝ] orthogonalAlgebra W) :
    (orthogonalMatrixEquiv b (scalarConjugation z)).val = -(orthogonalMatrixEquiv b z).valᴴ := by
  have hreal : (orthogonalMatrixEquiv b (scalarConjugation z)).val =
      (orthogonalMatrixEquiv b z).val.map conj := by
    induction z using TensorProduct.induction_on with
    | zero =>
      have hz : orthogonalMatrixEquiv b 0 = 0 := (orthogonalMatrixEquiv b).toLinearEquiv.map_zero
      rw [map_zero, hz]; ext; simp
    | tmul a x =>
      ext i j
      rw [scalarConjugation_tmul, Matrix.map_apply, matrix_tmul_entry, matrix_tmul_entry]
      simp
    | add x y hx hy =>
      rw [map_add, map_add, map_add]
      change (orthogonalMatrixEquiv b (scalarConjugation x)).val +
        (orthogonalMatrixEquiv b (scalarConjugation y)).val =
        ((orthogonalMatrixEquiv b x).val + (orthogonalMatrixEquiv b y).val).map conj
      rw [hx, hy]
      ext i j; simp
  have hsk := (Orthogonal.mem_so ι ℂ _).mp (orthogonalMatrixEquiv b z).property
  rw [hreal]
  ext i j
  have he : (orthogonalMatrixEquiv b z).val j i = -(orthogonalMatrixEquiv b z).val i j :=
    congrFun (congrFun hsk i) j
  simp [Matrix.conjTranspose_apply, he]

variable (ι) in
/-- The change of basis diagonalizing the split orthogonal form in pairs of coordinates. -/
def evenChange : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fromBlocks 1 ((-Complex.I) • 1) 1 (Complex.I • 1)

theorem even_transform : (evenChange ι)ᵀ * Orthogonal.JD ι ℂ * evenChange ι = 2 • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  simp [evenChange, Orthogonal.JD, fromBlocks_transpose, fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_add, smul_smul, two_smul]

theorem even_right : evenChange ι * (evenChange ι)ᴴ = (2 : ℂ) • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
  simp [evenChange, fromBlocks_conjTranspose, fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_add, smul_smul, two_smul]


private instance : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)

def gramEquiv {J P : Matrix ι ι ℂ} (hp : Invertible P)
    (h : Pᵀ * J * P = (2 : ℂ) • (1 : Matrix ι ι ℂ)) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅ℂ⁆ Orthogonal.so ι ℂ :=
  (skewAdjointMatricesLieSubalgebraEquiv J P hp).trans (LieEquiv.ofEq _ _ (by
    ext X
    rw [h, ← val_unitOfInvertible (2 : ℂ), ← Units.smul_def, LieSubalgebra.mem_coe,
      mem_skewAdjointMatricesLieSubalgebra_unit_smul]
    rfl))

theorem gramEquiv_symm_apply {J P : Matrix ι ι ℂ} (hp : Invertible P)
    (h : Pᵀ * J * P = (2 : ℂ) • (1 : Matrix ι ι ℂ)) (X : Orthogonal.so ι ℂ) :
    ((gramEquiv hp h).symm X).val = P * X.val * P⁻¹ := by
  let Y := (gramEquiv hp h).symm X
  have he := congrArg Subtype.val ((gramEquiv hp h).apply_symm_apply X)
  have hc : (gramEquiv hp h Y).val = P⁻¹ * Y.val * P := by
    rw [gramEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply, skewAdjointMatricesLieSubalgebraEquiv_apply]
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible P)
  calc
    Y.val = (P * P⁻¹) * Y.val * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv P hdet, one_mul, mul_one]
    _ = P * (P⁻¹ * Y.val * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = P * X.val * P⁻¹ := congrArg (fun U => P * U * P⁻¹) (hc.symm.trans he)

def evenInv := (2 : ℂ)⁻¹ • (evenChange ι)ᴴ

theorem even_inv_mul : evenChange ι * evenInv (ι := ι) = 1 := by
  rw [evenInv, Matrix.mul_smul, even_right, smul_smul]
  norm_num

private def evenInvertible : Invertible (evenChange ι) :=
  invertibleOfRightInverse _ _ even_inv_mul

private theorem even_inv_eq : (evenChange ι)⁻¹ = evenInv (ι := ι) := Matrix.inv_eq_right_inv even_inv_mul

private theorem even_gram (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (evenChange ι)ᵀ * Orthogonal.JD ι ℂ * evenChange ι = (2 : ℂ) • 1 := by
  simpa only [two_smul] using even_transform (ι := ι)

private def evenEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Orthogonal.so (ι ⊕ ι) ℂ ≃ₗ⁅ℂ⁆ Orthogonal.typeD ι ℂ :=
  (gramEquiv evenInvertible (even_gram ι)).symm

private theorem evenEquiv_apply (X : Orthogonal.so (ι ⊕ ι) ℂ) :
    (evenEquiv ι X).val = evenChange ι * X.val * evenInv := by
  exact (gramEquiv_symm_apply evenInvertible (even_gram ι) X).trans
    (congrArg (fun Q => evenChange ι * X.val * Q) even_inv_eq)

variable (ι) in
/-- The scalar extension of the compact real orthogonal algebra in split type-D coordinates. -/
def matrixDEquiv : (ℂ ⊗[ℝ] orthogonalAlgebra (EuclideanSpace ℝ (ι ⊕ ι))) ≃ₗ⁅ℂ⁆ Orthogonal.typeD ι ℂ :=
  (orthogonalMatrixEquiv (EuclideanSpace.basisFun _ ℝ)).trans
    (evenEquiv ι)

private theorem matrixDEquiv_val (z : ℂ ⊗[ℝ] orthogonalAlgebra (EuclideanSpace ℝ (ι ⊕ ι))) :
    (matrixDEquiv ι z).val = evenChange ι * (orthogonalMatrixEquiv (EuclideanSpace.basisFun _ ℝ) z).val *
      evenInv (ι := ι) := by
  rw [matrixDEquiv, LieEquiv.trans_apply]
  exact evenEquiv_apply _

/-- In split type D, compact conjugation sends each operator to its negative adjoint. -/
theorem typeD_scalar_conjugation (z : ℂ ⊗[ℝ] orthogonalAlgebra (EuclideanSpace ℝ (ι ⊕ ι))) :
    (matrixDEquiv ι (scalarConjugation z)).val = -(matrixDEquiv ι z).valᴴ := by
  rw [matrixDEquiv_val, matrixDEquiv_val, orthogonal_matrix_scalar_conjugation]
  simp [evenInv, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, Matrix.mul_assoc]


end
end CubicAnomaly.Classification.OrthogonalCompactModel
