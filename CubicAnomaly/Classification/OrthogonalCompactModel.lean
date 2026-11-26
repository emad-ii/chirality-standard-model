import CubicAnomaly.Classification.OrthogonalCompactModelD

/-! The compact conjugation and its positive Hermitian metric in split type B. -/
namespace CubicAnomaly.Classification.OrthogonalCompactModel

open LieAlgebra Matrix OrthogonalDefining OrthogonalComplexification CompactChevalleyConjugation
open scoped Matrix ComplexConjugate TensorProduct

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The change of split orthogonal coordinates in odd dimension. -/
def oddChange : Matrix (Unit ⊕ (ι ⊕ ι)) (Unit ⊕ (ι ⊕ ι)) ℂ := fromBlocks 1 0 0 (evenChange ι)

private def oddInv : Matrix (Unit ⊕ (ι ⊕ ι)) (Unit ⊕ (ι ⊕ ι)) ℂ := fromBlocks 1 0 0 (evenInv (ι := ι))

private theorem odd_transform : (oddChange ι)ᵀ * Orthogonal.JB ι ℂ * oddChange ι =
    (2 : ℂ) • (1 : Matrix (Unit ⊕ (ι ⊕ ι)) (Unit ⊕ (ι ⊕ ι)) ℂ) := by
  have h : (evenChange ι)ᵀ * Orthogonal.JD ι ℂ * evenChange ι = (2 : ℂ) • 1 := by
    simpa only [two_smul] using even_transform (ι := ι)
  simp [oddChange, Orthogonal.JB, fromBlocks_transpose, fromBlocks_multiply, h,
    ← fromBlocks_one, two_smul, fromBlocks_add]

private theorem odd_mul_inv : oddChange ι * oddInv (ι := ι) = 1 := by
  simp [oddChange, oddInv, fromBlocks_multiply, even_inv_mul, fromBlocks_one]

private def oddInvertible : Invertible (oddChange ι) := invertibleOfRightInverse _ _ odd_mul_inv

private theorem odd_inv_eq : (oddChange ι)⁻¹ = oddInv (ι := ι) := Matrix.inv_eq_right_inv odd_mul_inv

private def oddEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Orthogonal.so (Unit ⊕ (ι ⊕ ι)) ℂ ≃ₗ⁅ℂ⁆ Orthogonal.typeB ι ℂ :=
  (gramEquiv oddInvertible odd_transform).symm

private theorem oddEquiv_apply (X : Orthogonal.so (Unit ⊕ (ι ⊕ ι)) ℂ) :
    (oddEquiv ι X).val = oddChange ι * X.val * oddInv := by
  exact (gramEquiv_symm_apply oddInvertible odd_transform X).trans
    (congrArg (fun Q => oddChange ι * X.val * Q) odd_inv_eq)

variable (ι) in
/-- The scalar extension of the compact real orthogonal algebra in split type-B coordinates. -/
def matrixBEquiv : (ℂ ⊗[ℝ] orthogonalAlgebra (EuclideanSpace ℝ (Unit ⊕ (ι ⊕ ι)))) ≃ₗ⁅ℂ⁆ Orthogonal.typeB ι ℂ :=
  (orthogonalMatrixEquiv (EuclideanSpace.basisFun _ ℝ)).trans (oddEquiv ι)

private theorem matrixBEquiv_val (z : ℂ ⊗[ℝ] orthogonalAlgebra (EuclideanSpace ℝ (Unit ⊕ (ι ⊕ ι)))) :
    (matrixBEquiv ι z).val = oddChange ι * (orthogonalMatrixEquiv (EuclideanSpace.basisFun _ ℝ) z).val *
      oddInv (ι := ι) := by
  rw [matrixBEquiv, LieEquiv.trans_apply]
  exact oddEquiv_apply _

variable (ι) in
/-- The positive Hermitian metric in the split type-B basis. The central coordinate has norm squared two. -/
def oddMetric : Matrix (Unit ⊕ (ι ⊕ ι)) (Unit ⊕ (ι ⊕ ι)) ℂ := fromBlocks ((2 : ℂ) • 1) 0 0 1

variable (ι) in
/-- The inverse metric in the split type-B basis. -/
def oddMetricInv : Matrix (Unit ⊕ (ι ⊕ ι)) (Unit ⊕ (ι ⊕ ι)) ℂ := fromBlocks ((2 : ℂ)⁻¹ • 1) 0 0 1

private theorem odd_metric_left : oddMetricInv ι * (oddInv (ι := ι))ᴴ = (2 : ℂ)⁻¹ • oddChange ι := by
  simp [oddMetricInv, oddInv, evenInv, oddChange, fromBlocks_conjTranspose, fromBlocks_multiply,
    Matrix.conjTranspose_smul, fromBlocks_smul]

private theorem odd_metric_right : (oddChange ι)ᴴ * oddMetric ι = (2 : ℂ) • oddInv (ι := ι) := by
  simp [oddMetric, oddInv, evenInv, oddChange, fromBlocks_conjTranspose, fromBlocks_multiply,
    fromBlocks_smul, smul_smul]

/-- Compact conjugation in split type B is negative adjunction for the weighted metric. -/
theorem typeB_scalar_conjugation (z : ℂ ⊗[ℝ] orthogonalAlgebra (EuclideanSpace ℝ (Unit ⊕ (ι ⊕ ι)))) :
    (matrixBEquiv ι (scalarConjugation z)).val =
      -(oddMetricInv ι * (matrixBEquiv ι z).valᴴ * oddMetric ι) := by
  rw [matrixBEquiv_val, matrixBEquiv_val, orthogonal_matrix_scalar_conjugation, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul]
  let A := (orthogonalMatrixEquiv (EuclideanSpace.basisFun _ ℝ) z).valᴴ
  change oddChange ι * (-A) * oddInv = -(oddMetricInv ι * (oddInvᴴ * (A * (oddChange ι)ᴴ)) * oddMetric ι)
  rw [← Matrix.mul_assoc (oddMetricInv ι), odd_metric_left]
  have hr : ((2 : ℂ)⁻¹ • oddChange ι) * (A * (oddChange ι)ᴴ) * oddMetric ι =
      ((2 : ℂ)⁻¹ • oddChange ι) * A * ((oddChange ι)ᴴ * oddMetric ι) := by simp only [Matrix.mul_assoc]
  rw [hr, odd_metric_right]
  simp [smul_smul]

end
end CubicAnomaly.Classification.OrthogonalCompactModel
