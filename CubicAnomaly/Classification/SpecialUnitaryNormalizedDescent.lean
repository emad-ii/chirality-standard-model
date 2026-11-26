import CubicAnomaly.Classification.UnitaryComplexification
import CubicAnomaly.Classification.SpecialLinearGenerators
import CubicAnomaly.Classification.CompactChevalleyConjugation

/-! In orthonormal coordinates the real structure on the scalar extension
of the special unitary algebra is the negative conjugate transpose. -/

namespace CubicAnomaly.Classification.SpecialUnitaryNormalizedDescent

open UnitaryGeometry UnitaryComplexification SpecialLinearGenerators CompactChevalleyConjugation
open scoped TensorProduct Matrix ComplexConjugate

variable {W ι : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [Fintype ι] [DecidableEq ι]

/-- Scalar conjugation in the complexification of the compact real form
sends a traceless matrix to its negative adjoint. -/
theorem matrix_scalar_conjugation (b : OrthonormalBasis ι ℂ W) (z : ℂ ⊗[ℝ] specialUnitaryAlgebra W) :
    (specialUnitaryMatrixEquiv b.toBasis (scalarConjugation z)).val =
      -(specialUnitaryMatrixEquiv b.toBasis z).valᴴ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [scalarConjugation_tmul, special_unitary_matrix_equiv_tmul, special_unitary_matrix_equiv_tmul,
      Matrix.conjTranspose_smul, ← LinearMap.toMatrix_adjoint b b, x.property.1, map_neg, smul_neg, neg_neg]
    rfl
  | add x y hx hy =>
    simp only [map_add]
    change _ + _ = -(_ + _)ᴴ
    rw [Matrix.conjTranspose_add, neg_add, hx, hy]

/-- Under the standard compact real form, every adjacent raising operator
has conjugate equal to the negative of the corresponding lowering operator. -/
theorem scalar_conjugation_raising {n : ℕ} (i : Fin n) :
    let F := specialUnitaryMatrixEquiv (EuclideanSpace.basisFun (Fin (n+1)) ℂ).toBasis
    scalarConjugation (F.symm (raising i)) = -F.symm (lowering i) := by
  let b := EuclideanSpace.basisFun (Fin (n+1)) ℂ
  let F := specialUnitaryMatrixEquiv b.toBasis
  apply F.injective
  apply Subtype.ext
  change (F (scalarConjugation (F.symm (raising i)))).val = (F (-F.symm (lowering i))).val
  rw [matrix_scalar_conjugation b, F.apply_symm_apply, map_neg, F.apply_symm_apply]
  simp [raising, lowering, Matrix.conjTranspose_single]

end CubicAnomaly.Classification.SpecialUnitaryNormalizedDescent
