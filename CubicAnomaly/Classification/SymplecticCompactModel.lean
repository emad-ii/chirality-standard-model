import CubicAnomaly.Classification.SymplecticComplexification
import CubicAnomaly.Classification.CompactChevalleyConjugation
import Mathlib.Algebra.Lie.Classical

/-! The compact quaternionic model in orthonormal symplectic coordinates. -/

namespace CubicAnomaly.Classification.SymplecticCompactModel

open SymplecticGeometry SymplecticForm SymplecticComplexification CompactChevalleyConjugation
open scoped ComplexConjugate Matrix TensorProduct

noncomputable section

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

abbrev Space := EuclideanSpace ℂ (ι ⊕ ι)

private def swapConj (v : Space ι) : Space ι := WithLp.toLp 2
  (Sum.elim (fun i => -conj (v (.inr i))) (fun i => conj (v (.inl i))))

/-- The standard quaternionic structure sends `(a,b)` to `(-conj b,conj a)`. -/
def quaternionicStructure : QuaternionicStructure (Space ι) where
  toConjLinearMap := {
    toFun := swapConj ι
    map_add' := by
      intro u v
      ext i
      cases i <;> simp [swapConj, add_comm]
    map_smul' := by
      intro a u
      ext i
      cases i <;> simp [swapConj, map_mul, mul_neg] }
  square := by
    intro v
    ext i
    cases i <;> simp [swapConj]
  inner_map := by
    intro u v
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_sum_type,
      swapConj, add_comm, mul_comm]

/-- The ordered orthonormal coordinate basis of the two copies of the index set. -/
abbrev coordinateBasis := (EuclideanSpace.basisFun (ι ⊕ ι) ℂ).toBasis

/-- In the ordered orthonormal basis the form has matrix `-J`. -/
theorem quaternionic_form_toMatrix :
    LinearMap.toMatrix₂ (coordinateBasis ι) (coordinateBasis ι) (quaternionicForm (quaternionicStructure ι)) =
      -Matrix.J ι ℂ := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix₂_apply, coordinateBasis, quaternionic_form_apply, quaternionicStructure,
      EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, swapConj,
      Matrix.J, Matrix.one_apply, eq_comm]

private theorem matrix_mem_iff (A : Module.End ℂ (Space ι)) :
    A ∈ skewAdjointLieSubalgebra (quaternionicForm (quaternionicStructure ι)) ↔
      LinearMap.toMatrix (coordinateBasis ι) (coordinateBasis ι) A ∈ LieAlgebra.Symplectic.sp ι ℂ := by
  let b := coordinateBasis ι
  let B := quaternionicForm (quaternionicStructure ι)
  let X := LinearMap.toMatrix b b A
  let G := LinearMap.toMatrix₂ b b B
  have h := isAdjointPair_toLinearMap₂ b b G G X (-X)
  dsimp only [G, X] at h
  rw [Matrix.toLinearMap₂_toMatrix₂, Matrix.toLin_toMatrix, map_neg, Matrix.toLin_toMatrix] at h
  change A ∈ B.skewAdjointSubmodule ↔ X ∈ skewAdjointMatricesSubmodule (Matrix.J ι ℂ)
  rw [LinearMap.mem_skewAdjointSubmodule, mem_skewAdjointMatricesSubmodule]
  apply h.trans
  change (Xᵀ * G = G * (-X)) ↔ Xᵀ * Matrix.J ι ℂ = Matrix.J ι ℂ * (-X)
  have hg : G = -Matrix.J ι ℂ := quaternionic_form_toMatrix ι
  simp [hg, neg_eq_iff_eq_neg]

/-- The complexified compact quaternionic algebra in its standard orthonormal matrix basis. -/
def matrixEquiv :
    (ℂ ⊗[ℝ] symplecticAlgebra (quaternionicStructure ι)) ≃ₗ⁅ℂ⁆ LieAlgebra.Symplectic.sp ι ℂ :=
  (symplecticComplexificationEquiv (quaternionicStructure ι)).trans
    ((LinearMap.toMatrixAlgEquiv (coordinateBasis ι)).toLieEquiv.ofSubalgebras _ _ (by
      ext X
      constructor
      · rintro ⟨A, hA, rfl⟩
        exact (matrix_mem_iff ι A).mp hA
      · intro hX
        let A := (LinearMap.toMatrixAlgEquiv (coordinateBasis ι)).symm X
        have ha : LinearMap.toMatrix (coordinateBasis ι) (coordinateBasis ι) A = X :=
          (LinearMap.toMatrixAlgEquiv (coordinateBasis ι)).apply_symm_apply X
        exact ⟨A, (matrix_mem_iff ι A).mpr (ha.symm ▸ hX), ha⟩))

/-- On pure tensors, the equivalence is the scalar multiple of the defining operator matrix. -/
theorem matrixEquiv_tmul (a : ℂ) (x : symplecticAlgebra (quaternionicStructure ι)) :
    (matrixEquiv ι (a ⊗ₜ[ℝ] x)).val = a • LinearMap.toMatrix (coordinateBasis ι) (coordinateBasis ι) x.val := by
  change LinearMap.toMatrix (coordinateBasis ι) (coordinateBasis ι) (a • x.val) = _
  exact map_smul _ _ _

/-- Complex conjugation on the scalar factor becomes the negative conjugate transpose. -/
theorem symplectic_matrix_scalar_conjugation (z : ℂ ⊗[ℝ] symplecticAlgebra (quaternionicStructure ι)) :
    (matrixEquiv ι (scalarConjugation z)).val = -(matrixEquiv ι z).valᴴ := by
  induction z using TensorProduct.induction_on with
  | zero =>
    have hz : matrixEquiv ι 0 = 0 := (matrixEquiv ι).toLinearEquiv.map_zero
    rw [map_zero, hz]
    change (0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) = -(0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)ᴴ
    rw [Matrix.conjTranspose_zero, neg_zero]
  | tmul a x =>
    have hx : x.val.adjoint = -x.val := (UnitaryGeometry.unitary_mem_iff x.val).mpr x.property.1
    rw [scalarConjugation_tmul, matrixEquiv_tmul, matrixEquiv_tmul, Matrix.conjTranspose_smul,
      ← LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun _ ℂ) (EuclideanSpace.basisFun _ ℂ),
      hx, map_neg, smul_neg, neg_neg]
    rfl
  | add x y hx hy =>
    simp only [map_add]
    change _ + _ = -(_ + _)ᴴ
    rw [Matrix.conjTranspose_add, neg_add, hx, hy]

end
end CubicAnomaly.Classification.SymplecticCompactModel
