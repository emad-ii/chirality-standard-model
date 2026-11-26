import Mathlib.Analysis.Complex.Basic

import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A Hamiltonian matrix injects into the symmetric matrices by left multiplication by `J`. -/
namespace CubicAnomaly.Classification.SymplecticMatrixDimension

open LieAlgebra Matrix Module
open scoped Matrix

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

private theorem symmetric_product (X : Symplectic.sp ι ℂ) : (J ι ℂ * X.val)ᵀ = J ι ℂ * X.val := by
  have h := X.property
  simp only [Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] at h
  change X.valᵀ * J ι ℂ = J ι ℂ * (-X.val) at h
  rw [Matrix.transpose_mul, J_transpose, mul_neg, h, mul_neg, neg_neg]

private noncomputable def coordinates : Symplectic.sp ι ℂ →ₗ[ℂ] Sym2 (ι ⊕ ι) → ℂ where
  toFun X := Sym2.lift ⟨fun i j => (J ι ℂ * X.val) i j, fun i j =>
    congrFun (congrFun (symmetric_product ι X) j) i⟩
  map_add' X Y := by
    funext p
    refine Sym2.inductionOn p (fun i j => ?_)
    change (J ι ℂ * (X.val + Y.val)) i j = (J ι ℂ * X.val) i j + (J ι ℂ * Y.val) i j
    rw [mul_add, Matrix.add_apply]
  map_smul' a X := by
    funext p
    refine Sym2.inductionOn p (fun i j => ?_)
    change (J ι ℂ * (a • X.val)) i j = (a • (J ι ℂ * X.val)) i j
    rw [Matrix.mul_smul]

private theorem coordinates_injective : Function.Injective (coordinates ι) := by
  intro X Y h
  have h' : J ι ℂ * X.val = J ι ℂ * Y.val := by
    ext i j
    exact congrFun h (Sym2.mk (i,j))
  have := congrArg (J ι ℂ * ·) h'
  apply Subtype.ext
  simpa [← mul_assoc, J_squared] using this

/-- The complex Hamiltonian matrices on a symplectic space of dimension `2n`
are determined by at most `n(2n+1)` entries. -/
theorem finrank_le (n : ℕ) : finrank ℂ (Symplectic.sp (Fin n) ℂ) ≤ n * (2*n+1) := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := coordinates (Fin n))
    (coordinates_injective (Fin n))
  rw [Module.finrank_pi, Sym2.card, Fintype.card_sum, Fintype.card_fin, Nat.choose_two_right] at h
  apply h.trans_eq
  rw [Nat.add_sub_cancel]
  have he : (n+n+1)*(n+n) = n*(2*n+1)*2 := by ring
  rw [he, Nat.mul_div_cancel _ (by decide : 0 < 2)]

end CubicAnomaly.Classification.SymplecticMatrixDimension
