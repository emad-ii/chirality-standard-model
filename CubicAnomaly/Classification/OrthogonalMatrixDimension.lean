import Mathlib.Algebra.Lie.Classical
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Counting the independent off-diagonal entries of a skew-symmetric matrix. -/
namespace CubicAnomaly.Classification.OrthogonalMatrixDimension

open LieAlgebra Matrix Module
open scoped Matrix

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

private abbrev Pairs := {p : Sym2 ι // ¬p.IsDiag}

private noncomputable def entries : Orthogonal.so ι ℂ →ₗ[ℂ] Pairs ι → ℂ where
  toFun X p := X.val p.val.out.1 p.val.out.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem swap (X : Orthogonal.so ι ℂ) (i j : ι) : X.val j i = -X.val i j :=
  congrFun (congrFun ((Orthogonal.mem_so ι ℂ _).mp X.property) i) j

private theorem entries_injective : Function.Injective (entries ι) := by
  intro X Y he
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    have hx := swap ι X i i
    have hy := swap ι Y i i
    linear_combination (hx-hy)/2
  let p : Pairs ι := ⟨Sym2.mk (i,j), fun h => hij (Sym2.mk_isDiag_iff.mp h)⟩
  have hp : Sym2.mk p.val.out = Sym2.mk (i,j) := Quot.out_eq p.val
  have hr : X.val p.val.out.1 p.val.out.2 = Y.val p.val.out.1 p.val.out.2 := congrFun he p
  rcases Sym2.mk_eq_mk_iff.mp hp with h | h
  · simpa [h] using hr
  · have h' : X.val j i = Y.val j i := by simpa [h] using hr
    simpa only [swap ι X i j, swap ι Y i j, neg_inj] using h'

/-- A skew-symmetric complex matrix has at most one free entry per unordered pair of distinct indices. -/
theorem so_finrank_le : finrank ℂ (Orthogonal.so ι ℂ) ≤ (Fintype.card ι).choose 2 := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := entries ι) (entries_injective ι)
  rw [Module.finrank_pi] at h
  exact h.trans_eq Sym2.card_subtype_not_diag

private noncomputable instance : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)

/-- Upper bound for the split even orthogonal matrix algebra. -/
theorem typeD_finrank_le (n : ℕ) : finrank ℂ (Orthogonal.typeD (Fin n) ℂ) ≤ n*(2*n-1) := by
  let E := (Orthogonal.typeDEquivSo' (Fin n) ℂ).trans
    (Orthogonal.soIndefiniteEquiv _ _ ℂ Complex.I_mul_I)
  rw [E.toLinearEquiv.finrank_eq]
  apply (so_finrank_le _).trans_eq
  simp only [Fintype.card_sum, Fintype.card_fin, Nat.choose_two_right, ← two_mul]
  have he : 2*n*(2*n-1) = n*(2*n-1)*2 := by ring
  rw [he, Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- Upper bound for the split odd orthogonal matrix algebra. -/
theorem typeB_finrank_le (n : ℕ) : finrank ℂ (Orthogonal.typeB (Fin n) ℂ) ≤ n*(2*n+1) := by
  let E := (Orthogonal.typeBEquivSo' (Fin n) ℂ).trans
    (Orthogonal.soIndefiniteEquiv _ _ ℂ Complex.I_mul_I)
  rw [E.toLinearEquiv.finrank_eq]
  apply (so_finrank_le _).trans_eq
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.choose_two_right]
  have h : 1+n+n-1 = 2*n := by omega
  rw [h]
  have he : (1+n+n)*(2*n) = n*(2*n+1)*2 := by ring
  rw [he, Nat.mul_div_cancel _ (by decide : 0 < 2)]

end CubicAnomaly.Classification.OrthogonalMatrixDimension
