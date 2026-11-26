import CubicAnomaly.Classification.MinusculeClassicalDimension
import CubicAnomaly.Classification.OrthogonalComplexification
import CubicAnomaly.Classification.OrthogonalMatrixDimension
import CubicAnomaly.Classification.TypeDCartanCoordinates

/-!
# Exclusion of the small fixed-node orthogonal modules

A proper isotropy subalgebra has dimension strictly less than the number
of independent skew entries in the defining space. The small minuscule
modules in types A₃ and D reach this bound already in the isotropy.
-/

namespace CubicAnomaly.Classification.OrthogonalMinusculeExclusion

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentHighest
open OrthogonalDefining OrthogonalComplexification MinusculeClassicalDimension
open scoped TensorProduct

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) (hp : h ≠ ⊤)

include hp in
/-- A proper compact orthogonal subalgebra has strictly smaller dimension
than the count of off-diagonal entries of its defining representation. -/
theorem proper_orthogonal_dimension_lt :
    finrank ℂ (ℂ ⊗[ℝ] h) < (finrank ℂ (ℂ ⊗[ℝ] W)).choose 2 := by
  have hs : h.toSubmodule < ⊤ := lt_top_iff_ne_top.mpr (fun he => hp ((h.toSubmodule_eq_top).mp he))
  have hlt := Submodule.finrank_lt_finrank_of_lt hs
  rw [finrank_top] at hlt
  have he := (standardOrthogonalMatrixEquiv (W := W)).toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange] at he
  have hu := OrthogonalMatrixDimension.so_finrank_le (Fin (finrank ℝ W))
  rw [Fintype.card_fin] at hu
  rw [Module.finrank_baseChange, Module.finrank_baseChange]
  exact hlt.trans_le (he.trans_le hu)

variable [IsKilling ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    [IsIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W)] {χ : Weight ℂ H (ℂ ⊗[ℝ] W)}
    {v : ℂ ⊗[ℝ] W} (hv : IsHighestVector H b χ v)

include hv hp in
/-- The first fundamental D module is too small to define a proper compact
orthogonal inclusion, in every rank at least three. -/
theorem no_typeD_vector {n : ℕ} (hn : 3 ≤ n) (s : Fin n ≃ b.support)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.D n i j)
    (hχ : ∀ i, χ (coroot (s i).val.val) = if i.val = 0 then 1 else 0) : False := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+2 := ⟨n-2,by omega⟩
  have hw := typeD_vector_finrank_le H b hv hn s hC hχ
  have hsize := (proper_orthogonal_dimension_lt h hp).trans_le (Nat.choose_le_choose 2 hw)
  have hm : b.cartanMatrix.reindex s.symm s.symm = CartanMatrix.D (m+2) := by
    ext i j
    exact hC i j
  have hd := TypeDCartanCoordinates.typeD_source_dimension H b s.symm hm
  have hc (r : ℕ) : (2*r).choose 2 = r*(2*r-1) := by
    rw [Nat.choose_two_right, show 2*r*(2*r-1) = r*(2*r-1)*2 by ring,
      Nat.mul_div_cancel _ (by decide : 0 < 2)]
  exact (not_lt_of_ge hd) (hc _ ▸ hsize)

include hv hp in
/-- The middle fundamental A₃ module cannot be the defining representation
of a proper orthogonal isotropy algebra. -/
theorem no_typeA_three_middle (s : Fin 3 ≃ b.support)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.A 3 i j)
    (hχ : ∀ i, χ (coroot (s i).val.val) = if i.val = 1 then 1 else 0) : False := by
  let p := Equiv.swap (0 : Fin 3) 1
  have ht : ∀ i j, CartanMatrix.A 3 (p i) (p j) = CartanMatrix.D 3 i j := by decide
  have hlabels : ∀ i, (if (p i).val = 1 then (1:ℂ) else 0) =
      (if i.val = 0 then 1 else 0) := by intro i; fin_cases i <;> norm_num [p,Equiv.swap_apply_def]
  exact no_typeD_vector h hp H b hv (by decide : 3 ≤ 3) (p.trans s)
    (fun i j => (hC (p i) (p j)).trans (ht i j)) (fun i => (hχ (p i)).trans (hlabels i))

end CubicAnomaly.Classification.OrthogonalMinusculeExclusion
