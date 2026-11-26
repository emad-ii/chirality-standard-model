import CubicAnomaly.Classification.TypeACubicHighestWeight

/-! # A symmetric type-A highest label can be supported only at the central node

Lowering one end of a noncentral exchanged pair gives a genuine skew
highest weight with nonzero cubic, contradicting the compact anomaly.
-/

namespace CubicAnomaly.Classification.TypeAOrthogonalExchanged

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentHighest ClassicalConstituentWeights
open TypeACubicHighestWeight TypeACubicArithmetic CompactOperatorModel Structural HermitianRealization
open scoped TensorProduct

private theorem simple_difference {n : ℕ} (i j : Fin n) :
    ((if j.castSucc = i.castSucc then (1 : ℂ) else 0) - (if j.castSucc = i.succ then 1 else 0)) -
    ((if j.succ = i.castSucc then 1 else 0) - (if j.succ = i.succ then 1 else 0)) =
      (CartanMatrix.A n i j : ℂ) := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> norm_num <;> omega

variable {g W : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)] [IsSimple ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    {n : ℕ} (s : b.support ≃ Fin n) (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n)
    [AddCommGroup W] [Module ℂ W] [LieRingModule (ℂ ⊗[ℝ] h) W] [LieModule ℂ (ℂ ⊗[ℝ] h) W]
    [FiniteDimensional ℂ W] [IsIrreducible ℂ (ℂ ⊗[ℝ] h) W]

include hp hr hm in
/-- At every noncentral node of a type-A orthogonal model the actual
symmetric Dynkin labels vanish. This holds in arbitrary rank. -/
theorem symmetric_label_eq_zero_of_noncentral (β : LinearMap.BilinForm ℂ W) (A : Model h β)
    (hβ : β.Nondegenerate) (hInv : β.lieInvariant (ℂ ⊗[ℝ] h)) (hSym : β.IsSymm)
    (χ : H → ℂ) (v : W) (hv : IsHighestVector H b χ v) (a : Fin n → ℕ)
    (ha : ∀ i : b.support, χ (coroot i.val.val) = (a (s i) : ℂ))
    (hrev : ∀ i, a i.rev = a i) (j : Fin n) (hne : j ≠ j.rev) : a j = 0 := by
  haveI := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) W
  obtain ⟨_,u,hs,hd,_,_⟩ := highest_matrix_coordinates H b s hm χ v hv
  have hd' (i : Fin n) : u i.castSucc - u i.succ = (a i : ℂ) := by
    obtain ⟨k,rfl⟩ := s.surjective i
    exact (hd k).trans (ha k)
  have husym (k : Fin (n+1)) : u k.rev = -u k := by
    have z : (∑ i : Fin (n+1), -u i.rev) = 0 := by
      rw [Finset.sum_neg_distrib, show (∑ i : Fin (n+1), u i.rev) = ∑ i,u i from Equiv.sum_comp Fin.revPerm u, hs, neg_zero]
    have eq := coords_unique hs z (fun i : Fin n => by
      rw [Fin.rev_castSucc, Fin.rev_succ, neg_sub_neg, hd' i, hd' i.rev, hrev])
    exact neg_eq_iff_eq_neg.mp (congrFun eq k).symm
  have hdom : Antitone fun k : Fin (n+1) => (2 * u k).re := by
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    have hh := congrArg Complex.re (hd' i)
    simp only [Complex.sub_re, Complex.natCast_re] at hh
    simp only [two_mul, Complex.add_re]
    linarith [Nat.cast_nonneg (α := ℝ) (a i)]
  have left (i : Fin n) (hi : i < i.rev) : a i = 0 := by
    by_contra hpositive
    let p := s.symm i
    obtain ⟨chi,w,c,hw,hew,hkw,hc⟩ := orthogonal_support_weights H b β hβ hInv hSym
    have heq := (irreducible_highest_weight_unique H b hv (show IsHighestVector H b chi w from ⟨hw,hew,hkw⟩)).2
    have hl : (c p : ℕ) = a i := by
      apply Nat.cast_injective (R := ℂ)
      rw [← (hc p).1, ← heq, ha, s.apply_symm_apply]
    have hskew := (hc p).2.1 (by omega)
    rw [← heq] at hskew
    let t := fun k : Fin (n+1) => 2 * u k - (if k = i.castSucc then 1 else 0) + (if k = i.succ then 1 else 0)
    have ht : ∑ k, t k = 0 := by simp [t, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
    have hδ (q : b.support) : p.val.val (coroot q.val.val) = (CartanMatrix.A n i (s q) : ℂ) := by
      have h := b.algebraMap_cartanMatrixIn_apply ℤ p q
      change ((b.cartanMatrix p q : ℤ) : ℂ) = p.val.val (coroot q.val.val) at h
      rw [← h]
      have h' := congrFun (congrFun hm i) (s q)
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, s.symm_apply_apply] at h'
      exact_mod_cast h'
    have he := skew_highest_eigenvalue_eq B h hp e hr H b s hm β A _ hskew t ht (fun q => by
      rw [hδ q, ← hd q]
      unfold t
      linear_combination -(simple_difference i (s q)))
    have hdiff : 2 * u i.castSucc ≠ 2 * u i.succ := by
      intro h
      have hzero : (a i : ℂ) = 0 := by linear_combination h / 2 - hd' i
      exact hpositive (Nat.cast_eq_zero.mp hzero)
    apply shifted_difference_ne_zero (fun k => 2 * u k) (fun k => by change 2*u k.rev = -(2*u k); rw [husym, mul_neg])
      hdom i.castSucc i.succ rfl (by simpa only [Fin.rev_succ, Fin.castSucc_lt_castSucc_iff] using hi)
      hdiff
    exact sub_eq_zero.mpr he
  rcases lt_or_gt_of_ne hne with h | h
  · exact left j h
  · rw [← hrev j]
    exact left j.rev (by simpa using h)

end CubicAnomaly.Classification.TypeAOrthogonalExchanged
