import CubicAnomaly.Classification.ClassicalConstituentDiagram
import Mathlib.Data.Matrix.Cartan
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-! A permutation preserving the numbered type-A Cartan matrix fixes the
path pointwise or reverses its order. -/

namespace CubicAnomaly.Classification.TypeADiagramOpposition

/-- An injective walk along a finite path has constant direction. The
only permutations of its Cartan matrix are the identity and reversal. -/
theorem type_A_path_permutation {n : ℕ} (p : Equiv.Perm (Fin n))
    (hm : ∀ i j, CartanMatrix.A n (p i) (p j) = CartanMatrix.A n i j) :
    p = Equiv.refl _ ∨ p = Fin.revPerm := by
  by_cases hn : n ≤ 1
  · left
    ext i
    have hp := (p i).isLt
    have hi := i.isLt
    change (p i).val = i.val
    omega
  let a (k : ℕ) : ℤ := if h : k < n then (p ⟨k,h⟩).val else 0
  have ha (k : ℕ) (h : k < n) : a k = ((p ⟨k,h⟩).val : ℤ) := by simp [a, h]
  have step (k : ℕ) (h : k+1 < n) : a (k+1) - a k = 1 ∨ a (k+1) - a k = -1 := by
    let i : Fin n := ⟨k, by omega⟩
    let j : Fin n := ⟨k+1, h⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i, j] at this
    have hpij := p.injective.ne hij
    have hstep := hm i j
    simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij, if_neg hpij] at hstep
    rw [if_pos (Or.inl (show i.val + 1 = j.val from rfl))] at hstep
    have h' : (p i).val + 1 = (p j).val ∨ (p j).val + 1 = (p i).val := by
      by_contra h'
      rw [if_neg h'] at hstep
      contradiction
    rw [ha _ h, ha _ (by omega)]
    change (↑(p j).val : ℤ) - (p i).val = 1 ∨ (↑(p j).val : ℤ) - (p i).val = -1
    rcases h' with he | he
    · left; have hh : (p i).val + 1 = ((p j).val : ℤ) := by exact_mod_cast he
      linarith
    · right; have hh : (p j).val + 1 = ((p i).val : ℤ) := by exact_mod_cast he
      linarith
  have nowrap (k : ℕ) (h : k+2 < n) : a (k+2) ≠ a k := by
    rw [ha _ h, ha _ (by omega)]
    intro he
    have hval : (p ⟨k+2,h⟩).val = (p ⟨k,by omega⟩).val := by exact_mod_cast he
    have hh := congrArg Fin.val (p.injective (Fin.ext hval))
    change k+2 = k at hh
    omega
  let d := a 1 - a 0
  have hd (k : ℕ) (h : k+1 < n) : a (k+1) - a k = d := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have h1 := ih (by omega)
      have h2 := step (k+1) h
      have h3 := step k (by omega)
      have h4 := nowrap k h
      change a (k+1+1) ≠ a k at h4
      change a (k+1+1) - a (k+1) = d
      omega
  have hline (k : ℕ) (h : k < n) : a k = a 0 + k * d := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := ih (by omega)
      have h2 := hd k h
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, ← h1]
      omega
  have lo (k : ℕ) (hk : k < n) : 0 ≤ a k := by rw [ha _ hk]; positivity
  have hi (k : ℕ) (hk : k < n) : a k < (n : ℤ) := by
    rw [ha _ hk]; exact_mod_cast (p ⟨k,hk⟩).isLt
  have hlast : n-1 < n := by omega
  have tend := hline (n-1) hlast
  have low := lo (n-1) hlast
  have high := hi (n-1) hlast
  have low₀ := lo 0 (by omega)
  have high₀ := hi 0 (by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at tend
  rcases step 0 (by omega) with hs | hs
  · left
    change d = 1 at hs
    rw [hs, mul_one] at tend
    have hz : a 0 = 0 := by omega
    ext i
    have he := hline i.val i.isLt
    rw [hs, mul_one, ha _ i.isLt, hz, zero_add] at he
    exact_mod_cast he
  · right
    change d = -1 at hs
    rw [hs, mul_neg_one] at tend
    have hz : a 0 = n-1 := by omega
    ext i
    have he := hline i.val i.isLt
    rw [hs, mul_neg_one, ha _ i.isLt, hz] at he
    change (p i).val = n - (i.val + 1)
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_sub (by omega : i.val+1 ≤ n), Nat.cast_add, Nat.cast_one]
    change ((p i).val : ℤ) = n - 1 + -(i.val : ℤ) at he
    linarith

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ClassicalConstituentWeyl ClassicalConstituentDiagram WeylDualityObstruction

/-- Without a Weyl negation every opposition word for a numbered A-chain
acts on its simple nodes by the specified reversal. -/
theorem type_A_opposition_eq_rev {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] [IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (b : (rootSystem H).Base) {n : ℕ} (s : b.support ≃ Fin n)
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n)
    (hn : ¬ ∃ w : List H.root, ∀ z : H, applyWord H w z = -z)
    (w : List H.root) (δ : Equiv.Perm b.support)
    (hd : ∀ i z, (δ i).val.val z = -i.val.val (cartanWord H w z)) :
    ∀ i, s (δ i) = (s i).rev := by
  let σ := s.symm.trans (δ.trans s)
  have hc := cartan_preserved_of_dual_word H b w δ hd
  have hA (i j : Fin n) : CartanMatrix.A n (σ i) (σ j) = CartanMatrix.A n i j := by
    rw [← hm]
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, σ, Equiv.trans_apply, s.symm_apply_apply]
      using hc (s.symm i) (s.symm j)
  rcases type_A_path_permutation σ hA with hid | hrev
  · exfalso
    have hi (i : b.support) : δ i = i := by
      apply s.injective
      have he := DFunLike.congr_fun hid (s i)
      simpa only [σ, Equiv.trans_apply, Equiv.refl_apply, s.symm_apply_apply] using he
    apply hn
    refine ⟨w, fun z => ?_⟩
    have hword (l : List H.root) (x : H) : applyWord H l x = cartanWord H l x := by
      induction l generalizing x with
      | nil => rfl
      | cons j l ih => exact ih _
    rw [hword]
    apply (Module.evalEquiv ℂ H).injective
    apply b.toWeightBasis.ext
    intro i
    change (b.toWeightBasis i) (cartanWord H w z) = (b.toWeightBasis i) (-z)
    rw [b.toWeightBasis_apply, map_neg]
    change i.val.val (cartanWord H w z) = -i.val.val z
    have hz := hd i z
    rw [hi] at hz
    linear_combination hz
  · intro i
    have he := DFunLike.congr_fun hrev (s i)
    simpa only [σ, Equiv.trans_apply, s.symm_apply_apply, Fin.revPerm_apply] using he

end CubicAnomaly.Classification.TypeADiagramOpposition
