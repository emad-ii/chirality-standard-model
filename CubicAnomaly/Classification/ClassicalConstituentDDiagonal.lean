import CubicAnomaly.Classification.ClassicalConstituentDiagonal

/-!
# The inverse Cartan diagonal of an orthogonal singleton in type D

The column at a chain node has diagonal entry equal to its one-based index.
At a fork node that entry is one quarter of the rank. Testing either column
against the actual first-lowering root forces the defining vector weight.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentDDiagonal

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentDiagonal

private theorem apply_D (n : ℕ) (hn : 5 ≤ n) (q : ℕ → ℤ) (l : Fin n) :
    ∑ k, q k.val * CartanMatrix.D n k l =
      if n ≤ l.val+2 then 2*q l.val-q (n-3)
      else 2*q l.val - (if l.val = 0 then 0 else q (l.val-1)) - q (l.val+1) -
        (if l.val+3=n then q (n-1) else 0) := by
  let p := if n ≤ l.val+2 then n-3 else previous n l.val
  let t := if l.val+3 ≤ n then l.val+1 else n
  let u := if l.val+3 = n then n-1 else n
  have hh := apply_sparse n (CartanMatrix.D n) q l p t u (by
    intro k
    have hk := k.isLt
    have hl := l.isLt
    simp only [CartanMatrix.D, Matrix.of_apply, previous, Fin.ext_iff, p,t,u]
    split_ifs <;> omega)
  rw [hh]
  have hl := l.isLt
  simp only [p,t,u,previous]
  split_ifs <;> omega

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

/-- A positive singleton in type D whose first lowering is a root is the
first fundamental weight, for every rank at least five. -/
theorem D_diagonal {n : ℕ} (hn : 5 ≤ n) (e : Fin n ≃ b.support)
    (j : Fin n) (a : ℕ) (ha : 0 < a) (χ : H → ℂ)
    (hl : ∀ k, χ (coroot (e k).val.val) = if k=j then (a:ℂ) else 0)
    (γ : H.root) (hγ : ∀ x, γ.val x = 2*χ x - (e j).val.val x)
    (hD : ∀ i k, b.cartanMatrix (e i) (e k) = CartanMatrix.D n i k) :
    j.val = 0 ∧ a = 1 := by
  have hs (i k : b.support) : b.cartanMatrix i k = b.cartanMatrix k i := by
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨k,rfl⟩ := e.surjective k
    rw [hD,hD]
    simp only [CartanMatrix.D,Matrix.of_apply,Fin.ext_iff]
    grind
  by_cases hj : j.val+3 ≤ n
  · let q (k : ℕ) : ℤ := if k+3 ≤ n then 2 * ((min j.val k : ℕ) + 1 : ℕ) else j.val + 1
    have hq (l : Fin n) : ∑ k : Fin n, q k.val * b.cartanMatrix (e k) (e l) =
        if l=j then 2 else 0 := by
      simp only [hD]
      rw [apply_D n hn]
      have hl := l.isLt
      simp only [q,Fin.ext_iff]
      split_ifs <;> omega
    have ht := singleton_inverse_column H b e j a ha χ hl γ hγ hs (fun k => q k.val) 2 hq
    have hqj : q j.val = 2*((j.val:ℤ)+1) := by simp [q,hj]
    change (a:ℤ) * q j.val = 2 at ht
    rw [hqj] at ht
    have he : (a:ℤ)*((j.val:ℤ)+1) = 1 := by nlinarith
    have he' : a * (j.val+1) = 1 := by exact_mod_cast he
    have jle : j.val+1 ≤ 1 := (Nat.le_mul_of_pos_left _ ha).trans_eq he'
    have ale : a ≤ 1 := (Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ j.val)).trans_eq he'
    omega
  · let q (k : ℕ) : ℤ := if k+3 ≤ n then 2*((k:ℤ)+1) else
        if k=j.val then n else (n:ℤ)-2
    have hq (l : Fin n) : ∑ k : Fin n, q k.val * b.cartanMatrix (e k) (e l) =
        if l=j then 4 else 0 := by
      simp only [hD]
      rw [apply_D n hn]
      have hl := l.isLt
      have hbj := j.isLt
      simp only [q,Fin.ext_iff]
      split_ifs <;> omega
    have ht := singleton_inverse_column H b e j a ha χ hl γ hγ hs (fun k => q k.val) 4 hq
    simp only [q,hj,if_false,if_true] at ht
    have hn' : a*n = 4 := by exact_mod_cast ht
    have hle : n ≤ a*n := Nat.le_mul_of_pos_left n ha
    omega

end CubicAnomaly.Classification.ClassicalConstituentDDiagonal
