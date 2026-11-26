import CubicAnomaly.Classification.ClassicalConstituentPathRoot

/-!
# The inverse Cartan diagonal at a singleton orthogonal support

If the only positive Dynkin label is a at a node j, the first lowering
has weight twice the defining weight minus the simple root j. If it is
a root, the normalization of a root on its own coroot implies that
a times the jth diagonal entry of the inverse Cartan matrix equals one.
Integer multiples of an inverse column suffice for the calculation.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentDiagonal

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentPathRoot

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

/-- An integral multiple of an inverse Cartan column tests a singleton
highest label. The kernel of the argument is the identity
γ(coroot γ)=2 for the actual first-lowering root γ. -/
theorem singleton_inverse_column {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ b.support)
    (j : ι) (a : ℕ) (ha : 0 < a) (χ : H → ℂ)
    (hl : ∀ k, χ (coroot (e k).val.val) = if k = j then (a : ℂ) else 0)
    (γ : H.root) (hγ : ∀ x, γ.val x = 2 * χ x - (e j).val.val x)
    (hs : ∀ i k, b.cartanMatrix i k = b.cartanMatrix k i)
    (q : ι → ℤ) (d : ℤ)
    (hq : ∀ l, ∑ k, q k * b.cartanMatrix (e k) (e l) = if l = j then d else 0) :
    (a : ℤ) * q j = d := by
  classical
  let P := rootSystem H
  let C := b.toCoweightBasis.reindex e.symm
  have co (k : ι) : C k = P.coroot (e k) := by simp [C]; rfl
  let T := C.repr (P.coroot γ)
  have eval (f : Dual ℂ H) : f (P.coroot γ) = ∑ k, T k * f (C k) := by
    conv_lhs => rw [← C.sum_repr (P.coroot γ)]
    simp only [map_sum,map_smul,smul_eq_mul,T]
  let g := P.root γ + P.root (e j)
  have gg (x : H) : g x = 2 * χ x := by
    change γ.val x + (e j).val.val x = _
    rw [hγ]; ring
  have gl (k : ι) : g (C k) = if k=j then 2*(a:ℂ) else 0 := by
    rw [gg,co]
    change 2 * χ (coroot (e k).val.val) = _
    rw [hl]
    split_ifs <;> ring
  have tj : T j = 1 := by
    have he := eval g
    rw [show g (P.coroot γ) = P.pairing γ γ + P.pairing (e j) γ from rfl, P.pairing_same,
      pairing_symmetric_of_cartan_symmetric H b hs (e j) γ] at he
    change 2 + γ.val (coroot (e j).val.val) = _ at he
    rw [hγ,hl,if_pos rfl,root_apply_coroot (Finset.mem_filter.mp (e j).val.property).2] at he
    simp only [gl,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] at he
    have hne : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    apply (mul_left_injective₀ hne)
    linear_combination -he/2
  let f : Dual ℂ H := ∑ k, (q k : ℂ) • P.root (e k)
  have fl (l : ι) : f (C l) = if l=j then (d:ℂ) else 0 := by
    have hh := congrArg (fun x : ℤ => (x : ℂ)) (hq l)
    push_cast at hh
    simp only [f,co,LinearMap.sum_apply, LinearMap.smul_apply,smul_eq_mul]
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro k _
      rw [show (P.root (e k)) (P.coroot (e l)) = (b.cartanMatrix (e k) (e l) : ℂ) from
        (b.algebraMap_cartanMatrixIn_apply ℤ _ _).symm]
  have fd : f (P.coroot γ) = (d : ℂ) := by
    rw [eval f]
    simp [fl,mul_ite,tj]
  let z := ∑ k, (q k : ℂ) • C k
  have act (i : H.root) : (P.root i) z = f (P.coroot i) := by
    simp only [z,f,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,co]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg ((q k:ℂ) * ·) (pairing_symmetric_of_cartan_symmetric H b hs i (e k))
  have hz : g z = (d : ℂ) + d := by
    change (P.root γ) z + (P.root (e j)) z = _
    rw [act,act,fd,← co j,fl,if_pos rfl]
  have eqn := hz
  simp only [z,map_sum,map_smul,smul_eq_mul,gl,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] at eqn
  have h : (a : ℂ) * (q j : ℂ) = (d : ℂ) := by linear_combination eqn/2
  exact_mod_cast h

/-- Index of the predecessor, with the rank used as an absent index. -/
def previous (n l : ℕ) := if l = 0 then n else l-1

/-- Evaluate a Cartan column with at most three distinct neighbours.
An index at or above the rank contributes zero. -/
theorem apply_sparse (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (q : ℕ → ℤ)
    (l : Fin n) (p t u : ℕ) (hC : ∀ k, C k l =
      (if k = l then 2 else 0) - (if k.val=p then 1 else 0) -
      (if k.val=t then 1 else 0) - (if k.val=u then 1 else 0)) :
    ∑ k, q k.val * C k l = 2*q l.val -
      (if p<n then q p else 0) - (if t<n then q t else 0) - (if u<n then q u else 0) := by
  have select (m : ℕ) : (∑ k : Fin n, if k.val=m then q k.val else 0) =
      if m<n then q m else 0 := by
    split_ifs with hm
    · let i : Fin n := ⟨m,hm⟩
      have hk (k : Fin n) : k.val=m ↔ k=i := ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp_rw [hk]
      simp [i]
    · apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (by have := k.isLt; omega)]
  simp only [hC,mul_sub,mul_ite,mul_zero,mul_one,Finset.sum_sub_distrib,select,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,mul_comm]

private theorem apply_A (n : ℕ) (q : ℕ → ℤ) (l : Fin n) :
    ∑ k, q k.val * CartanMatrix.A n k l = 2*q l.val -
      (if previous n l.val < n then q (previous n l.val) else 0) -
      (if l.val+1 < n then q (l.val+1) else 0) := by
  have h := apply_sparse n (CartanMatrix.A n) q l (previous n l.val) (l.val+1) n (by
    intro k
    have hk := k.isLt; have hl := l.isLt
    simp only [CartanMatrix.A, Matrix.of_apply,previous,Fin.ext_iff]
    split_ifs <;> omega)
  simpa using h

/-- At the center of A of rank 2r+1, a singleton highest label with
adjoint first lowering satisfies a(r+1)=2. -/
theorem middle_A_diagonal {n : ℕ} (r : ℕ) (hn : n = 2*r+1) (e : Fin n ≃ b.support)
    (j : Fin n) (hj : j.val = r) (a : ℕ) (ha : 0 < a) (χ : H → ℂ)
    (hl : ∀ k, χ (coroot (e k).val.val) = if k = j then (a : ℂ) else 0)
    (γ : H.root) (hγ : ∀ x, γ.val x = 2 * χ x - (e j).val.val x)
    (hA : ∀ i k, b.cartanMatrix (e i) (e k) = CartanMatrix.A n i k) :
    a*(r+1) = 2 := by
  let q := fun k : ℕ => (min (k+1) (n-k) : ℕ)
  have hq (l : Fin n) : ∑ k : Fin n, (q k.val : ℤ) * b.cartanMatrix (e k) (e l) =
      if l=j then 2 else 0 := by
    simp only [hA]
    rw [apply_A n (fun i => (q i : ℤ))]
    have hh := l.isLt
    simp only [previous,q,Fin.ext_iff]
    split_ifs <;> omega
  have hs (i k : b.support) : b.cartanMatrix i k = b.cartanMatrix k i := by
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨k,rfl⟩ := e.surjective k
    rw [hA,hA]; exact (CartanMatrix.A_isSymm n).apply _ _
  have h := singleton_inverse_column H b e j a ha χ hl γ hγ hs (fun k => q k.val) 2 hq
  have hj' : q j.val = r+1 := by dsimp [q]; omega
  change (a : ℤ) * (q j.val : ℤ) = 2 at h
  rw [hj'] at h
  exact_mod_cast h

end CubicAnomaly.Classification.ClassicalConstituentDiagonal
