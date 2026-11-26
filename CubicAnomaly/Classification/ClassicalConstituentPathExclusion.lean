import CubicAnomaly.Classification.ClassicalConstituentPathRoot
import CubicAnomaly.Classification.ClassicalConstituentCompact

/-!
# Exclusion of proper straight support paths

A compact orthogonal model has only two nonadjoint irreducible
constituents. Three nonroot highest weights cannot occur in its skew
algebra. On a simply laced diagram this first bounds the defining
module's support by two nodes. The additional alternating-square
highest weight rules out proper straight paths with unit end labels.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentPathExclusion

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ClassicalConstituentWeights ClassicalConstituentHighest ClassicalConstituentCompact
open ClassicalConstituentPath ClassicalConstituentPathRoot CompactOperatorModel Structural
open scoped TensorProduct

set_option linter.unusedSectionVars false

variable {g W : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)] [IsSimple ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    [AddCommGroup W] [Module ℂ W] [LieRingModule (ℂ ⊗[ℝ] h) W]
    [LieModule ℂ (ℂ ⊗[ℝ] h) W] [FiniteDimensional ℂ W] [IsIrreducible ℂ (ℂ ⊗[ℝ] h) W]
    (β : LinearMap.BilinForm ℂ W) (A : Model h β) (hnd : β.Nondegenerate)
    (hi : β.lieInvariant (ℂ ⊗[ℝ] h)) (hsym : β.IsSymm)
    {χ : H → ℂ} {v : W} (hv : IsHighestVector H b χ v)

include hnd hi hsym hv in
private theorem first_highest (i : b.support) (a : ℕ) (ha : 1 ≤ a) (hl : χ (coroot i.val.val) = (a : ℂ)) :
    HasSkewHighestWeight H b β (fun x => 2 * χ x - i.val.val x) := by
  letI := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) W
  obtain ⟨μ,u,l,hu,hw,hr,hs⟩ := orthogonal_support_weights H b β hnd hi hsym
  have he := (irreducible_highest_weight_unique H b hv
    (show IsHighestVector H b μ u from ⟨hu,hw,hr⟩)).2
  subst χ
  have hc := (hs i).1.symm.trans hl
  have he' : (l i : ℕ) = a := by exact_mod_cast hc
  exact (hs i).2.1 (he' ▸ ha)

include hp e A in
private theorem at_most_two_nonroot_highest :
    ∃ p q : H → ℂ, ∀ f : H → ℂ, HasSkewHighestWeight H b β f →
      (¬∃ r : H.root, ∀ x, r.val x = f x) → f = p ∨ f = q := by
  letI := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) W
  obtain ⟨θ,p,q,⟨u,hu⟩,_,_,hall⟩ := compact_model_highest_weights B h hp e H b A
  obtain ⟨γ,hγ,_,_⟩ := adjoint_highest_is_maximal_root H b hu
  refine ⟨p,q,fun f hf hnr => (hall _ hf).resolve_left ?_⟩
  rintro rfl
  exact hnr ⟨γ,congrFun hγ⟩

private theorem shift_injective : Function.Injective (fun (i : b.support) (x : H) => 2 * χ x - i.val.val x) := by
  intro i j he
  apply Subtype.ext
  apply Subtype.ext
  exact Weight.ext fun x => sub_right_inj.mp (congrFun he x)

include hp e A hnd hi hsym hv in
/-- At most two simple-root labels can be positive in an orthogonal
model over a symmetric Cartan matrix, independently of the rank. -/
theorem no_three_positive_labels (hs : ∀ i j, b.cartanMatrix i j = b.cartanMatrix j i)
    (a : b.support → ℕ) (hl : ∀ i, χ (coroot i.val.val) = (a i : ℂ))
    (i j k : b.support) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hi' : 1 ≤ a i) (hj' : 1 ≤ a j) (hk' : 1 ≤ a k) : False := by
  let shift := fun (l : b.support) (x : H) => 2 * χ x - l.val.val x
  obtain ⟨p,q,hall⟩ := at_most_two_nonroot_highest B h hp e H b β A
  have two (l m n : b.support) (hlm : l ≠ m) (hln : l ≠ n) (hmn : m ≠ n)
      (il : 1 ≤ a l) (im : 1 ≤ a m) (in' : 1 ≤ a n) : shift l = p ∨ shift l = q := by
    apply hall _ (first_highest h H b β hnd hi hsym hv l _ il (hl l))
    rintro ⟨γ,hγ⟩
    have h₁ := first_shift_root_eq_other H b l m hs hlm _ im (hl m) hγ
    have h₂ := first_shift_root_eq_other H b l n hs hln _ in' (hl n) hγ
    exact hmn (Subtype.ext (h₁.symm.trans h₂))
  have ti := two i j k hij hki.symm hjk hi' hj' hk'
  have tj := two j k i hjk hij.symm hki hj' hk' hi'
  have tk := two k i j hki hjk.symm hij hk' hi' hj'
  have inj : Function.Injective shift := shift_injective h H b
  rcases ti with ti|ti <;> rcases tj with tj|tj <;> rcases tk with tk|tk <;>
    first | exact hij (inj (ti.trans tj.symm)) | exact hjk (inj (tj.trans tk.symm)) |
      exact hki (inj (tk.trans ti.symm))

include hp e A hnd hi hsym hv in
/-- End labels one on a proper path of three, four or five simple
nodes are incompatible with the compact orthogonal decomposition.
A negative column sum witnesses adjacency of a node outside the path. -/
theorem no_proper_path_unit_ends {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (s : Fin n ↪ b.support) (hA : ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.A n i j)
    (hs : ∀ i j, b.cartanMatrix i j = b.cartanMatrix j i)
    (a : b.support → ℕ) (hl : ∀ i, χ (coroot i.val.val) = (a i : ℂ))
    (hends : ∀ i : Fin n, i.val = 0 ∨ i.val + 1 = n → a (s i) = 1)
    (k : b.support) (hadj : ((List.finRange n).map (fun i => b.cartanMatrix (s i) k)).sum < 0) : False := by
  let u : Fin n := ⟨0,by omega⟩
  let t : Fin n := ⟨1,by omega⟩
  let w : Fin n := ⟨n-1,by omega⟩
  have huw : s u ≠ s w := by intro he; have := congrArg Fin.val (s.injective he); dsimp [u,w] at this; omega
  have au := hends u (Or.inl rfl)
  have aw := hends w (Or.inr (by dsimp [w]; omega))
  have hunit (i : Fin n) : χ (coroot (s i).val.val) = if i.val = 0 ∨ i.val+1 = n then 1 else 0 := by
    split_ifs with he
    · rw [hl,hends _ he,Nat.cast_one]
    · have h₁ : s i ≠ s u := by intro h; exact he (Or.inl (congrArg Fin.val (s.injective h)))
      have h₂ : s w ≠ s i := by
        intro h
        have hi := congrArg Fin.val (s.injective h)
        apply he
        right
        dsimp [w] at hi
        omega
      rw [hl]
      suffices a (s i) = 0 by simp [this]
      by_contra! hpos
      exact no_three_positive_labels B h hp e H b β A hnd hi hsym hv hs a hl (s u) (s w) (s i)
        huw h₂ h₁ (by omega) (by omega) (by omega)
  have hnear : b.cartanMatrix (s u) (s t) + b.cartanMatrix (s w) (s t) < 0 := by
    rcases hn with rfl|rfl|rfl <;> norm_num [hA,u,t,w,CartanMatrix.A,Fin.ext_iff]
  let shift := fun (i : b.support) (x : H) => 2 * χ x - i.val.val x
  let full := fun x : H => 2 * χ x - ((List.finRange n).map (fun i => (s i).val.val x)).sum
  obtain ⟨p,q,hall⟩ := at_most_two_nonroot_highest B h hp e H b β A
  have hu : shift (s u) = p ∨ shift (s u) = q :=
    hall _ (first_highest h H b β hnd hi hsym hv _ _ (by omega) (hl _))
      (first_shift_not_root_of_neighbor H b (s u) (s w) (s t) hs huw _ _ (by omega) (hl _) (hl _) hnear)
  have hw : shift (s w) = p ∨ shift (s w) = q :=
    hall _ (first_highest h H b β hnd hi hsym hv _ _ (by omega) (hl _))
      (first_shift_not_root_of_neighbor H b (s w) (s u) (s t) hs huw.symm _ _ (by omega) (hl _) (hl _)
        (by rwa [add_comm]))
  have hz : full = p ∨ full = q := hall _
    (orthogonal_path_weight H b β hnd hi hsym χ v hv.1 hv.2.1 hv.2.2 (Or.inr hn) s hA hunit)
    (proper_path_shift_not_root H b (Or.inr hn) s hA hs χ hunit k _ (hl k) hadj)
  have neq : shift (s u) ≠ shift (s w) := fun he => huw (shift_injective h H b he)
  obtain ⟨y,hy⟩ := ExceptionalSieveWeights.exists_height_element H b
  have one (i : b.support) : i.val.val y = 1 := by rw [hy, b.height_one_of_mem_support i.property, Int.cast_one]
  have hdist (i : b.support) : full ≠ shift i := by
    intro he
    have hh := congrFun he y
    change 2 * χ y - ((List.finRange n).map fun j => (s j).val.val y).sum = 2 * χ y - i.val.val y at hh
    simp only [one,sub_right_inj] at hh
    rcases hn with rfl|rfl|rfl <;> norm_num [List.finRange_succ] at hh
  rcases hu with hu|hu <;> rcases hw with hw|hw <;> rcases hz with hz|hz <;>
    first | exact neq (hu.trans hw.symm) | exact hdist _ (hz.trans hu.symm) | exact hdist _ (hz.trans hw.symm)

end CubicAnomaly.Classification.ClassicalConstituentPathExclusion
