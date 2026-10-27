import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

/-!
# Root-lattice steps in the full-rank reduction

The saturation theorem below is uniform in the dimension and the number of
roots.  It proves the root-lattice assertion used in the manuscript from the
root-string subtraction property and the definition of a closed subsystem.
For an actual finite crystallographic `RootPairing`, Mathlib supplies both
the subtraction property and a positive root form, so only the subsystem's
closure properties remain as hypotheses.

The hypotheses are stated explicitly for subsets of a real inner-product
space.  This file does not identify those subsets with the root spaces of a
compact Lie-algebra pair, or prove the representation-theoretic argument
producing a nonzero bracket of two grade-one spaces.
-/

namespace CubicAnomaly.Classification.RootReduction

open scoped InnerProductSpace

private theorem positive_member_of_positive_list_sum (xs : List ℝ)
    (h : 0 < xs.sum) : ∃ x ∈ xs, 0 < x := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : 0 < x
      · exact ⟨x, by simp, hx⟩
      · have hxs : 0 < xs.sum := by
          simp only [List.sum_cons] at h
          linarith
        obtain ⟨y, hy, hpos⟩ := ih hxs
        exact ⟨y, by simp [hy], hpos⟩

private theorem list_sum_bilinear_right {E : Type*}
    [AddCommGroup E] [Module ℝ E] (B : LinearMap.BilinForm ℝ E)
    (a : E) (xs : List E) :
    (xs.map (fun x => B a x)).sum = B a xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem list_sum_neg {E : Type*} [AddCommGroup E] (xs : List E) :
    (xs.map (fun x => -x)).sum = -xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_comm]

private theorem subgroup_closure_has_list_expression {E : Type*}
    [AddCommGroup E] (Ψ : Set E)
    (hneg : ∀ x ∈ Ψ, -x ∈ Ψ) {a : E}
    (ha : a ∈ AddSubgroup.closure Ψ) :
    ∃ xs : List E, (∀ x ∈ xs, x ∈ Ψ) ∧ xs.sum = a := by
  let sums : AddSubgroup E := {
    carrier := {x | ∃ xs : List E, (∀ y ∈ xs, y ∈ Ψ) ∧ xs.sum = x}
    zero_mem' := ⟨[], by simp, by simp⟩
    add_mem' := by
      rintro a b ⟨xs, hxs, rfl⟩ ⟨ys, hys, rfl⟩
      refine ⟨xs ++ ys, ?_, by simp⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hxs x hx
      · exact hys x hx
    neg_mem' := by
      rintro a ⟨xs, hxs, rfl⟩
      refine ⟨xs.map (fun x => -x), ?_, list_sum_neg xs⟩
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hneg y (hxs y hy)
  }
  have hsub : AddSubgroup.closure Ψ ≤ sums :=
    (AddSubgroup.closure_le sums).mpr (by
      intro x hx
      exact ⟨[x], by simpa using hx, by simp⟩)
  exact hsub ha

private theorem root_list_sum_mem_closed {E : Type*}
    [AddCommGroup E] [Module ℝ E] (B : LinearMap.BilinForm ℝ E)
    (Φ Ψ : Set E) (hpositive : ∀ a ∈ Φ, 0 < B a a) (hsub : Ψ ⊆ Φ)
    (hroot : ∀ a ∈ Φ, ∀ b ∈ Φ,
      a ≠ b → 0 < B a b → a - b ∈ Φ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ, a + b ∈ Φ → a + b ∈ Ψ)
    (xs : List E) (hxs : ∀ x ∈ xs, x ∈ Ψ)
    (hsum : xs.sum ∈ Φ) : xs.sum ∈ Ψ := by
  suffices ∀ n, ∀ ys : List E, ys.length = n →
      (∀ y ∈ ys, y ∈ Ψ) → ys.sum ∈ Φ → ys.sum ∈ Ψ by
    exact this xs.length xs rfl hxs hsum
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro ys hlen hys hsum
      have hpositiveSum : 0 < (ys.map (fun y => B ys.sum y)).sum := by
        rw [list_sum_bilinear_right]
        exact hpositive ys.sum hsum
      obtain ⟨t, ht, htpos⟩ := positive_member_of_positive_list_sum _ hpositiveSum
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
      by_cases heq : ys.sum = b
      · simpa only [heq] using hys b hb
      obtain ⟨left, right, hsplit⟩ := List.append_of_mem hb
      have hshort : (left ++ right).length < n := by
        rw [hsplit] at hlen
        simp only [List.length_append, List.length_cons] at hlen ⊢
        omega
      have hsumremove : (left ++ right).sum + b = ys.sum := by
        rw [hsplit]
        simp only [List.sum_append, List.sum_cons]
        abel
      have hremove : (left ++ right).sum = ys.sum - b := by
        exact (eq_sub_iff_add_eq).mpr hsumremove
      have hremoveΦ : (left ++ right).sum ∈ Φ := by
        rw [hremove]
        exact hroot ys.sum hsum b (hsub (hys b hb)) heq htpos
      have hremoveΨ : (left ++ right).sum ∈ Ψ := by
        apply ih _ hshort (left ++ right) rfl
        · intro x hx
          apply hys x
          rw [hsplit]
          simp only [List.mem_append, List.mem_cons] at hx ⊢
          tauto
        · exact hremoveΦ
      have hresult := hclosed _ hremoveΨ b (hys b hb)
        (by simpa only [hsumremove] using hsum)
      simpa only [hsumremove] using hresult

/-- Saturation in a bilinear-form formulation, requiring positivity only on
ambient roots.  This also applies to Mathlib's canonical root form. -/
theorem bilinear_closed_root_subsystem_saturated {E : Type*}
    [AddCommGroup E] [Module ℝ E] (B : LinearMap.BilinForm ℝ E)
    (Φ Ψ : Set E) (hpositive : ∀ a ∈ Φ, 0 < B a a) (hsub : Ψ ⊆ Φ)
    (hroot : ∀ a ∈ Φ, ∀ b ∈ Φ,
      a ≠ b → 0 < B a b → a - b ∈ Φ)
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ, a + b ∈ Φ → a + b ∈ Ψ) :
    Φ ∩ (AddSubgroup.closure Ψ : Set E) = Ψ := by
  apply Set.Subset.antisymm
  · rintro a ⟨haΦ, haL⟩
    obtain ⟨xs, hxs, rfl⟩ := subgroup_closure_has_list_expression Ψ hneg haL
    exact root_list_sum_mem_closed B Φ Ψ hpositive hsub hroot hclosed xs hxs haΦ
  · intro a ha
    exact ⟨hsub ha, AddSubgroup.subset_closure ha⟩

/-- A closed root subsystem contains every ambient root in its root lattice.

`hroot` is the root-string consequence that distinct roots with positive
inner product have a root as their difference.  No finiteness or rank bound
is imposed.  `AddSubgroup.closure Ψ` is the integer span of `Ψ`.
-/
theorem closed_root_subsystem_saturated {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Φ Ψ : Set E) (hzero : (0 : E) ∉ Φ) (hsub : Ψ ⊆ Φ)
    (hroot : ∀ a ∈ Φ, ∀ b ∈ Φ,
      a ≠ b → 0 < ⟪a, b⟫_ℝ → a - b ∈ Φ)
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ, a + b ∈ Φ → a + b ∈ Ψ) :
    Φ ∩ (AddSubgroup.closure Ψ : Set E) = Ψ := by
  apply bilinear_closed_root_subsystem_saturated (innerₗ E) Φ Ψ _ hsub hroot hneg hclosed
  intro a ha
  exact real_inner_self_pos.mpr (fun hz => hzero (hz ▸ ha))

/-- Saturation for an actual finite crystallographic `RootPairing`.

The root-string subtraction property and the positive root form are supplied
by Mathlib.  Only the defining closure properties of the subsystem are
hypotheses; no bound on the root-system rank is imposed.
-/
theorem crystallographic_closed_root_subsystem_saturated
    {ι M N : Type*} [Finite ι] [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsCrystallographic]
    (Ψ : Set M) (hsub : Ψ ⊆ Set.range P.root)
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ Set.range P.root → a + b ∈ Ψ) :
    Set.range P.root ∩ (AddSubgroup.closure Ψ : Set M) = Ψ := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hpositive (i : ι) : 0 < P.RootForm (P.root i) (P.root i) :=
    P.rootForm_pos_of_ne_zero (Submodule.subset_span (Set.mem_range_self i)) (P.ne_zero i)
  apply bilinear_closed_root_subsystem_saturated P.RootForm (Set.range P.root) Ψ _
    hsub _ hneg hclosed
  · rintro a ⟨i, rfl⟩
    exact hpositive i
  · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ hne hpos
    apply P.root_sub_root_mem_of_pairingIn_pos _
      (fun hij => hne (congrArg P.root hij))
    have heq := P.toInvariantForm.two_mul_apply_root_root i j
    change 2 * P.RootForm (P.root i) (P.root j) =
      P.pairing i j * P.RootForm (P.root j) (P.root j) at heq
    have hpair : 0 < P.pairing i j := by
      apply (mul_pos_iff_of_pos_right (hpositive j)).mp
      rw [← heq]
      positivity
    rw [← P.algebraMap_pairingIn ℤ i j] at hpair
    change (0 : ℝ) < (P.pairingIn ℤ i j : ℝ) at hpair
    exact_mod_cast hpair

/-- A proper closed subsystem of a finite crystallographic root pairing has
a strictly smaller integer root lattice. -/
theorem crystallographic_proper_closed_root_subsystem_lattice_ne
    {ι M N : Type*} [Finite ι] [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsCrystallographic]
    (Ψ : Set M) (hsub : Ψ ⊆ Set.range P.root)
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ Set.range P.root → a + b ∈ Ψ)
    (hne : Ψ ≠ Set.range P.root) :
    AddSubgroup.closure Ψ ≠ AddSubgroup.closure (Set.range P.root) := by
  intro heq
  apply hne
  apply Set.Subset.antisymm hsub
  intro a ha
  have hsat := crystallographic_closed_root_subsystem_saturated P Ψ hsub hneg hclosed
  have haL : a ∈ AddSubgroup.closure Ψ := by
    rw [heq]
    exact AddSubgroup.subset_closure ha
  have : a ∈ Set.range P.root ∩ (AddSubgroup.closure Ψ : Set M) := ⟨ha, haL⟩
  simpa only [hsat] using this

/-- A proper closed root subsystem has a proper root lattice. -/
theorem proper_closed_root_subsystem_lattice_ne {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Φ Ψ : Set E) (hzero : (0 : E) ∉ Φ) (hsub : Ψ ⊆ Φ)
    (hroot : ∀ a ∈ Φ, ∀ b ∈ Φ,
      a ≠ b → 0 < ⟪a, b⟫_ℝ → a - b ∈ Φ)
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ, a + b ∈ Φ → a + b ∈ Ψ)
    (hne : Ψ ≠ Φ) : AddSubgroup.closure Ψ ≠ AddSubgroup.closure Φ := by
  intro heq
  apply hne
  apply Set.Subset.antisymm hsub
  intro a ha
  have hsat := closed_root_subsystem_saturated Φ Ψ hzero hsub hroot hneg hclosed
  have haL : a ∈ AddSubgroup.closure Ψ := by
    rw [heq]
    exact AddSubgroup.subset_closure ha
  have : a ∈ Φ ∩ (AddSubgroup.closure Ψ : Set E) := ⟨ha, haL⟩
  simpa only [hsat] using this

/-- The non-involutive three-class bracket alternative forces order three.

In the Lie-algebra application, the final hypothesis is obtained from a
nonzero bracket of two grade-one root spaces.  That representation-theoretic
bridge is not assumed to have been formalized by this arithmetic lemma.
-/
theorem three_class_noninvolutive_nsmul {A : Type*} [AddCommGroup A]
    (c : A) (hne : c ≠ 0) (hnotTwo : 2 • c ≠ 0)
    (hclass : 2 • c = 0 ∨ 2 • c = c ∨ 2 • c = -c) :
    3 • c = 0 := by
  rcases hclass with hzero | hone | hneg
  · exact False.elim (hnotTwo hzero)
  · have hc : c = 0 := by
      have : c + c = c + 0 := by simpa only [two_nsmul, add_zero] using hone
      exact add_left_cancel this
    exact False.elim (hne hc)
  · calc
      3 • c = 2 • c + c := by simp [succ_nsmul]
      _ = -c + c := by rw [hneg]
      _ = 0 := neg_add_cancel c

/-- The nonzero grading class in the non-involutive alternative has exact
additive order three, rather than merely order dividing three. -/
theorem three_class_noninvolutive_order {A : Type*} [AddCommGroup A]
    (c : A) (hne : c ≠ 0) (hnotTwo : 2 • c ≠ 0)
    (hclass : 2 • c = 0 ∨ 2 • c = c ∨ 2 • c = -c) :
    addOrderOf c = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact addOrderOf_eq_prime (three_class_noninvolutive_nsmul c hne hnotTwo hclass) hne

end CubicAnomaly.Classification.RootReduction
