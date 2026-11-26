import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Root-lattice saturation over characteristic-zero scalar rings

The saturation argument does not need to order the ambient scalar field.
If a root `α` is the sum of roots `βⱼ`, pairing with `α`'s coroot gives
`Σ ⟨βⱼ, α∨⟩ = 2` in the integers.  One summand is positive.  Mathlib's
root-string subtraction theorem then shortens the expression.

Consequently the result applies directly to the actual complex root system of
a splitting Killing Lie algebra.  No identification of complex roots with a
separately assumed real root system is required.
-/

namespace CubicAnomaly.Classification.RootSaturation

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsCrystallographic]

omit [IsDomain R] in
/-- A root expressed as a sum of roots has total integer coroot pairing two. -/
theorem integer_pairing_sum_eq_two (xs : List ι) (i : ι)
    (hsum : (xs.map fun j => P.root j).sum = P.root i) :
    (xs.map fun j => P.pairingIn ℤ j i).sum = 2 := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  have hmap : algebraMap ℤ R ((xs.map fun j => P.pairingIn ℤ j i).sum) =
      P.coroot' i ((xs.map fun j => P.root j).sum) := by
    clear hsum
    induction xs with
    | nil => simp
    | cons j xs ih =>
        simp only [List.map_cons, List.sum_cons, map_add,
          P.algebraMap_pairingIn, P.root_coroot'_eq_pairing, ih]
  rw [hmap, hsum]
  simp

private theorem positive_member_of_positive_integer_sum (xs : List ℤ)
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

omit [IsDomain R] in
/-- Every expression of a root as a sum of roots contains a summand with
positive integer coroot pairing.  No ordering on `R` is used. -/
theorem root_sum_has_positive_pairing (xs : List ι) (i : ι)
    (hsum : (xs.map fun j => P.root j).sum = P.root i) :
    ∃ j ∈ xs, 0 < P.pairingIn ℤ j i := by
  have hpositive : 0 < (xs.map fun j => P.pairingIn ℤ j i).sum := by
    rw [integer_pairing_sum_eq_two P xs i hsum]
    norm_num
  obtain ⟨z, hz, hpos⟩ := positive_member_of_positive_integer_sum _ hpositive
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
  exact ⟨j, hj, hpos⟩

omit [IsDomain R] [CharZero R] [P.IsCrystallographic] in
private theorem subgroup_closure_has_root_list_expression
    (Ψ : Set M) (hsub : Ψ ⊆ Set.range P.root)
    (hneg : ∀ x ∈ Ψ, -x ∈ Ψ) {a : M}
    (ha : a ∈ AddSubgroup.closure Ψ) :
    ∃ xs : List ι, (∀ i ∈ xs, P.root i ∈ Ψ) ∧
      (xs.map fun i => P.root i).sum = a := by
  let sums : AddSubgroup M := {
    carrier := {x | ∃ xs : List ι, (∀ i ∈ xs, P.root i ∈ Ψ) ∧
      (xs.map fun i => P.root i).sum = x}
    zero_mem' := ⟨[], by simp, by simp⟩
    add_mem' := by
      rintro a b ⟨xs, hxs, rfl⟩ ⟨ys, hys, rfl⟩
      refine ⟨xs ++ ys, ?_, by simp⟩
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hxs i hi
      · exact hys i hi
    neg_mem' := by
      rintro a ⟨xs, hxs, rfl⟩
      refine ⟨xs.map (fun i => P.reflectionPerm i i), ?_, ?_⟩
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        simpa using hneg (P.root j) (hxs j hj)
      · clear hxs
        induction xs with
        | nil => simp
        | cons i xs ih =>
            simpa only [List.map_cons, List.sum_cons, P.root_reflectionPerm,
              P.reflection_apply_self, neg_add_rev, add_comm] using
              (congrArg (fun z => -P.root i + z) ih)
  }
  have hle : AddSubgroup.closure Ψ ≤ sums := (AddSubgroup.closure_le sums).mpr (by
    intro x hx
    obtain ⟨i, rfl⟩ := hsub hx
    exact ⟨[i], by simpa using hx, by simp⟩)
  exact hle ha

private theorem root_list_sum_mem_closed [Finite ι]
    (Ψ : Set M)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ Set.range P.root → a + b ∈ Ψ)
    (xs : List ι) (hxs : ∀ i ∈ xs, P.root i ∈ Ψ)
    (i : ι) (hsum : (xs.map fun j => P.root j).sum = P.root i) : P.root i ∈ Ψ := by
  suffices ∀ n, ∀ ys : List ι, ys.length = n →
      (∀ j ∈ ys, P.root j ∈ Ψ) → ∀ i : ι,
        (ys.map fun j => P.root j).sum = P.root i → P.root i ∈ Ψ by
    exact this xs.length xs rfl hxs i hsum
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro ys hlen hys i hsum
      obtain ⟨j, hj, hpos⟩ := root_sum_has_positive_pairing P ys i hsum
      by_cases heq : P.root i = P.root j
      · simpa only [heq] using hys j hj
      have hpos' : 0 < P.pairingIn ℤ i j :=
        (P.zero_lt_pairingIn_iff' ℤ (i := j) (j := i)).mp hpos
      obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hpos'
        (fun hij => heq (congrArg P.root hij))
      obtain ⟨left, right, hsplit⟩ := List.append_of_mem hj
      have hshort : (left ++ right).length < n := by
        rw [hsplit] at hlen
        simp only [List.length_append, List.length_cons] at hlen ⊢
        omega
      have hsumremove : ((left ++ right).map fun j => P.root j).sum + P.root j =
          P.root i := by
        rw [← hsum, hsplit]
        simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
        abel
      have hremove : ((left ++ right).map fun j => P.root j).sum = P.root k := by
        rw [hk]
        exact (eq_sub_iff_add_eq).mpr hsumremove
      have hkΨ : P.root k ∈ Ψ := by
        apply ih _ hshort (left ++ right) rfl _ k hremove
        intro l hl
        apply hys l
        rw [hsplit]
        simpa only [List.mem_append, List.mem_cons] using
          (List.mem_append.mp hl).elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr h))
      have hkj : P.root k + P.root j = P.root i := by rwa [hremove] at hsumremove
      have hresult := hclosed (P.root k) hkΨ (P.root j) (hys j hj)
        (by rw [hkj]; exact Set.mem_range_self i)
      simpa only [hkj] using hresult

/-- A closed subsystem of a finite crystallographic root pairing is saturated
inside the ambient roots, over any characteristic-zero integral domain.

All root-string and positivity consequences are derived by Mathlib from the
actual root pairing.  Positivity is used only for integers whose sum is two.
-/
theorem characteristic_zero_closed_root_subsystem_saturated [Finite ι]
    (Ψ : Set M) (hsub : Ψ ⊆ Set.range P.root)
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ Set.range P.root → a + b ∈ Ψ) :
    Set.range P.root ∩ (AddSubgroup.closure Ψ : Set M) = Ψ := by
  apply Set.Subset.antisymm
  · rintro a ⟨⟨i, rfl⟩, ha⟩
    obtain ⟨xs, hxs, hsum⟩ :=
      subgroup_closure_has_root_list_expression P Ψ hsub hneg ha
    exact root_list_sum_mem_closed P Ψ hclosed xs hxs i hsum
  · intro a ha
    exact ⟨hsub ha, AddSubgroup.subset_closure ha⟩

/-- A proper closed root subsystem has a proper integer root lattice over the
same general scalar rings, including `ℂ`. -/
theorem characteristic_zero_proper_closed_root_subsystem_lattice_ne [Finite ι]
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
  have hsat := characteristic_zero_closed_root_subsystem_saturated P Ψ hsub hneg hclosed
  have haL : a ∈ AddSubgroup.closure Ψ := by
    rw [heq]
    exact AddSubgroup.subset_closure ha
  have : a ∈ Set.range P.root ∩ (AddSubgroup.closure Ψ : Set M) := ⟨ha, haL⟩
  simpa only [hsat] using this

/-- Saturation is unchanged by any faithful additive realization of the roots.
This permits the linear-form roots of a Lie algebra to be used as actual weight
functions, without changing the integer lattice. -/
theorem crystallographic_closed_root_subsystem_saturated_of_injective [Finite ι]
    {G : Type*} [AddCommGroup G] (f : M →+ G) (hf : Function.Injective f)
    (Ψ : Set G) (hsub : Ψ ⊆ Set.range (fun i => f (P.root i)))
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ Set.range (fun i => f (P.root i)) → a + b ∈ Ψ) :
    Set.range (fun i => f (P.root i)) ∩ (AddSubgroup.closure Ψ : Set G) = Ψ := by
  let Ω := f ⁻¹' Ψ
  have hsub' : Ω ⊆ Set.range P.root := by
    intro x hx
    obtain ⟨i, hi⟩ := hsub hx
    exact ⟨i, hf hi⟩
  have hneg' : ∀ x ∈ Ω, -x ∈ Ω := by
    intro x hx
    change f (-x) ∈ Ψ
    simpa only [map_neg] using hneg (f x) hx
  have hclosed' : ∀ x ∈ Ω, ∀ y ∈ Ω, x + y ∈ Set.range P.root → x + y ∈ Ω := by
    intro x hx y hy hxy
    change f (x + y) ∈ Ψ
    rw [map_add]
    apply hclosed (f x) hx (f y) hy
    obtain ⟨i, hi⟩ := hxy
    exact ⟨i, by change f (P.root i) = _; rw [hi, map_add]⟩
  have hsat := characteristic_zero_closed_root_subsystem_saturated P Ω hsub' hneg' hclosed'
  have himage : f '' Ω = Ψ := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      obtain ⟨i, hi⟩ := hsub hx
      change f (P.root i) = x at hi
      exact ⟨P.root i, by change f (P.root i) ∈ Ψ; rwa [hi], hi⟩
  apply Set.Subset.antisymm
  · rintro z ⟨⟨i, rfl⟩, hz⟩
    have hz' : f (P.root i) ∈ (AddSubgroup.closure Ω).map f := by
      rw [f.map_closure, himage]
      exact hz
    obtain ⟨x, hx, hx'⟩ := AddSubgroup.mem_map.mp hz'
    have hxroot : x = P.root i := hf hx'
    have hi : P.root i ∈ Set.range P.root ∩ (AddSubgroup.closure Ω : Set M) :=
      ⟨Set.mem_range_self i, hxroot ▸ hx⟩
    rw [hsat] at hi
    exact hi
  · intro z hz
    exact ⟨hsub hz, AddSubgroup.subset_closure hz⟩

section LieAlgebra

variable {K g : Type*} [Field K] [CharZero K] [LieRing g] [LieAlgebra K g]
  [LieAlgebra.IsKilling K g] [FiniteDimensional K g]
  (H : LieSubalgebra K g) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H g]

/-- Saturation for the actual root system of a splitting Killing Lie algebra.
In particular this applies directly to complexified compact centreless algebras. -/
theorem lie_rootSystem_closed_subsystem_saturated
    (Ψ : Set (Module.Dual K H))
    (hsub : Ψ ⊆ Set.range (LieAlgebra.IsKilling.rootSystem H).root)
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ Set.range (LieAlgebra.IsKilling.rootSystem H).root → a + b ∈ Ψ) :
    Set.range (LieAlgebra.IsKilling.rootSystem H).root ∩
      (AddSubgroup.closure Ψ : Set (Module.Dual K H)) = Ψ :=
  characteristic_zero_closed_root_subsystem_saturated
    (LieAlgebra.IsKilling.rootSystem H) Ψ hsub hneg hclosed

/-- Properness of a closed subsystem of an actual Lie root system survives
passage to its integer root lattice. -/
theorem lie_rootSystem_proper_closed_subsystem_lattice_ne
    (Ψ : Set (Module.Dual K H))
    (hsub : Ψ ⊆ Set.range (LieAlgebra.IsKilling.rootSystem H).root)
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ Set.range (LieAlgebra.IsKilling.rootSystem H).root → a + b ∈ Ψ)
    (hne : Ψ ≠ Set.range (LieAlgebra.IsKilling.rootSystem H).root) :
    AddSubgroup.closure Ψ ≠
      AddSubgroup.closure (Set.range (LieAlgebra.IsKilling.rootSystem H).root) :=
  characteristic_zero_proper_closed_root_subsystem_lattice_ne
    (LieAlgebra.IsKilling.rootSystem H) Ψ hsub hneg hclosed hne

/-- The actual Lie root-system roots, evaluated as functions, are exactly the
nonzero generalized adjoint weights used by the root-grading construction. -/
theorem lie_weight_root_range :
    Set.range (fun α : H.root =>
      ((LieAlgebra.IsKilling.rootSystem H).root α : H → K)) =
      {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥} := by
  classical
  ext χ
  constructor
  · rintro ⟨α, rfl⟩
    have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
    exact ⟨hα, α.val.genWeightSpace_ne_bot⟩
  · rintro ⟨hne, hχ⟩
    let α : LieModule.Weight K H g := ⟨χ, hχ⟩
    have hα : α ∈ H.root := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    exact ⟨⟨α, hα⟩, rfl⟩

/-- Saturation directly for actual weight functions, the same carrier used by
`RootGrading.rootLattice`.  This is valid over `ℂ` without any ordered-field assumption. -/
theorem lie_weight_closed_subsystem_saturated
    (Ψ : Set (H → K))
    (hsub : Ψ ⊆ {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥})
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥} → a + b ∈ Ψ) :
    {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥} ∩
      (AddSubgroup.closure Ψ : Set (H → K)) = Ψ := by
  let f : Module.Dual K H →+ (H → K) := {
    toFun := fun α => α
    map_zero' := rfl
    map_add' := fun _ _ => rfl
  }
  have hf : Function.Injective f := fun α β h => LinearMap.ext (congrFun h)
  have hΦ : Set.range (fun i => f ((LieAlgebra.IsKilling.rootSystem H).root i)) =
      {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥} := lie_weight_root_range H
  simpa only [hΦ] using crystallographic_closed_root_subsystem_saturated_of_injective
    (LieAlgebra.IsKilling.rootSystem H) f hf Ψ
    (by simpa only [hΦ] using hsub) hneg (by simpa only [hΦ] using hclosed)

/-- Properness of a closed subsystem also survives in the exact function-valued
integer lattice used for quotient root gradings. -/
theorem lie_weight_proper_closed_subsystem_lattice_ne
    (Ψ : Set (H → K))
    (hsub : Ψ ⊆ {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥})
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥} → a + b ∈ Ψ)
    (hne : Ψ ≠ {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥}) :
    AddSubgroup.closure Ψ ≠
      AddSubgroup.closure {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥} := by
  intro heq
  apply hne
  apply Set.Subset.antisymm hsub
  intro χ hχ
  have hsat := lie_weight_closed_subsystem_saturated H Ψ hsub hneg hclosed
  have hχL : χ ∈ AddSubgroup.closure Ψ := by
    rw [heq]
    exact AddSubgroup.subset_closure hχ
  have : χ ∈ {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥} ∩
      (AddSubgroup.closure Ψ : Set (H → K)) := ⟨hχ, hχL⟩
  simpa only [hsat] using this

end LieAlgebra

end CubicAnomaly.Classification.RootSaturation
