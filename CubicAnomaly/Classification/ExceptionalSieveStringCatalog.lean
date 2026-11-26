import CubicAnomaly.Classification.ExceptionalSieveSimpleStrings
import CubicAnomaly.Classification.ExceptionalSieveProducts

/-!
# Bounded labels from actual simple-root strings

For each possible starting node, extend its ordered list by the first unused
neighbor. The largest of these string counts bounds the dimension of a module
with the specified highest weight. Monotonicity permits a finite enumeration
of all labels whose counts are at most 121.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveStringCatalog

open ExceptionalSieveCatalog ExceptionalSieveSimpleStrings
open LieAlgebra LieModule Module LieAlgebra.IsKilling

def matrix (t : Factor) : Matrix t.Node t.Node ℤ :=
  let rows := t.datum.cartan
  fun i j => (rows[i.val]!)[j.val]!

private def extend (t : Factor) (C : Matrix t.Node t.Node ℤ) (seen : List t.Node) : List t.Node :=
  match (List.finRange t.rank).find? (fun j => !seen.contains j && seen.any (fun k => C k j != 0)) with
  | some j => j :: seen
  | none => seen

def steps (t : Factor) (i : t.Node) : List t.Node := (extend t (matrix t))^[t.rank - 1] [i]

private theorem steps_nodup (t : Factor) (i : t.Node) : (steps t i).Nodup := by
  have extNodup (seen : List t.Node) (hs : seen.Nodup) : (extend t (matrix t) seen).Nodup := by
    unfold extend
    split
    next j h =>
      have hj := List.find?_some h
      exact List.nodup_cons.mpr ⟨by simpa using (Bool.and_eq_true_iff.mp hj).1, hs⟩
    next => exact hs
  exact Function.Iterate.rec List.Nodup (by simp : [i].Nodup) extNodup _

def lower (t : Factor) (a : t.Label) : ℕ :=
  Finset.univ.sup fun i => (profileList (matrix t) a (steps t i)).length

theorem lower_pos (t : Factor) (a : t.Label) : 0 < lower t a := by
  have zero_mem (w : List t.Node) : 0 ∈ profiles (matrix t) a w := by
    induction w with
    | nil => simp [profiles]
    | cons i w ih =>
      refine Finset.mem_biUnion.mpr ⟨0, ih, Finset.mem_image.mpr ⟨0, ?_, ?_⟩⟩
      · exact Finset.mem_range.mpr (Nat.zero_lt_succ _)
      · simp
  let i : t.Node := ⟨0, by cases t <;> simp [Factor.rank]⟩
  have hl := Finset.le_sup (f := fun j => (profileList (matrix t) a (steps t j)).length)
    (Finset.mem_univ i)
  change (profileList (matrix t) a (steps t i)).length ≤ lower t a at hl
  rw [profileList_length _ _ _ (steps_nodup t i)] at hl
  exact (Finset.card_pos.mpr ⟨0,zero_mem _⟩).trans_le hl

theorem lower_mono (t : Factor) : Monotone (lower t) := by
  intro a b hab
  apply Finset.sup_mono_fun
  intro i _
  rw [profileList_length _ _ _ (steps_nodup t i), profileList_length _ _ _ (steps_nodup t i)]
  exact profiles_card_monotone _ _ hab

theorem lower_le_finrank {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [LieAlgebra.IsKilling ℂ L] [AddCommGroup M] [Module ℂ M] [LieRingModule L M]
    [LieModule ℂ L M] [FiniteDimensional ℂ M]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    (t : Factor) (s : t.Node ≃ b.support)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t i j)
    (a : t.Label) (χ : Module.Dual ℂ H) (v : M) (hv : v ≠ 0)
    (hw : ∀ h : H, ⁅h,v⁆ = χ h • v) (hlabels : ∀ i, χ (coroot (s i).val.val) = (a i : ℂ))
    (hkill : ∀ i : t.Node, ∀ x ∈ rootSpace H (s i).val.val, ⁅x,v⁆ = 0) :
    lower t a ≤ finrank ℂ M := by
  apply Finset.sup_le
  intro i _
  rw [profileList_length _ _ _ (steps_nodup t i)]
  exact simple_string_card_le_finrank H b s _ hC a χ v hv hw hlabels hkill _ (steps_nodup t i)

private def search (t : Factor) : List t.Node → t.Label → List t.Label
  | [], lab => [lab]
  | i :: nodes, lab =>
    let vals := (List.range 122).takeWhile fun k => lower t (Function.update lab i k) ≤ 121
    vals.flatMap fun k => search t nodes (Function.update lab i k)

/-- Nonnegative labels with coordinates at most 121 are enumerated by a
monotone search starting at the zero label. -/
def labels (t : Factor) : List t.Label := search t (List.finRange t.rank) 0

private theorem mem_search (t : Factor) (a : t.Label) (hf : lower t a ≤ 121)
    (ha : ∀ i, a i ≤ 121) (nodes : List t.Node) (lab : t.Label)
    (hle : lab ≤ a) (heq : ∀ i ∉ nodes, lab i = a i) : a ∈ search t nodes lab := by
  induction nodes generalizing lab with
  | nil =>
    have : lab = a := funext fun i => heq i (by simp)
    simp [search, this]
  | cons i nodes ih =>
    apply List.mem_flatMap.mpr
    refine ⟨a i, ?_, ih _ (update_le_iff.mpr ⟨le_rfl, fun j _ => hle j⟩) ?_⟩
    · have hm (k : ℕ) (hk : k ≤ a i) : lower t (Function.update lab i k) ≤ 121 :=
        (lower_mono t (update_le_iff.mpr ⟨hk, fun j _ => hle j⟩)).trans hf
      have hr : 122 = a i + 1 + (121 - a i) := by have := ha i; omega
      change a i ∈ (List.range 122).takeWhile _
      rw [hr, List.range_add, List.takeWhile_append_of_pos]
      · exact List.mem_append_left _ (List.mem_range.mpr (Nat.lt_succ_self _))
      · intro k hk
        exact decide_eq_true (hm k (by have := List.mem_range.mp hk; omega))
    · intro j hj
      by_cases h : j = i
      · subst j; exact Function.update_self ..
      · exact (Function.update_of_ne h ..).trans (heq j (by simp [h,hj]))

theorem label_mem_of_lower (t : Factor) (a : t.Label) (hf : lower t a ≤ 121)
    (ha : ∀ i, a i ≤ 121) : a ∈ labels t :=
  mem_search t a hf ha _ _ (fun _ => Nat.zero_le _) (by simp)

end CubicAnomaly.Classification.ExceptionalSieveStringCatalog
