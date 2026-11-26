import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum

/-! Counting the signed one- and two-coordinate roots of type C in an actual root set. -/
namespace CubicAnomaly.Classification.TypeCPositiveRootCount

private def entries {r : ℕ} (s : Bool) (i j k : Fin r) : ℤ :=
  (if s then 1 else -1) * ((if i = k then 1 else 0) +
    (if i < j then -1 else 1) * (if j = k then 1 else 0))

private theorem entries_injective {r : ℕ} {s t : Bool} {i j a b : Fin r}
    (h : ∀ k, entries s i j k = entries t a b k) : s = t ∧ i = a ∧ j = b := by
  have hi := h i
  have hj := h j
  have ha := h a
  have hb := h b
  clear h
  cases s <;> cases t <;> simp [entries] at * <;> grind

variable {H : Type*} [AddCommGroup H] [Module ℂ H] {r : ℕ}

private def rootWeight (ε : Fin r → Module.Dual ℂ H) (p : Bool × Fin r × Fin r) : Module.Dual ℂ H :=
  let t := if p.2.1 < p.2.2 then ε p.2.1 - ε p.2.2 else ε p.2.1 + ε p.2.2
  if p.1 then t else -t

private theorem rootWeight_apply (ε : Fin r → Module.Dual ℂ H) (v : Fin r → H)
    (hev : ∀ i k, ε i (v k) = if i = k then 1 else 0) (s : Bool) (i j k : Fin r) :
    rootWeight ε (s,i,j) (v k) = (entries s i j k : ℂ) := by
  cases s <;> by_cases hlt : i < j <;>
    simp only [rootWeight, entries, hlt, if_true, if_false, Bool.false_eq_true,
      LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sub_apply, hev] <;>
    by_cases hi : i = k <;> by_cases hj : j = k <;> norm_num [hi,hj]

/-- An actual finite weight set containing the differences and signed sums of a
biorthogonal coordinate family contains at least `2r²` weights. -/
theorem card_le {R : Type*} [Fintype R] (φ : R → Module.Dual ℂ H)
    (ε : Fin r → Module.Dual ℂ H) (v : Fin r → H)
    (hev : ∀ i k, ε i (v k) = if i = k then 1 else 0)
    (hdiff : ∀ i j, i ≠ j → ε i - ε j ∈ Set.range φ)
    (hsum : ∀ i j, ε i + ε j ∈ Set.range φ)
    (hneg : ∀ i j, -(ε i + ε j) ∈ Set.range φ) : 2*r^2 ≤ Fintype.card R := by
  classical
  have hm (p : Bool × Fin r × Fin r) : rootWeight ε p ∈ Set.range φ := by
    rcases p with ⟨s,i,j⟩
    cases s <;> by_cases h : i < j
    · simpa [rootWeight, h, neg_sub] using hdiff j i h.ne'
    · simpa [rootWeight, h] using hneg i j
    · simpa [rootWeight, h] using hdiff i j h.ne
    · simpa [rootWeight, h] using hsum i j
  choose f hf using hm
  have hi : Function.Injective f := by
    rintro ⟨s,i,j⟩ ⟨t,a,b⟩ h
    have he := (hf (s,i,j)).symm.trans ((congrArg φ h).trans (hf (t,a,b)))
    have hentries (k : Fin r) : entries s i j k = entries t a b k := by
      apply Int.cast_injective (α := ℂ)
      rw [← rootWeight_apply ε v hev, ← rootWeight_apply ε v hev, he]
    obtain ⟨rfl,rfl,rfl⟩ := entries_injective hentries
    rfl
  simpa [pow_two] using Fintype.card_le_of_injective f hi

end CubicAnomaly.Classification.TypeCPositiveRootCount
