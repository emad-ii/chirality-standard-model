import CubicAnomaly.Classification.TypeCPositiveRootCount

/-! Count the even and odd orthogonal roots by adjoining or rescaling
the diagonal roots of the signed-coordinate family. -/
namespace CubicAnomaly.Classification.OrthogonalRootCounts

open Module

variable {H R : Type*} [AddCommGroup H] [Module ℂ H] [Fintype R] {r : ℕ}
    (φ : R → Dual ℂ H) (ε : Fin r → Dual ℂ H) (v : Fin r → H)
    (hev : ∀ i k, ε i (v k) = if i = k then 1 else 0)
    (hd : ∀ i j, i ≠ j → ε i - ε j ∈ Set.range φ)
    (hp : ∀ i j, i ≠ j → ε i + ε j ∈ Set.range φ)
    (hm : ∀ i j, i ≠ j → -(ε i + ε j) ∈ Set.range φ)

include hev hd hp hm in
/-- Distinct-coordinate signed pairs give all the off-diagonal contributions
in type D. -/
theorem even_bound : 2*r^2 ≤ Fintype.card R + 2*r := by
  classical
  let F : R ⊕ (Bool × Fin r) → Dual ℂ H := Sum.elim φ fun p =>
    if p.1 then ε p.2 + ε p.2 else -(ε p.2 + ε p.2)
  have hin : Set.range φ ⊆ Set.range F := by
    rintro _ ⟨x,rfl⟩; exact ⟨Sum.inl x,rfl⟩
  have h := TypeCPositiveRootCount.card_le F ε v hev (fun i j h => hin (hd i j h))
    (fun i j => by
      by_cases h : i = j
      · subst j; exact ⟨.inr (true,i),rfl⟩
      · exact hin (hp i j h))
    (fun i j => by
      by_cases h : i = j
      · subst j; exact ⟨.inr (false,i),rfl⟩
      · exact hin (hm i j h))
  simpa using h

include hev hd hp hm in
/-- The remaining type-B roots have one nonzero coordinate. Doubling
them identifies their count with the diagonal members of the type-C family. -/
theorem odd_bound (w : H) (hw : ∀ i, ε i w = 1) (hpos : ∀ i, ε i ∈ Set.range φ)
    (hneg : ∀ i, -ε i ∈ Set.range φ) : 2*r^2 ≤ Fintype.card R := by
  classical
  let F (a : R) := if φ a w = 1 ∨ φ a w = -1 then φ a + φ a else φ a
  have keep {z : Dual ℂ H} (hz : z ∈ Set.range φ) (hw : z w ≠ 1 ∧ z w ≠ -1) : z ∈ Set.range F := by
    obtain ⟨a,rfl⟩ := hz
    exact ⟨a, if_neg (not_or.mpr hw)⟩
  apply TypeCPositiveRootCount.card_le F ε v hev
  · intro i j hij
    apply keep (hd i j hij)
    norm_num [hw]
  · intro i j
    by_cases hij : i = j
    · subst j
      obtain ⟨a,ha⟩ := hpos i
      exact ⟨a, by simp [F,ha,hw]⟩
    · apply keep (hp i j hij)
      norm_num [hw]
  · intro i j
    by_cases hij : i = j
    · subst j
      obtain ⟨a,ha⟩ := hneg i
      exact ⟨a, by simp [F,ha,hw]⟩
    · apply keep (hm i j hij)
      norm_num [hw]

end CubicAnomaly.Classification.OrthogonalRootCounts
