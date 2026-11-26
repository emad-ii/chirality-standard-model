import CubicAnomaly.Classification.ExceptionalSieveA2
import CubicAnomaly.Classification.ExceptionalSieveProducts

/-!
# The rank-two A₂ case in a rank-deficient F₄ ambient algebra

The two ordered root strings bound both Dynkin labels. The long-coroot index
congruence then forces a cubic symmetric-power label; its triangular spanning
bound excludes dimension twenty-two.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveA2Index

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ExceptionalSieveA2 ExceptionalSieveCatalog ExceptionalSieveProducts

private theorem f4_index_label_candidates : ∀ a c : Fin 23,
    Fintype.card (Strings a.val c.val) ≤ 22 →
    Fintype.card (Strings c.val a.val) ≤ 22 →
    Compatible .f4 22 (row (.a 1) ![a.val,c.val]) →
    (a.val = 3 ∧ c.val = 0) ∨ (a.val = 0 ∧ c.val = 3) := by native_decide

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  (b : (rootSystem H).Base) [AddCommGroup M] [Module ℂ M]
  [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M] [IsIrreducible ℂ L M]

/-- Either cubic symmetric-power edge of A₂ has exactly ten dimensions. -/
theorem a2_edge_three_dimension (s : Fin 2 ≃ b.support)
    (h01 : b.cartanMatrix (s 0) (s 1) = -1) (h10 : b.cartanMatrix (s 1) (s 0) = -1)
    (v : M) (hv : v ≠ 0) (χ : H → ℂ) (hw : ∀ x : H, ⁅x,v⁆ = χ x • v)
    (hc : (χ (coroot (s 0).val.val) = 3 ∧ χ (coroot (s 1).val.val) = 0) ∨
      (χ (coroot (s 0).val.val) = 0 ∧ χ (coroot (s 1).val.val) = 3))
    (he : ∀ i : b.support, ∀ x ∈ rootSpace H i.val.val, ⁅x,v⁆ = 0) : finrank ℂ M = 10 := by
  have one (u : Fin 2 ≃ b.support) (h0 : b.cartanMatrix (u 0) (u 1) = -1)
      (h1 : b.cartanMatrix (u 1) (u 0) = -1)
      (ha : χ (coroot (u 0).val.val) = 3) (hb : χ (coroot (u 1).val.val) = 0) :
      finrank ℂ M = 10 := by
    have lo := a2_two_string_dimension_lower H b u h0 h1 v hv χ hw 3 0 (by simpa using ha)
      (by simpa using hb) he
    have hi := a2_edge_highest_dimension_le H b u h0 h1 v hv 3
      (by simpa [ha] using hw (coroot (u 0).val.val))
      (by simpa [hb] using hw (coroot (u 1).val.val)) he
    exact le_antisymm (hi.trans (by decide)) ((by decide : 10 ≤ Fintype.card (Strings 3 0)).trans lo)
  rcases hc with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact one s h01 h10 ha hb
  · let u := (Equiv.swap (0 : Fin 2) 1).trans s
    have hu₀ : u 0 = s 1 := by simp [u]
    have hu₁ : u 1 = s 0 := by simp [u]
    exact one u (hu₀ ▸ hu₁ ▸ h10) (hu₁ ▸ hu₀ ▸ h01) (hu₀ ▸ hb) (hu₁ ▸ ha)

/-- No A₂ highest weight of a twenty-two-dimensional representation
satisfies the index constraint on an embedding in F₄. -/
theorem f4_a2_dimension_ne_twenty_two (s : Fin 2 ≃ b.support)
    (h01 : b.cartanMatrix (s 0) (s 1) = -1) (h10 : b.cartanMatrix (s 1) (s 0) = -1)
    (v : M) (hv : v ≠ 0) (χ : H → ℂ) (hw : ∀ x : H, ⁅x,v⁆ = χ x • v)
    (labels : (Factor.a 1).Label)
    (hc : ∀ i : Fin 2, χ (coroot (s i).val.val) = (labels i : ℂ))
    (he : ∀ i : b.support, ∀ x ∈ rootSpace H i.val.val, ⁅x,v⁆ = 0)
    (hindex : Compatible .f4 22 (row (.a 1) labels)) : finrank ℂ M ≠ 22 := by
  intro hdim
  have lower := a2_two_string_dimension_lower H b s h01 h10 v hv χ hw _ _ (hc 0) (hc 1) he
  let s' : Fin 2 ≃ b.support := (Equiv.swap 0 1).trans s
  have s0 : s' 0 = s 1 := by simp [s']
  have s1 : s' 1 = s 0 := by simp [s']
  have h10' : b.cartanMatrix (s' 0) (s' 1) = -1 := by simpa only [s0,s1] using h10
  have h01' : b.cartanMatrix (s' 1) (s' 0) = -1 := by simpa only [s0,s1] using h01
  have lower' := a2_two_string_dimension_lower H b s' h10' h01' v hv χ hw _ _
    (s0 ▸ hc 1) (s1 ▸ hc 0) he
  rw [hdim] at lower lower'
  have bound (a c : ℕ) (h : Fintype.card (Strings a c) ≤ 22) : a < 23 := by
    have emb : Function.Injective (fun p : Fin (a+1) => (⟨p,0⟩ : Strings a c)) :=
      fun _ _ h => congrArg Sigma.fst h
    have hc' := Fintype.card_le_of_injective _ emb
    simp only [Fintype.card_fin] at hc'
    change a+1 ≤ Fintype.card (Strings a c) at hc'
    omega
  let a : Fin 23 := ⟨labels (0 : Fin 2), bound _ _ lower⟩
  let c : Fin 23 := ⟨labels (1 : Fin 2), bound _ _ lower'⟩
  have hlabels : ![a.val,c.val] = labels := by funext i; fin_cases i <;> rfl
  rcases f4_index_label_candidates a c lower lower' (hlabels ▸ hindex) with h | h
  · have h₀ : labels (0 : Fin 2) = 3 := h.1
    have h₁ : labels (1 : Fin 2) = 0 := h.2
    have ub : finrank ℂ M ≤ (3+2).choose 2 := a2_edge_highest_dimension_le H b s h01 h10 v hv 3
      (by simpa [hc,h₀] using hw (coroot (s 0).val.val))
      (by simpa [hc,h₁] using hw (coroot (s 1).val.val)) he
    rw [hdim] at ub
    exact (by decide : ¬22 ≤ (3+2).choose 2) ub
  · have h₀ : labels (0 : Fin 2) = 0 := h.1
    have h₁ : labels (1 : Fin 2) = 3 := h.2
    have ub : finrank ℂ M ≤ (3+2).choose 2 := a2_edge_highest_dimension_le H b s' h10' h01' v hv 3
      (by simpa [s0,hc,h₁] using hw (coroot (s 1).val.val))
      (by simpa [s1,hc,h₀] using hw (coroot (s 0).val.val)) he
    rw [hdim] at ub
    exact (by decide : ¬22 ≤ (3+2).choose 2) ub

end CubicAnomaly.Classification.ExceptionalSieveA2Index
