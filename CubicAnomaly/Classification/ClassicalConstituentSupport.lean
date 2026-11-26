import CubicAnomaly.Classification.ClassicalConstituentCompact
import CubicAnomaly.Classification.ClassicalSimplicity

/-!
# Support restrictions from the three actual ambient constituents

The projections onto the compact isotropy and its two quotient halves
bound the number of highest weights in the form-preserving algebra.
All three weights come from the original constituents. The first- and
third-lowering highest operators therefore restrict the number and size
of support labels of the orthogonal defining representation.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentSupport

open LieAlgebra LieModule Module LieAlgebra.IsKilling Submodule
open CubicAnomaly.Classification
open ClassicalConstituentHighest ClassicalConstituentWeights
open Structural ComplexDuality Complexification CompactGeometry SelfDualQuotientObstruction
open CompactOperatorModel ClassicalConstituentCompact
open scoped TensorProduct

section Count

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

private theorem count_shifted_weights (b : (rootSystem H).Base) {d : ℕ}
    (a : b.support → Fin d) (χ : H → ℂ) (θ p q : H → ℂ)
    (hc : ∀ i : b.support,
      (1 ≤ (a i : ℕ) → (fun x => 2 * χ x - i.val.val x) ∈ ({θ, p, q} : Set (H → ℂ))) ∧
      (3 ≤ (a i : ℕ) → (fun x => 2 * χ x - 3 * i.val.val x) ∈ ({θ, p, q} : Set (H → ℂ)))) :
    Nat.card {i : b.support // 1 ≤ (a i : ℕ)} + Nat.card {i : b.support // 3 ≤ (a i : ℕ)} ≤ 3 := by
  classical
  let D := {i : b.support // 1 ≤ (a i : ℕ)} ⊕ {i : b.support // 3 ≤ (a i : ℕ)}
  let F : D → H → ℂ := Sum.elim
    (fun i x => 2 * χ x - i.val.val.val x) (fun i x => 2 * χ x - 3 * i.val.val.val x)
  obtain ⟨t, ht⟩ := ExceptionalSieveWeights.exists_height_element H b
  have ht' (i : b.support) : i.val.val t = 1 := by
    rw [ht, RootPairing.Base.height_one_of_mem_support i.property, Int.cast_one]
  have hstrong (i j : b.support) :
      (fun x => 2 * χ x - i.val.val x) ≠ (fun x => 2 * χ x - 3 * j.val.val x) := by
    intro he
    have h := congrFun he t
    rw [ht' i, ht' j, sub_right_inj] at h
    norm_num at h
  have hinj : Function.Injective F := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        congr 1
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        apply Weight.ext
        intro x
        exact sub_right_inj.mp (congrFun hij x)
      | inr j => exact (hstrong i.val j.val hij).elim
    | inr i =>
      cases j with
      | inl j => exact (hstrong j.val i.val hij.symm).elim
      | inr j =>
        congr 1
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        apply Weight.ext
        intro x
        have he : 3 * i.val.val.val x = 3 * j.val.val.val x := sub_right_inj.mp (congrFun hij x)
        exact mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) he
  let S : Finset (H → ℂ) := {θ, p, q}
  have hmem (u : D) : F u ∈ S := by
    cases u with
    | inl i => simpa [F, S] using (hc i).1 i.property
    | inr i => simpa [F, S] using (hc i).2 i.property
  have hcard := Nat.card_le_card_of_injective (fun u : D => (⟨F u, hmem u⟩ : S))
    (fun _ _ heq => hinj (congrArg Subtype.val heq))
  change Nat.card (_ ⊕ _) ≤ Nat.card S at hcard
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := S), Fintype.card_coe] at hcard
  have hS : S.card ≤ 3 := by
    have h₁ := Finset.card_insert_le θ ({p, q} : Finset (H → ℂ))
    have h₂ := Finset.card_insert_le p ({q} : Finset (H → ℂ))
    simpa [S] using h₁.trans (Nat.add_le_add_right (by simpa using h₂) 1)
  exact hcard.trans hS

end Count

section Model

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)] [IsSimple ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [LieRingModule (ℂ ⊗[ℝ] h) W]
    [LieModule ℂ (ℂ ⊗[ℝ] h) W] [FiniteDimensional ℂ W] [Nontrivial W]

include hp e in
private theorem model_support_budget (b : (rootSystem H).Base) (β : LinearMap.BilinForm ℂ W)
    (A : Model h β) (hnd : β.Nondegenerate) (hi : β.lieInvariant (ℂ ⊗[ℝ] h)) (hsym : β.IsSymm) :
    ∃ (χ : Weight ℂ H W) (v : W) (a : b.support → Fin (finrank ℂ W)),
      IsHighestVector H b χ v ∧ (∀ i : b.support, χ (coroot i.val.val) = ((a i : ℕ) : ℂ)) ∧
      Nat.card {i : b.support // 1 ≤ (a i : ℕ)} + Nat.card {i : b.support // 3 ≤ (a i : ℕ)} ≤ 3 := by
  obtain ⟨χ, v, a, hv, hχ, hrts, ha⟩ := orthogonal_support_weights H b β hnd hi hsym
  obtain ⟨θ, p, q, _, _, _, hall⟩ := compact_model_highest_weights B h hp e H b A
  refine ⟨χ, v, a, ⟨hv, hχ, hrts⟩, fun i => (ha i).1, count_shifted_weights H b a χ θ p q ?_⟩
  intro i
  exact ⟨fun h => hall _ ((ha i).2.1 h), fun h => hall _ ((ha i).2.2 h)⟩

end Model

section Orthogonal

open HermitianRealization OrthogonalDefining OrthogonalComplexification ClassicalModuleBridge
open ClassicalSimplicity AllRankComplex

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

set_option maxHeartbeats 1000000 in
/-- Under the original compact orthogonal hypotheses, the number of positive
simple labels plus the number of labels at least three is at most three.
In particular two distinct labels at least three are impossible. -/
theorem all_rank_orthogonal_support_budget
    (B : CompactForm (orthogonalAlgebra W)) (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra] :
    letI : IsKilling ℂ (ℂ ⊗[ℝ] h) := (all_rank_complex_structural_reduction B h heff hp e hr).2.2.2.1
    ∀ b : (rootSystem H).Base,
      ∃ (χ : Weight ℂ H (ℂ ⊗[ℝ] W)) (v : ℂ ⊗[ℝ] W)
          (a : b.support → Fin (finrank ℂ (ℂ ⊗[ℝ] W))),
        IsHighestVector H b χ v ∧ (∀ i : b.support, χ (coroot i.val.val) = ((a i : ℕ) : ℂ)) ∧
        Nat.card {i : b.support // 1 ≤ (a i : ℕ)} + Nat.card {i : b.support // 3 ≤ (a i : ℕ)} ≤ 3 := by
  letI : IsKilling ℂ (ℂ ⊗[ℝ] h) := (all_rank_complex_structural_reduction B h heff hp e hr).2.2.2.1
  letI : IsSimple ℂ (ℂ ⊗[ℝ] h) := all_rank_orthogonal_complexified_isotropy_simple B h heff hp e hr
  letI := all_rank_orthogonal_defining_complex_irreducible B h heff hp e hr
  letI := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W)
  intro b
  have hnd : (orthogonalExtendedForm (W := W)).Nondegenerate := by
    apply complexified_bilinForm_nondegenerate (innerₗ W)
    constructor <;> intro w hw <;> exact inner_self_eq_zero.mp (hw w)
  have hsym : (orthogonalExtendedForm (W := W)).IsSymm := by
    apply LinearMap.BilinForm.isSymm_iff.mpr
    exact LinearMap.BilinForm.IsSymm.baseChange ℂ (B₂ := innerₗ W) ⟨fun x y => real_inner_comm y x⟩
  exact model_support_budget B h hp e H b _ (orthogonalModel h) hnd
    (orthogonal_complexified_defining_form_invariant h) hsym

end Orthogonal

end CubicAnomaly.Classification.ClassicalConstituentSupport
