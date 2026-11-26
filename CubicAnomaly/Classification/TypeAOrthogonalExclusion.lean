import CubicAnomaly.Classification.TypeAOrthogonalExchanged
import CubicAnomaly.Classification.TypeADiagramOpposition
import CubicAnomaly.Classification.ClassicalConstituentDiagonal
import CubicAnomaly.Classification.OrthogonalMinusculeExclusion
import CubicAnomaly.Classification.ExceptionalSieveFaithful

/-! # Excluding type-A isotropy in a proper compact orthogonal pair -/

namespace CubicAnomaly.Classification.TypeAOrthogonalExclusion

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ClassicalConstituentHighest ClassicalConstituentOrthogonal ClassicalConstituentDiagram
open ComplexDuality Structural CompactGeometry HermitianRealization CompactOperatorModel Complexification
open OrthogonalDefining OrthogonalComplexification ClassicalModuleBridge ClassicalSimplicity
open TypeADiagramOpposition TypeAOrthogonalExchanged WeylComponentObstruction
open ExceptionalSieveFaithful OrthogonalMinusculeExclusion
open scoped TensorProduct

section Model

variable {g U : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)] [IsSimple ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    (b : (rootSystem H).Base) {n : ℕ} (s : b.support ≃ Fin n)
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n)
    [AddCommGroup U] [Module ℂ U] [LieRingModule (ℂ ⊗[ℝ] h) U] [LieModule ℂ (ℂ ⊗[ℝ] h) U]
    [FiniteDimensional ℂ U] [IsIrreducible ℂ (ℂ ⊗[ℝ] h) U] [IsFaithful ℂ (ℂ ⊗[ℝ] h) U]

noncomputable local instance (priority := high) : DecidableEq b.support := Classical.decEq _

include hp hr hm in
set_option maxHeartbeats 1200000 in
private theorem model_fixed_node (β : LinearMap.BilinForm ℂ U) (A : Model h β)
    (hnd : β.Nondegenerate) (hi : β.lieInvariant (ℂ ⊗[ℝ] h)) (hsym : β.IsSymm) :
    2 ≤ n ∧ ∃ (χ : Weight ℂ H U) (v : U) (j : Fin n) (a : ℕ) (γ : H.root),
      IsHighestVector H b χ v ∧ 0 < a ∧ n = 2*j.val+1 ∧
      (∀ k : Fin n, χ (coroot (s.symm k).val.val) = if k=j then (a : ℂ) else 0) ∧
      ∀ z : H, γ.val z = 2 * χ z - (s.symm j).val.val z := by
  classical
  letI : Nontrivial (ℂ ⊗[ℝ] h) := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] h)
  obtain ⟨χ,v,c,θ,w,δ,hv,_,⟨γ,hγ,_,_⟩,hc,_⟩ :=
    orthogonal_model_opposition_support B h hp e H b β A hnd hi hsym
  let a (i : Fin n) : ℕ := c (s.symm i)
  have ha (i : b.support) : χ (coroot i.val.val) = (a (s i) : ℂ) := by
    simpa only [a, s.symm_apply_apply] using (hc i).1
  have hn := compact_isotropy_no_weyl_negation B h hp e H b
  obtain ⟨δ',⟨p,hp'⟩,_⟩ := exists_nontrivial_diagram_symmetry H b hn
  have hpne := s.injective.ne hp'
  have hn₂ : 2 ≤ n := by
    by_contra! hn'
    apply hpne
    apply Fin.ext
    have h₁ := (s (δ' p)).isLt
    have h₂ := (s p).isLt
    omega
  have hδ := type_A_opposition_eq_rev H b s hm hn w δ fun i => (hc i).2.2.1
  have hrev (i : Fin n) : a i.rev = a i := by
    obtain ⟨q,rfl⟩ := s.surjective i
    rw [← hδ q]
    simp only [a, s.symm_apply_apply, (hc q).2.1]
  have hzero (k : Fin n) (hn : k ≠ k.rev) : a k = 0 :=
    symmetric_label_eq_zero_of_noncentral B h hp e hr H b s hm β A
      hnd hi hsym χ v hv a ha hrev k hn
  have hlabel (i : Fin n) :
      ⁅((coroot (s.symm i).val.val : H) : ℂ ⊗[ℝ] h),v⁆ = (a i : ℂ) • v :=
    (hv.2.1 (coroot (s.symm i).val.val)).trans (congrArg (fun z : ℂ => z • v) (hc (s.symm i)).1)
  have hnon : a ≠ 0 := faithful_highest_label_ne_zero (L := ℂ ⊗[ℝ] h) (M := U) H b s.symm a v hv.1 hlabel
    (fun i => hv.2.2 i.val (b.isPos_of_mem_support i.property))
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hnon
  change a j ≠ 0 at hj
  have hfix : j = j.rev := by by_contra he; exact hj (hzero j he)
  have hmid : n=2*j.val+1 := by
    have he := congrArg Fin.val hfix
    rw [Fin.val_rev] at he
    have hj' := j.isLt
    omega
  have hshift := ((hc (s.symm j)).2.2.2.1 (by exact Nat.pos_of_ne_zero hj)).mpr (s.injective (by
    rw [hδ, s.apply_symm_apply, ← hfix]))
  refine ⟨hn₂,χ,v,j,a j,γ,hv,Nat.pos_of_ne_zero hj,hmid,?_,?_⟩
  · intro k
    have hk := (hc (s.symm k)).1
    change χ (coroot (s.symm k).val.val) = (a k : ℂ) at hk
    rw [hk]
    split_ifs with he
    · rw [he]
    · rw [hzero k (fun hfixed => he (Fin.ext (by
        have h₁ := congrArg Fin.val hfixed
        rw [Fin.val_rev] at h₁
        have h₂ := k.isLt
        omega))), Nat.cast_zero]
  · intro z
    exact (congrFun hγ z).trans (congrFun hshift z).symm

end Model

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (B : CompactForm (orthogonalAlgebra W)) (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    (b : (rootSystem H).Base) {n : ℕ} (s : b.support ≃ Fin n)
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n)

include heff hp hr hm in
set_option maxHeartbeats 1500000 in
/-- In a proper compact orthogonal model, a type-A base leaves exactly
one supported node. It is the middle node and twice the defining
highest weight minus its simple root is an actual root. -/
theorem compact_typeA_fixed_node :
    2 ≤ n ∧ ∃ (χ : Weight ℂ H (ℂ ⊗[ℝ] W)) (v : ℂ ⊗[ℝ] W) (j : Fin n) (a : ℕ) (γ : H.root),
      IsHighestVector H b χ v ∧ 0 < a ∧ n = 2*j.val+1 ∧
      (∀ k : Fin n, χ (coroot (s.symm k).val.val) = if k=j then (a : ℂ) else 0) ∧
      ∀ z : H, γ.val z = 2 * χ z - (s.symm j).val.val z := by
  letI : IsSimple ℂ (ℂ ⊗[ℝ] h) := all_rank_orthogonal_complexified_isotropy_simple B h heff hp e hr
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) :=
    all_rank_orthogonal_defining_complex_irreducible B h heff hp e hr
  letI : IsFaithful ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) := orthogonal_complexified_defining_faithful h
  letI : Nontrivial (ℂ ⊗[ℝ] h) := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] h)
  let β := orthogonalExtendedForm (W := W)
  have hnd : β.Nondegenerate := by
    apply complexified_bilinForm_nondegenerate (innerₗ W)
    constructor <;> intro x hx <;> exact inner_self_eq_zero.mp (hx x)
  have hsym : β.IsSymm := by
    apply LinearMap.BilinForm.isSymm_iff.mpr
    exact LinearMap.BilinForm.IsSymm.baseChange ℂ (B₂ := innerₗ W) ⟨fun x y => real_inner_comm y x⟩
  have hi := orthogonal_complexified_defining_form_invariant h
  exact model_fixed_node B h hp e hr H b s hm β (orthogonalModel h) hnd hi hsym

include heff hp hr hm in
set_option maxHeartbeats 600000 in
/-- A proper compact orthogonal pair with the canonical nonzero radical has
no type-A isotropy Cartan matrix, in any rank. -/
theorem compact_orthogonal_no_type_A : False := by
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) :=
    all_rank_orthogonal_defining_complex_irreducible B h heff hp e hr
  obtain ⟨hn, χ, v, j, a, γ, hv, ha, hmid, hl, hγ⟩ :=
    compact_typeA_fixed_node B h heff hp e hr H b s hm
  have hA (i k : Fin n) : b.cartanMatrix (s.symm i) (s.symm k) = CartanMatrix.A n i k :=
    congrFun (congrFun hm i) k
  have heq := ClassicalConstituentDiagonal.middle_A_diagonal H b j.val hmid s.symm j rfl a ha χ hl γ hγ hA
  have hle : j.val+1 ≤ a*(j.val+1) := Nat.le_mul_of_pos_left _ ha
  have hj : j.val = 1 := by omega
  rw [hj] at heq
  have ha₁ : a = 1 := by omega
  have hn₃ : n = 3 := by omega
  subst n
  exact no_typeA_three_middle h hp H b hv s.symm hA (fun i => by
    rw [hl, ha₁]
    simp only [Fin.ext_iff, hj, Nat.cast_one])

end CubicAnomaly.Classification.TypeAOrthogonalExclusion
