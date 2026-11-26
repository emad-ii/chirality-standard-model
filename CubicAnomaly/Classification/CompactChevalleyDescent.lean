import CubicAnomaly.Classification.CompactChevalleyConjugation

/-!
# Descent of an isomorphism matching compact-normalized generators

A complex Lie isomorphism taking normalized generating root vectors to matching
root vectors intertwines the compact conjugations on the whole algebra.
Restriction to the fixed points yields a real Lie isomorphism of the original
compact algebras and of the corresponding real pairs.
-/

namespace CubicAnomaly.Classification.CompactChevalleyDescent

open LieAlgebra LieSubalgebra Module Complexification CompactGeometry CompactChevalleyConjugation
open scoped TensorProduct ComplexConjugate

noncomputable section

variable {g₁ g₂ ι : Type*} [LieRing g₁] [LieAlgebra ℝ g₁] [LieRing g₂] [LieAlgebra ℝ g₂]

/-- Matching normalized generators forces an isomorphism to commute with
the two compact conjugations on every element of the complexification. -/
theorem intertwines_conjugation_of_normalized_generators
    (Φ : (ℂ ⊗[ℝ] g₁) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] g₂))
    (e₁ f₁ : ι → ℂ ⊗[ℝ] g₁) (e₂ f₂ : ι → ℂ ⊗[ℝ] g₂)
    (hgen : lieSpan ℂ _ (Set.range e₁ ∪ Set.range f₁) = ⊤)
    (h₁ : ∀ i, scalarConjugation (e₁ i) = -f₁ i)
    (h₂ : ∀ i, scalarConjugation (e₂ i) = -f₂ i)
    (he : ∀ i, Φ (e₁ i) = e₂ i) (hf : ∀ i, Φ (f₁ i) = f₂ i) :
    ∀ x, Φ (scalarConjugation x) = scalarConjugation (Φ x) := by
  let S : LieSubalgebra ℂ (ℂ ⊗[ℝ] g₁) := {
    carrier := {x | Φ (scalarConjugation x) = scalarConjugation (Φ x)}
    zero_mem' := by simp
    add_mem' := fun hx hy => by simp_all
    smul_mem' := fun c x hx => by
      change Φ (scalarConjugation x) = scalarConjugation (Φ x) at hx
      change Φ (scalarConjugation (c • x)) = scalarConjugation (Φ (c • x))
      simp only [scalarConjugation_complex_smul, map_smul, hx]
    lie_mem' := fun hx hy => by
      simp_all only [Set.mem_setOf_eq, scalarConjugation_lie, LieEquiv.map_lie] }
  suffices htop : (⊤ : LieSubalgebra ℂ (ℂ ⊗[ℝ] g₁)) ≤ S from
    fun x => htop (LieSubalgebra.mem_top x)
  rw [← hgen, lieSpan_le]
  rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · change Φ (scalarConjugation (e₁ i)) = scalarConjugation (Φ (e₁ i))
    simp only [h₁, h₂, he, hf, map_neg]
  · have h₁' := congrArg scalarConjugation (h₁ i)
    have h₂' := congrArg scalarConjugation (h₂ i)
    simp only [scalarConjugation_twice, map_neg] at h₁' h₂'
    change Φ (scalarConjugation (f₁ i)) = scalarConjugation (Φ (f₁ i))
    have hcf : scalarConjugation (f₁ i) = -e₁ i := by rw [h₁', neg_neg]
    rw [hf, hcf, map_neg, he, h₂', neg_neg]

private def realEmbedding (g : Type*) [LieRing g] [LieAlgebra ℝ g] :
    g →ₗ[ℝ] ℂ ⊗[ℝ] g := TensorProduct.mk ℝ ℂ g 1

private theorem realEmbedding_injective (g : Type*) [LieRing g] [LieAlgebra ℝ g] :
    Function.Injective (realEmbedding g) := by
  intro x y h
  simpa [realEmbedding, tensorRealPart] using congrArg (tensorRealPart g) h

private theorem embLie {G : Type*} [LieRing G] [LieAlgebra ℝ G] (x y : G) :
    realEmbedding G ⁅x,y⁆ = ⁅realEmbedding G x, realEmbedding G y⁆ := by
  simp [realEmbedding, LieAlgebra.ExtendScalars.bracket_tmul]

private theorem recover_fixed {g : Type*} [LieRing g] [LieAlgebra ℝ g]
    (z : ℂ ⊗[ℝ] g) (hz : scalarConjugation z = z) :
    realEmbedding g (tensorRealPart g z) = z := by
  have hIm (x : ℂ ⊗[ℝ] g) : tensorImagPart g (scalarConjugation x) = -(tensorImagPart g x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [tensorImagPart]
    | add x y hx hy => simp [hx, hy, add_comm]
  have hz' : (2 : ℝ) • tensorImagPart g z = 0 := by
    have ht := hIm z
    rw [hz] at ht
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp ht
  have him := (smul_eq_zero.mp hz').resolve_left (by norm_num)
  conv_rhs => rw [complexification_real_imag_decomposition g z, him, TensorProduct.tmul_zero, add_zero]
  rfl

/-- A conjugation-equivariant complex Lie equivalence descends to the
original real Lie algebras, agreeing on their canonical inclusions. -/
theorem exists_real_equiv_of_conjugation
    (Φ : (ℂ ⊗[ℝ] g₁) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] g₂))
    (hΦ : ∀ x, Φ (scalarConjugation x) = scalarConjugation (Φ x)) :
    ∃ f : g₁ ≃ₗ⁅ℝ⁆ g₂, ∀ x : g₁, 1 ⊗ₜ[ℝ] f x = Φ (1 ⊗ₜ[ℝ] x) := by
  let f := (tensorRealPart g₂).comp
    ((Φ.toLinearMap.restrictScalars ℝ).comp (realEmbedding g₁))
  let r := (tensorRealPart g₁).comp
    ((Φ.symm.toLinearMap.restrictScalars ℝ).comp (realEmbedding g₂))
  have hfix (x : g₁) : realEmbedding g₂ (f x) = Φ (realEmbedding g₁ x) := by
    apply recover_fixed
    change scalarConjugation (Φ (realEmbedding g₁ x)) = Φ (realEmbedding g₁ x)
    rw [← hΦ]
    simp [realEmbedding]
  have hrfix (x : g₂) : realEmbedding g₁ (r x) = Φ.symm (realEmbedding g₂ x) := by
    apply recover_fixed
    change scalarConjugation (Φ.symm (realEmbedding g₂ x)) = Φ.symm (realEmbedding g₂ x)
    apply Φ.injective
    change Φ (scalarConjugation _) = Φ (Φ.symm _)
    rw [hΦ]
    simp [realEmbedding]
  let e : g₁ ≃ₗ[ℝ] g₂ := LinearEquiv.ofLinear f r
    (by ext x; apply realEmbedding_injective g₂; simp only [LinearMap.comp_apply,
      LinearMap.id_apply, hfix, hrfix, LieEquiv.apply_symm_apply])
    (by ext x; apply realEmbedding_injective g₁; simp only [LinearMap.comp_apply,
      LinearMap.id_apply, hrfix, hfix, LieEquiv.symm_apply_apply])
  refine ⟨{ __ := e, map_lie' := ?_ }, hfix⟩
  intro x y
  apply realEmbedding_injective g₂
  change realEmbedding g₂ (f ⁅x,y⁆) = 1 ⊗ₜ[ℝ] ⁅f x, f y⁆
  rw [hfix]
  change _ = realEmbedding g₂ ⁅f x, f y⁆
  rw [embLie x y, Φ.map_lie, embLie (f x) (f y), hfix, hfix]

/-- Equality of the complexified subalgebras under a conjugation-equivariant
equivalence descends to equality of the original real subalgebras. -/
theorem exists_real_pair_equiv_of_conjugation
    (h₁ : LieSubalgebra ℝ g₁) (h₂ : LieSubalgebra ℝ g₂)
    (Φ : (ℂ ⊗[ℝ] g₁) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] g₂))
    (hΦ : ∀ x, Φ (scalarConjugation x) = scalarConjugation (Φ x))
    (hmap : (h₁.toSubmodule.baseChange ℂ).map Φ.toLinearMap = h₂.toSubmodule.baseChange ℂ) :
    ∃ f : g₁ ≃ₗ⁅ℝ⁆ g₂, h₁.map f.toLieHom = h₂ ∧ ∀ x : g₁, 1 ⊗ₜ[ℝ] f x = Φ (1 ⊗ₜ[ℝ] x) := by
  obtain ⟨f, hf⟩ := exists_real_equiv_of_conjugation Φ hΦ
  have hiff (x : g₁) : f x ∈ h₂ ↔ x ∈ h₁ := by
    change f x ∈ h₂.toSubmodule ↔ x ∈ h₁.toSubmodule
    rw [← complexification_real_mem_baseChange_iff g₂ h₂.toSubmodule,
      ← complexification_real_mem_baseChange_iff g₁ h₁.toSubmodule, hf, ← hmap]
    constructor
    · rintro ⟨y, hy, hey⟩
      exact Φ.injective hey ▸ hy
    · exact fun hx => ⟨_, hx, rfl⟩
  refine ⟨f, ?_, hf⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hiff _).mpr hx
  · intro hy
    exact ⟨f.symm y, (hiff _).mp (by simpa using hy), f.apply_symm_apply y⟩

end

end CubicAnomaly.Classification.CompactChevalleyDescent
