import CubicAnomaly.Classification.SelfDualAbsorption

/-!
# Self-dual blocks in the actual compact quotient

An injective map from a nonzero self-dual module into an inequivalent
irreducible dual pair is surjective. Consequently it cannot coexist with
another nonzero block whose sum injects. The compact specialization uses
the actual complexified orthogonal-complement projection and identifies
its kernel with the actual complexified isotropy.
-/

namespace CubicAnomaly.Classification.SelfDualQuotientObstruction

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.SelfDualAbsorption
open Submodule
open scoped TensorProduct

noncomputable section

section General

variable {K L M S T : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup S] [Module K S] [LieRingModule L S] [LieModule K L S]
  [AddCommGroup T] [Module K T] [LieRingModule L T] [LieModule K L T]

/-- An injective equivariant map identifies its source with its actual
invariant range. -/
def equivariantRangeEquiv (f : S →ₗ⁅K,L⁆ M) (hf : Function.Injective f) :
    S ≃ₗ⁅K,L⁆ f.range := by
  let F := f.codRestrict f.range (fun s => ⟨s, rfl⟩)
  have hF : Function.Bijective F := by
    constructor
    · intro s t h
      exact hf (congrArg Subtype.val h)
    · rintro ⟨m, s, rfl⟩
      exact ⟨s, rfl⟩
  exact { F, LinearEquiv.ofBijective F.toLinearMap hF with }

/-- Actual invariant ranges of injective self-dual modules are self-dual. -/
theorem injective_range_self_dual (f : S →ₗ⁅K,L⁆ M) (hf : Function.Injective f)
    (hs : Nonempty (S ≃ₗ⁅K,L⁆ Module.Dual K S)) :
    Nonempty (f.range ≃ₗ⁅K,L⁆ Module.Dual K f.range) := by
  obtain ⟨d⟩ := hs
  let e := equivariantRangeEquiv f hf
  exact ⟨e.symm.trans (d.trans (contragredientEquiv e).symm)⟩

/-- If a module has no nonzero proper self-dual submodule, every
embedding of a nonzero self-dual module is surjective. -/
theorem self_dual_embedding_surjective [Nontrivial S]
    (hM : ∀ U : LieSubmodule K L M,
      Nonempty (U ≃ₗ⁅K,L⁆ Module.Dual K U) → U = ⊥ ∨ U = ⊤)
    (f : S →ₗ⁅K,L⁆ M) (hf : Function.Injective f)
    (hs : Nonempty (S ≃ₗ⁅K,L⁆ Module.Dual K S)) : Function.Surjective f := by
  rcases hM f.range (injective_range_self_dual f hf hs) with h | h
  · obtain ⟨s, hs0⟩ := exists_ne (0 : S)
    exfalso
    apply hs0
    apply hf
    rw [map_zero]
    have hmem : f s ∈ f.range := ⟨s, rfl⟩
    simpa only [h, LieSubmodule.mem_bot] using hmem
  · exact (LieModuleHom.range_eq_top f).mp h

omit [LieModule K L T] in
/-- Two nonzero independent blocks cannot embed in a module having no
proper nonzero self-dual submodule when either block is self-dual. -/
theorem two_blocks_obstruction [Nontrivial S] [Nontrivial T]
    (hM : ∀ U : LieSubmodule K L M,
      Nonempty (U ≃ₗ⁅K,L⁆ Module.Dual K U) → U = ⊥ ∨ U = ⊤)
    (f : S →ₗ⁅K,L⁆ M) (g : T →ₗ⁅K,L⁆ M)
    (hs : Nonempty (S ≃ₗ⁅K,L⁆ Module.Dual K S))
    (hsep : ∀ s t, f s + g t = 0 → s = 0 ∧ t = 0) : False := by
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro s h
    exact (hsep s 0 (by simpa only [map_zero, add_zero] using h)).1
  have hsurj := self_dual_embedding_surjective hM f hf hs
  obtain ⟨t, ht⟩ := exists_ne (0 : T)
  obtain ⟨s, hs'⟩ := hsurj (-g t)
  exact ht (hsep s t (by rw [hs', neg_add_cancel])).2

end General

section Compact

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The actual complexified projection onto the compact orthogonal
complement, along the original isotropy algebra. -/
def complexifiedComplementProjection (B : CompactForm g) (h : LieSubalgebra ℝ g) :
    (ℂ ⊗[ℝ] g) →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] orthogonalComplement B h) :=
  complexifiedHom (invariantProjection (orthogonalComplement B h) h.toLieSubmodule
    (compact_orthogonal_complement_isCompl B h).symm)

/-- The kernel of the actual complexified complement projection is
exactly the scalar extension of the original isotropy subspace. -/
theorem complexified_complement_projection_eq_zero_iff
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (z : ℂ ⊗[ℝ] g) :
    complexifiedComplementProjection B h z = 0 ↔ z ∈ h.toSubmodule.baseChange ℂ := by
  let q := orthogonalComplement B h
  let hc := compact_orthogonal_complement_isCompl B h
  let p := invariantProjection q h.toLieSubmodule hc.symm
  change p.toLinearMap.baseChange ℂ z = 0 ↔ _
  rw [complexification_zero_iff_parts q,
    complexification_realPart_natural, complexification_imagPart_natural,
    complexification_mem_baseChange_iff_parts]
  have hp (x : g) : p x = 0 ↔ x ∈ h := by
    rw [← Subtype.val_inj]
    exact hc.symm.projection_apply_eq_zero_iff
  exact and_congr (hp _) (hp _)

/-- An actual self-dual block whose projection is injective fills the
whole complexified compact complement. -/
theorem compact_self_dual_block_projection_surjective
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    {S : Type*} [AddCommGroup S] [Module ℂ S] [Nontrivial S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] g))
    (hs : Nonempty (S ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ S))
    (hsep : ∀ s, f s ∈ h.toSubmodule.baseChange ℂ → s = 0) :
    Function.Surjective ((complexifiedComplementProjection B h).comp f) := by
  apply self_dual_embedding_surjective
    (compact_complement_self_dual_submodule_eq_bot_or_top B h hproper e) _ _ hs
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs'
  exact hsep s ((complexified_complement_projection_eq_zero_iff B h (f s)).mp hs')

/-- Two actual ambient blocks that are independent modulo the original
isotropy contradict the complex-type complement, as soon as one nonzero
block is self-dual. No irreducibility of either block is assumed. -/
theorem compact_two_ambient_blocks_obstruction
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    {S T : Type*} [AddCommGroup S] [Module ℂ S] [Nontrivial S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    [AddCommGroup T] [Module ℂ T] [Nontrivial T]
    [LieRingModule (ℂ ⊗[ℝ] h) T] [LieModule ℂ (ℂ ⊗[ℝ] h) T]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] g))
    (g' : T →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] g))
    (hs : Nonempty (S ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ S))
    (hsep : ∀ s t, f s + g' t ∈ h.toSubmodule.baseChange ℂ → s = 0 ∧ t = 0) :
    False := by
  apply two_blocks_obstruction
    (compact_complement_self_dual_submodule_eq_bot_or_top B h hproper e)
    ((complexifiedComplementProjection B h).comp f)
    ((complexifiedComplementProjection B h).comp g') hs
  intro s t hst
  apply hsep s t
  apply (complexified_complement_projection_eq_zero_iff B h _).mp
  simpa only [map_add] using hst

end Compact

end

end CubicAnomaly.Classification.SelfDualQuotientObstruction
