import CubicAnomaly.Classification.ComplexDuality
import CubicAnomaly.Classification.AmbientComplexification

/-!
# Self-dual constituents of a complex-type complement

An inequivalent irreducible dual pair has exactly four invariant submodules.
Its only self-dual submodules are zero and the whole module.  In particular,
every equivariant map from a self-dual irreducible module to this complement
vanishes.  Applied to the actual compact-pair complexification, this absorbs
every self-dual irreducible ambient constituent into the isotropy algebra.

These statements are independent of highest-weight or root-system
classification.  They supply the constituent obstruction used in the
classical defining-module argument without assuming a table of constituents.
-/

namespace CubicAnomaly.Classification.SelfDualAbsorption

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.ComplexDuality
open Submodule
open scoped TensorProduct

noncomputable section

section General

variable {K L M N S : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [AddCommGroup S] [Module K S] [LieRingModule L S] [LieModule K L S]

/-- Contravariance of the dual preserves equivariant equivalences. -/
def contragredientEquiv (e : M ≃ₗ⁅K,L⁆ N) :
    Module.Dual K N ≃ₗ⁅K,L⁆ Module.Dual K M := {
  e.toLinearEquiv.dualMap with
  map_lie' := by
    intro x f
    ext m
    change -f ⁅x, e m⁆ = -f (e ⁅x, m⁆)
    exact congrArg (fun n : N => -f n) (e.toLieModuleHom.map_lie x m).symm }

/-- The canonical map to the double dual respects the contragredient action. -/
def doubleContragredientEquiv [Module.Finite K M] :
    M ≃ₗ⁅K,L⁆ Module.Dual K (Module.Dual K M) := {
  Module.evalEquiv K M with
  map_lie' := by
    intro x m
    ext f
    simp }

private def equivOfBijective (f : M →ₗ⁅K,L⁆ N) (hf : Function.Bijective f) :
    M ≃ₗ⁅K,L⁆ N := {
  LinearEquiv.ofBijective f.toLinearMap hf with
  toFun := f
  map_lie' := by intro x m; exact f.map_lie x m }

omit [LieAlgebra K L] [LieModule K L M] [LieModule K L N] in
private theorem nonzero_hom_bijective
    [LieModule.IsIrreducible K L M] [LieModule.IsIrreducible K L N]
    (f : M →ₗ⁅K,L⁆ N) (hf : f ≠ 0) : Function.Bijective f := by
  constructor
  · apply (LieModuleHom.ker_eq_bot f).mp
    rcases IsSimpleOrder.eq_bot_or_eq_top f.ker with h | h
    · exact h
    · exact (hf (by
        ext m
        have hm : m ∈ f.ker := by rw [h]; trivial
        exact hm)).elim
  · apply (LieModuleHom.range_eq_top f).mp
    rcases IsSimpleOrder.eq_bot_or_eq_top f.range with h | h
    · exact (hf (by
        ext m
        have hm : f m ∈ f.range := ⟨m, rfl⟩
        rw [h, LieSubmodule.mem_bot] at hm
        exact hm)).elim
    · exact h

/-- A finite-dimensional module with an invariant nondegenerate bilinear
form is equivariantly self-dual; symmetry of the form is unnecessary. -/
theorem invariant_nondegenerate_form_self_dual [Module.Finite K M]
    (Φ : LinearMap.BilinForm K M) (hΦ : Φ.lieInvariant L) (hnd : Φ.Nondegenerate) :
    Nonempty (M ≃ₗ⁅K,L⁆ Module.Dual K M) := by
  let f : M →ₗ⁅K,L⁆ Module.Dual K M := {
    Φ with
    map_lie' := by
      intro x m
      ext n
      exact hΦ x m n }
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero _).mpr
    intro m hm
    apply hnd.1
    intro n
    exact LinearMap.congr_fun hm n
  exact ⟨{
    f.toLinearMap.linearEquivOfInjective hinj (Subspace.dual_finrank_eq.symm) with
    toFun := f
    map_lie' := by intro x m; exact f.map_lie x m }⟩

/-- A self-dual irreducible source has no nonzero map to a non-self-dual
irreducible target. -/
theorem self_dual_irreducible_hom_eq_zero
    [LieModule.IsIrreducible K L S] [LieModule.IsIrreducible K L M]
    (hs : Nonempty (S ≃ₗ⁅K,L⁆ Module.Dual K S))
    (hm : ¬Nonempty (M ≃ₗ⁅K,L⁆ Module.Dual K M))
    (f : S →ₗ⁅K,L⁆ M) : f = 0 := by
  by_contra hf
  obtain ⟨s⟩ := hs
  let e := equivOfBijective f (nonzero_hom_bijective f hf)
  exact hm ⟨e.symm.trans (s.trans (contragredientEquiv e).symm)⟩

/-- Neither member of an inequivalent finite-dimensional dual pair is
self-dual. -/
theorem inequivalent_dual_pair_not_self_dual [Module.Finite K M]
    (d : N ≃ₗ⁅K,L⁆ Module.Dual K M) (hne : ¬Nonempty (M ≃ₗ⁅K,L⁆ N)) :
    ¬Nonempty (M ≃ₗ⁅K,L⁆ Module.Dual K M) ∧
      ¬Nonempty (N ≃ₗ⁅K,L⁆ Module.Dual K N) := by
  constructor
  · rintro ⟨e⟩
    exact hne ⟨e.trans d.symm⟩
  · rintro ⟨e⟩
    exact hne ⟨(doubleContragredientEquiv (K := K) (L := L) (M := M)).trans
      ((contragredientEquiv d).trans e.symm)⟩

private def summandProjection (P Q : LieSubmodule K L M) (hc : IsCompl P Q) :
    M →ₗ⁅K,L⁆ P where
  __ := P.toSubmodule.linearProjOfIsCompl Q.toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr hc)
  map_lie' := by
    intro x m
    apply Subtype.ext
    let hc' := LieSubmodule.isCompl_toSubmodule.mpr hc
    change hc'.projection ⁅x, m⁆ = ⁅x, hc'.projection m⁆
    have hm : m ∈ P ⊔ Q := by rw [hc.sup_eq_top]; trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := (LieSubmodule.mem_sup P Q m).mp hm
    have hp' := (hc'.projection_eq_self_iff p).mpr hp
    have hq' := hc'.projection_apply_eq_zero_iff.mpr hq
    have hxp := (hc'.projection_eq_self_iff ⁅x, p⁆).mpr (P.lie_mem hp)
    have hxq := hc'.projection_apply_eq_zero_iff.mpr (Q.lie_mem (x := x) hq)
    simp only [lie_add, map_add, hp', hq', hxp, hxq, add_zero]

omit [LieAlgebra K L] [LieModule K L M] in
private theorem summandProjection_eq_zero_iff
    (P Q : LieSubmodule K L M) (hc : IsCompl P Q) (m : M) :
    summandProjection P Q hc m = 0 ↔ m ∈ Q := by
  change ((P.toSubmodule.linearProjOfIsCompl Q.toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr hc)) m = 0) ↔ m ∈ Q
  rw [← Subtype.val_inj]
  exact (LieSubmodule.isCompl_toSubmodule.mpr hc).projection_apply_eq_zero_iff

omit [LieAlgebra K L] [LieModule K L M] in
private theorem submodule_le_left_of_right_disjoint
    (P Q T : LieSubmodule K L M) (hc : IsCompl P Q)
    (hP : P ≤ T) (hQ : T.comap Q.incl = ⊥) : T = P := by
  apply le_antisymm _ hP
  intro m hm
  have hm' : m ∈ P ⊔ Q := by rw [hc.sup_eq_top]; trivial
  obtain ⟨p, hp, q, hq, rfl⟩ := (LieSubmodule.mem_sup P Q m).mp hm'
  have hqt : q ∈ T := by
    have := T.sub_mem hm (hP hp)
    simpa only [add_sub_cancel_left] using this
  have hqT : (⟨q, hq⟩ : Q) ∈ T.comap Q.incl := hqt
  rw [hQ, LieSubmodule.mem_bot] at hqT
  have hq0 : q = 0 := congrArg Subtype.val hqT
  simpa [hq0] using hp

omit [LieAlgebra K L] [LieModule K L M] in
private theorem projection_restriction_bijective
    (P Q T : LieSubmodule K L M) (hc : IsCompl P Q)
    [LieModule.IsIrreducible K L P]
    (hT : T ≠ ⊥) (hQ : T.comap Q.incl = ⊥) :
    Function.Bijective ((summandProjection P Q hc).comp T.incl) := by
  let f := (summandProjection P Q hc).comp T.incl
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero _).mpr
    intro m hm
    have hmq : m.val ∈ Q := (summandProjection_eq_zero_iff P Q hc m.val).mp hm
    have hmT : (⟨m.val, hmq⟩ : Q) ∈ T.comap Q.incl := m.property
    rw [hQ, LieSubmodule.mem_bot] at hmT
    exact Subtype.ext (congrArg (fun x : Q => (x : M)) hmT)
  refine ⟨hinj, ?_⟩
  apply (LieModuleHom.range_eq_top f).mp
  rcases IsSimpleOrder.eq_bot_or_eq_top f.range with h | h
  · exfalso
    apply hT
    apply le_antisymm _ bot_le
    intro m hm
    have hfm : f (⟨m, hm⟩ : T) ∈ f.range := ⟨_, rfl⟩
    rw [h, LieSubmodule.mem_bot] at hfm
    have hm0 : (⟨m, hm⟩ : T) = 0 := hinj (by simpa using hfm)
    exact congrArg Subtype.val hm0
  · exact h

omit [LieAlgebra K L] [LieModule K L M] in
/-- An internal sum of two inequivalent irreducible modules has exactly
four invariant submodules. No complete-reducibility theorem is assumed. -/
theorem inequivalent_irreducible_pair_submodules
    (P Q : LieSubmodule K L M) (hc : IsCompl P Q)
    [LieModule.IsIrreducible K L P] [LieModule.IsIrreducible K L Q]
    (hne : ¬Nonempty (P ≃ₗ⁅K,L⁆ Q)) (T : LieSubmodule K L M) :
    T = ⊥ ∨ T = P ∨ T = Q ∨ T = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (T.comap P.incl) with hP | hP <;>
    rcases IsSimpleOrder.eq_bot_or_eq_top (T.comap Q.incl) with hQ | hQ
  · left
    by_contra hT
    let eP := equivOfBijective _ (projection_restriction_bijective P Q T hc hT hQ)
    let eQ := equivOfBijective _ (projection_restriction_bijective Q P T hc.symm hT hP)
    exact hne ⟨eP.symm.trans eQ⟩
  · exact Or.inr (Or.inr (Or.inl (submodule_le_left_of_right_disjoint Q P T hc.symm
      (LieSubmodule.comap_incl_eq_top.mp hQ) hP)))
  · exact Or.inr (Or.inl (submodule_le_left_of_right_disjoint P Q T hc
      (LieSubmodule.comap_incl_eq_top.mp hP) hQ))
  · right; right; right
    apply top_unique
    rw [← hc.sup_eq_top]
    exact sup_le (LieSubmodule.comap_incl_eq_top.mp hP)
      (LieSubmodule.comap_incl_eq_top.mp hQ)

/-- The only self-dual submodules of an inequivalent irreducible dual pair
are zero and the whole module. -/
theorem self_dual_submodule_eq_bot_or_top [Module.Finite K M]
    (P Q : LieSubmodule K L M) (hc : IsCompl P Q)
    [LieModule.IsIrreducible K L P] [LieModule.IsIrreducible K L Q]
    (d : Q ≃ₗ⁅K,L⁆ Module.Dual K P) (hne : ¬Nonempty (P ≃ₗ⁅K,L⁆ Q))
    (T : LieSubmodule K L M) (hT : Nonempty (T ≃ₗ⁅K,L⁆ Module.Dual K T)) :
    T = ⊥ ∨ T = ⊤ := by
  have hns := inequivalent_dual_pair_not_self_dual d hne
  rcases inequivalent_irreducible_pair_submodules P Q hc hne T with h | h | h | h
  · exact Or.inl h
  · subst T; exact (hns.1 hT).elim
  · subst T; exact (hns.2 hT).elim
  · exact Or.inr h

/-- Every map from a self-dual irreducible module into an inequivalent
irreducible dual pair is zero. -/
theorem self_dual_irreducible_pair_hom_eq_zero [Module.Finite K M]
    [LieModule.IsIrreducible K L S]
    (P Q : LieSubmodule K L M) (hc : IsCompl P Q)
    [LieModule.IsIrreducible K L P] [LieModule.IsIrreducible K L Q]
    (d : Q ≃ₗ⁅K,L⁆ Module.Dual K P) (hne : ¬Nonempty (P ≃ₗ⁅K,L⁆ Q))
    (hs : Nonempty (S ≃ₗ⁅K,L⁆ Module.Dual K S)) (f : S →ₗ⁅K,L⁆ M) : f = 0 := by
  have hns := inequivalent_dual_pair_not_self_dual d hne
  have hP := self_dual_irreducible_hom_eq_zero hs hns.1
    ((summandProjection P Q hc).comp f)
  have hQ := self_dual_irreducible_hom_eq_zero hs hns.2
    ((summandProjection Q P hc.symm).comp f)
  ext s
  have hp : f s ∈ P := (summandProjection_eq_zero_iff Q P hc.symm (f s)).mp
    (congrArg (fun t : S →ₗ⁅K,L⁆ Q => t s) hQ)
  have hq : f s ∈ Q := (summandProjection_eq_zero_iff P Q hc (f s)).mp
    (congrArg (fun t : S →ₗ⁅K,L⁆ P => t s) hP)
  have hmem : f s ∈ P ⊓ Q := ⟨hp, hq⟩
  simpa only [hc.inf_eq_bot, LieSubmodule.mem_bot] using hmem

end General

section CompactPair

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- In the actual complexified complement, every invariant self-dual
submodule is zero or the whole complement. -/
theorem compact_complement_self_dual_submodule_eq_bot_or_top
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (T : LieSubmodule ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] orthogonalComplement B h))
    (hT : Nonempty (T ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ T)) :
    T = ⊥ ∨ T = ⊤ := by
  obtain ⟨hc, hP, hQ, ⟨d⟩, hne⟩ :=
    compact_complement_complex_type_decomposition B h hproper e
  letI := hP
  letI := hQ
  exact self_dual_submodule_eq_bot_or_top _ _ hc d hne T hT

/-- No self-dual irreducible module maps nontrivially to the actual
complexified complement of the original compact pair. -/
theorem compact_complement_self_dual_irreducible_hom_eq_zero
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    [LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) S]
    (hs : Nonempty (S ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ S))
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] orthogonalComplement B h)) : f = 0 := by
  obtain ⟨hc, hP, hQ, ⟨d⟩, hne⟩ :=
    compact_complement_complex_type_decomposition B h hproper e
  letI := hP
  letI := hQ
  exact self_dual_irreducible_pair_hom_eq_zero _ _ hc d hne hs f

/-- Every self-dual irreducible ambient constituent is contained in the
actual complexified isotropy algebra.  This conclusion uses only the
original compact form, properness, and complex commutant. -/
theorem compact_self_dual_irreducible_ambient_range_le
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    [LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) S]
    (hs : Nonempty (S ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ S))
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] g)) :
    f.range.toSubmodule ≤ h.toSubmodule.baseChange ℂ := by
  let q := orthogonalComplement B h
  let hc := compact_orthogonal_complement_isCompl B h
  let p := invariantProjection q h.toLieSubmodule hc.symm
  have hf : (complexifiedHom p).comp f = 0 :=
    compact_complement_self_dual_irreducible_hom_eq_zero B h hproper e hs _
  rintro z ⟨s, rfl⟩
  have hz : complexifiedHom p (f s) = 0 :=
    congrArg (fun t : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] q) => t s) hf
  apply (complexification_mem_baseChange_iff_parts g h.toSubmodule (f s)).mpr
  have hr := congrArg (tensorRealPart q) hz
  have hi := congrArg (tensorImagPart q) hz
  change tensorRealPart q (p.toLinearMap.baseChange ℂ (f s)) = 0 at hr
  change tensorImagPart q (p.toLinearMap.baseChange ℂ (f s)) = 0 at hi
  rw [complexification_realPart_natural] at hr
  rw [complexification_imagPart_natural] at hi
  constructor
  · exact hc.symm.projection_apply_eq_zero_iff.mp (congrArg Subtype.val hr)
  · exact hc.symm.projection_apply_eq_zero_iff.mp (congrArg Subtype.val hi)

/-- The absorption criterion applies directly to irreducible constituents
carrying an invariant nondegenerate bilinear form, including trace-form
constructions in classical defining modules. -/
theorem compact_nondegenerate_irreducible_ambient_range_le
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    {S : Type*} [AddCommGroup S] [Module ℂ S] [Module.Finite ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    [LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) S]
    (Φ : LinearMap.BilinForm ℂ S) (hΦ : Φ.lieInvariant (ℂ ⊗[ℝ] h))
    (hnd : Φ.Nondegenerate)
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] g)) :
    f.range.toSubmodule ≤ h.toSubmodule.baseChange ℂ :=
  compact_self_dual_irreducible_ambient_range_le B h hproper e
    (invariant_nondegenerate_form_self_dual Φ hΦ hnd) f

end CompactPair

end

end CubicAnomaly.Classification.SelfDualAbsorption
