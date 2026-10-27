import CubicAnomaly.Classification.TensorFactorDuality

/-!
# An invariant skew operator on an inequivalent dual pair

Every invariant bilinear form vanishes on an irreducible module that is
not self-dual. Therefore the difference of the two actual summand
projections of an inequivalent irreducible dual pair is a nonzero
equivariant operator skew for every invariant bilinear form.
-/

namespace CubicAnomaly.Classification.DualPairSkew

open CubicAnomaly.Classification.SelfDualAbsorption
open CubicAnomaly.Classification.TensorFactorDuality
open Submodule

noncomputable section

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- A finite irreducible module that is not self-dual has no nonzero
invariant bilinear form. -/
theorem invariant_form_eq_zero_of_not_self_dual
    [Module.Finite K M] [LieModule.IsIrreducible K L M]
    (hns : ¬Nonempty (M ≃ₗ⁅K,L⁆ Module.Dual K M))
    (Φ : LinearMap.BilinForm K M) (hΦ : Φ.lieInvariant L) : Φ = 0 := by
  by_contra hne
  exact hns (invariant_nondegenerate_form_self_dual Φ hΦ
    (invariant_form_nondegenerate_of_ne_zero Φ hΦ hne))

private def invariantSummandProjection (P Q : LieSubmodule K L M)
    (hc : IsCompl P Q) : M →ₗ⁅K,L⁆ P where
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

/-- The difference of the actual invariant summand projections. -/
def dualPairSign (P Q : LieSubmodule K L M) (hc : IsCompl P Q) : M →ₗ⁅K,L⁆ M :=
  P.incl.comp (invariantSummandProjection P Q hc) -
    Q.incl.comp (invariantSummandProjection Q P hc.symm)

omit [LieAlgebra K L] [LieModule K L M] in
private theorem dualPairSign_left (P Q : LieSubmodule K L M) (hc : IsCompl P Q) (p : P) :
    dualPairSign P Q hc p = p := by
  let hc' := LieSubmodule.isCompl_toSubmodule.mpr hc
  have hp : invariantSummandProjection P Q hc p = p :=
    Subtype.ext ((hc'.projection_eq_self_iff p.val).mpr p.property)
  have hq : invariantSummandProjection Q P hc.symm p = 0 :=
    Subtype.ext (hc'.symm.projection_apply_eq_zero_iff.mpr p.property)
  change (invariantSummandProjection P Q hc p : M) -
    (invariantSummandProjection Q P hc.symm p : M) = p
  rw [hp, hq]
  simp

omit [LieAlgebra K L] [LieModule K L M] in
private theorem dualPairSign_right (P Q : LieSubmodule K L M) (hc : IsCompl P Q) (q : Q) :
    dualPairSign P Q hc q = -q := by
  let hc' := LieSubmodule.isCompl_toSubmodule.mpr hc
  have hp : invariantSummandProjection P Q hc q = 0 :=
    Subtype.ext (hc'.projection_apply_eq_zero_iff.mpr q.property)
  have hq : invariantSummandProjection Q P hc.symm q = q :=
    Subtype.ext ((hc'.symm.projection_eq_self_iff q.val).mpr q.property)
  change (invariantSummandProjection P Q hc q : M) -
    (invariantSummandProjection Q P hc.symm q : M) = -q
  rw [hp, hq]
  simp

omit [LieAlgebra K L] [LieModule K L M] in
/-- The sign operator is nonzero whenever its first summand is nonzero. -/
theorem dual_pair_sign_ne_zero (P Q : LieSubmodule K L M) (hc : IsCompl P Q)
    [Nontrivial P] : dualPairSign P Q hc ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_ne (0 : P)
  intro hz
  apply hp
  apply Subtype.ext
  have he := congrArg (fun f : M →ₗ⁅K,L⁆ M => f p.val) hz
  simpa only [dualPairSign_left, LieModuleHom.zero_apply] using he

/-- On complementary non-self-dual irreducibles, the actual sign operator
is skew for every invariant bilinear form. -/
theorem dual_pair_sign_skew
    [Module.Finite K M]
    (P Q : LieSubmodule K L M) (hc : IsCompl P Q)
    [LieModule.IsIrreducible K L P] [LieModule.IsIrreducible K L Q]
    (hP : ¬Nonempty (P ≃ₗ⁅K,L⁆ Module.Dual K P))
    (hQ : ¬Nonempty (Q ≃ₗ⁅K,L⁆ Module.Dual K Q))
    (Φ : LinearMap.BilinForm K M) (hΦ : Φ.lieInvariant L) (x y : M) :
    Φ (dualPairSign P Q hc x) y = -Φ x (dualPairSign P Q hc y) := by
  have hpp : ∀ p p' : P, Φ p p' = 0 := by
    have h := invariant_form_eq_zero_of_not_self_dual hP (Φ.restrict P.toSubmodule)
      (fun z p p' => hΦ z p p')
    intro p p'
    exact congrArg (fun B : LinearMap.BilinForm K P => B p p') h
  have hqq : ∀ q q' : Q, Φ q q' = 0 := by
    have h := invariant_form_eq_zero_of_not_self_dual hQ (Φ.restrict Q.toSubmodule)
      (fun z q q' => hΦ z q q')
    intro q q'
    exact congrArg (fun B : LinearMap.BilinForm K Q => B q q') h
  have hx : x ∈ P ⊔ Q := by rw [hc.sup_eq_top]; trivial
  have hy : y ∈ P ⊔ Q := by rw [hc.sup_eq_top]; trivial
  obtain ⟨p, hp, q, hq, rfl⟩ := (LieSubmodule.mem_sup P Q x).mp hx
  obtain ⟨p', hp', q', hq', rfl⟩ := (LieSubmodule.mem_sup P Q y).mp hy
  have hpl := dualPairSign_left P Q hc ⟨p, hp⟩
  have hpr := dualPairSign_left P Q hc ⟨p', hp'⟩
  have hql := dualPairSign_right P Q hc ⟨q, hq⟩
  have hqr := dualPairSign_right P Q hc ⟨q', hq'⟩
  change dualPairSign P Q hc p = p at hpl
  change dualPairSign P Q hc p' = p' at hpr
  change dualPairSign P Q hc q = -q at hql
  change dualPairSign P Q hc q' = -q' at hqr
  have hp0 : Φ p p' = 0 := hpp ⟨p, hp⟩ ⟨p', hp'⟩
  have hq0 : Φ q q' = 0 := hqq ⟨q, hq⟩ ⟨q', hq'⟩
  simp only [map_add, hpl, hpr, hql, hqr, LinearMap.add_apply,
    map_neg, LinearMap.neg_apply, hp0, hq0]
  ring

/-- An inequivalent finite irreducible dual pair has a nonzero equivariant
operator skew for every invariant bilinear form, without a chosen form
or nondegeneracy input. -/
theorem inequivalent_dual_pair_exists_skew_end
    [Module.Finite K M]
    (P Q : LieSubmodule K L M) (hc : IsCompl P Q)
    [LieModule.IsIrreducible K L P] [LieModule.IsIrreducible K L Q]
    (d : Q ≃ₗ⁅K,L⁆ Module.Dual K P) (hne : ¬Nonempty (P ≃ₗ⁅K,L⁆ Q)) :
    ∃ D : M →ₗ⁅K,L⁆ M, D ≠ 0 ∧
      ∀ (Φ : LinearMap.BilinForm K M), Φ.lieInvariant L →
        ∀ x y, Φ (D x) y = -Φ x (D y) := by
  letI : Nontrivial P := LieModule.nontrivial_of_isIrreducible K L P
  have hns := inequivalent_dual_pair_not_self_dual d hne
  exact ⟨dualPairSign P Q hc, dual_pair_sign_ne_zero P Q hc,
    fun Φ hΦ x y => dual_pair_sign_skew P Q hc hns.1 hns.2 Φ hΦ x y⟩

/-- An actual equivariant equivalence transports a nonzero endomorphism
skew for all invariant forms to an operator with the same property. -/
theorem exists_skew_end_of_equiv
    {S : Type*} [AddCommGroup S] [Module K S] [LieRingModule L S] [LieModule K L S]
    (E : S ≃ₗ⁅K,L⁆ M)
    (h : ∃ D : M →ₗ⁅K,L⁆ M, D ≠ 0 ∧
      ∀ (Φ : LinearMap.BilinForm K M), Φ.lieInvariant L →
        ∀ x y, Φ (D x) y = -Φ x (D y)) :
    ∃ D : S →ₗ⁅K,L⁆ S, D ≠ 0 ∧
      ∀ (Φ : LinearMap.BilinForm K S), Φ.lieInvariant L →
        ∀ x y, Φ (D x) y = -Φ x (D y) := by
  obtain ⟨D, hD, hsk⟩ := h
  let F := E.symm.toLieModuleHom.comp (D.comp E.toLieModuleHom)
  refine ⟨F, ?_, ?_⟩
  · intro hz
    apply hD
    ext m
    obtain ⟨s, rfl⟩ := E.surjective m
    have hs := congrArg (fun f : S →ₗ⁅K,L⁆ S => E (f s)) hz
    change E (E.symm (D (E s))) = E 0 at hs
    simpa only [E.apply_symm_apply, map_zero] using hs
  · intro Φ hΦ s t
    let Ψ : LinearMap.BilinForm K M :=
      Φ.compl₁₂ E.symm.toLinearEquiv.toLinearMap E.symm.toLinearEquiv.toLinearMap
    have hi : Ψ.lieInvariant L := by
      intro x m n
      change Φ (E.symm ⁅x, m⁆) (E.symm n) = -Φ (E.symm m) (E.symm ⁅x, n⁆)
      have hm : E.symm ⁅x, m⁆ = ⁅x, E.symm m⁆ := E.symm.toLieModuleHom.map_lie x m
      have hn : E.symm ⁅x, n⁆ = ⁅x, E.symm n⁆ := E.symm.toLieModuleHom.map_lie x n
      rw [hm, hn]
      exact hΦ x (E.symm m) (E.symm n)
    have hs := hsk Ψ hi (E s) (E t)
    change Φ (E.symm (D (E s))) (E.symm (E t)) =
      -Φ (E.symm (E s)) (E.symm (D (E t))) at hs
    simpa only [E.symm_apply_apply] using hs

end

end CubicAnomaly.Classification.DualPairSkew
