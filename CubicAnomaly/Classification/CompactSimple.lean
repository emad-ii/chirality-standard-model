import CubicAnomaly.Classification.Structural

/-!
# Simplicity of the compact ambient algebra

An effective compact pair with an irreducible complex-type complement has a
simple ambient Lie algebra.  This proof uses arbitrary ambient ideals and
their invariant orthogonal complements; it does not assume a decomposition
into a classified list of simple Lie algebras.

Every nonzero ideal projects surjectively onto the irreducible complement.
If two nonzero complementary ideals existed, effectivity would make either
projection an isomorphism.  The transported complex structure would then lie
in the centroid of a compact ideal.  The compact centroid obstruction makes
that ideal abelian, contradicting the already established zero ambient center.
-/

namespace CubicAnomaly.Classification.CompactSimple

open CubicAnomaly.Classification.Structural
open Submodule

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

private noncomputable def projectedIdeal
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (I : LieIdeal ℝ g) :
    I →ₗ⁅ℝ,h⁆ q :=
  (invariantProjection q h.toLieSubmodule hc.symm).comp
    ((LieSubmodule.incl I).restrictLie h)

private theorem projectedIdeal_eq_zero_iff
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (I : LieIdeal ℝ g) (x : I) :
    projectedIdeal h q hc I x = 0 ↔ (x : g) ∈ h := by
  constructor
  · intro hx
    exact hc.symm.projection_apply_eq_zero_iff.mp (congrArg Subtype.val hx)
  · intro hx
    apply Subtype.ext
    exact hc.symm.projection_apply_eq_zero_iff.mpr hx

private theorem projectedIdeal_surjective
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (heff : Effective h)
    [LieModule.IsIrreducible ℝ h q]
    (I : LieIdeal ℝ g) (hI : I ≠ ⊥) :
    Function.Surjective (projectedIdeal h q hc I) := by
  let f := projectedIdeal h q hc I
  apply (LieModuleHom.range_eq_top f).mp
  apply (IsSimpleOrder.eq_bot_or_eq_top f.range).resolve_left
  intro hzero
  apply hI
  apply heff
  intro x hx
  apply (projectedIdeal_eq_zero_iff h q hc I ⟨x, hx⟩).mp
  have hmem : f ⟨x, hx⟩ ∈ f.range := ⟨⟨x, hx⟩, rfl⟩
  rw [hzero, LieSubmodule.mem_bot] at hmem
  exact hmem

private theorem ideal_supplements_subalgebra
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (heff : Effective h)
    [LieModule.IsIrreducible ℝ h q]
    (I : LieIdeal ℝ g) (hI : I ≠ ⊥) :
    h.toSubmodule ⊔ I.toSubmodule = ⊤ := by
  let p := invariantProjection q h.toLieSubmodule hc.symm
  have hsurj := projectedIdeal_surjective h q hc heff I hI
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := hsurj (p x)
  have hpi : p (i : g) = p x := hi
  have hdiff : x - (i : g) ∈ h := by
    apply hc.symm.projection_apply_eq_zero_iff.mp
    have hz : p (x - (i : g)) = 0 := by rw [map_sub, hpi, sub_self]
    exact congrArg Subtype.val hz
  exact Submodule.mem_sup.mpr
    ⟨x - (i : g), hdiff, i, i.property, sub_add_cancel x (i : g)⟩

private theorem complementary_ideals_commute
    (I K : LieIdeal ℝ g) (hc : IsCompl I.toSubmodule K.toSubmodule)
    (x : g) (hx : x ∈ I) (y : g) (hy : y ∈ K) : ⁅x, y⁆ = 0 := by
  have hmem : ⁅x, y⁆ ∈ I.toSubmodule ⊓ K.toSubmodule :=
    ⟨lie_mem_left ℝ g I x y hx, lie_mem_right ℝ g K x y hy⟩
  rw [hc.disjoint.eq_bot, Submodule.mem_bot] at hmem
  exact hmem

private def intersectionIdealOfSupplement
    (h : LieSubalgebra ℝ g) (I K : LieIdeal ℝ g)
    (hspan : h.toSubmodule ⊔ K.toSubmodule = ⊤)
    (hcomm : ∀ x ∈ I, ∀ y ∈ K, ⁅x, y⁆ = 0) : LieIdeal ℝ g where
  __ := h.toSubmodule ⊓ I.toSubmodule
  lie_mem := by
    intro z x hx
    have hz : z ∈ h.toSubmodule ⊔ K.toSubmodule := by rw [hspan]; trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    have hvx : ⁅v, x⁆ = 0 := by rw [← lie_skew, hcomm x hx.2 v hv, neg_zero]
    rw [add_lie, hvx, add_zero]
    exact ⟨h.lie_mem hu hx.1, I.lie_mem hx.2⟩

private theorem projectedIdeal_injective_of_complement
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (heff : Effective h)
    (I K : LieIdeal ℝ g) (hspan : h.toSubmodule ⊔ K.toSubmodule = ⊤)
    (hcomm : ∀ x ∈ I, ∀ y ∈ K, ⁅x, y⁆ = 0) :
    Function.Injective (projectedIdeal h q hc I) := by
  let S := intersectionIdealOfSupplement h I K hspan hcomm
  have hS : S = ⊥ := heff S (by intro x hx; exact hx.1)
  apply (LieModuleHom.ker_eq_bot (projectedIdeal h q hc I)).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hxh : (x : g) ∈ h := (projectedIdeal_eq_zero_iff h q hc I x).mp
    (LieModuleHom.mem_ker.mp hx)
  have hxS : (x : g) ∈ S := ⟨hxh, x.property⟩
  rw [hS, LieSubmodule.mem_bot] at hxS
  exact (LieSubmodule.mem_bot x).mpr (Subtype.ext hxS)

private theorem compact_ideal_orthogonal_isCompl [Module.Finite ℝ g]
    (B : CompactForm g) (I : LieIdeal ℝ g) :
    IsCompl I.toSubmodule
      (LieAlgebra.InvariantForm.orthogonal B.form B.invariant I).toSubmodule := by
  have hrefl : B.form.IsRefl := by
    intro x y hxy
    rw [B.symmetric, hxy]
  have hanisotropic : ∀ x, B.form x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have := B.positive x hne
    linarith
  apply B.form.isCompl_orthogonal_of_restrict_nondegenerate hrefl
  constructor <;> intro x hx <;> apply Subtype.ext
  all_goals exact hanisotropic x (hx x)

private theorem ideal_complex_structure_forces_abelian
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (I K : LieIdeal ℝ g) (q : LieSubmodule ℝ h g)
    (hspan : h.toSubmodule ⊔ K.toSubmodule = ⊤)
    (hcomm : ∀ x ∈ I, ∀ y ∈ K, ⁅x, y⁆ = 0)
    (e : I ≃ₗ⁅ℝ,h⁆ q) (J : q →ₗ⁅ℝ,h⁆ q)
    (hJ : ∀ x, J (J x) = -x) : IsLieAbelian I := by
  let T : I →ₗ⁅ℝ,h⁆ I := e.symm.toLieModuleHom.comp (J.comp e.toLieModuleHom)
  have hT : ∀ x, T (T x) = -x := by
    intro x
    apply e.injective
    change e (e.symm (J (e (e.symm (J (e x)))))) = e (-x)
    simp only [e.apply_symm_apply, hJ, map_neg]
  apply compact_complex_centroid_abelian (B.restrict (I : LieSubalgebra ℝ g))
    T.toLinearMap hT
  intro x y
  have hx : (x : g) ∈ h.toSubmodule ⊔ K.toSubmodule := by rw [hspan]; trivial
  obtain ⟨u, hu, v, hv, hxsplit⟩ := Submodule.mem_sup.mp hx
  have hact (w : I) : ⁅x, w⁆ = ⁅(⟨u, hu⟩ : h), w⁆ := by
    apply Subtype.ext
    change ⁅(x : g), (w : g)⁆ = ⁅u, (w : g)⁆
    rw [← hxsplit, add_lie]
    have hvw : ⁅v, (w : g)⁆ = 0 := by
      rw [← lie_skew, hcomm w w.property v hv, neg_zero]
    rw [hvw, add_zero]
  calc
    T ⁅x, y⁆ = T ⁅(⟨u, hu⟩ : h), y⁆ := by rw [hact y]
    _ = ⁅(⟨u, hu⟩ : h), T y⁆ := T.map_lie _ _
    _ = ⁅x, T y⁆ := (hact (T y)).symm

/-- The ambient algebra is simple for every effective compact pair with an
irreducible invariant complement carrying an equivariant complex structure.
No simple-factor classification or rank bound is assumed. -/
theorem ambient_simple_of_compact_complex_complement [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (heff : Effective h)
    (hproper : h ≠ ⊤) [LieModule.IsIrreducible ℝ h q]
    (J : q →ₗ⁅ℝ,h⁆ q) (hJ : ∀ x, J (J x) = -x) :
    LieAlgebra.IsSimple ℝ g := by
  have hcenter := ambient_center_eq_bot_of_complex_complement h q hc heff J hJ
  constructor
  · intro I
    by_cases hI : I = ⊥
    · exact Or.inl hI
    by_cases hItop : I = ⊤
    · exact Or.inr hItop
    exfalso
    let K := LieAlgebra.InvariantForm.orthogonal B.form B.invariant I
    have hcI : IsCompl I.toSubmodule K.toSubmodule := compact_ideal_orthogonal_isCompl B I
    have hK : K ≠ ⊥ := by
      intro hzero
      have hzero' : K.toSubmodule = ⊥ := congrArg LieSubmodule.toSubmodule hzero
      have htop := hcI.sup_eq_top
      rw [hzero', sup_bot_eq] at htop
      exact hItop ((LieSubmodule.toSubmodule_eq_top I).mp htop)
    have hspan := ideal_supplements_subalgebra h q hc heff K hK
    have hcomm := complementary_ideals_commute I K hcI
    let f := projectedIdeal h q hc I
    have hf : Function.Bijective f :=
      ⟨projectedIdeal_injective_of_complement h q hc heff I K hspan hcomm,
        projectedIdeal_surjective h q hc heff I hI⟩
    let e : I ≃ₗ⁅ℝ,h⁆ q := {
      LinearEquiv.ofBijective f.toLinearMap hf with
      toFun := f
      map_lie' := by intro x y; exact f.map_lie x y }
    letI : IsLieAbelian I := ideal_complex_structure_forces_abelian B h I K q hspan hcomm e J hJ
    have hle := compact_abelian_ideal_le_center B I
    rw [hcenter] at hle
    exact hI (le_bot_iff.mp hle)
  · intro hab
    have htop := (LieAlgebra.isLieAbelian_iff_center_eq_top ℝ g).mp hab
    apply hproper
    apply top_unique
    intro x _
    have hx : x ∈ LieAlgebra.center ℝ g := by rw [htop]; trivial
    rw [hcenter, LieSubmodule.mem_bot] at hx
    simpa only [hx] using h.zero_mem

/-- Ambient simplicity directly from the manuscript's compactness,
effectivity, properness and complex-commutant hypotheses. -/
theorem compact_pair_ambient_simple [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    LieAlgebra.IsSimple ℝ g := by
  let q := orthogonalComplement B h
  have hc := compact_orthogonal_complement_isCompl B h
  have hqne : q ≠ ⊥ := by
    intro hq
    have hq' : q.toSubmodule = ⊥ := congrArg LieSubmodule.toSubmodule hq
    have htop := hc.sup_eq_top
    rw [hq', sup_bot_eq] at htop
    exact hproper ((LieSubalgebra.toSubmodule_eq_top h).mp htop)
  letI : Nontrivial q := (LieSubmodule.nontrivial_iff_ne_bot ℝ h g).mpr hqne
  letI : LieModule.IsIrreducible ℝ h q := compact_complex_commutant_irreducible B h q e
  exact ambient_simple_of_compact_complex_complement B h q hc heff hproper
    (commutantComplexStructure e) (commutant_complex_structure_square e)

end CubicAnomaly.Classification.CompactSimple
