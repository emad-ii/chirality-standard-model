import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Structural lemmas for effective compact Lie-algebra pairs

These statements concern actual Mathlib Lie algebras and Lie submodules, with
no bound on their dimension or rank.  An invariant complement is sufficient
for the faithfulness argument; irreducibility additionally gives maximality.
The compactness input is expressed by a positive definite invariant real
bilinear form, the convention used by the manuscript.

This module does not assert the classification of simple Lie algebras or the
representation-theoretic reduction to the exceptional finite census.
-/

namespace CubicAnomaly.Classification.Structural

open Submodule

section Complement

variable {R g : Type*} [CommRing R] [LieRing g] [LieAlgebra R g]

/-- Effectivity: the subalgebra contains no nonzero ambient ideal. -/
def Effective (h : LieSubalgebra R g) : Prop :=
  ∀ I : LieIdeal R g, I.toSubmodule ≤ h.toSubmodule → I = ⊥

private def complementAnnihilator (h : LieSubalgebra R g)
    (q : LieSubmodule R h g)
    (hspan : h.toSubmodule ⊔ q.toSubmodule = ⊤) : LieIdeal R g where
  carrier := {x | x ∈ h ∧ ∀ y ∈ q, ⁅x, y⁆ = 0}
  zero_mem' := ⟨h.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨hxh, hxq⟩ ⟨hyh, hyq⟩
    exact ⟨h.add_mem hxh hyh, by intro z hz; simp [add_lie, hxq z hz, hyq z hz]⟩
  smul_mem' := by
    rintro t x ⟨hxh, hxq⟩
    exact ⟨h.smul_mem t hxh, by intro z hz; simp [smul_lie, hxq z hz]⟩
  lie_mem := by
    rintro z x ⟨hxh, hxq⟩
    have hz : z ∈ h.toSubmodule ⊔ q.toSubmodule := by rw [hspan]; trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    have hvx : ⁅v, x⁆ = 0 := by rw [← lie_skew, hxq v hv, neg_zero]
    rw [add_lie, hvx, add_zero]
    refine ⟨h.lie_mem hu hxh, ?_⟩
    intro y hy
    have huy : ⁅u, y⁆ ∈ q := q.lie_mem (x := ⟨u, hu⟩) hy
    rw [lie_lie, hxq y hy, lie_zero, hxq _ huy, sub_self]

/-- The action on an invariant complement of an effective pair is faithful. -/
theorem effective_invariant_complement_faithful
    (h : LieSubalgebra R g) (q : LieSubmodule R h g)
    (heff : Effective h) (hspan : h.toSubmodule ⊔ q.toSubmodule = ⊤) :
    LieModule.IsFaithful R h q := by
  rw [LieModule.isFaithful_iff_ker_eq_bot]
  apply le_antisymm _ bot_le
  intro x hx
  have hkill := (LieModule.mem_ker R h q x).mp hx
  have hxI : (x : g) ∈ complementAnnihilator h q hspan := by
    refine ⟨x.property, ?_⟩
    intro y hy
    exact congrArg Subtype.val (hkill ⟨y, hy⟩)
  have hI : complementAnnihilator h q hspan = ⊥ :=
    heff _ (by intro y hy; exact hy.1)
  rw [hI, LieSubmodule.mem_bot] at hxI
  exact (LieSubmodule.mem_bot x).mpr (Subtype.ext hxI)

private def intermediateSubmodule (h k : LieSubalgebra R g) (hhk : h ≤ k) :
    LieSubmodule R h g where
  __ := k.toSubmodule
  lie_mem := fun {x} {_m} hm => k.lie_mem (hhk x.property) hm

/-- Irreducibility of a complement rules out every strict intermediate algebra. -/
theorem intermediate_eq_of_irreducible_complement
    (h : LieSubalgebra R g) (q : LieSubmodule R h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule)
    [LieModule.IsIrreducible R h q]
    (k : LieSubalgebra R g) (hhk : h ≤ k) : k = h ∨ k = ⊤ := by
  let N := (intermediateSubmodule h k hhk).comap q.incl
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · left
    apply le_antisymm _ hhk
    intro x hx
    have hxspan : x ∈ h.toSubmodule ⊔ q.toSubmodule := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hxspan
    have hvk : v ∈ k := by
      have := k.sub_mem hx (hhk hu)
      simpa only [add_sub_cancel_left] using this
    have hvN : (⟨v, hv⟩ : q) ∈ N := hvk
    rw [hN, LieSubmodule.mem_bot] at hvN
    have hvzero : v = 0 := congrArg Subtype.val hvN
    simpa [hvzero] using hu
  · right
    apply top_unique
    intro x _
    have hxspan : x ∈ h.toSubmodule ⊔ q.toSubmodule := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hxspan
    have hvN : (⟨v, hv⟩ : q) ∈ N := by rw [hN]; trivial
    exact k.add_mem (hhk hu) hvN

/-- Maximality is an unbounded structural consequence, not a census assumption. -/
theorem maximal_of_irreducible_complement
    (h : LieSubalgebra R g) (q : LieSubmodule R h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule)
    (hproper : h ≠ ⊤) [LieModule.IsIrreducible R h q] : IsCoatom h := by
  refine ⟨hproper, ?_⟩
  intro k hhk
  exact (intermediate_eq_of_irreducible_complement h q hc k hhk.le).resolve_left
    (fun heq => hhk.ne heq.symm)

end Complement

section ComplexModules

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]

/-- The algebra of real endomorphisms commuting with a Lie action. -/
def lieCommutant : Subalgebra ℝ (Module.End ℝ M) where
  carrier := {f | ∀ (x : L) (m : M), f ⁅x, m⁆ = ⁅x, f m⁆}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro f g hf hg x m
    simp only [LinearMap.add_apply, lie_add]
    rw [hf x m, hg x m]
  mul_mem' := by
    intro f g hf hg x m
    simp only [Module.End.mul_apply]
    rw [hg x m, hf x (g m)]
  algebraMap_mem' := by intro r x m; simp

omit [LieAlgebra ℝ L] [LieModule ℝ L M] in
/-- Projection along invariant complementary submodules commutes with the action. -/
theorem invariant_complement_projection_equivariant
    (N P : LieSubmodule ℝ L M) (hc : IsCompl N.toSubmodule P.toSubmodule)
    (x : L) (m : M) : hc.projection ⁅x, m⁆ = ⁅x, hc.projection m⁆ := by
  have hm : m ∈ N.toSubmodule ⊔ P.toSubmodule := by rw [hc.sup_eq_top]; trivial
  obtain ⟨n, hn, p, hp, rfl⟩ := Submodule.mem_sup.mp hm
  have hn' := (hc.projection_eq_self_iff n).mpr hn
  have hp' := hc.projection_apply_eq_zero_iff.mpr hp
  have hxn := (hc.projection_eq_self_iff ⁅x, n⁆).mpr (N.lie_mem hn)
  have hxp := hc.projection_apply_eq_zero_iff.mpr (P.lie_mem (x := x) hp)
  simp only [lie_add, map_add, hn', hp', hxn, hxp, add_zero]

/-- Projection onto an invariant summand as a morphism of Lie modules. -/
noncomputable def invariantProjection
    (N P : LieSubmodule ℝ L M) (hc : IsCompl N.toSubmodule P.toSubmodule) :
    M →ₗ⁅ℝ,L⁆ N where
  __ := N.toSubmodule.linearProjOfIsCompl P.toSubmodule hc
  map_lie' := by
    intro x m
    apply Subtype.ext
    exact invariant_complement_projection_equivariant N P hc x m

/-- A positive invariant form and complex commutant imply irreducibility.

The proof constructs the projection onto each invariant submodule and uses
the fact that the only idempotents of `ℂ` are zero and one.
-/
theorem irreducible_of_complex_commutant [Module.Finite ℝ M] [Nontrivial M]
    (Φ : LinearMap.BilinForm ℝ M) (hΦrefl : Φ.IsRefl)
    (hΦdef : ∀ x, Φ x x = 0 → x = 0) (hΦinv : Φ.lieInvariant L)
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) :
    LieModule.IsIrreducible ℝ L M := by
  apply LieModule.IsIrreducible.mk
  intro N hN
  let P := LieAlgebra.InvariantForm.orthogonal Φ hΦinv N
  have hc : IsCompl N.toSubmodule P.toSubmodule := by
    apply Φ.isCompl_orthogonal_of_restrict_nondegenerate hΦrefl
    constructor <;> intro x hx <;> apply Subtype.ext
    all_goals exact hΦdef x (hx x)
  let p : lieCommutant (L := L) (M := M) :=
    ⟨hc.projection, invariant_complement_projection_equivariant N P hc⟩
  have hp : p * p = p := Subtype.ext hc.projection_isIdempotentElem
  have he : e p * e p = e p := by rw [← map_mul, hp]
  have he' : e p * (e p - 1) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  rcases mul_eq_zero.mp he' with hz | ho
  · have hp0 : p = 0 := e.injective (by simpa using hz)
    have hp0' : hc.projection = 0 := congrArg Subtype.val hp0
    have hn0 : N.toSubmodule = ⊥ := by rw [← hc.projection_range, hp0']; simp
    exact False.elim (hN (LieSubmodule.toSubmodule_injective hn0))
  · have hp1 : p = 1 := e.injective (by simpa using sub_eq_zero.mp ho)
    have hp1' : hc.projection = 1 := congrArg Subtype.val hp1
    apply LieSubmodule.toSubmodule_injective
    change N.toSubmodule = ⊤
    rw [← hc.projection_range, hp1']
    exact LinearMap.range_id

/-- Multiplication by `i`, transported from the complex commutant. -/
noncomputable def commutantComplexStructure
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) : M →ₗ⁅ℝ,L⁆ M where
  __ := (e.symm Complex.I).val
  map_lie' := (e.symm Complex.I).property _ _

/-- The transported operator really squares to minus the identity. -/
theorem commutant_complex_structure_square
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) (m : M) :
    commutantComplexStructure e (commutantComplexStructure e m) = -m := by
  have h : e.symm Complex.I * e.symm Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  exact congrArg (fun f : lieCommutant (L := L) (M := M) => (f : Module.End ℝ M) m) h

/-- An irreducible real module carrying a complex structure has no fixed vectors. -/
theorem no_fixed_vector_of_irreducible_complex_structure
    [LieModule.IsIrreducible ℝ L M]
    (J : M →ₗ⁅ℝ,L⁆ M) (hJ : ∀ m, J (J m) = -m)
    (m : M) (hm : ∀ x : L, ⁅x, m⁆ = 0) : m = 0 := by
  by_contra hm0
  let N : LieSubmodule ℝ L M := {
    __ := Submodule.span ℝ {m}
    lie_mem := by
      intro x y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [lie_smul, hm, smul_zero]
      exact Submodule.zero_mem _
  }
  have hmN : m ∈ N := Submodule.mem_span_singleton_self m
  have hN : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left (by
    intro h
    rw [h, LieSubmodule.mem_bot] at hmN
    exact hm0 hmN)
  have hJm : J m ∈ N := by rw [hN]; trivial
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hJm
  have hsq : (a * a) • m = -m := by
    calc
      (a * a) • m = J (J m) := by rw [← ha, map_smul, ← ha, mul_smul]
      _ = -m := hJ m
  have hz : (a * a + 1) • m = 0 := by rw [add_smul, one_smul, hsq, neg_add_cancel]
  have ha0 : a * a + 1 ≠ 0 := by nlinarith [sq_nonneg a]
  exact hm0 ((smul_eq_zero.mp hz).resolve_left ha0)

end ComplexModules

section CenterReduction

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- The ambient center vanishes for an effective irreducible complex complement. -/
theorem ambient_center_eq_bot_of_complex_complement
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (heff : Effective h)
    [LieModule.IsIrreducible ℝ h q]
    (J : q →ₗ⁅ℝ,h⁆ q) (hJ : ∀ x, J (J x) = -x) :
    LieAlgebra.center ℝ g = ⊥ := by
  apply heff
  intro z hz
  let p := invariantProjection q h.toLieSubmodule hc.symm
  have hpz : p z = 0 := by
    apply no_fixed_vector_of_irreducible_complex_structure J hJ
    intro x
    rw [← p.map_lie]
    have hzx : ⁅x, z⁆ = 0 := hz x.val
    rw [hzx, map_zero]
  have hpz' : hc.symm.projection z = 0 := congrArg Subtype.val hpz
  exact hc.symm.projection_apply_eq_zero_iff.mp hpz'

end CenterReduction

section QuotientBridge

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- The quotient and the chosen invariant complement are equivariantly isomorphic. -/
noncomputable def quotientComplementEquiv
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) :
    (g ⧸ h.toLieSubmodule) ≃ₗ⁅ℝ,h⁆ q :=
  ({ (Submodule.quotientEquivOfIsCompl h.toSubmodule q.toSubmodule hc).symm with
      map_lie' := by intro x m; rfl } : q ≃ₗ⁅ℝ,h⁆ (g ⧸ h.toLieSubmodule)).symm

/-- The quotient-complement equivalence sends the class of a complement vector to itself. -/
theorem quotient_complement_equiv_apply_mk
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (x : q) :
    quotientComplementEquiv h q hc (LieSubmodule.Quotient.mk' h.toLieSubmodule x) = x :=
  (quotientComplementEquiv h q hc).apply_symm_apply x

end QuotientBridge

section Compact

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- The algebraic compactness hypothesis used by the manuscript. -/
structure CompactForm (g : Type*) [LieRing g] [LieAlgebra ℝ g] where
  form : LinearMap.BilinForm ℝ g
  symmetric : ∀ x y, form x y = form y x
  positive : ∀ x, x ≠ 0 → 0 < form x x
  invariant : form.lieInvariant g

private theorem compact_form_anisotropic (B : CompactForm g) (x : g)
    (hx : B.form x x = 0) : x = 0 := by
  by_contra h
  have := B.positive x h
  linarith

private theorem compact_form_reflexive (B : CompactForm g) : B.form.IsRefl := by
  intro x y hxy
  rw [B.symmetric, hxy]

private theorem compact_form_nondegenerate (B : CompactForm g) : B.form.Nondegenerate := by
  constructor <;> intro x hx <;> exact compact_form_anisotropic B x (hx x)

/-- Orthogonal complements in a compact Lie algebra are invariant. -/
def orthogonalComplement (B : CompactForm g) (h : LieSubalgebra ℝ g) :
    LieSubmodule ℝ h g :=
  LieAlgebra.InvariantForm.orthogonal B.form
    (fun x y z => B.invariant x.val y z) h.toLieSubmodule

/-- Positive definiteness supplies the direct sum used in the structural proof. -/
theorem compact_orthogonal_complement_isCompl [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) :
    IsCompl h.toSubmodule (orthogonalComplement B h).toSubmodule := by
  apply B.form.isCompl_orthogonal_of_restrict_nondegenerate (compact_form_reflexive B)
  constructor <;> intro x hx <;> apply Subtype.ext
  all_goals exact compact_form_anisotropic B x (hx x)

/-- A Lie subalgebra inherits the positive invariant form. -/
def CompactForm.restrict (B : CompactForm g) (h : LieSubalgebra ℝ g) : CompactForm h where
  form := B.form.restrict h.toSubmodule
  symmetric x y := B.symmetric x y
  positive x hx := B.positive x (fun hzero => hx (Subtype.ext hzero))
  invariant x y z := B.invariant x.val y.val z.val

/-- Compactness supplies complete reducibility in the complex-commutant argument. -/
theorem compact_complex_commutant_irreducible [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    [Nontrivial q] (e : lieCommutant (L := h) (M := q) ≃ₐ[ℝ] ℂ) :
    LieModule.IsIrreducible ℝ h q := by
  apply irreducible_of_complex_commutant (L := h) (M := q)
    (B.form.restrict q.toSubmodule) _ _ _ e
  · intro x y hxy
    exact (B.symmetric y x).trans hxy
  · intro x hx
    exact Subtype.ext (compact_form_anisotropic B x hx)
  · intro x y z
    exact B.invariant x.val y.val z.val

/-- Every abelian ideal of a compact Lie algebra is central. -/
theorem compact_abelian_ideal_le_center (B : CompactForm g)
    (I : LieIdeal ℝ g) [IsLieAbelian I] : I ≤ LieAlgebra.center ℝ g := by
  intro x hx y
  have hb : ⁅x, y⁆ ∈ I := lie_mem_left ℝ g I x y hx
  have hzero : ⁅x, ⁅x, y⁆⁆ = 0 :=
    congrArg Subtype.val (trivial_lie_zero I I (⟨x, hx⟩ : I) (⟨⁅x, y⁆, hb⟩ : I))
  have hxy : ⁅x, y⁆ = 0 := by
    apply compact_form_anisotropic B
    rw [B.invariant, hzero, map_zero, neg_zero]
  rw [← lie_skew, hxy, neg_zero]

/-- A compact real Lie algebra with zero center is semisimple. -/
theorem compact_semisimple_of_center_eq_bot [Module.Finite ℝ g]
    (B : CompactForm g) (hcenter : LieAlgebra.center ℝ g = ⊥) :
    LieAlgebra.IsSemisimple ℝ g := by
  apply LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate B.form
    (compact_form_nondegenerate B) B.invariant (compact_form_reflexive B)
  intro I hI habelian
  letI : IsLieAbelian I := habelian
  have hle := compact_abelian_ideal_le_center B I
  rw [hcenter] at hle
  exact hI.ne_bot (le_bot_iff.mp hle)

/-- A compact Lie algebra admitting a complex structure in its centroid is abelian.

The two skew-adjoint operators `ad x` and `ad (J x)` have opposite squares.
Positive definiteness therefore forces both to vanish.  No classification of
compact simple Lie algebras is needed for this obstruction.
-/
theorem compact_complex_centroid_abelian (B : CompactForm g)
    (J : g →ₗ[ℝ] g) (hJ : ∀ x, J (J x) = -x)
    (hcomm : ∀ x y : g, J ⁅x, y⁆ = ⁅x, J y⁆) : IsLieAbelian g := by
  have hleft : ∀ x y : g, ⁅J x, y⁆ = J ⁅x, y⁆ := by
    intro x y
    rw [← lie_skew, ← hcomm, ← map_neg, lie_skew]
  have hnonneg : ∀ x, 0 ≤ B.form x x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (B.positive x hx).le
  constructor
  intro x y
  have hsquare : ⁅J x, ⁅J x, y⁆⁆ = -⁅x, ⁅x, y⁆⁆ := by
    rw [hleft, hleft, ← hcomm, hJ]
  have hsum : B.form ⁅J x, y⁆ ⁅J x, y⁆ + B.form ⁅x, y⁆ ⁅x, y⁆ = 0 := by
    rw [B.invariant, hsquare, map_neg, neg_neg, B.invariant]
    exact add_neg_cancel _
  apply compact_form_anisotropic B
  have h1 := hnonneg ⁅J x, y⁆
  have h2 := hnonneg ⁅x, y⁆
  linarith

/-- The first structural reduction, directly from compactness and the commutant.

The hypotheses are the manuscript's effectivity, properness and complex-type
endomorphism condition.  The cubic condition is not needed for these conclusions.
-/
theorem compact_pair_reduction_to_semisimple_ambient [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    IsCoatom h ∧ LieModule.IsFaithful ℝ h (orthogonalComplement B h) ∧
      LieAlgebra.center ℝ g = ⊥ ∧ LieAlgebra.IsSemisimple ℝ g := by
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
  have hcenter := ambient_center_eq_bot_of_complex_complement h q hc heff
    (commutantComplexStructure e) (commutant_complex_structure_square e)
  exact ⟨maximal_of_irreducible_complement h q hc hproper,
    effective_invariant_complement_faithful h q heff hc.sup_eq_top,
    hcenter, compact_semisimple_of_center_eq_bot B hcenter⟩

end Compact

end CubicAnomaly.Classification.Structural
