import CubicAnomaly.Classification.Structural
import CubicAnomaly.Classification.CompactKilling
import CubicAnomaly.Classification.HermitianRealization
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Ring

/-!
# Bracket obstructions for a complex isotropy complement

An invariant complex structure is automatically skew-adjoint for every
positive invariant real bilinear form when the real commutant is `ℂ`.
If the complement is symmetric, this structure extends by zero on the
isotropy algebra to a derivation of the whole algebra.  For a Killing
ambient algebra the derivation is inner; the vanishing isotropy centralizer
then rules it out.

This eliminates the involutive branch uniformly.  It does not claim that
every complex-type complement defines an order-three grading: that stronger
statement fails without further hypotheses.
-/

namespace CubicAnomaly.Classification.CyclicBracket

open CubicAnomaly.Classification.Structural
open Submodule

section Adjoint

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]
  [Module.Finite ℝ M] [Nontrivial M]

/-- The complex structure in the commutant is skew-adjoint for any positive
invariant real bilinear form.  Its skewness is a conclusion, not extra data. -/
theorem complex_commutant_structure_skew
    (Φ : LinearMap.BilinForm ℝ M)
    (hpositive : ∀ x : M, x ≠ 0 → 0 < Φ x x)
    (hinvariant : Φ.lieInvariant L)
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) (x y : M) :
    Φ (commutantComplexStructure e x) y =
      -Φ x (commutantComplexStructure e y) := by
  let J := commutantComplexStructure e
  have hJ := commutant_complex_structure_square e
  change ∀ m, J (J m) = -m at hJ
  have hdef : ∀ x : M, Φ x x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have := hpositive x hx0
    linarith
  have hnondeg : Φ.Nondegenerate := by
    constructor <;> intro x hx <;> exact hdef x (hx x)
  let A := Φ.leftAdjointOfNondegenerate hnondeg J.toLinearMap
  have hA : ∀ x y : M, Φ (A x) y = Φ x (J y) :=
    Φ.isAdjointPairLeftAdjointOfNondegenerate hnondeg J.toLinearMap
  have hAeq : ∀ z : L, ∀ x : M, A ⁅z, x⁆ = ⁅z, A x⁆ := by
    intro z x
    apply sub_eq_zero.mp
    apply hnondeg.1
    intro y
    rw [map_sub, LinearMap.sub_apply, hA, hinvariant, ← J.map_lie, ← hA,
      hinvariant, sub_self]
  let a : lieCommutant (L := L) (M := M) := ⟨A, hAeq⟩
  have hAsquare : a * a = -1 := by
    apply Subtype.ext
    ext x
    apply sub_eq_zero.mp
    apply hnondeg.1
    intro y
    change Φ (A (A x) - -x) y = 0
    simp only [map_sub, LinearMap.sub_apply, hA, hJ, map_neg,
      LinearMap.neg_apply, sub_self]
  have hasquare : e a * e a = -1 := by
    rw [← map_mul, hAsquare, map_neg, map_one]
  have hafactor : (e a - Complex.I) * (e a + Complex.I) = 0 := by
    calc
      (e a - Complex.I) * (e a + Complex.I) =
          e a * e a - Complex.I * Complex.I := by ring
      _ = 0 := by rw [hasquare, Complex.I_mul_I, sub_self]
  have haneq : e a ≠ Complex.I := by
    intro ha
    have haJ : a = e.symm Complex.I := e.injective (by simpa using ha)
    have hAJ : ∀ x : M, A x = J x := fun x =>
      congrArg (fun f : lieCommutant (L := L) (M := M) => (f : Module.End ℝ M) x) haJ
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    have hJv : J v ≠ 0 := by
      intro hz
      have := hJ v
      change J (J v) = -v at this
      rw [hz, map_zero] at this
      exact hv (neg_eq_zero.mp this.symm)
    have hsq : Φ (J v) (J v) = -Φ v v := by
      calc
        Φ (J v) (J v) = Φ (A v) (J v) := by rw [hAJ]
        _ = Φ v (J (J v)) := hA v (J v)
        _ = -Φ v v := by rw [hJ, map_neg]
    have hp := hpositive v hv
    have hpJ := hpositive (J v) hJv
    linarith
  have haI : e a = -Complex.I :=
    eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hafactor).resolve_left
      (fun hz => haneq (sub_eq_zero.mp hz)))
  have hanegJ : a = -e.symm Complex.I := e.injective (by simpa using haI)
  have hAJ : A x = -J x :=
    congrArg (fun f : lieCommutant (L := L) (M := M) => (f : Module.End ℝ M) x) hanegJ
  have := hA x y
  rw [hAJ, map_neg, LinearMap.neg_apply] at this
  change Φ (J x) y = -Φ x (J y)
  linarith

end Adjoint

section Complement

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- A centerless isotropy algebra and an irreducible complex complement have
zero ambient centralizer.  No equality-of-ranks assumption is needed. -/
theorem centralizer_vanishes_of_complex_complement
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule)
    [LieModule.IsIrreducible ℝ h q]
    (J : q →ₗ⁅ℝ,h⁆ q) (hJ : ∀ x, J (J x) = -x)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    (z : g) (hz : ∀ x : h, ⁅x.val, z⁆ = 0) : z = 0 := by
  let p := invariantProjection q h.toLieSubmodule hc.symm
  have hpz : p z = 0 := by
    apply no_fixed_vector_of_irreducible_complex_structure J hJ
    intro x
    rw [← p.map_lie]
    change p ⁅x.val, z⁆ = 0
    rw [hz x, map_zero]
  have hzh : z ∈ h :=
    hc.symm.projection_apply_eq_zero_iff.mp (congrArg Subtype.val hpz)
  have hzcenter : (⟨z, hzh⟩ : h) ∈ LieAlgebra.center ℝ h := by
    intro x
    exact Subtype.ext (hz x)
  rw [hcenter, LieSubmodule.mem_bot] at hzcenter
  exact congrArg Subtype.val hzcenter

private noncomputable def complementComplexExtension
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (J : q →ₗ⁅ℝ,h⁆ q) :
    g →ₗ⁅ℝ,h⁆ g :=
  q.incl.comp (J.comp (invariantProjection q h.toLieSubmodule hc.symm))

private theorem extension_isotropy_zero
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (J : q →ₗ⁅ℝ,h⁆ q) (x : h) :
    complementComplexExtension h q hc J x = 0 := by
  let p := invariantProjection q h.toLieSubmodule hc.symm
  have hp : p x = 0 :=
    Subtype.ext (hc.symm.projection_apply_eq_zero_iff.mpr x.property)
  change ((J (p x) : q) : g) = 0
  rw [hp, map_zero]
  rfl

private theorem extension_complement_apply
    (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (J : q →ₗ⁅ℝ,h⁆ q) (x : q) :
    complementComplexExtension h q hc J x = J x := by
  let p := invariantProjection q h.toLieSubmodule hc.symm
  have hp : p x = x :=
    Subtype.ext ((hc.symm.projection_eq_self_iff x).mpr x.property)
  change ((J (p x) : q) : g) = J x
  rw [hp]

private theorem symmetric_bracket_complex_cancel
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (J : q →ₗ⁅ℝ,h⁆ q)
    (hskew : ∀ x y : q, B.form (J x) y = -B.form x (J y))
    (hsymmetric : ∀ x y : q, ⁅x.val, y.val⁆ ∈ h) (x y : q) :
    ⁅(J x : g), (y : g)⁆ + ⁅(x : g), (J y : g)⁆ = 0 := by
  let t := ⁅(J x : g), (y : g)⁆ + ⁅(x : g), (J y : g)⁆
  have ht : t ∈ h := h.add_mem (hsymmetric (J x) y) (hsymmetric x (J y))
  let z : h := ⟨t, ht⟩
  have hbracketJ : ⁅(J x : g), t⁆ = -(J ⁅z, x⁆ : g) := by
    calc
      ⁅(J x : g), t⁆ = -⁅t, (J x : g)⁆ := (lie_skew _ _).symm
      _ = -(J ⁅z, x⁆ : g) := by rw [J.map_lie]; rfl
  have hbracket : ⁅(x : g), t⁆ = -(⁅z, x⁆ : q).val :=
    (lie_skew _ _).symm
  have hzero : B.form t t = 0 := by
    change B.form (⁅(J x : g), (y : g)⁆ + ⁅(x : g), (J y : g)⁆) t = 0
    rw [LinearMap.BilinForm.add_left, B.invariant, B.invariant,
      hbracketJ, hbracket, map_neg, map_neg, neg_neg, neg_neg, hskew,
      add_neg_cancel]
  by_contra ht0
  have hp := B.positive t ht0
  linarith

private noncomputable def symmetricComplexDerivation
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) (J : q →ₗ⁅ℝ,h⁆ q)
    (hskew : ∀ x y : q, B.form (J x) y = -B.form x (J y))
    (hsymmetric : ∀ x y : q, ⁅x.val, y.val⁆ ∈ h) :
    LieDerivation ℝ g g where
  toLinearMap := (complementComplexExtension h q hc J).toLinearMap
  leibniz' := by
    let D := complementComplexExtension h q hc J
    have hleft : ∀ (x : h) (y : g),
        D ⁅x.val, y⁆ = ⁅x.val, D y⁆ + ⁅D x, y⁆ := by
      intro x y
      rw [extension_isotropy_zero, zero_lie, add_zero]
      exact D.map_lie x y
    have hright : ∀ (x : g) (y : h),
        D ⁅x, y.val⁆ = ⁅x, D y⁆ + ⁅D x, y.val⁆ := by
      intro x y
      rw [extension_isotropy_zero, lie_zero, zero_add]
      calc
        D ⁅x, y.val⁆ = -D ⁅y.val, x⁆ := by rw [← lie_skew, map_neg]
        _ = -⁅y.val, D x⁆ := congrArg Neg.neg (D.map_lie y x)
        _ = ⁅D x, y.val⁆ := lie_skew _ _
    have hqq : ∀ x y : q,
        D ⁅x.val, y.val⁆ = ⁅x.val, D y⁆ + ⁅D x, y.val⁆ := by
      intro x y
      have hz : D ⁅x.val, y.val⁆ = 0 :=
        extension_isotropy_zero h q hc J ⟨_, hsymmetric x y⟩
      rw [hz, extension_complement_apply, extension_complement_apply]
      have hcancel := symmetric_bracket_complex_cancel B h q J hskew hsymmetric x y
      simpa only [add_comm] using hcancel.symm
    intro x y
    have hx : x ∈ h.toSubmodule ⊔ q.toSubmodule := by rw [hc.sup_eq_top]; trivial
    have hy : y ∈ h.toSubmodule ⊔ q.toSubmodule := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
    change D ⁅u + v, s + t⁆ = ⁅u + v, D (s + t)⁆ - ⁅s + t, D (u + v)⁆
    have hus := hleft ⟨u, hu⟩ s
    have hut := hleft ⟨u, hu⟩ t
    have hvs := hright v ⟨s, hs⟩
    have hvt := hqq ⟨v, hv⟩ ⟨t, ht⟩
    simp only [add_lie, lie_add, map_add, hus, hut, hvs, hvt,
      sub_eq_add_neg, neg_add_rev, lie_skew]
    abel

/-- A symmetric complement of complex type forces a nonzero isotropy center.
This is the classification-free obstruction to the involutive branch. -/
theorem killing_symmetric_complex_complement_center_ne_bot
    [Module.Finite ℝ g] [LieAlgebra.IsKilling ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule)
    [LieModule.IsIrreducible ℝ h q]
    (J : q →ₗ⁅ℝ,h⁆ q) (hJ : ∀ x, J (J x) = -x)
    (hskew : ∀ x y : q, B.form (J x) y = -B.form x (J y))
    (hsymmetric : ∀ x y : q, ⁅x.val, y.val⁆ ∈ h) :
    LieAlgebra.center ℝ h ≠ ⊥ := by
  intro hcenter
  letI : Nontrivial q := LieModule.nontrivial_of_isIrreducible ℝ h q
  let D := symmetricComplexDerivation B h q hc J hskew hsymmetric
  obtain ⟨z, hz⟩ := LieDerivation.IsKilling.exists_eq_ad D
  have hzc : ∀ x : h, ⁅x.val, z⁆ = 0 := by
    intro x
    have hx : ⁅z, x.val⁆ = 0 := by
      have : ⁅z, x.val⁆ = D x.val := by simpa using LieDerivation.congr_fun hz x.val
      rw [this]
      exact extension_isotropy_zero h q hc J x
    rw [← lie_skew, hx, neg_zero]
  have hz0 := centralizer_vanishes_of_complex_complement h q hc J hJ hcenter z hzc
  obtain ⟨x, hx⟩ := exists_ne (0 : q)
  have hJx : J x = 0 := by
    apply Subtype.ext
    have hxD : ⁅z, x.val⁆ = D x.val := by simpa using LieDerivation.congr_fun hz x.val
    rw [hz0, zero_lie] at hxD
    exact (extension_complement_apply h q hc J x).symm.trans hxD.symm
  have hsq := hJ x
  rw [hJx, map_zero] at hsq
  exact hx (neg_eq_zero.mp hsq.symm)

/-- An effective compact complex-type pair with centerless isotropy cannot
have a symmetric complement.  No rank hypothesis or involution census is used. -/
theorem compact_complex_complement_nonsymmetric [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥) :
    ∃ x y : orthogonalComplement B h, ⁅x.val, y.val⁆ ∉ h := by
  classical
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
  let J := commutantComplexStructure e
  have hJ := commutant_complex_structure_square e
  have hgcenter := ambient_center_eq_bot_of_complex_complement h q hc heff J hJ
  letI : LieAlgebra.IsKilling ℝ g :=
    CompactKilling.compact_centerless_isKilling B hgcenter
  let Φ : LinearMap.BilinForm ℝ q := B.form.restrict q.toSubmodule
  have hskew : ∀ x y : q, B.form (J x) y = -B.form x (J y) := by
    intro x y
    exact complex_commutant_structure_skew Φ
      (fun x hx => B.positive x (fun hz => hx (Subtype.ext hz)))
      (fun x y z => B.invariant x.val y.val z.val) e x y
  by_contra hsymmetric
  push_neg at hsymmetric
  exact killing_symmetric_complex_complement_center_ne_bot B h q hc J hJ hskew
    hsymmetric hcenter

/-- In the original algebraic domain, a symmetric complement has zero full
mixed cubic radical.  This replaces every separate order-two case check. -/
theorem symmetric_complex_complement_cubic_radical_eq_bot [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hsymmetric : ∀ x y : orthogonalComplement B h, ⁅x.val, y.val⁆ ∈ h) :
    (HermitianRealization.hermitianHalfOfCommutant B h e).cubicRadical = ⊥ := by
  by_contra hradical
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (HermitianRealization.all_rank_structural_reduction_of_commutant
      B h heff hproper e hradical).2.2.2.1
  obtain ⟨x, y, hxy⟩ := compact_complex_complement_nonsymmetric
    B h heff hproper e (LieAlgebra.center_eq_bot ℝ h)
  exact hxy (hsymmetric x y)

end Complement

end CubicAnomaly.Classification.CyclicBracket
