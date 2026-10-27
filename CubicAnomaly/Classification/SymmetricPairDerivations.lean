import CubicAnomaly.Classification.Structural
import CubicAnomaly.Classification.DualPairSkew
import Mathlib.Algebra.Lie.Derivation.Killing

/-!
# A bilinear obstruction in a symmetric complement

An equivariant skew endomorphism of a symmetric complement extends by zero
to an ambient derivation. Nondegeneracy on the isotropy algebra replaces
positivity in this argument. If the ambient algebra is Killing and the
isotropy centralizer is zero, the endomorphism must vanish.
-/

namespace CubicAnomaly.Classification.SymmetricPairDerivations

open CubicAnomaly.Classification.Structural
open Submodule

noncomputable section

variable {K g : Type*} [Field K] [LieRing g] [LieAlgebra K g]

private theorem symmetric_bracket_cancel
    (h : LieSubalgebra K g) (q : LieSubmodule K h g)
    (Φ : LinearMap.BilinForm K g) (hΦ : Φ.lieInvariant g)
    (hnd : (Φ.restrict h.toSubmodule).Nondegenerate)
    (D : g →ₗ⁅K,h⁆ g) (hDq : ∀ x : q, D x ∈ q)
    (hskew : ∀ x y : q, Φ (D x) y = -Φ x (D y))
    (hsym : ∀ x y : q, ⁅x.val, y.val⁆ ∈ h) (x y : q) :
    ⁅D x, y.val⁆ + ⁅x.val, D y⁆ = 0 := by
  let t := ⁅D x, y.val⁆ + ⁅x.val, D y⁆
  have ht : t ∈ h := h.add_mem (hsym ⟨D x, hDq x⟩ y) (hsym x ⟨D y, hDq y⟩)
  have hz : (⟨t, ht⟩ : h) = 0 := by
    apply hnd.1
    intro z
    change Φ t z = 0
    have hx : ⁅D x, z.val⁆ = -D ⁅z.val, x.val⁆ := by
      rw [← lie_skew]
      exact congrArg Neg.neg (D.map_lie z x.val).symm
    have hy : ⁅x.val, z.val⁆ = -⁅z.val, x.val⁆ := (lie_skew _ _).symm
    have hs := hskew y (⁅z, x⁆ : q)
    change Φ (D y.val) ⁅z.val, x.val⁆ = -Φ y.val (D ⁅z.val, x.val⁆) at hs
    dsimp [t]
    rw [map_add, LinearMap.add_apply, hΦ, hΦ, hx, hy, map_neg, map_neg,
      neg_neg, neg_neg, hs, add_neg_cancel]
  exact congrArg Subtype.val hz

private def symmetricExtensionDerivation
    (h : LieSubalgebra K g) (q : LieSubmodule K h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule)
    (Φ : LinearMap.BilinForm K g) (hΦ : Φ.lieInvariant g)
    (hnd : (Φ.restrict h.toSubmodule).Nondegenerate)
    (D : g →ₗ⁅K,h⁆ g) (hDh : ∀ x : h, D x = 0)
    (hDq : ∀ x : q, D x ∈ q)
    (hskew : ∀ x y : q, Φ (D x) y = -Φ x (D y))
    (hsym : ∀ x y : q, ⁅x.val, y.val⁆ ∈ h) : LieDerivation K g g where
  toLinearMap := D.toLinearMap
  leibniz' := by
    have hl : ∀ (x : h) (y : g), D ⁅x.val, y⁆ = ⁅x.val, D y⁆ + ⁅D x, y⁆ := by
      intro x y
      rw [hDh, zero_lie, add_zero]
      exact D.map_lie x y
    have hr : ∀ (x : g) (y : h), D ⁅x, y.val⁆ = ⁅x, D y⁆ + ⁅D x, y.val⁆ := by
      intro x y
      rw [hDh, lie_zero, zero_add]
      calc
        D ⁅x, y.val⁆ = -D ⁅y.val, x⁆ := by rw [← lie_skew, map_neg]
        _ = -⁅y.val, D x⁆ := congrArg Neg.neg (D.map_lie y x)
        _ = ⁅D x, y.val⁆ := lie_skew _ _
    have hqq : ∀ x y : q, D ⁅x.val, y.val⁆ = ⁅x.val, D y⁆ + ⁅D x, y.val⁆ := by
      intro x y
      have hz := hDh ⟨_, hsym x y⟩
      change D ⁅x.val, y.val⁆ = 0 at hz
      rw [hz]
      have hc := symmetric_bracket_cancel h q Φ hΦ hnd D hDq hskew hsym x y
      simpa only [add_comm] using hc.symm
    intro x y
    have hx : x ∈ h.toSubmodule ⊔ q.toSubmodule := by rw [hc.sup_eq_top]; trivial
    have hy : y ∈ h.toSubmodule ⊔ q.toSubmodule := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
    change D ⁅u + v, s + t⁆ = ⁅u + v, D (s + t)⁆ - ⁅s + t, D (u + v)⁆
    have hus := hl ⟨u, hu⟩ s
    have hut := hl ⟨u, hu⟩ t
    have hvs := hr v ⟨s, hs⟩
    have hvt := hqq ⟨v, hv⟩ ⟨t, ht⟩
    simp only [add_lie, lie_add, map_add, hus, hut, hvs, hvt,
      sub_eq_add_neg, neg_add_rev, lie_skew]
    abel

/-- In a Killing Lie algebra with zero isotropy centralizer, an equivariant
endomorphism vanishing on the isotropy and skew on a symmetric complement
must vanish. Only nondegeneracy on the isotropy is needed for the form. -/
theorem equivariant_skew_extension_eq_zero [Module.Finite K g] [LieAlgebra.IsKilling K g]
    (h : LieSubalgebra K g) (q : LieSubmodule K h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule)
    (Φ : LinearMap.BilinForm K g) (hΦ : Φ.lieInvariant g)
    (hnd : (Φ.restrict h.toSubmodule).Nondegenerate)
    (hcentralizer : ∀ z : g, (∀ x : h, ⁅x.val, z⁆ = 0) → z = 0)
    (D : g →ₗ⁅K,h⁆ g) (hDh : ∀ x : h, D x = 0)
    (hDq : ∀ x : q, D x ∈ q)
    (hskew : ∀ x y : q, Φ (D x) y = -Φ x (D y))
    (hsym : ∀ x y : q, ⁅x.val, y.val⁆ ∈ h) : D = 0 := by
  let δ := symmetricExtensionDerivation h q hc Φ hΦ hnd D hDh hDq hskew hsym
  obtain ⟨z, hz⟩ := LieDerivation.IsKilling.exists_eq_ad δ
  have hz0 : z = 0 := by
    apply hcentralizer z
    intro x
    have hx : ⁅z, x.val⁆ = 0 := by
      have he : ⁅z, x.val⁆ = D x.val := by simpa using LieDerivation.congr_fun hz x.val
      exact he.trans (hDh x)
    rw [← lie_skew, hx, neg_zero]
  ext x
  have hx : ⁅z, x⁆ = D x := by simpa using LieDerivation.congr_fun hz x
  simpa only [hz0, zero_lie] using hx.symm

private def complementProjection
    (h : LieSubalgebra K g) (q : LieSubmodule K h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule) : g →ₗ⁅K,h⁆ q where
  __ := q.toSubmodule.linearProjOfIsCompl h.toSubmodule hc.symm
  map_lie' := by
    intro x m
    apply Subtype.ext
    change hc.symm.projection ⁅x.val, m⁆ = ⁅x.val, hc.symm.projection m⁆
    have hm : m ∈ q.toSubmodule ⊔ h.toSubmodule := by rw [hc.symm.sup_eq_top]; trivial
    obtain ⟨v, hv, u, hu, rfl⟩ := Submodule.mem_sup.mp hm
    have hv' := (hc.symm.projection_eq_self_iff v).mpr hv
    have hu' := hc.symm.projection_apply_eq_zero_iff.mpr hu
    have hxv := (hc.symm.projection_eq_self_iff ⁅x.val, v⁆).mpr (q.lie_mem (x := x) hv)
    have hxu := hc.symm.projection_apply_eq_zero_iff.mpr (h.lie_mem x.property hu)
    simp only [lie_add, map_add, hv', hu', hxv, hxu, add_zero]

/-- The symmetric-complement obstruction applies directly to an
endomorphism of the complement, by extending it through the actual
invariant projection. -/
theorem symmetric_complement_skew_end_eq_zero
    [Module.Finite K g] [LieAlgebra.IsKilling K g]
    (h : LieSubalgebra K g) (q : LieSubmodule K h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule)
    (Φ : LinearMap.BilinForm K g) (hΦ : Φ.lieInvariant g)
    (hnd : (Φ.restrict h.toSubmodule).Nondegenerate)
    (hcentralizer : ∀ z : g, (∀ x : h, ⁅x.val, z⁆ = 0) → z = 0)
    (D : q →ₗ⁅K,h⁆ q)
    (hskew : ∀ x y : q, Φ (D x) y = -Φ x (D y))
    (hsym : ∀ x y : q, ⁅x.val, y.val⁆ ∈ h) : D = 0 := by
  let p := complementProjection h q hc
  let E := q.incl.comp (D.comp p)
  have hp (x : q) : p x.val = x :=
    Subtype.ext ((hc.symm.projection_eq_self_iff x.val).mpr x.property)
  have heq : E = 0 := by
    apply equivariant_skew_extension_eq_zero h q hc Φ hΦ hnd hcentralizer E
    · intro x
      have hx : p x.val = 0 :=
        Subtype.ext (hc.symm.projection_apply_eq_zero_iff.mpr x.property)
      change (D (p x.val) : g) = 0
      rw [hx, map_zero]
      rfl
    · intro x
      exact (D (p x.val)).property
    · intro x y
      change Φ (D (p x.val)) y = -Φ x (D (p y.val))
      rw [hp, hp]
      exact hskew x y
    · exact hsym
  ext x
  have hx := congrArg (fun f : g →ₗ⁅K,h⁆ g => f x.val) heq
  change (D (p x.val) : g) = 0 at hx
  rwa [hp] at hx

/-- A symmetric complement with nondegenerate isotropy form and zero
isotropy centralizer cannot be an inequivalent irreducible dual pair.
The contradiction is obtained from an actual nonzero skew endomorphism
and the inner-derivation theorem, without root or highest-weight data. -/
theorem symmetric_complement_not_inequivalent_dual_pair
    [Module.Finite K g] [LieAlgebra.IsKilling K g]
    (h : LieSubalgebra K g) (q : LieSubmodule K h g)
    (hc : IsCompl h.toSubmodule q.toSubmodule)
    (Φ : LinearMap.BilinForm K g) (hΦ : Φ.lieInvariant g)
    (hnd : (Φ.restrict h.toSubmodule).Nondegenerate)
    (hcentralizer : ∀ z : g, (∀ x : h, ⁅x.val, z⁆ = 0) → z = 0)
    (hsym : ∀ x y : q, ⁅x.val, y.val⁆ ∈ h)
    (P Q : LieSubmodule K h q) (hpq : IsCompl P Q)
    [LieModule.IsIrreducible K h P] [LieModule.IsIrreducible K h Q]
    (d : Q ≃ₗ⁅K,h⁆ Module.Dual K P) (hne : ¬Nonempty (P ≃ₗ⁅K,h⁆ Q)) : False := by
  obtain ⟨D, hD, hsk⟩ := DualPairSkew.inequivalent_dual_pair_exists_skew_end P Q hpq d hne
  apply hD
  apply symmetric_complement_skew_end_eq_zero h q hc Φ hΦ hnd hcentralizer D
  · exact hsk (Φ.restrict q.toSubmodule) (fun x y z => hΦ x.val y.val z.val)
  · exact hsym

end

end CubicAnomaly.Classification.SymmetricPairDerivations
