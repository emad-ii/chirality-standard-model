import CubicAnomaly.Classification.IdealProductRepresentation
import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.Algebra.Lie.SkewAdjoint

/-!
# Actual products of three ideal actions

The actual product of three defining action operators is an equivariant
map from the standard triple tensor module. It is nonzero on a faithful
irreducible module whenever all three ideals are nonzero. For three
pairwise disjoint ideals, two perfect factors already force every map to
the adjoint module to vanish, so the product cannot lie in the action
image. When the action preserves a bilinear form, the odd product also
preserves that same form.

All tensor products use the association `((I ⊗ J) ⊗ T)` and the actual
diagonal Lie action. No decomposition of the defining module is assumed.
-/

namespace CubicAnomaly.Classification.IdealTripleProduct

open LieAlgebra LieModule Module
open CubicAnomaly.Classification.IdealActionProducts
open CubicAnomaly.Classification.IdealProductRepresentation
open CubicAnomaly.Classification.CubicIdealDecomposition
open scoped TensorProduct

section Product

variable {R L W : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]

private def idealTripleProductLinearMap (I J T : LieIdeal R L) :
    (I ⊗[R] J) ⊗[R] T →ₗ[R] Module.End R W :=
  TensorProduct.lift ((LinearMap.mul R (Module.End R W)).compl₁₂
    (idealProductMap (W := W) I J).toLinearMap
    ((toEnd R L W).toLinearMap.comp T.incl.toLinearMap))

/-- Literal composition of three ideal action operators, equivariant for
the standard diagonal tensor and endomorphism actions. -/
def idealTripleProductMap (I J T : LieIdeal R L) :
    (I ⊗[R] J) ⊗[R] T →ₗ⁅R,L⁆ Module.End R W where
  __ := idealTripleProductLinearMap I J T
  map_lie' := by
    intro a t
    change idealTripleProductLinearMap (W := W) I J T ⁅a, t⁆ =
      ⁅a, idealTripleProductLinearMap (W := W) I J T t⁆
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u z =>
      rw [TensorProduct.LieModule.lie_tmul_right, map_add]
      change idealProductMap (W := W) I J ⁅a, u⁆ * toEnd R L W (z : L) +
        idealProductMap (W := W) I J u * toEnd R L W ⁅a, (z : L)⁆ =
        toEnd R L W a * (idealProductMap (W := W) I J u * toEnd R L W (z : L)) -
          (idealProductMap (W := W) I J u * toEnd R L W (z : L)) * toEnd R L W a
      rw [(idealProductMap (W := W) I J).map_lie, LieHom.map_lie]
      change (toEnd R L W a * idealProductMap (W := W) I J u -
          idealProductMap (W := W) I J u * toEnd R L W a) * toEnd R L W (z : L) +
        idealProductMap (W := W) I J u *
          (toEnd R L W a * toEnd R L W (z : L) -
            toEnd R L W (z : L) * toEnd R L W a) = _
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    | add t u ht hu => simp only [lie_add, map_add, ht, hu]

/-- Evaluation on an outer pure tensor multiplies the actual double
product by the actual third ideal action. -/
@[simp] theorem ideal_triple_product_map_outer_tmul
    (I J T : LieIdeal R L) (u : I ⊗[R] J) (z : T) :
    idealTripleProductMap (W := W) I J T (u ⊗ₜ[R] z) =
      idealProductMap (W := W) I J u * toEnd R L W (z : L) := rfl

/-- Evaluation on a pure triple tensor is the literal product of its
three defining action operators. -/
@[simp] theorem ideal_triple_product_map_tmul
    (I J T : LieIdeal R L) (x : I) (y : J) (z : T) :
    idealTripleProductMap (W := W) I J T ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      toEnd R L W (x : L) * toEnd R L W (y : L) * toEnd R L W (z : L) := rfl

/-- Three nonzero ideals have a nonzero actual product of their action
operators on a faithful irreducible module. -/
theorem exists_nonzero_ideal_action_triple_product
    [LieModule.IsFaithful R L W] [LieModule.IsIrreducible R L W]
    (I J T : LieIdeal R L) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hT : T ≠ ⊥) :
    ∃ x : I, ∃ y : J, ∃ z : T,
      toEnd R L W (x : L) * toEnd R L W (y : L) * toEnd R L W (z : L) ≠ 0 := by
  by_contra! hzero
  obtain ⟨x, y, hxy⟩ := exists_nonzero_ideal_action_product (M := W) I J hI hJ
  apply hxy
  apply linearMap_eq_zero_of_annihilates_ideal_actions T hT
    (toEnd R L W (x : L) * toEnd R L W (y : L))
  intro z w
  exact congrArg (fun f : Module.End R W => f w) (hzero x y z)

/-- The actual triple product map is nonzero without requiring a tensor
factorization or any finite-dimensionality hypothesis. -/
theorem ideal_triple_product_map_ne_zero
    [LieModule.IsFaithful R L W] [LieModule.IsIrreducible R L W]
    (I J T : LieIdeal R L) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hT : T ≠ ⊥) :
    idealTripleProductMap (W := W) I J T ≠ 0 := by
  obtain ⟨x, y, z, hxyz⟩ :=
    exists_nonzero_ideal_action_triple_product (W := W) I J T hI hJ hT
  intro hzero
  exact hxyz (congrArg
    (fun f : (I ⊗[R] J) ⊗[R] T →ₗ⁅R,L⁆ Module.End R W =>
      f ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) hzero)

end Product

section Adjoint

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

private theorem perfect_ideal_bracket_span (I : LieIdeal R L) (hI : ⁅I, I⁆ = I) :
    Submodule.span R {⁅a, b⁆ | (a : I) (b : I)} = ⊤ := by
  have hp : ⁅(⊤ : LieIdeal R I), (⊤ : LieIdeal R I)⁆ = (⊤ : LieIdeal R I) := by
    have h := I.derivedSeries_eq_derivedSeriesOfIdeal_comap 1
    simpa only [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
      hI, LieIdeal.comap_incl_self] using h
  have hsub : (⁅(⊤ : LieIdeal R I), (⊤ : LieIdeal R I)⁆).toSubmodule ≤
      Submodule.span R {⁅a, b⁆ | (a : I) (b : I)} := by
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span]
    apply Submodule.span_mono
    rintro _ ⟨a, b, rfl⟩
    exact ⟨(a : I), (b : I), rfl⟩
  apply top_unique
  simpa only [hp, LieSubmodule.top_toSubmodule] using hsub

/-- Perfectness forces a triple-tensor map to the adjoint module to have
image in the first ideal when that ideal commutes with the other factors. -/
theorem ideal_triple_tensor_to_adjoint_mem_left (I J T : LieIdeal R L)
    (hI : ⁅I, I⁆ = I) (hIJ : Disjoint I J) (hIT : Disjoint I T)
    (f : (I ⊗[R] J) ⊗[R] T →ₗ⁅R,L⁆ L) (t : (I ⊗[R] J) ⊗[R] T) : f t ∈ I := by
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using I.zero_mem
  | tmul u z =>
    induction u using TensorProduct.induction_on with
    | zero => simpa only [TensorProduct.zero_tmul, map_zero] using I.zero_mem
    | tmul x y =>
      have hx : x ∈ Submodule.span R {⁅a, b⁆ | (a : I) (b : I)} := by
        rw [perfect_ideal_bracket_span I hI]
        trivial
      refine Submodule.span_induction (p := fun v _ => f ((v ⊗ₜ[R] y) ⊗ₜ[R] z) ∈ I)
        ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨a, b, rfl⟩
        have hy : ⁅(a : L), y⁆ = (0 : J) :=
          Subtype.ext (disjoint_ideals_bracket_zero I J hIJ a y)
        have hz : ⁅(a : L), z⁆ = (0 : T) :=
          Subtype.ext (disjoint_ideals_bracket_zero I T hIT a z)
        have he : ((⁅a, b⁆ ⊗ₜ[R] y) ⊗ₜ[R] z) =
            ⁅(a : L), (b ⊗ₜ[R] y) ⊗ₜ[R] z⁆ := by
          rw [TensorProduct.LieModule.lie_tmul_right,
            TensorProduct.LieModule.lie_tmul_right, hy, hz,
            TensorProduct.tmul_zero, add_zero, TensorProduct.tmul_zero, add_zero]
          rfl
        rw [he, f.map_lie]
        exact lie_mem_left R L I a _ a.property
      · simpa only [TensorProduct.zero_tmul, map_zero] using I.zero_mem
      · intro a b _ _ ha hb
        simpa only [TensorProduct.add_tmul, map_add] using I.add_mem ha hb
      · intro c a _ ha
        simpa only [← TensorProduct.smul_tmul', map_smul] using I.smul_mem c ha
    | add u v hu hv => simpa only [TensorProduct.add_tmul, map_add] using I.add_mem hu hv
  | add t u ht hu => simpa only [map_add] using I.add_mem ht hu

/-- The middle perfect ideal also contains the image of any equivariant
triple-tensor map to the adjoint module. -/
theorem ideal_triple_tensor_to_adjoint_mem_middle (I J T : LieIdeal R L)
    (hJ : ⁅J, J⁆ = J) (hIJ : Disjoint I J) (hJT : Disjoint J T)
    (f : (I ⊗[R] J) ⊗[R] T →ₗ⁅R,L⁆ L) (t : (I ⊗[R] J) ⊗[R] T) : f t ∈ J := by
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using J.zero_mem
  | tmul u z =>
    induction u using TensorProduct.induction_on with
    | zero => simpa only [TensorProduct.zero_tmul, map_zero] using J.zero_mem
    | tmul x y =>
      have hy : y ∈ Submodule.span R {⁅a, b⁆ | (a : J) (b : J)} := by
        rw [perfect_ideal_bracket_span J hJ]
        trivial
      refine Submodule.span_induction (p := fun v _ => f ((x ⊗ₜ[R] v) ⊗ₜ[R] z) ∈ J)
        ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, b, rfl⟩
        have hx : ⁅(a : L), x⁆ = (0 : I) :=
          Subtype.ext (disjoint_ideals_bracket_zero J I hIJ.symm a x)
        have hz : ⁅(a : L), z⁆ = (0 : T) :=
          Subtype.ext (disjoint_ideals_bracket_zero J T hJT a z)
        have he : ((x ⊗ₜ[R] ⁅a, b⁆) ⊗ₜ[R] z) =
            ⁅(a : L), (x ⊗ₜ[R] b) ⊗ₜ[R] z⁆ := by
          rw [TensorProduct.LieModule.lie_tmul_right,
            TensorProduct.LieModule.lie_tmul_right, hx, hz,
            TensorProduct.zero_tmul, zero_add, TensorProduct.tmul_zero, add_zero]
          rfl
        rw [he, f.map_lie]
        exact lie_mem_left R L J a _ a.property
      · simpa only [TensorProduct.tmul_zero, TensorProduct.zero_tmul, map_zero] using J.zero_mem
      · intro a b _ _ ha hb
        simpa only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add] using J.add_mem ha hb
      · intro c a _ ha
        simpa only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul]
          using J.smul_mem c ha
    | add u v hu hv => simpa only [TensorProduct.add_tmul, map_add] using J.add_mem hu hv
  | add t u ht hu => simpa only [map_add] using J.add_mem ht hu

/-- Every equivariant triple-tensor map to the adjoint module vanishes
for pairwise disjoint ideals with the first two factors perfect. -/
theorem ideal_triple_tensor_to_adjoint_eq_zero (I J T : LieIdeal R L)
    (hI : ⁅I, I⁆ = I) (hJ : ⁅J, J⁆ = J)
    (hIJ : Disjoint I J) (hIT : Disjoint I T) (hJT : Disjoint J T)
    (f : (I ⊗[R] J) ⊗[R] T →ₗ⁅R,L⁆ L) : f = 0 := by
  ext t
  have hm : f t ∈ I ⊓ J :=
    ⟨ideal_triple_tensor_to_adjoint_mem_left I J T hI hIJ hIT f t,
      ideal_triple_tensor_to_adjoint_mem_middle I J T hJ hIJ hJT f t⟩
  simpa only [hIJ.eq_bot, LieSubmodule.mem_bot] using hm

end Adjoint

section Range

variable {R L W : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]
  [LieModule.IsFaithful R L W] [LieModule.IsIrreducible R L W]

/-- The actual triple product cannot have its entire image in the
defining action image for three nonzero pairwise disjoint ideals, when
the first two are perfect. -/
theorem ideal_triple_product_range_not_le_action_range (I J T : LieIdeal R L)
    (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hT0 : T ≠ ⊥)
    (hI : ⁅I, I⁆ = I) (hJ : ⁅J, J⁆ = J)
    (hIJ : Disjoint I J) (hIT : Disjoint I T) (hJT : Disjoint J T) :
    ¬(idealTripleProductMap (W := W) I J T).range.toSubmodule ≤
      (toEnd R L W).range.toSubmodule := by
  classical
  intro hle
  let ρ := toEnd R L W
  let μ := idealTripleProductMap (W := W) I J T
  have hall (t : (I ⊗[R] J) ⊗[R] T) : ∃ x : L, ρ x = μ t := hle ⟨t, rfl⟩
  let f₀ : (I ⊗[R] J) ⊗[R] T → L := fun t => Classical.choose (hall t)
  have hf₀ (t : (I ⊗[R] J) ⊗[R] T) : ρ (f₀ t) = μ t := Classical.choose_spec (hall t)
  have hρ : Function.Injective ρ := LieModule.IsFaithful.injective_toEnd
  let f : (I ⊗[R] J) ⊗[R] T →ₗ⁅R,L⁆ L := {
    toFun := f₀
    map_add' := by
      intro t u
      apply hρ
      simp only [hf₀, map_add]
    map_smul' := by
      intro c t
      apply hρ
      simp only [hf₀, map_smul, RingHom.id_apply]
    map_lie' := by
      intro a t
      apply hρ
      rw [hf₀, LieHom.map_lie, hf₀]
      exact μ.map_lie a t }
  have hf : f = 0 := ideal_triple_tensor_to_adjoint_eq_zero I J T hI hJ hIJ hIT hJT f
  apply ideal_triple_product_map_ne_zero (W := W) I J T hI0 hJ0 hT0
  apply DFunLike.ext
  intro t
  have ht : f₀ t = 0 := congrArg (fun g : (I ⊗[R] J) ⊗[R] T →ₗ⁅R,L⁆ L => g t) hf
  change μ t = 0
  rw [← hf₀, ht, map_zero]

/-- Semisimplicity supplies perfectness in the actual triple-product
range obstruction. -/
theorem semisimple_ideal_triple_product_range_not_le_action_range
    [LieAlgebra.IsSemisimple R L] (I J T : LieIdeal R L)
    (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hT0 : T ≠ ⊥)
    (hIJ : Disjoint I J) (hIT : Disjoint I T) (hJT : Disjoint J T) :
    ¬(idealTripleProductMap (W := W) I J T).range.toSubmodule ≤
      (toEnd R L W).range.toSubmodule :=
  ideal_triple_product_range_not_le_action_range I J T hI0 hJ0 hT0
    (semisimple_ideal_perfect I) (semisimple_ideal_perfect J) hIJ hIT hJT

end Range

section Forms

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

/-- Three commuting operators that are skew for the same bilinear form
have a skew product. The sign comes from moving all three operators
across the form; commutativity restores their original order. -/
theorem commuting_skew_triple_product (Φ : LinearMap.BilinForm R W)
    (A B C : Module.End R W) (hAB : Commute A B) (hAC : Commute A C) (hBC : Commute B C)
    (hA : ∀ u v, Φ (A u) v = -Φ u (A v))
    (hB : ∀ u v, Φ (B u) v = -Φ u (B v))
    (hC : ∀ u v, Φ (C u) v = -Φ u (C v)) (u v : W) :
    Φ ((A * B * C) u) v = -Φ u ((A * B * C) v) := by
  have hrev : C * (B * A) = A * B * C := by
    calc
      C * (B * A) = C * (A * B) := congrArg (C * ·) hAB.eq.symm
      _ = (C * A) * B := (mul_assoc _ _ _).symm
      _ = (A * C) * B := congrArg (· * B) hAC.eq.symm
      _ = A * (C * B) := mul_assoc _ _ _
      _ = A * (B * C) := congrArg (A * ·) hBC.eq.symm
      _ = A * B * C := (mul_assoc _ _ _).symm
  change Φ (A (B (C u))) v = _
  rw [hA, hB, neg_neg, hC]
  change -Φ u ((C * (B * A)) v) = _
  rw [hrev]

variable {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L W] [LieModule R L W]

/-- Disjoint ideals give commuting actual action operators. -/
theorem disjoint_ideal_actions_commute (I J : LieIdeal R L) (hIJ : Disjoint I J)
    (x : I) (y : J) : Commute (toEnd R L W (x : L)) (toEnd R L W (y : L)) := by
  change toEnd R L W (x : L) * toEnd R L W (y : L) =
    toEnd R L W (y : L) * toEnd R L W (x : L)
  apply sub_eq_zero.mp
  change ⁅toEnd R L W (x : L), toEnd R L W (y : L)⁆ = 0
  rw [← LieHom.map_lie, disjoint_ideals_bracket_zero I J hIJ x y, map_zero]

/-- The actual odd product has values in the literal Lie algebra of
operators preserving the original invariant bilinear form. -/
theorem ideal_triple_product_map_mem_skewAdjointLieSubalgebra
    (Φ : LinearMap.BilinForm R W) (hΦ : Φ.lieInvariant L)
    (I J T : LieIdeal R L)
    (hIJ : Disjoint I J) (hIT : Disjoint I T) (hJT : Disjoint J T)
    (t : (I ⊗[R] J) ⊗[R] T) :
    idealTripleProductMap (W := W) I J T t ∈ skewAdjointLieSubalgebra Φ := by
  change idealTripleProductMap (W := W) I J T t ∈ Φ.skewAdjointSubmodule
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using Φ.skewAdjointSubmodule.zero_mem
  | tmul s z =>
    induction s using TensorProduct.induction_on with
    | zero =>
      simpa only [TensorProduct.zero_tmul, map_zero] using Φ.skewAdjointSubmodule.zero_mem
    | tmul x y =>
      apply (LinearMap.mem_skewAdjointSubmodule _).mpr
      intro u v
      change Φ ((toEnd R L W (x : L) * toEnd R L W (y : L) * toEnd R L W (z : L)) u) v =
        Φ u (-((toEnd R L W (x : L) * toEnd R L W (y : L) * toEnd R L W (z : L)) v))
      rw [map_neg]
      exact commuting_skew_triple_product Φ _ _ _
        (disjoint_ideal_actions_commute I J hIJ x y)
        (disjoint_ideal_actions_commute I T hIT x z)
        (disjoint_ideal_actions_commute J T hJT y z)
        (hΦ (x : L)) (hΦ (y : L)) (hΦ (z : L)) u v
    | add s t hs ht =>
      simpa only [TensorProduct.add_tmul, map_add] using Φ.skewAdjointSubmodule.add_mem hs ht
  | add s t hs ht => simpa only [map_add] using Φ.skewAdjointSubmodule.add_mem hs ht

/-- Pointwise preservation of the invariant bilinear form by every value
of the actual triple product map. This applies to symmetric and alternating
forms alike. -/
theorem ideal_triple_product_map_skew (Φ : LinearMap.BilinForm R W) (hΦ : Φ.lieInvariant L)
    (I J T : LieIdeal R L)
    (hIJ : Disjoint I J) (hIT : Disjoint I T) (hJT : Disjoint J T)
    (t : (I ⊗[R] J) ⊗[R] T) (u v : W) :
    Φ (idealTripleProductMap (W := W) I J T t u) v =
      -Φ u (idealTripleProductMap (W := W) I J T t v) := by
  have h := (LinearMap.mem_skewAdjointSubmodule _).mp
    (ideal_triple_product_map_mem_skewAdjointLieSubalgebra Φ hΦ I J T hIJ hIT hJT t)
  have huv := h u v
  change Φ (idealTripleProductMap (W := W) I J T t u) v =
    Φ u (-(idealTripleProductMap (W := W) I J T t v)) at huv
  simpa only [map_neg] using huv

end Forms

end CubicAnomaly.Classification.IdealTripleProduct
