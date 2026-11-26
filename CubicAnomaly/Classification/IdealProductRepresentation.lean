import CubicAnomaly.Classification.IdealActionProducts
import CubicAnomaly.Classification.CubicIdealDecomposition
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.TraceForm

/-!
# Actual products of ideal actions

Multiplication of action operators defines an equivariant map from the
tensor product of two actual ideals into the endomorphism representation.
Disjointness and perfectness make its values traceless. On a faithful
irreducible defining module this map is nonzero.

Perfectness and disjointness also force every equivariant map from the
same tensor product to the adjoint module to vanish. These constructions
use the actual ideals and operators, without a tensor factorization of the
defining module or a classification witness.
-/

namespace CubicAnomaly.Classification.IdealProductRepresentation

open LieAlgebra LieModule Module
open CubicAnomaly.Classification.IdealActionProducts
open CubicAnomaly.Classification.CubicIdealDecomposition
open scoped TensorProduct

section Product

variable {R L W : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]

private def idealProductLinearMap (I J : LieIdeal R L) :
    I ⊗[R] J →ₗ[R] Module.End R W :=
  TensorProduct.lift ((LinearMap.mul R (Module.End R W)).compl₁₂
    ((toEnd R L W).toLinearMap.comp I.incl.toLinearMap)
    ((toEnd R L W).toLinearMap.comp J.incl.toLinearMap))

/-- The actual product of the action operators is equivariant for the
standard diagonal tensor action and the standard endomorphism action. -/
def idealProductMap (I J : LieIdeal R L) :
    I ⊗[R] J →ₗ⁅R,L⁆ Module.End R W where
  __ := idealProductLinearMap I J
  map_lie' := by
    intro a t
    change idealProductLinearMap (W := W) I J ⁅a, t⁆ =
      ⁅a, idealProductLinearMap (W := W) I J t⁆
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [TensorProduct.LieModule.lie_tmul_right, map_add]
      change toEnd R L W ⁅a, (x : L)⁆ * toEnd R L W (y : L) +
        toEnd R L W (x : L) * toEnd R L W ⁅a, (y : L)⁆ =
        toEnd R L W a * (toEnd R L W (x : L) * toEnd R L W (y : L)) -
          (toEnd R L W (x : L) * toEnd R L W (y : L)) * toEnd R L W a
      rw [LieHom.map_lie, LieHom.map_lie]
      simp only [Ring.lie_def, sub_mul, mul_sub, mul_assoc]
      abel
    | add t u ht hu => simp only [lie_add, map_add, ht, hu]

/-- On pure tensors the equivariant map is literal composition of the
two actual defining action operators. -/
@[simp] theorem ideal_product_map_tmul (I J : LieIdeal R L) (x : I) (y : J) :
    idealProductMap (W := W) I J (x ⊗ₜ[R] y) =
      toEnd R L W (x : L) * toEnd R L W (y : L) := rfl

/-- Disjoint ideals commute in the actual ambient Lie algebra. -/
theorem disjoint_ideals_bracket_zero (I J : LieIdeal R L) (hIJ : Disjoint I J)
    (x : I) (y : J) : ⁅(x : L), (y : L)⁆ = 0 := by
  have hm : ⁅(x : L), (y : L)⁆ ∈ I ⊓ J :=
    ⟨lie_mem_left R L I x y x.property, lie_mem_right R L J x y y.property⟩
  simpa only [hIJ.eq_bot, LieSubmodule.mem_bot] using hm

/-- Perfectness and disjointness make the actual cross-action trace form
zero, without choosing representation factors or coordinates. -/
theorem perfect_disjoint_ideal_trace_zero (I J : LieIdeal R L)
    (hI : ⁅I, I⁆ = I) (hIJ : Disjoint I J) (x : I) (y : J) :
    LinearMap.trace R W (toEnd R L W (x : L) * toEnd R L W (y : L)) = 0 := by
  change traceForm R L W (x : L) (y : L) = 0
  have hx : (x : L) ∈ Submodule.span R {⁅(a : L), (b : L)⁆ | (a : I) (b : I)} := by
    rw [← LieSubmodule.lieIdeal_oper_eq_linear_span, hI]
    exact x.property
  refine Submodule.span_induction
    (p := fun z _ => traceForm R L W z (y : L) = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, b, rfl⟩
    rw [traceForm_apply_lie_apply, disjoint_ideals_bracket_zero I J hIJ b y]
    simp
  · simp
  · intro a b _ _ ha hb
    simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
  · intro c a _ ha
    simp only [map_smul, LinearMap.smul_apply, ha, smul_zero]

/-- The entire product map has trace-zero values for disjoint perfect
ideals, not only its values on pure tensors. -/
theorem ideal_product_map_trace_zero (I J : LieIdeal R L)
    (hI : ⁅I, I⁆ = I) (hIJ : Disjoint I J) (t : I ⊗[R] J) :
    LinearMap.trace R W (idealProductMap (W := W) I J t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => exact perfect_disjoint_ideal_trace_zero I J hI hIJ x y
  | add t u ht hu => simp only [map_add, ht, hu, add_zero]

/-- On a faithful irreducible defining module, products of nonzero ideals
give a nonzero actual equivariant map. -/
theorem ideal_product_map_ne_zero
    [LieModule.IsFaithful R L W] [LieModule.IsIrreducible R L W]
    (I J : LieIdeal R L) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealProductMap (W := W) I J ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := exists_nonzero_ideal_action_product (M := W) I J hI hJ
  intro hzero
  exact hxy (congrArg (fun f : I ⊗[R] J →ₗ⁅R,L⁆ Module.End R W => f (x ⊗ₜ[R] y)) hzero)

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

/-- Perfectness of the left ideal forces every equivariant tensor-to-adjoint
map to have image in that ideal, when the two ideals are disjoint. -/
theorem ideal_tensor_to_adjoint_mem_left (I J : LieIdeal R L)
    (hI : ⁅I, I⁆ = I) (hIJ : Disjoint I J)
    (f : I ⊗[R] J →ₗ⁅R,L⁆ L) (t : I ⊗[R] J) : f t ∈ I := by
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using I.zero_mem
  | tmul x y =>
    have hx : x ∈ Submodule.span R {⁅a, b⁆ | (a : I) (b : I)} := by
      rw [perfect_ideal_bracket_span I hI]
      trivial
    refine Submodule.span_induction (p := fun z _ => f (z ⊗ₜ[R] y) ∈ I)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, b, rfl⟩
      have hy : ⁅(a : L), y⁆ = (0 : J) :=
        Subtype.ext (disjoint_ideals_bracket_zero I J hIJ a y)
      have he : ⁅a, b⁆ ⊗ₜ[R] y = ⁅(a : L), b ⊗ₜ[R] y⁆ := by
        rw [TensorProduct.LieModule.lie_tmul_right, hy, TensorProduct.tmul_zero, add_zero]
        rfl
      rw [he, f.map_lie]
      exact lie_mem_left R L I a _ a.property
    · simpa only [TensorProduct.zero_tmul, map_zero] using I.zero_mem
    · intro a b _ _ ha hb
      simpa only [TensorProduct.add_tmul, map_add] using I.add_mem ha hb
    · intro c a _ ha
      simpa only [← TensorProduct.smul_tmul', map_smul] using I.smul_mem c ha
  | add t u ht hu => simpa only [map_add] using I.add_mem ht hu

/-- Perfectness of the right ideal gives the corresponding right-image
containment for every actual equivariant tensor-to-adjoint map. -/
theorem ideal_tensor_to_adjoint_mem_right (I J : LieIdeal R L)
    (hJ : ⁅J, J⁆ = J) (hIJ : Disjoint I J)
    (f : I ⊗[R] J →ₗ⁅R,L⁆ L) (t : I ⊗[R] J) : f t ∈ J := by
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using J.zero_mem
  | tmul x y =>
    have hy : y ∈ Submodule.span R {⁅a, b⁆ | (a : J) (b : J)} := by
      rw [perfect_ideal_bracket_span J hJ]
      trivial
    refine Submodule.span_induction (p := fun z _ => f (x ⊗ₜ[R] z) ∈ J)
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨a, b, rfl⟩
      have hx : ⁅(a : L), x⁆ = (0 : I) :=
        Subtype.ext (disjoint_ideals_bracket_zero J I hIJ.symm a x)
      have he : x ⊗ₜ[R] ⁅a, b⁆ = ⁅(a : L), x ⊗ₜ[R] b⁆ := by
        rw [TensorProduct.LieModule.lie_tmul_right, hx, TensorProduct.zero_tmul, zero_add]
        rfl
      rw [he, f.map_lie]
      exact lie_mem_left R L J a _ a.property
    · simpa only [TensorProduct.tmul_zero, map_zero] using J.zero_mem
    · intro a b _ _ ha hb
      simpa only [TensorProduct.tmul_add, map_add] using J.add_mem ha hb
    · intro c a _ ha
      simpa only [TensorProduct.tmul_smul, map_smul] using J.smul_mem c ha
  | add t u ht hu => simpa only [map_add] using J.add_mem ht hu

/-- There is no nonzero equivariant map from the tensor of two disjoint
perfect ideals to the adjoint module. Both ideals would contain its image. -/
theorem ideal_tensor_to_adjoint_eq_zero (I J : LieIdeal R L)
    (hI : ⁅I, I⁆ = I) (hJ : ⁅J, J⁆ = J) (hIJ : Disjoint I J)
    (f : I ⊗[R] J →ₗ⁅R,L⁆ L) : f = 0 := by
  ext t
  have hm : f t ∈ I ⊓ J :=
    ⟨ideal_tensor_to_adjoint_mem_left I J hI hIJ f t,
      ideal_tensor_to_adjoint_mem_right I J hJ hIJ f t⟩
  simpa only [hIJ.eq_bot, LieSubmodule.mem_bot] using hm

end Adjoint

section Range

variable {R L W : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]
  [LieModule.IsFaithful R L W] [LieModule.IsIrreducible R L W]

/-- For disjoint nonzero perfect ideals, the actual product representation
cannot take all its values in the original defining action's image. If it
did, faithfulness would lift it to the adjoint module, where perfectness
forces it to vanish. -/
theorem ideal_product_range_not_le_action_range (I J : LieIdeal R L)
    (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥)
    (hI : ⁅I, I⁆ = I) (hJ : ⁅J, J⁆ = J) (hIJ : Disjoint I J) :
    ¬(idealProductMap (W := W) I J).range.toSubmodule ≤
      (toEnd R L W).range.toSubmodule := by
  classical
  intro hle
  let ρ := toEnd R L W
  let μ := idealProductMap (W := W) I J
  have hall (t : I ⊗[R] J) : ∃ x : L, ρ x = μ t := hle ⟨t, rfl⟩
  let f₀ : I ⊗[R] J → L := fun t => Classical.choose (hall t)
  have hf₀ (t : I ⊗[R] J) : ρ (f₀ t) = μ t := Classical.choose_spec (hall t)
  have hρ : Function.Injective ρ := LieModule.IsFaithful.injective_toEnd
  let f : I ⊗[R] J →ₗ⁅R,L⁆ L := {
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
  have hf : f = 0 := ideal_tensor_to_adjoint_eq_zero I J hI hJ hIJ f
  apply ideal_product_map_ne_zero (W := W) I J hI0 hJ0
  apply DFunLike.ext
  intro t
  have ht : f₀ t = 0 := congrArg (fun g : I ⊗[R] J →ₗ⁅R,L⁆ L => g t) hf
  change μ t = 0
  rw [← hf₀, ht, map_zero]

/-- Semisimplicity derives the perfectness used by the product-range
obstruction, leaving only the actual nonzero disjoint ideals as inputs. -/
theorem semisimple_ideal_product_range_not_le_action_range
    [LieAlgebra.IsSemisimple R L] (I J : LieIdeal R L)
    (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hIJ : Disjoint I J) :
    ¬(idealProductMap (W := W) I J).range.toSubmodule ≤
      (toEnd R L W).range.toSubmodule :=
  ideal_product_range_not_le_action_range I J hI0 hJ0
    (semisimple_ideal_perfect I) (semisimple_ideal_perfect J) hIJ

end Range

end CubicAnomaly.Classification.IdealProductRepresentation
