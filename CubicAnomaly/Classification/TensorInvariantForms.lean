import CubicAnomaly.Classification.IdealTensorDuality
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Invariance and nondegeneracy of actual tensor forms

The literal tensor product of invariant bilinear forms is invariant for
the standard diagonal action. The literal tensor product of two
nondegenerate finite-dimensional forms is nondegenerate, through the
canonical tensor-dual equivalence. Pullback along an actual linear
equivalence preserves nondegeneracy without a dimension assumption.
-/

namespace CubicAnomaly.Classification.TensorInvariantForms

open Module LieModule
open scoped TensorProduct

noncomputable section

section Invariance

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- Invariant factor forms have an invariant literal tensor product
for the actual standard diagonal action. -/
theorem tensor_bilin_form_invariant
    (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L) :
    LinearMap.BilinForm.lieInvariant L (β.tmul γ) := by
  intro x z w
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m' n' =>
      simp only [TensorProduct.LieModule.lie_tmul_right, map_add, LinearMap.add_apply,
        LinearMap.BilinForm.tmul, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
      rw [hβ x m m', hγ x n n']
      ring
    | add w v hw hv => simp only [lie_add, map_add, hw, hv, neg_add]
  | add z t hz ht =>
    simp only [lie_add, map_add, LinearMap.add_apply, hz, ht, neg_add]

end Invariance

section Nondegeneracy

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- Pulling back the original nondegenerate form through an actual
linear equivalence preserves nondegeneracy. -/
theorem pullback_bilin_form_nondegenerate
    (B : LinearMap.BilinForm K N) (hB : B.Nondegenerate) (e : M ≃ₗ[K] N) :
    (B.compl₁₂ e.toLinearMap e.toLinearMap).Nondegenerate := by
  constructor
  · intro m hm
    apply e.injective
    rw [map_zero]
    apply hB.1
    intro n
    obtain ⟨u, rfl⟩ := e.surjective n
    exact hm u
  · intro m hm
    apply e.injective
    rw [map_zero]
    apply hB.2
    intro n
    obtain ⟨u, rfl⟩ := e.surjective n
    exact hm u

variable [FiniteDimensional K M] [FiniteDimensional K N]

/-- Nondegenerate finite factor forms have a nondegenerate literal
tensor product, via the canonical tensor-dual equivalence. -/
theorem tensor_bilin_form_nondegenerate
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate)
    (γ : LinearMap.BilinForm K N) (hγ : γ.Nondegenerate) :
    (β.tmul γ).Nondegenerate := by
  let E : M ⊗[K] N ≃ₗ[K] Module.Dual K (M ⊗[K] N) :=
    (TensorProduct.congr (β.toDual hβ) (γ.toDual hγ)).trans
      (TensorProduct.dualDistribEquiv K M N)
  have he (z w : M ⊗[K] N) : E z w = (β.tmul γ) z w := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul m' n' =>
        change β m m' * γ n n' = γ n n' * β m m'
        exact mul_comm _ _
      | add w v hw hv => simp only [map_add, hw, hv]
    | add z t hz ht => simp only [map_add, LinearMap.add_apply, hz, ht]
  constructor
  · intro z hz
    apply E.injective
    apply LinearMap.ext
    intro w
    simpa only [he, map_zero, LinearMap.zero_apply] using hz w
  · intro z hz
    apply (Module.forall_dual_apply_eq_zero_iff K z).mp
    intro f
    obtain ⟨w, rfl⟩ := E.surjective f
    rw [he]
    exact hz w

end Nondegeneracy

end

end CubicAnomaly.Classification.TensorInvariantForms
