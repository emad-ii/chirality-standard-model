import CubicAnomaly.Classification.SelfDualAbsorption
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The actual invariant form of an equivariant self-duality

An equivariant equivalence with the contragredient dual is literally a
bilinear form. Equivariance is its invariance identity, and bijectivity
makes it nondegenerate in both variables. No symmetry, irreducibility,
algebraic closure, or finite-dimensionality is needed for this direction.
-/

namespace CubicAnomaly.Classification.SelfDualInvariantForm

open Module LieModule

noncomputable section

variable {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

/-- The actual bilinear form supplied by the actual equivariant
equivalence with the contragredient dual. -/
def selfDualBilinForm (E : W ≃ₗ⁅K,L⁆ Module.Dual K W) : LinearMap.BilinForm K W :=
  E.toLinearMap

/-- The form evaluates by applying the given duality to its first input. -/
@[simp] theorem self_dual_bilin_form_apply
    (E : W ≃ₗ⁅K,L⁆ Module.Dual K W) (u v : W) :
    selfDualBilinForm E u v = E u v := rfl

/-- Equivariance for the actual contragredient action is exactly
invariance of the constructed bilinear form. -/
theorem self_dual_bilin_form_invariant
    (E : W ≃ₗ⁅K,L⁆ Module.Dual K W) : (selfDualBilinForm E).lieInvariant L := by
  intro x u v
  exact LinearMap.congr_fun (E.toLieModuleHom.map_lie x u) v

/-- Bijectivity of the actual duality makes its constructed bilinear
form nondegenerate in both variables. The right-variable argument uses
surjectivity onto all linear functionals. -/
theorem self_dual_bilin_form_nondegenerate
    (E : W ≃ₗ⁅K,L⁆ Module.Dual K W) : (selfDualBilinForm E).Nondegenerate := by
  constructor
  · intro u hu
    apply E.injective
    rw [map_zero]
    apply LinearMap.ext
    intro v
    exact hu v
  · intro v hv
    apply (Module.forall_dual_apply_eq_zero_iff K v).mp
    intro φ
    obtain ⟨u, rfl⟩ := E.surjective φ
    exact hv u

/-- Actual equivariant self-duality constructs an actual invariant
nondegenerate bilinear form without any further representation witness. -/
theorem exists_invariant_nondegenerate_form_of_self_dual
    (hself : Nonempty (W ≃ₗ⁅K,L⁆ Module.Dual K W)) :
    ∃ β : LinearMap.BilinForm K W, β.lieInvariant L ∧ β.Nondegenerate := by
  obtain ⟨E⟩ := hself
  exact ⟨selfDualBilinForm E, self_dual_bilin_form_invariant E,
    self_dual_bilin_form_nondegenerate E⟩

end

end CubicAnomaly.Classification.SelfDualInvariantForm
