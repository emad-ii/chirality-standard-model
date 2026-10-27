import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Nonzero products of ideal actions

On a faithful irreducible Lie module, every nonzero ideal generates the
entire module by its action.  Consequently an arbitrary linear map that
annihilates those actions is zero, and the actions of any two nonzero ideals
have a nonzero product.

These facts do not require a tensor-factor decomposition of the module,
complete reducibility, finite dimension, or a classification of Lie algebras.
They supply the nonvanishing step for actual products of commuting simple
ideal actions in classical defining representations.
-/

namespace CubicAnomaly.Classification.IdealActionProducts

open LieModule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [LieModule.IsFaithful R L M] [LieModule.IsIrreducible R L M]

/-- Every nonzero ideal acts with full generated image on a faithful
irreducible module. -/
theorem nonzero_ideal_action_eq_top (I : LieIdeal R L) (hI : I ≠ ⊥) :
    ⁅I, (⊤ : LieSubmodule R L M)⁆ = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top ⁅I, (⊤ : LieSubmodule R L M)⁆ with h | h
  · exfalso
    apply hI
    apply bot_unique
    intro x hx
    change x = 0
    apply (LieModule.isFaithful_iff' R L M).mp inferInstance x
    intro m
    rw [LieSubmodule.lie_eq_bot_iff] at h
    exact h x hx m (LieSubmodule.mem_top m)
  · exact h

/-- An arbitrary linear map is zero if it vanishes on the images of every
action operator from one nonzero ideal. -/
theorem linearMap_eq_zero_of_annihilates_ideal_actions
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : LieIdeal R L) (hI : I ≠ ⊥) (f : M →ₗ[R] N)
    (hf : ∀ x : I, ∀ m : M, f ⁅(x : L), m⁆ = 0) : f = 0 := by
  have hk : (⁅I, (⊤ : LieSubmodule R L M)⁆).toSubmodule ≤ LinearMap.ker f := by
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, m, rfl⟩
    exact hf x m
  ext m
  apply hk
  rw [nonzero_ideal_action_eq_top (M := M) I hI]
  trivial

/-- Two nonzero ideals have action operators whose actual composition is
nonzero, without assuming a factorization of the representation. -/
theorem exists_nonzero_ideal_action_product (I J : LieIdeal R L)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ∃ x : I, ∃ y : J, toEnd R L M (x : L) * toEnd R L M (y : L) ≠ 0 := by
  by_contra! hzero
  apply hI
  apply bot_unique
  intro x hx
  change x = 0
  apply (LieModule.toEnd_eq_zero_iff R L M).mp
  apply linearMap_eq_zero_of_annihilates_ideal_actions J hJ (toEnd R L M x)
  intro y m
  have h := congrArg (fun f : Module.End R M => f m) (hzero ⟨x, hx⟩ y)
  exact h

end CubicAnomaly.Classification.IdealActionProducts
