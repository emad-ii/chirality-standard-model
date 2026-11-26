import CubicAnomaly.Classification.SelfDualAbsorption
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# The actual one-dimensional scalar module

The scalar summand in defining endomorphisms is irreducible and self-dual
with the trivial Lie action. A simple nonabelian adjoint module cannot be
equivalent to this summand.
-/

namespace CubicAnomaly.Classification.ScalarModule

open Module LieModule
open CubicAnomaly.Classification.SelfDualAbsorption

noncomputable section

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

omit [LieAlgebra K L] in
/-- The actual scalar module is irreducible for its trivial action. -/
theorem scalar_module_irreducible :
    LieModule.IsIrreducible K L (TrivialLieModule K L K) := by
  letI : Nontrivial (TrivialLieModule K L K) := inferInstanceAs (Nontrivial K)
  letI : IsSimpleOrder (Submodule K (TrivialLieModule K L K)) :=
    inferInstanceAs (IsSimpleOrder (Submodule K K))
  apply LieModule.IsIrreducible.mk
  intro N hN
  rcases eq_bot_or_eq_top N.toSubmodule with hb | ht
  · exact (hN (LieSubmodule.toSubmodule_injective hb)).elim
  · exact LieSubmodule.toSubmodule_injective ht

/-- Multiplication in the scalar field is an actual invariant
nondegenerate form, hence gives actual equivariant scalar self-duality. -/
theorem scalar_module_self_dual :
    Nonempty (TrivialLieModule K L K ≃ₗ⁅K,L⁆
      Module.Dual K (TrivialLieModule K L K)) := by
  let U := TrivialLieModule K L K
  let E : U ≃ₗ[K] K := TrivialLieModule.equiv K L K
  letI : FiniteDimensional K U := E.symm.finiteDimensional
  let β : LinearMap.BilinForm K U := LinearMap.mul K K
  apply invariant_nondegenerate_form_self_dual β
  · intro x a b
    change β 0 b = -β a 0
    simp
  · constructor
    · intro a ha
      have he := ha (E.symm 1)
      change (show K from a) * 1 = 0 at he
      simpa only [mul_one] using he
    · intro a ha
      have he := ha (E.symm 1)
      change 1 * (show K from a) = 0 at he
      simpa only [one_mul] using he

/-- The scalar module cannot be an actual simple adjoint module. -/
theorem scalar_module_not_adjoint [LieAlgebra.IsSimple K L] :
    ¬ Nonempty (TrivialLieModule K L K ≃ₗ⁅K,L⁆ L) := by
  rintro ⟨E⟩
  apply LieAlgebra.IsSimple.non_abelian (L := L) K
  constructor
  intro x y
  obtain ⟨c, rfl⟩ := E.surjective y
  have he := E.map_lie x c
  rw [trivial_lie_zero, map_zero] at he
  exact he.symm

end

end CubicAnomaly.Classification.ScalarModule
