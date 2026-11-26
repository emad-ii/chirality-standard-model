import CubicAnomaly.Classification.SelfDualAbsorption
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Actual self-duality of tensor products of atomic ideals

The ambient Killing form restricts nondegenerately to every atomic ideal
of a finite-dimensional Killing Lie algebra. Its restriction is invariant
for the actual ambient action, not merely the ideal's own adjoint action.
Tensoring the resulting equivariant dualities gives self-duality of the
actual tensor product with its standard diagonal ambient Lie action.

The tensor-dual identification is proved equivariant directly on pure
functionals and pure tensors. No factorization, bilinear form, or
classification witness is supplied to the final ideal endpoint.
-/

namespace CubicAnomaly.Classification.IdealTensorDuality

open Module LieModule LieAlgebra
open CubicAnomaly.Classification.SelfDualAbsorption
open scoped TensorProduct

noncomputable section

section General

variable {K L M N P Q : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [AddCommGroup P] [Module K P] [LieRingModule L P] [LieModule K L P]
  [AddCommGroup Q] [Module K Q] [LieRingModule L Q] [LieModule K L Q]

/-- Tensoring actual Lie module equivalences preserves the diagonal
ambient action. -/
def tensorLieEquiv (eM : M ≃ₗ⁅K,L⁆ P) (eN : N ≃ₗ⁅K,L⁆ Q) :
    (M ⊗[K] N) ≃ₗ⁅K,L⁆ (P ⊗[K] Q) := {
  TensorProduct.congr eM.toLinearEquiv eN.toLinearEquiv with
  map_lie' := by
    intro x t
    exact (TensorProduct.LieModule.map eM.toLieModuleHom eN.toLieModuleHom).map_lie x t }

attribute [local ext] TensorProduct.ext in
/-- The usual tensor-dual equivalence respects the actual contragredient
and diagonal Lie actions. -/
def tensorContragredientEquiv [FiniteDimensional K M] [FiniteDimensional K N] :
    (Module.Dual K M ⊗[K] Module.Dual K N) ≃ₗ⁅K,L⁆ Module.Dual K (M ⊗[K] N) := {
  TensorProduct.dualDistribEquiv K M N with
  map_lie' := by
    intro x t
    change TensorProduct.dualDistrib K M N ⁅x, t⁆ =
      ⁅x, TensorProduct.dualDistrib K M N t⁆
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [lie_zero (M := Module.Dual K M ⊗[K] Module.Dual K N) x, map_zero, lie_zero x]
    | tmul f g =>
      ext m n
      change (TensorProduct.dualDistrib K M N ⁅x, f ⊗ₜ[K] g⁆) (m ⊗ₜ[K] n) =
        (⁅x, TensorProduct.dualDistrib K M N (f ⊗ₜ[K] g)⁆) (m ⊗ₜ[K] n)
      simp only [TensorProduct.LieModule.lie_tmul_right, map_add, LinearMap.add_apply,
        TensorProduct.dualDistrib_apply, Module.Dual.lie_apply]
      ring
    | add t u ht hu => rw [lie_add x t u, map_add, ht, hu, map_add, lie_add] }

/-- Two actual finite-dimensional self-dual Lie modules have an actual
self-dual tensor product for the diagonal action. -/
def tensorSelfDualEquiv [FiniteDimensional K M] [FiniteDimensional K N]
    (eM : M ≃ₗ⁅K,L⁆ Module.Dual K M) (eN : N ≃ₗ⁅K,L⁆ Module.Dual K N) :
    (M ⊗[K] N) ≃ₗ⁅K,L⁆ Module.Dual K (M ⊗[K] N) :=
  (tensorLieEquiv eM eN).trans tensorContragredientEquiv

end General

section Ideals

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

/-- The actual ambient Killing form restricted to an ideal. -/
def idealKillingForm (I : LieIdeal K L) : LinearMap.BilinForm K I :=
  (killingForm K L).restrict I.toSubmodule

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
/-- The ambient Killing restriction is invariant for the whole ambient
Lie algebra's actual action on the ideal. -/
theorem ideal_killing_form_invariant (I : LieIdeal K L) :
    (idealKillingForm I).lieInvariant L := by
  intro x y z
  exact LieModule.traceForm_lieInvariant K L L x y z

/-- Atomic ideals inherit a nondegenerate restriction of the actual
ambient Killing form. -/
theorem atomic_ideal_killing_form_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (idealKillingForm I).Nondegenerate := by
  apply InvariantForm.restrict_nondegenerate (killingForm K L)
    (IsKilling.killingForm_nondegenerate K L)
    (LieModule.traceForm_lieInvariant K L L)
    (LieModule.traceForm_isSymm K L L).isRefl ?_ I hI
  intro J hJ habelian
  letI := habelian
  exact hJ.1 (IsKilling.ideal_eq_bot_of_isLieAbelian J)

/-- Every actual atomic ideal is equivariantly self-dual for the ambient
Lie action, through its derived Killing restriction. -/
theorem atomic_ideal_self_dual (I : LieIdeal K L) (hI : IsAtom I) :
    Nonempty (I ≃ₗ⁅K,L⁆ Module.Dual K I) :=
  invariant_nondegenerate_form_self_dual (idealKillingForm I)
    (ideal_killing_form_invariant I) (atomic_ideal_killing_form_nondegenerate I hI)

/-- The tensor product of actual atomic ideals is equivariantly self-dual
under the standard diagonal ambient action. All forms and dualities are
derived from the ambient Killing structure. -/
theorem atomic_ideal_tensor_self_dual (I J : LieIdeal K L)
    (hI : IsAtom I) (hJ : IsAtom J) :
    Nonempty ((I ⊗[K] J) ≃ₗ⁅K,L⁆ Module.Dual K (I ⊗[K] J)) := by
  obtain ⟨eI⟩ := atomic_ideal_self_dual I hI
  obtain ⟨eJ⟩ := atomic_ideal_self_dual J hJ
  exact ⟨tensorSelfDualEquiv eI eJ⟩

/-- Three actual atomic ideals also give an equivariantly self-dual
tensor product under the standard iterated diagonal ambient action. -/
theorem atomic_ideal_triple_self_dual (I J T : LieIdeal K L)
    (hI : IsAtom I) (hJ : IsAtom J) (hT : IsAtom T) :
    Nonempty (((I ⊗[K] J) ⊗[K] T) ≃ₗ⁅K,L⁆
      Module.Dual K ((I ⊗[K] J) ⊗[K] T)) := by
  obtain ⟨eIJ⟩ := atomic_ideal_tensor_self_dual I J hI hJ
  obtain ⟨eT⟩ := atomic_ideal_self_dual T hT
  exact ⟨tensorSelfDualEquiv eIJ eT⟩

end Ideals

end

end CubicAnomaly.Classification.IdealTensorDuality
