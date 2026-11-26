import CubicAnomaly.Classification.TensorEndomorphisms
import Mathlib.Algebra.Lie.SkewAdjoint

/-!
# Conjugating actual equivariant operators and bilinear forms

An equivariant equivalence of defining modules induces the literal
conjugation equivalence of their operator modules. It carries their
actual Lie actions to one another and preserves form-preserving operators
when the source form is the exact pullback of the target form.
-/

namespace CubicAnomaly.Classification.EquivariantOperatorTransport

open Module LieModule

noncomputable section

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- Literal conjugation by an actual equivariant defining-module
equivalence, bundled as an equivariant operator-module equivalence. -/
def operatorConjugation (e : M ≃ₗ⁅K,L⁆ N) :
    Module.End K M ≃ₗ⁅K,L⁆ Module.End K N := {
  e.toLinearEquiv.conj with
  map_lie' := by
    intro x A
    ext n
    change e (⁅x, A⁆ (e.symm n)) = ⁅x, e.toLinearEquiv.conj A⁆ n
    simp only [LieHom.lie_apply, map_sub, LinearEquiv.conj_apply_apply]
    change e ⁅x, A (e.symm n)⁆ - e (A ⁅x, e.symm n⁆) =
      ⁅x, e (A (e.symm n))⁆ - e (A (e.symm ⁅x, n⁆))
    congr 1
    · exact e.toLieModuleHom.map_lie x _
    · exact congrArg (fun m => e (A m)) (e.symm.toLieModuleHom.map_lie x n).symm }

/-- The operator equivalence is exactly conjugation on vectors. -/
@[simp] theorem operator_conjugation_apply (e : M ≃ₗ⁅K,L⁆ N)
    (A : Module.End K M) (n : N) : operatorConjugation e A n = e (A (e.symm n)) := rfl

/-- Conjugation carries the original action operator to the target's
actual action operator. -/
@[simp] theorem operator_conjugation_action (e : M ≃ₗ⁅K,L⁆ N) (x : L) :
    operatorConjugation e (toEnd K L M x) = toEnd K L N x := by
  ext n
  change e ⁅x, e.symm n⁆ = ⁅x, n⁆
  exact (e.toLieModuleHom.map_lie x (e.symm n)).trans
    (congrArg (fun n => ⁅x, n⁆) (e.apply_symm_apply n))

/-- Equality to an action operator is preserved and reflected by the
actual conjugation equivalence. -/
theorem operator_conjugation_eq_action_iff (e : M ≃ₗ⁅K,L⁆ N)
    (A : Module.End K M) (x : L) :
    operatorConjugation e A = toEnd K L N x ↔ A = toEnd K L M x := by
  rw [← operator_conjugation_action e x]
  exact (operatorConjugation e).injective.eq_iff

/-- An exact equality of actual forms transports skew-adjointness
through literal operator conjugation. -/
theorem operator_conjugation_mem_skew_iff (e : M ≃ₗ⁅K,L⁆ N)
    (Φ : LinearMap.BilinForm K N) (Ψ : LinearMap.BilinForm K M)
    (he : Φ.compl₁₂ e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap = Ψ)
    (A : Module.End K M) :
    operatorConjugation e A ∈ skewAdjointLieSubalgebra Φ ↔
      A ∈ skewAdjointLieSubalgebra Ψ := by
  have hform (u v : M) : Φ (e u) (e v) = Ψ u v :=
    LinearMap.congr_fun (LinearMap.congr_fun he u) v
  change operatorConjugation e A ∈ Φ.skewAdjointSubmodule ↔ A ∈ Ψ.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule, LinearMap.mem_skewAdjointSubmodule]
  constructor
  · intro h u v
    have h' := h (e u) (e v)
    change Φ (e (A (e.symm (e u)))) (e v) =
      Φ (e u) (-(e (A (e.symm (e v))))) at h'
    simpa only [e.symm_apply_apply, ← map_neg e, hform, Pi.neg_apply] using h'
  · intro h u v
    obtain ⟨u, rfl⟩ := e.surjective u
    obtain ⟨v, rfl⟩ := e.surjective v
    change Φ (e (A (e.symm (e u)))) (e v) =
      Φ (e u) (-(e (A (e.symm (e v)))))
    simpa only [e.symm_apply_apply, ← map_neg e, hform, Pi.neg_apply] using h u v

/-- Literal conjugation preserves the ordinary operator trace pairing. -/
theorem operator_conjugation_trace_product [FiniteDimensional K M]
    [FiniteDimensional K N] (e : M ≃ₗ⁅K,L⁆ N) (A B : Module.End K M) :
    LinearMap.trace K N (operatorConjugation e A * operatorConjugation e B) =
      LinearMap.trace K M (A * B) := by
  have he : operatorConjugation e A * operatorConjugation e B =
      e.toLinearEquiv.conj (A * B) := by
    ext n
    change e (A (e.symm (e (B (e.symm n))))) = e (A (B (e.symm n)))
    rw [e.symm_apply_apply]
  rw [he, LinearMap.trace_conj']

end

end CubicAnomaly.Classification.EquivariantOperatorTransport
