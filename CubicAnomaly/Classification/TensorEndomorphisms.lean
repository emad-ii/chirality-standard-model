import CubicAnomaly.Classification.IdealTensorDuality
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Actual endomorphisms of tensor modules

The canonical finite-dimensional identification of endomorphisms with a
tensor of endomorphism spaces respects the actual diagonal Lie action.
Its trace pairing factors on pure tensors. Skew/symmetric operator parity
for an actual tensor bilinear form is proved directly on pure vectors.
-/

namespace CubicAnomaly.Classification.TensorEndomorphisms

open Module LieModule
open scoped TensorProduct

noncomputable section

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

attribute [local ext] TensorProduct.ext in
/-- The usual tensor identification of endomorphisms is equivariant for
the standard diagonal action and the standard action on endomorphisms. -/
def tensorEndomorphismEquiv [FiniteDimensional K M] [FiniteDimensional K N] :
    (Module.End K M ⊗[K] Module.End K N) ≃ₗ⁅K,L⁆ Module.End K (M ⊗[K] N) := {
  homTensorHomEquiv K M N M N with
  map_lie' := by
    intro x t
    change homTensorHomEquiv K M N M N ⁅x, t⁆ =
      ⁅x, homTensorHomEquiv K M N M N t⁆
    simp only [homTensorHomEquiv_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      ext m n
      change (TensorProduct.homTensorHomMap (.id K) M N M N ⁅x, f ⊗ₜ[K] g⁆)
          (m ⊗ₜ[K] n) =
        (⁅x, TensorProduct.homTensorHomMap (.id K) M N M N (f ⊗ₜ[K] g)⁆)
          (m ⊗ₜ[K] n)
      simp only [TensorProduct.LieModule.lie_tmul_right, map_add,
        LinearMap.add_apply, TensorProduct.homTensorHomMap_apply,
        TensorProduct.map_tmul, LieHom.lie_apply, TensorProduct.sub_tmul,
        TensorProduct.tmul_sub]
      abel
    | add t u ht hu => rw [lie_add, map_add, ht, hu, map_add, lie_add] }

/-- The equivariant identification sends a pure operator tensor to its
literal tensor-product operator. -/
theorem tensor_endomorphism_equiv_tmul
    [FiniteDimensional K M] [FiniteDimensional K N]
    (f : Module.End K M) (g : Module.End K N) :
    tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N) (f ⊗ₜ[K] g) =
      TensorProduct.map f g := by
  exact homTensorHomEquiv_apply _

/-- The actual endomorphism identification loses no tensor of operators. -/
theorem tensor_endomorphism_equiv_injective
    [FiniteDimensional K M] [FiniteDimensional K N] :
    Function.Injective (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)) :=
  (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).injective

/-- On pure operator tensors, the actual trace pairing is the product
of the two factor trace pairings. -/
theorem tensor_endomorphism_trace_product
    [FiniteDimensional K M] [FiniteDimensional K N]
    (f f' : Module.End K M) (g g' : Module.End K N) :
    LinearMap.trace K (M ⊗[K] N)
        (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N) (f ⊗ₜ[K] g) *
          tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N) (f' ⊗ₜ[K] g')) =
      LinearMap.trace K M (f * f') * LinearMap.trace K N (g * g') := by
  rw [tensor_endomorphism_equiv_tmul, tensor_endomorphism_equiv_tmul]
  have hm : TensorProduct.map f g * TensorProduct.map f' g' =
      TensorProduct.map (f * f') (g * g') := by
    apply TensorProduct.ext'
    intro m n
    rfl
  rw [hm]
  exact LinearMap.trace_tensorProduct' _ _

/-- Adjointness signs multiply for literal tensor operators and the
literal tensor bilinear form. This needs no finite-dimensionality or
nondegeneracy hypotheses. -/
theorem tensor_operator_adjointness_signs
    (β : LinearMap.BilinForm K M) (γ : LinearMap.BilinForm K N)
    (f : Module.End K M) (g : Module.End K N) (a b : K)
    (hf : ∀ u v, β (f u) v = a * β u (f v))
    (hg : ∀ u v, γ (g u) v = b * γ u (g v))
    (z w : M ⊗[K] N) :
    (β.tmul γ) (TensorProduct.map f g z) w =
      (a * b) * (β.tmul γ) z (TensorProduct.map f g w) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m' n' =>
      simp only [TensorProduct.map_tmul, LinearMap.BilinForm.tmul,
        LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, hf, hg]
      ring
    | add w v hw hv => simp only [map_add, hw, hv, mul_add]
  | add z w hz hw => simp only [map_add, LinearMap.add_apply, hz, hw, mul_add]

/-- A skew operator in the first factor and a self-adjoint operator in
the second factor give a skew operator for the actual tensor form. -/
theorem tensor_skew_self_adjoint_operator
    (β : LinearMap.BilinForm K M) (γ : LinearMap.BilinForm K N)
    (f : Module.End K M) (g : Module.End K N)
    (hf : ∀ u v, β (f u) v = -β u (f v))
    (hg : ∀ u v, γ (g u) v = γ u (g v)) (z w : M ⊗[K] N) :
    (β.tmul γ) (TensorProduct.map f g z) w =
      -(β.tmul γ) z (TensorProduct.map f g w) := by
  simpa only [neg_one_mul, mul_one, one_mul] using
    tensor_operator_adjointness_signs β γ f g (-1) 1
      (by simpa only [neg_one_mul] using hf)
      (by simpa only [one_mul] using hg) z w

/-- Self-adjoint/skew parity in the opposite order has the same actual
form-preserving conclusion. -/
theorem tensor_self_adjoint_skew_operator
    (β : LinearMap.BilinForm K M) (γ : LinearMap.BilinForm K N)
    (f : Module.End K M) (g : Module.End K N)
    (hf : ∀ u v, β (f u) v = β u (f v))
    (hg : ∀ u v, γ (g u) v = -γ u (g v)) (z w : M ⊗[K] N) :
    (β.tmul γ) (TensorProduct.map f g z) w =
      -(β.tmul γ) z (TensorProduct.map f g w) := by
  simpa only [one_mul, neg_one_mul] using
    tensor_operator_adjointness_signs β γ f g 1 (-1)
      (by simpa only [one_mul] using hf)
      (by simpa only [neg_one_mul] using hg) z w

end

end CubicAnomaly.Classification.TensorEndomorphisms
