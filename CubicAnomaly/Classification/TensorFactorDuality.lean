import CubicAnomaly.Classification.ExternalTensor
import CubicAnomaly.Classification.SelfDualAbsorption
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Self-duality of irreducible tensor factors

A nonzero invariant bilinear form on a tensor product has a nonzero
coefficient form on each factor.  If one factor is irreducible and the
other factor has trivial action, its coefficient form is invariant and
therefore nondegenerate.  This constructs self-duality of the actual
irreducible factor without supplying any form on that factor.
-/

namespace CubicAnomaly.Classification.TensorFactorDuality

open scoped TensorProduct

noncomputable section

section Coefficients

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- A coefficient of the actual tensor form, retaining the left factor. -/
def leftCoefficientForm (B : LinearMap.BilinForm K (M ⊗[K] N)) (n n' : N) :
    LinearMap.BilinForm K M :=
  B.compl₁₂ ((TensorProduct.mk K M N).flip n) ((TensorProduct.mk K M N).flip n')

/-- A coefficient of the actual tensor form, retaining the right factor. -/
def rightCoefficientForm (B : LinearMap.BilinForm K (M ⊗[K] N)) (m m' : M) :
    LinearMap.BilinForm K N :=
  B.compl₁₂ (TensorProduct.mk K M N m) (TensorProduct.mk K M N m')

/-- Left coefficients evaluate the original form on literal pure tensors. -/
theorem left_coefficient_form_apply (B : LinearMap.BilinForm K (M ⊗[K] N))
    (n n' : N) (m m' : M) :
    leftCoefficientForm B n n' m m' = B (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n') := rfl

/-- Right coefficients evaluate the original form on literal pure tensors. -/
theorem right_coefficient_form_apply (B : LinearMap.BilinForm K (M ⊗[K] N))
    (m m' : M) (n n' : N) :
    rightCoefficientForm B m m' n n' = B (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n') := rfl

private theorem tensor_form_eq_zero_of_pure_eq_zero
    (B : LinearMap.BilinForm K (M ⊗[K] N))
    (hB : ∀ m n m' n', B (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n') = 0) : B = 0 := by
  apply LinearMap.ext
  intro t
  apply LinearMap.ext
  intro u
  change B t u = 0
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul m' n' => exact hB m n m' n'
    | add u v hu hv => simp only [map_add, hu, hv, add_zero]
  | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu, add_zero]

/-- A nonzero tensor form has a nonzero left coefficient. -/
theorem exists_nonzero_left_coefficient
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hB : B ≠ 0) :
    ∃ n n', leftCoefficientForm B n n' ≠ 0 := by
  by_contra! h
  apply hB
  apply tensor_form_eq_zero_of_pure_eq_zero
  intro m n m' n'
  exact congrArg (fun F : LinearMap.BilinForm K M => F m m') (h n n')

/-- A nonzero tensor form has a nonzero right coefficient. -/
theorem exists_nonzero_right_coefficient
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hB : B ≠ 0) :
    ∃ m m', rightCoefficientForm B m m' ≠ 0 := by
  by_contra! h
  apply hB
  apply tensor_form_eq_zero_of_pure_eq_zero
  intro m n m' n'
  exact congrArg (fun F : LinearMap.BilinForm K N => F n n') (h m m')

end Coefficients

section Irreducible

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- Every nonzero invariant form on a finite irreducible module is
nondegenerate, with no symmetry or algebraic-closure hypothesis. -/
theorem invariant_form_nondegenerate_of_ne_zero
    [Module.Finite K M] [LieModule.IsIrreducible K L M]
    (B : LinearMap.BilinForm K M) (hinv : B.lieInvariant L) (hB : B ≠ 0) :
    B.Nondegenerate := by
  let f : M →ₗ⁅K,L⁆ Module.Dual K M := {
    B with
    map_lie' := by
      intro x m
      ext n
      exact hinv x m n }
  have hker : f.ker = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top f.ker with h | h
    · exact h
    · exfalso
      apply hB
      apply LinearMap.ext
      intro m
      have hm : m ∈ f.ker := by rw [h]; trivial
      exact hm
  exact LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    (LinearMap.ker_eq_bot.mpr ((LieModuleHom.ker_eq_bot f).mp hker))

end Irreducible

section LieCoefficients

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- Triviality of the right action makes every left coefficient invariant. -/
theorem left_coefficient_form_invariant [LieModule.IsTrivial L N]
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hB : B.lieInvariant L) (n n' : N) :
    (leftCoefficientForm B n n').lieInvariant L := by
  intro x m m'
  change B (⁅x, m⁆ ⊗ₜ[K] n) (m' ⊗ₜ[K] n') =
    -B (m ⊗ₜ[K] n) (⁅x, m'⁆ ⊗ₜ[K] n')
  simpa only [TensorProduct.LieModule.lie_tmul_right, trivial_lie_zero,
    TensorProduct.tmul_zero, add_zero] using hB x (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n')

/-- Triviality of the left action makes every right coefficient invariant. -/
theorem right_coefficient_form_invariant [LieModule.IsTrivial L M]
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hB : B.lieInvariant L) (m m' : M) :
    (rightCoefficientForm B m m').lieInvariant L := by
  intro x n n'
  change B (m ⊗ₜ[K] ⁅x, n⁆) (m' ⊗ₜ[K] n') =
    -B (m ⊗ₜ[K] n) (m' ⊗ₜ[K] ⁅x, n'⁆)
  simpa only [TensorProduct.LieModule.lie_tmul_right, trivial_lie_zero,
    TensorProduct.zero_tmul, zero_add] using hB x (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n')

/-- A nonzero invariant tensor form constructs a nondegenerate actual
coefficient form on the finite irreducible left factor. -/
theorem exists_nondegenerate_left_coefficient
    [Module.Finite K M] [LieModule.IsIrreducible K L M] [LieModule.IsTrivial L N]
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hinv : B.lieInvariant L) (hB : B ≠ 0) :
    ∃ n n', (leftCoefficientForm B n n').Nondegenerate := by
  obtain ⟨n, n', h⟩ := exists_nonzero_left_coefficient B hB
  exact ⟨n, n', invariant_form_nondegenerate_of_ne_zero _
    (left_coefficient_form_invariant B hinv n n') h⟩

/-- A nonzero invariant tensor form constructs a nondegenerate actual
coefficient form on the finite irreducible right factor. -/
theorem exists_nondegenerate_right_coefficient
    [Module.Finite K N] [LieModule.IsIrreducible K L N] [LieModule.IsTrivial L M]
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hinv : B.lieInvariant L) (hB : B ≠ 0) :
    ∃ m m', (rightCoefficientForm B m m').Nondegenerate := by
  obtain ⟨m, m', h⟩ := exists_nonzero_right_coefficient B hB
  exact ⟨m, m', invariant_form_nondegenerate_of_ne_zero _
    (right_coefficient_form_invariant B hinv m m') h⟩

/-- The left factor is actually self-dual once the tensor product has any
nonzero invariant form and the complementary action is trivial. -/
theorem left_factor_self_dual_of_nonzero_invariant
    [Module.Finite K M] [LieModule.IsIrreducible K L M] [LieModule.IsTrivial L N]
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hinv : B.lieInvariant L) (hB : B ≠ 0) :
    Nonempty (M ≃ₗ⁅K,L⁆ Module.Dual K M) := by
  obtain ⟨n, n', h⟩ := exists_nondegenerate_left_coefficient B hinv hB
  exact SelfDualAbsorption.invariant_nondegenerate_form_self_dual _
    (left_coefficient_form_invariant B hinv n n') h

/-- The right factor is actually self-dual once the tensor product has any
nonzero invariant form and the complementary action is trivial. -/
theorem right_factor_self_dual_of_nonzero_invariant
    [Module.Finite K N] [LieModule.IsIrreducible K L N] [LieModule.IsTrivial L M]
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hinv : B.lieInvariant L) (hB : B ≠ 0) :
    Nonempty (N ≃ₗ⁅K,L⁆ Module.Dual K N) := by
  obtain ⟨m, m', h⟩ := exists_nondegenerate_right_coefficient B hinv hB
  exact SelfDualAbsorption.invariant_nondegenerate_form_self_dual _
    (right_coefficient_form_invariant B hinv m m') h

/-- A nondegenerate invariant tensor form implies actual self-duality of
the irreducible left factor whenever the right factor is nonzero and trivial. -/
theorem left_factor_self_dual_of_nondegenerate_invariant
    [Module.Finite K M] [LieModule.IsIrreducible K L M]
    [Nontrivial N] [LieModule.IsTrivial L N]
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hinv : B.lieInvariant L)
    (hB : B.Nondegenerate) : Nonempty (M ≃ₗ⁅K,L⁆ Module.Dual K M) := by
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
  letI : Nontrivial (M ⊗[K] N) := ExternalTensor.tensor_product_nontrivial
  exact left_factor_self_dual_of_nonzero_invariant B hinv hB.ne_zero

/-- A nondegenerate invariant tensor form implies actual self-duality of
the irreducible right factor whenever the left factor is nonzero and trivial. -/
theorem right_factor_self_dual_of_nondegenerate_invariant
    [Module.Finite K N] [LieModule.IsIrreducible K L N]
    [Nontrivial M] [LieModule.IsTrivial L M]
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hinv : B.lieInvariant L)
    (hB : B.Nondegenerate) : Nonempty (N ≃ₗ⁅K,L⁆ Module.Dual K N) := by
  letI : Nontrivial N := LieModule.nontrivial_of_isIrreducible K L N
  letI : Nontrivial (M ⊗[K] N) := ExternalTensor.tensor_product_nontrivial
  exact right_factor_self_dual_of_nonzero_invariant B hinv hB.ne_zero

end LieCoefficients

end

end CubicAnomaly.Classification.TensorFactorDuality
