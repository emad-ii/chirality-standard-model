import CubicAnomaly.Classification.TensorFactorDuality
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Factorization of actual invariant tensor forms

Schur's lemma makes every invariant coefficient form on an irreducible
factor a scalar multiple of one actual nondegenerate coefficient.  A
normalized coefficient on the other factor then gives an exact tensor
factorization of the original bilinear form.
-/

namespace CubicAnomaly.Classification.TensorFormFactorization

open CubicAnomaly.Classification.TensorFactorDuality
open scoped TensorProduct

noncomputable section

section Schur

variable {K L M : Type*} [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M] [LieModule.IsIrreducible K L M]

/-- Every actual equivariant endomorphism of a finite irreducible module
over an algebraically closed field is scalar. -/
theorem equivariant_end_eq_smul_id (f : M →ₗ⁅K,L⁆ M) :
    ∃ c : K, f = c • LieModuleHom.id := by
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f.toLinearMap
  obtain ⟨m, hm⟩ := hc.exists_hasEigenvector
  let g : M →ₗ⁅K,L⁆ M := f - c • LieModuleHom.id
  have hmem : m ∈ g.ker := by
    change f m - c • m = 0
    exact sub_eq_zero.mpr hm.apply_eq_smul
  have hne : g.ker ≠ ⊥ := by
    intro hz
    rw [hz, LieSubmodule.mem_bot] at hmem
    exact hm.2 hmem
  have htop : g.ker = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top g.ker).resolve_left hne
  refine ⟨c, ?_⟩
  apply LieModuleHom.ext
  intro u
  have hu : u ∈ g.ker := by rw [htop]; trivial
  exact sub_eq_zero.mp hu

private def invariantFormHom (B : LinearMap.BilinForm K M) (hB : B.lieInvariant L) :
    M →ₗ⁅K,L⁆ Module.Dual K M := {
  B with
  map_lie' := by
    intro x m
    ext n
    exact hB x m n }

private def invariantFormEquiv (B : LinearMap.BilinForm K M)
    (hinv : B.lieInvariant L) (hB : B.Nondegenerate) :
    M ≃ₗ⁅K,L⁆ Module.Dual K M := {
  B.linearEquivOfInjective (LinearMap.ker_eq_bot.mp hB.ker_eq_bot)
    Subspace.dual_finrank_eq.symm with
  toFun := B
  map_lie' := by
    intro x m
    ext n
    exact hinv x m n }

/-- Any invariant form is a scalar multiple of an actual invariant
nondegenerate form on the same finite irreducible module. -/
theorem invariant_form_eq_smul
    (B C : LinearMap.BilinForm K M) (hB : B.lieInvariant L)
    (hnd : B.Nondegenerate) (hC : C.lieInvariant L) :
    ∃ c : K, C = c • B := by
  let e := invariantFormEquiv B hB hnd
  let f := e.symm.toLieModuleHom.comp (invariantFormHom C hC)
  obtain ⟨c, hc⟩ := equivariant_end_eq_smul_id f
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  have h := congrArg (fun F : M →ₗ⁅K,L⁆ M => e (F m)) hc
  change e (e.symm (C m)) = e (c • m) at h
  rw [e.apply_symm_apply, map_smul] at h
  exact congrArg (fun φ : Module.Dual K M => φ n) h

/-- Every invariant form on a finite irreducible module over an
algebraically closed field is reflexive: orthogonality is symmetric even
before choosing between the symmetric and alternating possibilities. -/
theorem invariant_form_isRefl (B : LinearMap.BilinForm K M) (hB : B.lieInvariant L) :
    LinearMap.IsRefl B := by
  by_cases hz : B = 0
  · subst B
    intro m n _
    rfl
  have hflip : B.flip.lieInvariant L := by
    intro x m n
    change B n ⁅x, m⁆ = -B ⁅x, n⁆ m
    simpa only [neg_neg] using congrArg Neg.neg (hB x n m).symm
  obtain ⟨c, hc⟩ := invariant_form_eq_smul B B.flip hB
    (invariant_form_nondegenerate_of_ne_zero B hB hz) hflip
  intro m n hmn
  have h := congrArg (fun F : LinearMap.BilinForm K M => F m n) hc
  change B n m = c * B m n at h
  simpa only [hmn, mul_zero] using h

end Schur

section NormalizedCoefficient

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- The actual right coefficient normalized by a chosen nonzero value of
the actual left form. -/
def normalizedRightForm (B : LinearMap.BilinForm K (M ⊗[K] N))
    (β : LinearMap.BilinForm K M) (m₀ m₁ : M) : LinearMap.BilinForm K N :=
  (β m₀ m₁)⁻¹ • rightCoefficientForm B m₀ m₁

/-- The normalized coefficient is computed directly from the original form. -/
theorem normalized_right_form_apply (B : LinearMap.BilinForm K (M ⊗[K] N))
    (β : LinearMap.BilinForm K M) (m₀ m₁ : M) (n n' : N) :
    normalizedRightForm B β m₀ m₁ n n' =
      B (m₀ ⊗ₜ[K] n) (m₁ ⊗ₜ[K] n') / β m₀ m₁ := by
  change (β m₀ m₁)⁻¹ * B (m₀ ⊗ₜ[K] n) (m₁ ⊗ₜ[K] n') = _
  rw [div_eq_mul_inv, mul_comm]

private theorem right_eq_zero_of_tmul_eq_zero (m : M) (hm : m ≠ 0)
    (n : N) (h : m ⊗ₜ[K] n = 0) : n = 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hm
  have he := congrArg (fun t : M ⊗[K] N => (TensorProduct.lid K N) ((φ.rTensor N) t)) h
  simpa only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hφ, one_smul, map_zero] using he

/-- Nondegeneracy of an actual tensor product form forces nondegeneracy
of its right form as soon as the left vector space is nonzero. -/
theorem right_form_nondegenerate_of_tensor_factorization [Nontrivial M]
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hB : B.Nondegenerate)
    (β : LinearMap.BilinForm K M) (γ : LinearMap.BilinForm K N)
    (hfactor : B = β.tmul γ) : γ.Nondegenerate := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  constructor
  · intro n hn
    apply right_eq_zero_of_tmul_eq_zero (K := K) m hm n
    apply hB.1
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m' n' =>
      rw [hfactor]
      change γ n n' * β m m' = 0
      rw [hn, zero_mul]
    | add t u ht hu => simp only [map_add, ht, hu, add_zero]
  · intro n hn
    apply right_eq_zero_of_tmul_eq_zero (K := K) m hm n
    apply hB.2
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m' n' =>
      rw [hfactor]
      change γ n' n * β m' m = 0
      rw [hn, zero_mul]
    | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu, add_zero]

end NormalizedCoefficient

section RightInvariance

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [LieModule.IsTrivial L M]

/-- The normalized actual right coefficient inherits invariance under any
action that is trivial on the left factor and preserves the original form. -/
theorem normalized_right_form_invariant
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hB : B.lieInvariant L)
    (β : LinearMap.BilinForm K M) (m₀ m₁ : M) :
    (normalizedRightForm B β m₀ m₁).lieInvariant L := by
  intro x n n'
  change (β m₀ m₁)⁻¹ • rightCoefficientForm B m₀ m₁ ⁅x, n⁆ n' =
    -((β m₀ m₁)⁻¹ • rightCoefficientForm B m₀ m₁ n ⁅x, n'⁆)
  rw [right_coefficient_form_invariant B hB m₀ m₁, smul_neg]

end RightInvariance

section Factorization

variable {K L M N : Type*} [Field K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [Module.Finite K M] [LieModule.IsIrreducible K L M] [LieModule.IsTrivial L N]

/-- The original form factors on every pure tensor through its actual
normalized right coefficient and the chosen actual invariant left form. -/
theorem tensor_form_pure_factorization
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hB : B.lieInvariant L)
    (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L) (hnd : β.Nondegenerate)
    (m₀ m₁ : M) (hvalue : β m₀ m₁ ≠ 0) (m m' : M) (n n' : N) :
    B (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n') =
      β m m' * normalizedRightForm B β m₀ m₁ n n' := by
  obtain ⟨c, hc⟩ := invariant_form_eq_smul β (leftCoefficientForm B n n')
    hβ hnd (left_coefficient_form_invariant B hB n n')
  have hc₁ := congrArg (fun F : LinearMap.BilinForm K M => F m m') hc
  have hc₀ := congrArg (fun F : LinearMap.BilinForm K M => F m₀ m₁) hc
  change B (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n') = c * β m m' at hc₁
  change B (m₀ ⊗ₜ[K] n) (m₁ ⊗ₜ[K] n') = c * β m₀ m₁ at hc₀
  rw [normalized_right_form_apply, hc₀, mul_div_cancel_right₀ c hvalue, hc₁, mul_comm]

attribute [local ext] TensorProduct.ext in
/-- The pure-tensor factorization is equality with Mathlib's actual tensor
product of bilinear forms. -/
theorem tensor_form_eq_left_tmul_normalized_right
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hB : B.lieInvariant L)
    (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L) (hnd : β.Nondegenerate)
    (m₀ m₁ : M) (hvalue : β m₀ m₁ ≠ 0) :
    B = β.tmul (normalizedRightForm B β m₀ m₁) := by
  ext m n m' n'
  change B (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n') =
    normalizedRightForm B β m₀ m₁ n n' * β m m'
  rw [tensor_form_pure_factorization B hB β hβ hnd m₀ m₁ hvalue, mul_comm]

/-- The left form and its normalization vectors can be extracted from the
original tensor form itself; no factor form is supplied as a hypothesis. -/
theorem exists_coefficient_factorization
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hB : B.lieInvariant L) (hne : B ≠ 0) :
    ∃ n₀ n₁ : N, ∃ m₀ m₁ : M,
      (leftCoefficientForm B n₀ n₁).Nondegenerate ∧
      leftCoefficientForm B n₀ n₁ m₀ m₁ ≠ 0 ∧
      B = (leftCoefficientForm B n₀ n₁).tmul
        (normalizedRightForm B (leftCoefficientForm B n₀ n₁) m₀ m₁) := by
  obtain ⟨n₀, n₁, hnd⟩ := exists_nondegenerate_left_coefficient B hB hne
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, leftCoefficientForm B n₀ n₁ m₀ m₁ ≠ 0 := by
    by_contra! h
    exact hm₀ (hnd.1 m₀ h)
  refine ⟨n₀, n₁, m₀, m₁, hnd, hm₁, ?_⟩
  exact tensor_form_eq_left_tmul_normalized_right B hB _
    (left_coefficient_form_invariant B hB n₀ n₁) hnd m₀ m₁ hm₁

end Factorization

section TwoActions

variable {K I J M N : Type*} [Field K] [IsAlgClosed K]
  [LieRing I] [LieAlgebra K I] [LieRing J] [LieAlgebra K J]
  [AddCommGroup M] [Module K M] [LieRingModule I M] [LieModule K I M]
  [LieRingModule J M] [LieModule K J M] [LieModule.IsTrivial J M]
  [AddCommGroup N] [Module K N] [LieRingModule I N] [LieModule K I N]
  [LieModule.IsTrivial I N] [LieRingModule J N] [LieModule K J N]
  [Module.Finite K M] [LieModule.IsIrreducible K I M] [Nontrivial N]

/-- An actual nondegenerate form invariant under separate factor actions
factors as actual nondegenerate invariant forms on both factors.  Only the
left factor needs to be finite and irreducible. -/
theorem exists_nondegenerate_invariant_factorization
    (B : LinearMap.BilinForm K (M ⊗[K] N)) (hI : B.lieInvariant I)
    (hJ : B.lieInvariant J) (hB : B.Nondegenerate) :
    ∃ β : LinearMap.BilinForm K M, ∃ γ : LinearMap.BilinForm K N,
      β.lieInvariant I ∧ γ.lieInvariant J ∧
      β.Nondegenerate ∧ γ.Nondegenerate ∧ B = β.tmul γ := by
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible K I M
  letI : Nontrivial (M ⊗[K] N) := ExternalTensor.tensor_product_nontrivial
  obtain ⟨n₀, n₁, m₀, m₁, hnd, _, hfactor⟩ :=
    exists_coefficient_factorization B hI hB.ne_zero
  exact ⟨leftCoefficientForm B n₀ n₁,
    normalizedRightForm B (leftCoefficientForm B n₀ n₁) m₀ m₁,
    left_coefficient_form_invariant B hI n₀ n₁,
    normalized_right_form_invariant B hJ _ m₀ m₁,
    hnd, right_form_nondegenerate_of_tensor_factorization B hB _ _ hfactor, hfactor⟩

end TwoActions

end

end CubicAnomaly.Classification.TensorFormFactorization
