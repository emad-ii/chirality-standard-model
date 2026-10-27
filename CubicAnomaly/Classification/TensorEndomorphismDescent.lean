import CubicAnomaly.Classification.LieDensity
import CubicAnomaly.Classification.TensorEndomorphisms
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent of commuting tensor endomorphisms

An endomorphism commuting with an irreducible left factor action is the
identity on that factor tensored with a unique right-factor operator.
Density reduces this to commutation with rank-one operators. Both
equivariance and skew-adjointness descend to the actual right operator.
-/

namespace CubicAnomaly.Classification.TensorEndomorphismDescent

open Module LieModule
open CubicAnomaly.Classification.LieDensity
open scoped TensorProduct

noncomputable section

section Linear

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

private def leftCoefficient (φ : Module.Dual K M) : M ⊗[K] N →ₗ[K] N :=
  (TensorProduct.lid K N).toLinearMap.comp (φ.rTensor N)

private theorem leftCoefficient_tmul (φ : Module.Dual K M) (m : M) (n : N) :
    leftCoefficient φ (m ⊗ₜ[K] n) = φ m • n := by
  simp [leftCoefficient]

private theorem rank_one_left_tensor (φ : Module.Dual K M) (m : M) (t : M ⊗[K] N) :
    ((φ.smulRight m).rTensor N) t = m ⊗ₜ[K] leftCoefficient φ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    simp only [LinearMap.rTensor_tmul, LinearMap.smulRight_apply, leftCoefficient_tmul,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  | add t u ht hu => simp only [map_add, ht, hu, TensorProduct.tmul_add]

/-- Commutation with every left factor operator forces a unique literal
right tensor factor. Neither factor needs to be finite-dimensional. -/
theorem exists_unique_right_factor_of_commutes [Nontrivial M]
    (F : Module.End K (M ⊗[K] N))
    (hF : ∀ A : Module.End K M, Commute F (A.rTensor N)) :
    ∃! D : Module.End K N, F = D.lTensor M := by
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hm₀
  let D : Module.End K N :=
    (leftCoefficient φ).comp (F.comp (TensorProduct.mk K M N m₀))
  have hD (m : M) (n : N) : F (m ⊗ₜ[K] n) = m ⊗ₜ[K] D n := by
    have h := LinearMap.congr_fun (hF (φ.smulRight m)).eq (m₀ ⊗ₜ[K] n)
    change F (((φ.smulRight m).rTensor N) (m₀ ⊗ₜ[K] n)) =
      ((φ.smulRight m).rTensor N) (F (m₀ ⊗ₜ[K] n)) at h
    simpa only [LinearMap.rTensor_tmul, LinearMap.smulRight_apply, hφ, one_smul,
      rank_one_left_tensor] using h
  refine ⟨D, TensorProduct.ext' hD, ?_⟩
  intro D' hD'
  ext n
  have h := congrArg (leftCoefficient φ) (congrArg (fun A : Module.End K (M ⊗[K] N) =>
    A (m₀ ⊗ₜ[K] n)) hD')
  change D n = _ at h
  simpa only [LinearMap.lTensor_tmul, leftCoefficient_tmul, hφ, one_smul] using h.symm

/-- The literal right-factor embedding of operators is injective whenever
the left vector space is nonzero. -/
theorem right_tensor_operator_injective [Nontrivial M] :
    Function.Injective (fun D : Module.End K N => D.lTensor M) := by
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hm₀
  intro A B h
  ext n
  have he := congrArg (leftCoefficient φ)
    (LinearMap.congr_fun h (m₀ ⊗ₜ[K] n))
  simpa only [LinearMap.lTensor_tmul, leftCoefficient_tmul, hφ, one_smul] using he

/-- Skew-adjointness for the actual tensor bilinear form descends to the
right operator as soon as the left bilinear form is nonzero. -/
theorem right_factor_skew_of_tensor_skew
    (β : LinearMap.BilinForm K M) (hβ : β ≠ 0) (γ : LinearMap.BilinForm K N)
    (D : Module.End K N)
    (hD : ∀ z w : M ⊗[K] N,
      (β.tmul γ) (D.lTensor M z) w = -(β.tmul γ) z (D.lTensor M w)) :
    ∀ n n', γ (D n) n' = -γ n (D n') := by
  obtain ⟨m, m', hm⟩ : ∃ m m' : M, β m m' ≠ 0 := by
    by_contra! h
    apply hβ
    ext m m'
    exact h m m'
  intro n n'
  have h := hD (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n')
  simp only [LinearMap.lTensor_tmul, LinearMap.BilinForm.tmul,
    LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] at h
  apply mul_right_cancel₀ hm
  simpa only [neg_mul] using h

/-- A nonzero tensor operator cannot descend to the zero right operator. -/
theorem right_factor_ne_zero (F : Module.End K (M ⊗[K] N))
    (D : Module.End K N) (he : F = D.lTensor M) (hF : F ≠ 0) : D ≠ 0 := by
  intro hD
  apply hF
  rw [he, hD, LinearMap.lTensor_zero]

end Linear

section Density

variable {K I M N : Type*} [Field K] [IsAlgClosed K]
  [LieRing I] [LieAlgebra K I]
  [AddCommGroup M] [Module K M] [LieRingModule I M] [LieModule K I M]
  [FiniteDimensional K M] [LieModule.IsIrreducible K I M]
  [AddCommGroup N] [Module K N]

/-- Actual irreducibility upgrades commutation with the left Lie action
to commutation with every left factor endomorphism. -/
theorem commutes_all_left_of_commutes_action
    (F : Module.End K (M ⊗[K] N))
    (hF : ∀ x : I, Commute F ((toEnd K I M x).rTensor N))
    (A : Module.End K M) : Commute F (A.rTensor N) := by
  let C : Subalgebra K (Module.End K M) :=
    (Subalgebra.centralizer K ({F} : Set (Module.End K (M ⊗[K] N)))).comap
      (Module.End.rTensorAlgHom K M N)
  have hC : C = ⊤ := by
    apply subalgebra_eq_top_of_lie_action_mem (L := I)
    intro x
    change (toEnd K I M x).rTensor N ∈ Subalgebra.centralizer K {F}
    rw [Subalgebra.mem_centralizer_iff]
    intro G hG
    have : G = F := Set.mem_singleton_iff.mp hG
    subst G
    exact (hF x).eq
  have hA : A ∈ C := by rw [hC]; trivial
  change A.rTensor N ∈ Subalgebra.centralizer K {F} at hA
  rw [Subalgebra.mem_centralizer_iff] at hA
  exact hA F (Set.mem_singleton F)

/-- A tensor endomorphism commuting with the actual irreducible left Lie
action has a unique right tensor factor. -/
theorem exists_unique_right_factor_of_commutes_action
    (F : Module.End K (M ⊗[K] N))
    (hF : ∀ x : I, Commute F ((toEnd K I M x).rTensor N)) :
    ∃! D : Module.End K N, F = D.lTensor M := by
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible K I M
  exact exists_unique_right_factor_of_commutes F (commutes_all_left_of_commutes_action F hF)

end Density

section Equivariance

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- The literal tensor interchange is equivariant for the actual
diagonal actions. -/
def tensorCommLieEquiv : M ⊗[K] N ≃ₗ⁅K,L⁆ N ⊗[K] M := {
  TensorProduct.comm K M N with
  map_lie' := by
    intro x t
    change (TensorProduct.comm K M N) ⁅x, t⁆ = ⁅x, (TensorProduct.comm K M N) t⁆
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [TensorProduct.LieModule.lie_tmul_right, add_comm]
    | add t u ht hu => simp only [lie_add, map_add, ht, hu] }

/-- Equivariant tensor interchange retains its literal pure-tensor map. -/
@[simp] theorem tensor_comm_lie_equiv_tmul (m : M) (n : N) :
    tensorCommLieEquiv (L := L) (m ⊗ₜ[K] n) = n ⊗ₜ[K] m := rfl

/-- Interchanging the defining factors interchanges their actual tensor
forms, with no scalar ambiguity. -/
theorem tensor_form_pullback_comm
    (β : LinearMap.BilinForm K M) (γ : LinearMap.BilinForm K N) :
    (β.tmul γ).compl₁₂
      (tensorCommLieEquiv (K := K) (L := L) (M := N) (N := M)).toLinearMap
      (tensorCommLieEquiv (K := K) (L := L) (M := N) (N := M)).toLinearMap = γ.tmul β := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro w
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul n m =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul n' m' =>
      change (β.tmul γ) (m ⊗ₜ[K] n) (m' ⊗ₜ[K] n') =
        (γ.tmul β) (n ⊗ₜ[K] m) (n' ⊗ₜ[K] m')
      simp only [LinearMap.BilinForm.tmul, LinearMap.BilinForm.tensorDistrib_tmul,
        smul_eq_mul, mul_comm]
    | add w v hw hv => simp only [map_add, hw, hv]
  | add z u hz hu => simp only [map_add, LinearMap.add_apply, hz, hu]

/-- An actual tensor form isometry can be reversed together with its
two factor forms. -/
theorem tensor_form_isometry_swap
    {W : Type*} [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
    (Φ : LinearMap.BilinForm K W) (E : M ⊗[K] N ≃ₗ⁅K,L⁆ W)
    (β : LinearMap.BilinForm K M) (γ : LinearMap.BilinForm K N)
    (hE : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ) :
    Φ.compl₁₂
      ((tensorCommLieEquiv (K := K) (L := L) (M := N) (N := M)).trans E).toLinearMap
      ((tensorCommLieEquiv (K := K) (L := L) (M := N) (N := M)).trans E).toLinearMap =
        γ.tmul β := by
  change (Φ.compl₁₂ E.toLinearMap E.toLinearMap).compl₁₂
    (tensorCommLieEquiv (K := K) (L := L) (M := N) (N := M)).toLinearMap
    (tensorCommLieEquiv (K := K) (L := L) (M := N) (N := M)).toLinearMap = _
  rw [hE, tensor_form_pullback_comm]

/-- If an ideal is trivial on the right factor, every ambient-equivariant
tensor endomorphism commutes with its pure left action. -/
theorem equivariant_commutes_left_action
    (I : LieIdeal K L) (hN : ∀ (x : I) (n : N), ⁅(x : L), n⁆ = 0)
    (F : (M ⊗[K] N) →ₗ⁅K,L⁆ (M ⊗[K] N)) (x : I) :
    Commute F.toLinearMap ((toEnd K I M x).rTensor N) := by
  have he : (toEnd K I M x).rTensor N = toEnd K L (M ⊗[K] N) (x : L) := by
    apply TensorProduct.ext'
    intro m n
    change ⁅x, m⁆ ⊗ₜ[K] n =
      ⁅(x : L), m⁆ ⊗ₜ[K] n + m ⊗ₜ[K] ⁅(x : L), n⁆
    rw [hN, TensorProduct.tmul_zero, add_zero]
    rfl
  change F.toLinearMap * (toEnd K I M x).rTensor N =
    (toEnd K I M x).rTensor N * F.toLinearMap
  rw [he]
  apply LinearMap.ext
  intro t
  exact F.map_lie (x : L) t

/-- The actual right operator of an ambient-equivariant tensor operator
is itself ambient-equivariant. Cancellation of the left tensor action
proves this without a separate triviality assumption on that action. -/
theorem right_factor_equivariant [Nontrivial M]
    (F : (M ⊗[K] N) →ₗ⁅K,L⁆ (M ⊗[K] N)) (D : Module.End K N)
    (hD : F.toLinearMap = D.lTensor M) (x : L) (n : N) :
    D ⁅x, n⁆ = ⁅x, D n⁆ := by
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hm₀
  have hpure (m : M) (n : N) : F (m ⊗ₜ[K] n) = m ⊗ₜ[K] D n := by
    change F.toLinearMap (m ⊗ₜ[K] n) = _
    rw [hD, LinearMap.lTensor_tmul]
  have h := F.map_lie x (m₀ ⊗ₜ[K] n)
  simp only [TensorProduct.LieModule.lie_tmul_right, map_add, hpure] at h
  have hc := congrArg (leftCoefficient φ) (add_left_cancel h)
  simpa only [leftCoefficient_tmul, hφ, one_smul] using hc

/-- An actual equivariant tensor endomorphism descends to an actual
equivariant right-factor endomorphism when an ideal acts irreducibly on
the left and trivially on the right. -/
theorem exists_right_equivariant_factor [IsAlgClosed K] [FiniteDimensional K M]
    (I : LieIdeal K L) [LieModule.IsIrreducible K I M]
    (hN : ∀ (x : I) (n : N), ⁅(x : L), n⁆ = 0)
    (F : (M ⊗[K] N) →ₗ⁅K,L⁆ (M ⊗[K] N)) :
    ∃ D : N →ₗ⁅K,L⁆ N, F.toLinearMap = D.toLinearMap.lTensor M := by
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible K I M
  obtain ⟨D, hD, _⟩ := exists_unique_right_factor_of_commutes_action (I := I)
    F.toLinearMap (equivariant_commutes_left_action I hN F)
  exact ⟨{ D with map_lie' := by intro x n; exact right_factor_equivariant F D hD x n }, hD⟩

/-- Nonzero skew equivariant operators descend with all three properties
to the actual multiplicity factor. The source tensor form is literal. -/
theorem exists_nonzero_skew_right_equivariant_factor
    [IsAlgClosed K] [FiniteDimensional K M]
    (I : LieIdeal K L) [LieModule.IsIrreducible K I M]
    (hN : ∀ (x : I) (n : N), ⁅(x : L), n⁆ = 0)
    (β : LinearMap.BilinForm K M) (hβ : β ≠ 0) (γ : LinearMap.BilinForm K N)
    (F : (M ⊗[K] N) →ₗ⁅K,L⁆ (M ⊗[K] N)) (hF : F ≠ 0)
    (hskew : ∀ z w : M ⊗[K] N,
      (β.tmul γ) (F z) w = -(β.tmul γ) z (F w)) :
    ∃ D : N →ₗ⁅K,L⁆ N, D ≠ 0 ∧
      F.toLinearMap = D.toLinearMap.lTensor M ∧
      ∀ n n', γ (D n) n' = -γ n (D n') := by
  obtain ⟨D, hD⟩ := exists_right_equivariant_factor I hN F
  refine ⟨D, ?_, hD, ?_⟩
  · intro hzero
    apply hF
    apply LieModuleHom.ext
    intro t
    change F.toLinearMap t = 0
    rw [hD, hzero]
    change (0 : Module.End K N).lTensor M t = 0
    rw [LinearMap.lTensor_zero, LinearMap.zero_apply]
  · apply right_factor_skew_of_tensor_skew β hβ γ D.toLinearMap
    intro z w
    rw [← hD]
    exact hskew z w

end Equivariance

end

end CubicAnomaly.Classification.TensorEndomorphismDescent
