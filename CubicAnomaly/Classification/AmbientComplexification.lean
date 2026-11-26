import CubicAnomaly.Classification.ComplexHalf
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Ambient embeddings of complexified submodules

Scalar extension of a real inclusion is injective.  This file identifies
`ℂ ⊗[ℝ] N` with the actual subspace `N.baseChange ℂ` in the complexified
ambient space, including equivariance for Lie modules.  Complementary real
subspaces remain complementary, and the two irreducible complex halves of
an invariant real complement are embedded as actual ambient Lie submodules.
-/

namespace CubicAnomaly.Classification.Complexification

open CubicAnomaly.Classification.Structural
open scoped TensorProduct

section Linear

variable {M N : Type*} [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N]

/-- Real projection commutes with scalar extension of every real linear map. -/
theorem complexification_realPart_natural (f : M →ₗ[ℝ] N) (z : ℂ ⊗[ℝ] M) :
    tensorRealPart N (f.baseChange ℂ z) = f (tensorRealPart M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [tensorRealPart]
  | add x y hx hy => simp [hx, hy]

/-- Imaginary projection commutes with scalar extension of every real linear map. -/
theorem complexification_imagPart_natural (f : M →ₗ[ℝ] N) (z : ℂ ⊗[ℝ] M) :
    tensorImagPart N (f.baseChange ℂ z) = f (tensorImagPart M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [tensorImagPart]
  | add x y hx hy => simp [hx, hy]

/-- Complex scalar extension preserves injectivity of real linear maps. -/
theorem complexification_linearMap_injective (f : M →ₗ[ℝ] N)
    (hf : Function.Injective f) : Function.Injective (f.baseChange ℂ) := by
  intro x y hxy
  have hr := congrArg (tensorRealPart N) hxy
  have hi := congrArg (tensorImagPart N) hxy
  rw [complexification_realPart_natural, complexification_realPart_natural] at hr
  rw [complexification_imagPart_natural, complexification_imagPart_natural] at hi
  apply sub_eq_zero.mp
  apply (complexification_zero_iff_parts M (x - y)).mpr
  exact ⟨by simp [hf hr], by simp [hf hi]⟩

/-- Canonical identification of a tensor-product subspace with its actual
image inside the complexified ambient vector space. -/
noncomputable def submoduleComplexificationEquiv (p : Submodule ℝ M) :
    (ℂ ⊗[ℝ] p) ≃ₗ[ℂ] p.baseChange ℂ :=
  LinearEquiv.ofInjective (p.subtype.baseChange ℂ)
    (complexification_linearMap_injective p.subtype Subtype.val_injective)

/-- The ambient embedding sends a pure tensor to the same pure tensor of
the underlying real vector. -/
theorem submoduleComplexificationEquiv_tmul (p : Submodule ℝ M) (a : ℂ) (m : p) :
    (submoduleComplexificationEquiv p (a ⊗ₜ[ℝ] m) : ℂ ⊗[ℝ] M) =
      a ⊗ₜ[ℝ] (m : M) := rfl

/-- Complexification of a real subspace preserves its dimension. -/
theorem complexification_submodule_finrank (p : Submodule ℝ M) :
    Module.finrank ℂ (p.baseChange ℂ) = Module.finrank ℝ p := by
  rw [← (submoduleComplexificationEquiv p).finrank_eq]
  exact Module.finrank_baseChange

/-- Complementarity survives scalar extension inside the actual ambient
complexification. -/
theorem complexification_submodules_isCompl (p q : Submodule ℝ M)
    (hpq : IsCompl p q) : IsCompl (p.baseChange ℂ) (q.baseChange ℂ) := by
  apply IsCompl.of_eq
  · apply le_antisymm _ bot_le
    intro z hz
    have hp := (complexification_mem_baseChange_iff_parts M p z).mp hz.1
    have hq := (complexification_mem_baseChange_iff_parts M q z).mp hz.2
    have hr : tensorRealPart M z ∈ p ⊓ q := ⟨hp.1, hq.1⟩
    have hi : tensorImagPart M z ∈ p ⊓ q := ⟨hp.2, hq.2⟩
    rw [hpq.inf_eq_bot, Submodule.mem_bot] at hr hi
    exact (complexification_zero_iff_parts M z).mpr ⟨hr, hi⟩
  · apply top_unique
    intro z _
    have hr : tensorRealPart M z ∈ p ⊔ q := by rw [hpq.sup_eq_top]; trivial
    have hi : tensorImagPart M z ∈ p ⊔ q := by rw [hpq.sup_eq_top]; trivial
    obtain ⟨rp, hrp, rq, hrq, hr⟩ := Submodule.mem_sup.mp hr
    obtain ⟨ip, hip, iq, hiq, hi⟩ := Submodule.mem_sup.mp hi
    apply Submodule.mem_sup.mpr
    refine ⟨1 ⊗ₜ[ℝ] rp + Complex.I ⊗ₜ[ℝ] ip,
      (p.baseChange ℂ).add_mem (p.tmul_mem_baseChange_of_mem 1 hrp)
        (p.tmul_mem_baseChange_of_mem Complex.I hip),
      1 ⊗ₜ[ℝ] rq + Complex.I ⊗ₜ[ℝ] iq,
      (q.baseChange ℂ).add_mem (q.tmul_mem_baseChange_of_mem 1 hrq)
        (q.tmul_mem_baseChange_of_mem Complex.I hiq), ?_⟩
    calc
      _ = 1 ⊗ₜ[ℝ] (rp + rq) + Complex.I ⊗ₜ[ℝ] (ip + iq) := by
        simp only [TensorProduct.tmul_add]; abel
      _ = z := by rw [hr, hi]; exact (complexification_real_imag_decomposition M z).symm

end Linear

section LieModules

variable {L M N : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]
  [AddCommGroup N] [Module ℝ N] [LieRingModule L N] [LieModule ℝ L N]

/-- Scalar extension of an arbitrary real equivariant linear map. -/
noncomputable def complexifiedHom (f : M →ₗ⁅ℝ,L⁆ N) :
    (ℂ ⊗[ℝ] M) →ₗ⁅ℂ,ℂ ⊗[ℝ] L⁆ (ℂ ⊗[ℝ] N) := {
  f.toLinearMap.baseChange ℂ with
  map_lie' := by
    intro x m
    change (f.toLinearMap.baseChange ℂ)
        ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) x) m) =
      (LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] N) x)
        ((f.toLinearMap.baseChange ℂ) m)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      induction m using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b m => simp [LieModule.toEnd_apply_apply, f.map_lie]
      | add m n hm hn => simp only [map_add, hm, hn]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy] }

/-- Scalar extension of a Lie-module inclusion has exactly the expected
ambient range. -/
theorem complexified_inclusion_range (p : LieSubmodule ℝ L M) :
    (complexifiedHom p.incl).range = p.baseChange ℂ := rfl

/-- The canonical ambient identification also preserves the complexified
Lie action. -/
noncomputable def lieSubmoduleComplexificationEquiv (p : LieSubmodule ℝ L M) :
    (ℂ ⊗[ℝ] p) ≃ₗ⁅ℂ,ℂ ⊗[ℝ] L⁆ p.baseChange ℂ := {
  submoduleComplexificationEquiv p.toSubmodule with
  map_lie' := by
    intro x m
    apply Subtype.ext
    exact (complexifiedHom p.incl).map_lie x m }

/-- Pure-tensor formula for the equivariant ambient identification. -/
theorem lieSubmoduleComplexificationEquiv_tmul (p : LieSubmodule ℝ L M)
    (a : ℂ) (m : p) :
    (lieSubmoduleComplexificationEquiv p (a ⊗ₜ[ℝ] m) : ℂ ⊗[ℝ] M) =
      a ⊗ₜ[ℝ] (m : M) := rfl

/-- An invariant complex half, realized inside the ambient complexification. -/
noncomputable def ambientComplexifiedHalf (p : LieSubmodule ℝ L M)
    (J : p →ₗ⁅ℝ,L⁆ p) (a : ℂ) : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) :=
  (invariantEigenspace (complexifiedEnd J) a).map (complexifiedHom p.incl)

/-- Each abstract half is equivariantly isomorphic to its actual ambient
image. -/
noncomputable def ambientHalfEquiv (p : LieSubmodule ℝ L M)
    (J : p →ₗ⁅ℝ,L⁆ p) (a : ℂ) :
    invariantEigenspace (complexifiedEnd J) a ≃ₗ⁅ℂ,ℂ ⊗[ℝ] L⁆ ambientComplexifiedHalf p J a :=
  (invariantEigenspace (complexifiedEnd J) a).equivMapOfInjective
    (complexification_linearMap_injective p.incl.toLinearMap Subtype.val_injective)

/-- The two ambient complex halves have zero intersection. -/
theorem ambient_complex_halves_disjoint (p : LieSubmodule ℝ L M)
    (J : p →ₗ⁅ℝ,L⁆ p) (hJ : ∀ m, J (J m) = -m) :
    Disjoint (ambientComplexifiedHalf p J Complex.I)
      (ambientComplexifiedHalf p J (-Complex.I)) := by
  rw [disjoint_iff]
  unfold ambientComplexifiedHalf
  rw [← LieSubmodule.map_inf
    (complexification_linearMap_injective p.incl.toLinearMap Subtype.val_injective),
    (complexified_complex_structure_isCompl J hJ).inf_eq_bot, LieSubmodule.map_bot]

/-- Their sum is the whole complexified real submodule inside the ambient
complexification. -/
theorem ambient_complex_halves_sup (p : LieSubmodule ℝ L M)
    (J : p →ₗ⁅ℝ,L⁆ p) (hJ : ∀ m, J (J m) = -m) :
    ambientComplexifiedHalf p J Complex.I ⊔ ambientComplexifiedHalf p J (-Complex.I) =
      p.baseChange ℂ := by
  unfold ambientComplexifiedHalf
  rw [← LieSubmodule.map_sup, (complexified_complex_structure_isCompl J hJ).sup_eq_top,
    LieModuleHom.map_top, complexified_inclusion_range]

/-- Both actual ambient halves are irreducible whenever the original
real submodule is irreducible. -/
theorem ambient_complex_halves_irreducible (p : LieSubmodule ℝ L M)
    [LieModule.IsIrreducible ℝ L p]
    (J : p →ₗ⁅ℝ,L⁆ p) (hJ : ∀ m, J (J m) = -m) :
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] L) (ambientComplexifiedHalf p J Complex.I) ∧
      LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] L) (ambientComplexifiedHalf p J (-Complex.I)) := by
  constructor
  · exact (LieSubmodule.orderIsoMapComap (ambientHalfEquiv p J Complex.I)).isSimpleOrder_iff.mp
      (complexification_positive_half_irreducible J hJ)
  · exact (LieSubmodule.orderIsoMapComap (ambientHalfEquiv p J (-Complex.I))).isSimpleOrder_iff.mp
      (complexification_negative_half_irreducible J hJ)

end LieModules

section CompactPair

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The original orthogonal real decomposition gives an actual
complementary decomposition of the complexified ambient algebra. -/
theorem compact_pair_complexification_isCompl (B : CompactForm g)
    (h : LieSubalgebra ℝ g) :
    IsCompl (h.toSubmodule.baseChange ℂ)
      ((orthogonalComplement B h).toSubmodule.baseChange ℂ) :=
  complexification_submodules_isCompl _ _ (compact_orthogonal_complement_isCompl B h)

end CompactPair

end CubicAnomaly.Classification.Complexification
