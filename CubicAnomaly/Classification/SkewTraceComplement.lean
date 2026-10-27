import CubicAnomaly.Classification.AdjointTraceForms
import Mathlib.Algebra.Lie.SkewAdjoint

/-!
# Actual trace forms and complements inside skew-adjoint operators

The skew-adjoint operator space has a nondegenerate invariant ordinary
trace pairing. An actual Lie action with nondegenerate trace form has an
actual equivariant trace-orthogonal complement inside this space. The
complement is self-dual and vanishes exactly when the action is the full
skew-adjoint algebra.
-/

namespace CubicAnomaly.Classification.SkewTraceComplement

open Module LieModule
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.SelfDualAbsorption

noncomputable section

section Adjoint

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/-- Actual skew-adjointness is the negative eigenspace of the actual
bilinear adjoint. -/
theorem mem_skew_adjoint_iff_form_adjoint
    (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate) (A : Module.End K W) :
    A ∈ β.skewAdjointSubmodule ↔ formAdjoint β hβ A = -A := by
  rw [LinearMap.mem_skewAdjointSubmodule]
  constructor
  · intro h
    have hp : LinearMap.IsAdjointPair β β (-A) A := by
      intro u v
      have ht := h u v
      change β (A u) v = β u (-A v) at ht
      change β (-A u) v = β u (A v)
      simpa only [map_neg, LinearMap.neg_apply, neg_neg] using congrArg Neg.neg ht
    exact ((β.isAdjointPair_iff_eq_of_nondegenerate hβ (-A) A).mp hp).symm
  · intro h
    have hp := form_adjoint_pair β hβ A
    rw [h] at hp
    intro u v
    have ht := hp u v
    change β (-A u) v = β u (A v) at ht
    change β (A u) v = β u (-A v)
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using congrArg Neg.neg ht

/-- The ordinary trace pairing on the actual skew-adjoint subspace. -/
def skewAdjointTraceForm (β : LinearMap.BilinForm K W) :
    LinearMap.BilinForm K β.skewAdjointSubmodule :=
  (endTraceForm (K := K) (W := W)).restrict β.skewAdjointSubmodule

variable [CharZero K]

/-- Antisymmetrizing an arbitrary test operator proves that the actual
skew-adjoint trace pairing is nondegenerate. -/
theorem skew_adjoint_trace_form_nondegenerate
    (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate) (hr : LinearMap.IsRefl β) :
    (skewAdjointTraceForm β).Nondegenerate := by
  have hs : LinearMap.IsSymm (skewAdjointTraceForm β) :=
    ⟨fun A B => LinearMap.trace_mul_comm K (A : Module.End K W) B⟩
  apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro A hA
  apply Subtype.ext
  apply (end_trace_form_nondegenerate (K := K) (W := W)).1 (A : Module.End K W)
  intro B
  have hB : B - formAdjoint β hβ B ∈ β.skewAdjointSubmodule := by
    apply (mem_skew_adjoint_iff_form_adjoint β hβ _).mpr
    rw [map_sub, form_adjoint_involutive β hβ hr, neg_sub]
  have h := hA ⟨B - formAdjoint β hβ B, hB⟩
  change LinearMap.trace K W ((A : Module.End K W) * (B - formAdjoint β hβ B)) = 0 at h
  have hfix := (mem_skew_adjoint_iff_form_adjoint β hβ (A : Module.End K W)).mp A.property
  have htransfer := trace_form_adjoint_transfer β hβ hr (A : Module.End K W) B
  rw [hfix, neg_mul, map_neg] at htransfer
  rw [mul_sub, map_sub, ← htransfer] at h
  have htwo : (2 : K) * LinearMap.trace K W ((A : Module.End K W) * B) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end Adjoint

section LieModule

variable {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

/-- Every actual operator of an invariant Lie action is skew-adjoint. -/
theorem action_mem_skew_adjoint (β : LinearMap.BilinForm K W)
    (hβ : β.lieInvariant L) (x : L) : toEnd K L W x ∈ β.skewAdjointSubmodule := by
  apply (LinearMap.mem_skewAdjointSubmodule _).mpr
  intro u v
  change β ⁅x, u⁆ v = β u (-⁅x, v⁆)
  rw [map_neg]
  exact hβ x u v

/-- Actual skew-adjoint operators, with the standard endomorphism action. -/
def skewAdjointLieSubmodule (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    LieSubmodule K L (Module.End K W) where
  __ := β.skewAdjointSubmodule
  lie_mem := by
    intro x A hA
    exact β.isSkewAdjoint_bracket (action_mem_skew_adjoint β hβ x) hA

/-- The actual restricted ordinary trace pairing on skew-adjoint operators. -/
def skewAdjointModuleTraceForm (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    LinearMap.BilinForm K (skewAdjointLieSubmodule β hβ) :=
  (endTraceForm (K := K) (W := W)).restrict (skewAdjointLieSubmodule β hβ).toSubmodule

/-- The actual skew-adjoint trace pairing is invariant. -/
theorem skew_adjoint_module_trace_form_invariant
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    (skewAdjointModuleTraceForm β hβ).lieInvariant L := by
  intro x A B
  exact end_trace_form_invariant (L := L) x (A : Module.End K W) (B : Module.End K W)

/-- The actual defining action, with codomain the actual skew operators. -/
def skewActionModuleHom (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    L →ₗ⁅K,L⁆ skewAdjointLieSubmodule β hβ where
  toLinearMap := (toEnd K L W).toLinearMap.codRestrict
    (skewAdjointLieSubmodule β hβ).toSubmodule (action_mem_skew_adjoint β hβ)
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact (toEnd K L W).map_lie x y

/-- The complement uses the literal operator trace and the actual
representation image. -/
def skewActionComplement (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    LieSubmodule K L (skewAdjointLieSubmodule β hβ) :=
  LieAlgebra.InvariantForm.orthogonal (skewAdjointModuleTraceForm β hβ)
    (skew_adjoint_module_trace_form_invariant β hβ) (skewActionModuleHom β hβ).range

/-- Literal inclusion of the actual trace complement into endomorphisms. -/
def skewActionComplementInclusion (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    skewActionComplement β hβ →ₗ⁅K,L⁆ Module.End K W :=
  (skewAdjointLieSubmodule β hβ).incl.comp (skewActionComplement β hβ).incl

/-- The actual complement inclusion is injective. -/
theorem skew_action_complement_inclusion_injective
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    Function.Injective (skewActionComplementInclusion β hβ) :=
  (LieSubmodule.injective_incl _).comp (LieSubmodule.injective_incl _)

variable [CharZero K] [FiniteDimensional K W]

/-- The actual skew-adjoint Lie module has nondegenerate trace form. -/
theorem skew_adjoint_module_trace_form_nondegenerate
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (hnd : β.Nondegenerate) (hr : LinearMap.IsRefl β) :
    (skewAdjointModuleTraceForm β hβ).Nondegenerate :=
  skew_adjoint_trace_form_nondegenerate β hnd hr

/-- Equivariant self-duality of all actual skew-adjoint operators follows
from their derived invariant trace form. -/
theorem skew_adjoint_self_dual
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (hnd : β.Nondegenerate) (hr : LinearMap.IsRefl β) :
    Nonempty ((skewAdjointLieSubmodule β hβ) ≃ₗ⁅K,L⁆
      Module.Dual K (skewAdjointLieSubmodule β hβ)) :=
  invariant_nondegenerate_form_self_dual (skewAdjointModuleTraceForm β hβ)
    (skew_adjoint_module_trace_form_invariant β hβ)
    (skew_adjoint_module_trace_form_nondegenerate β hβ hnd hr)

omit [CharZero K] [FiniteDimensional K W] in
/-- Nondegeneracy of the representation trace form is exactly what is
needed to make its actual image a nondegenerate subspace of skew operators. -/
theorem skew_action_range_trace_nondegenerate
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (htrace : (traceForm K L W).Nondegenerate) :
    ((skewAdjointModuleTraceForm β hβ).restrict
      (skewActionModuleHom β hβ).range.toSubmodule).Nondegenerate := by
  have hs : LinearMap.IsSymm ((skewAdjointModuleTraceForm β hβ).restrict
      (skewActionModuleHom β hβ).range.toSubmodule) :=
    ⟨fun A B => LinearMap.trace_mul_comm K (A.val.val : Module.End K W) B.val.val⟩
  apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro A hA
  obtain ⟨x, hx⟩ := A.property
  have hx0 : x = 0 := by
    apply htrace.1
    intro y
    have ht := hA ⟨skewActionModuleHom β hβ y, ⟨y, rfl⟩⟩
    change LinearMap.trace K W (A.val.val * toEnd K L W y) = 0 at ht
    change LinearMap.trace K W (toEnd K L W x * toEnd K L W y) = 0
    exact congrArg (fun T : skewAdjointLieSubmodule β hβ =>
      LinearMap.trace K W (T.val * toEnd K L W y)) hx ▸ ht
  apply Subtype.ext
  rw [← hx, hx0, map_zero]
  rfl

omit [CharZero K] in
/-- The actual action and its trace complement are complementary. -/
theorem skew_action_complement_isCompl
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (htrace : (traceForm K L W).Nondegenerate) :
    IsCompl (skewActionModuleHom β hβ).range (skewActionComplement β hβ) := by
  rw [← LieSubmodule.isCompl_toSubmodule]
  have hs : LinearMap.IsSymm (skewAdjointModuleTraceForm β hβ) :=
    ⟨fun A B => LinearMap.trace_mul_comm K (A : Module.End K W) B⟩
  exact (skewAdjointModuleTraceForm β hβ).isCompl_orthogonal_of_restrict_nondegenerate
    hs.isRefl
    (skew_action_range_trace_nondegenerate β hβ htrace)

/-- The restricted trace pairing on the actual complement is nondegenerate. -/
theorem skew_action_complement_trace_nondegenerate
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (hnd : β.Nondegenerate) (hr : LinearMap.IsRefl β)
    (htrace : (traceForm K L W).Nondegenerate) :
    ((skewAdjointModuleTraceForm β hβ).restrict
      (skewActionComplement β hβ).toSubmodule).Nondegenerate := by
  have hs : LinearMap.IsSymm (skewAdjointModuleTraceForm β hβ) :=
    ⟨fun A B => LinearMap.trace_mul_comm K (A : Module.End K W) B⟩
  apply (skewAdjointModuleTraceForm β hβ).nondegenerate_restrict_of_disjoint_orthogonal hs.isRefl
  change Disjoint
    ((skewAdjointModuleTraceForm β hβ).orthogonal (skewActionModuleHom β hβ).range.toSubmodule)
    ((skewAdjointModuleTraceForm β hβ).orthogonal
      ((skewAdjointModuleTraceForm β hβ).orthogonal (skewActionModuleHom β hβ).range.toSubmodule))
  rw [LinearMap.BilinForm.orthogonal_orthogonal
    (skew_adjoint_module_trace_form_nondegenerate β hβ hnd hr) hs.isRefl]
  exact (LieSubmodule.isCompl_toSubmodule.mpr
    (skew_action_complement_isCompl β hβ htrace)).disjoint.symm

/-- The actual skew trace complement is equivariantly self-dual. -/
theorem skew_action_complement_self_dual
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (hnd : β.Nondegenerate) (hr : LinearMap.IsRefl β)
    (htrace : (traceForm K L W).Nondegenerate) :
    Nonempty ((skewActionComplement β hβ) ≃ₗ⁅K,L⁆
      Module.Dual K (skewActionComplement β hβ)) := by
  let Φ : LinearMap.BilinForm K (skewActionComplement β hβ) :=
    (skewAdjointModuleTraceForm β hβ).restrict (skewActionComplement β hβ).toSubmodule
  apply invariant_nondegenerate_form_self_dual Φ
  · intro x A B
    exact skew_adjoint_module_trace_form_invariant β hβ x A.val B.val
  · exact skew_action_complement_trace_nondegenerate β hβ hnd hr htrace

omit [CharZero K] [FiniteDimensional K W] in
/-- The actual skew-module image is all skew operators precisely when
the defining Lie image is the full skew-adjoint Lie algebra. -/
theorem skew_action_module_range_eq_top_iff
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    (skewActionModuleHom β hβ).range = ⊤ ↔
      (toEnd K L W).range = skewAdjointLieSubalgebra β := by
  constructor
  · intro htop
    apply le_antisymm
    · rintro A ⟨x, rfl⟩
      exact action_mem_skew_adjoint β hβ x
    · intro A hA
      have hm : (⟨A, hA⟩ : skewAdjointLieSubmodule β hβ) ∈
          (skewActionModuleHom β hβ).range := by rw [htop]; trivial
      obtain ⟨x, hx⟩ := hm
      exact ⟨x, congrArg Subtype.val hx⟩
  · intro hfull
    apply top_unique
    intro A _
    have hm : (A : Module.End K W) ∈ (toEnd K L W).range := by
      rw [hfull]
      exact A.property
    obtain ⟨x, hx⟩ := hm
    exact ⟨x, Subtype.ext hx⟩

/-- The actual trace complement vanishes exactly for a full skew action. -/
theorem skew_action_complement_eq_bot_iff
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (hnd : β.Nondegenerate) (hr : LinearMap.IsRefl β)
    (htrace : (traceForm K L W).Nondegenerate) :
    skewActionComplement β hβ = ⊥ ↔
      (toEnd K L W).range = skewAdjointLieSubalgebra β := by
  rw [← skew_action_module_range_eq_top_iff β hβ]
  constructor
  · intro hzero
    have h := (skew_action_complement_isCompl β hβ htrace).sup_eq_top
    rwa [hzero, sup_bot_eq] at h
  · intro hfull
    apply LieSubmodule.toSubmodule_injective
    change (skewAdjointModuleTraceForm β hβ).orthogonal
      (skewActionModuleHom β hβ).range.toSubmodule = ⊥
    rw [hfull, LieSubmodule.top_toSubmodule]
    have hs : LinearMap.IsSymm (skewAdjointModuleTraceForm β hβ) :=
      ⟨fun A B => LinearMap.trace_mul_comm K (A : Module.End K W) B⟩
    exact (skewAdjointModuleTraceForm β hβ).orthogonal_top_eq_bot
      (skew_adjoint_module_trace_form_nondegenerate β hβ hnd hr) hs.isRefl

end LieModule

end

end CubicAnomaly.Classification.SkewTraceComplement
