import CubicAnomaly.Classification.SelfDualAbsorption
import Mathlib.Algebra.Lie.TraceForm
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Trace forms on actual self-adjoint operators

The adjoint associated to a nondegenerate reflexive bilinear form is an
involution. The ordinary operator trace pairing restricts nondegenerately
to its self-adjoint eigenspace, and to the trace-zero part of that space.
These are actual subspaces of `End(W)` for the supplied bilinear form.
-/

namespace CubicAnomaly.Classification.AdjointTraceForms

open Module LieModule
open CubicAnomaly.Classification.SelfDualAbsorption

noncomputable section

section Reflexivity

variable {K W : Type*} [Field K] [CharZero K] [AddCommGroup W] [Module K W]

/-- Over a characteristic-zero field, every reflexive bilinear form is
symmetric or alternating. No nondegeneracy assumption is required. -/
theorem reflexive_form_symmetric_or_alternating (β : LinearMap.BilinForm K W)
    (hβ : LinearMap.IsRefl β) : LinearMap.IsSymm β ∨ LinearMap.IsAlt β := by
  classical
  by_cases halt : ∀ x, β x x = 0
  · exact Or.inr halt
  push_neg at halt
  obtain ⟨a, ha⟩ := halt
  have hp (x : W) (hx : β x x ≠ 0) (y : W) : β x y = β y x := by
    have hz : β x (β x x • y - β x y • x) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    have hz' := hβ x _ hz
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul] at hz'
    have hm : β x x * (β y x - β x y) = 0 := by linear_combination hz'
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hx)).symm
  left
  refine ⟨fun x y => ?_⟩
  change β x y = β y x
  by_cases hx : β x x = 0
  · by_cases hax : β (a + x) (a + x) = 0
    · have hminus : β (a - x) (a - x) ≠ 0 := by
        intro hm
        simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply] at hax hm
        have htwo : (2 : K) * β a a = 0 := by linear_combination hax + hm - 2 * hx
        exact (mul_ne_zero (by norm_num) ha) htwo
      have h := hp (a - x) hminus y
      have h' := hp a ha y
      simp only [map_sub, LinearMap.sub_apply] at h
      linear_combination h' - h
    · have h := hp (a + x) hax y
      have h' := hp a ha y
      simp only [map_add, LinearMap.add_apply] at h
      linear_combination h - h'
  · exact hp x hx y

end Reflexivity

section Adjoint

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/-- Mathlib's actual left adjoint, bundled as a linear operator on the
endomorphism space. -/
def formAdjoint (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate) :
    Module.End K W →ₗ[K] Module.End K W where
  toFun := β.leftAdjointOfNondegenerate hβ
  map_add' A B := by
    symm
    apply (β.isAdjointPair_iff_eq_of_nondegenerate hβ _ _).mp
    exact (β.isAdjointPairLeftAdjointOfNondegenerate hβ A).add
      (β.isAdjointPairLeftAdjointOfNondegenerate hβ B)
  map_smul' c A := by
    symm
    apply (β.isAdjointPair_iff_eq_of_nondegenerate hβ _ _).mp
    exact (β.isAdjointPairLeftAdjointOfNondegenerate hβ A).smul c

/-- The bundled adjoint satisfies the defining adjoint identity for the
original bilinear form. -/
theorem form_adjoint_pair (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate)
    (A : Module.End K W) : LinearMap.IsAdjointPair β β (formAdjoint β hβ A) A :=
  β.isAdjointPairLeftAdjointOfNondegenerate hβ A

/-- The actual adjoint reverses products. -/
theorem form_adjoint_mul (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate)
    (A B : Module.End K W) :
    formAdjoint β hβ (A * B) = formAdjoint β hβ B * formAdjoint β hβ A := by
  symm
  apply (β.isAdjointPair_iff_eq_of_nondegenerate hβ _ _).mp
  exact (form_adjoint_pair β hβ B).mul (form_adjoint_pair β hβ A)

/-- The actual adjoint fixes the identity operator. -/
@[simp] theorem form_adjoint_one (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate) :
    formAdjoint β hβ 1 = 1 := by
  symm
  apply (β.isAdjointPair_iff_eq_of_nondegenerate hβ _ _).mp
  exact LinearMap.isAdjointPair_one

/-- The actual adjoint preserves the ordinary operator trace. -/
theorem trace_form_adjoint (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate)
    (A : Module.End K W) : LinearMap.trace K W (formAdjoint β hβ A) = LinearMap.trace K W A := by
  have he : formAdjoint β hβ A =
      (β.toDual hβ).symm.conj (Module.Dual.transpose A) := rfl
  rw [he, LinearMap.trace_conj', LinearMap.trace_transpose']

/-- Self-adjointness is the actual fixed-space condition for the adjoint. -/
theorem mem_selfAdjoint_iff_form_adjoint (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate)
    (A : Module.End K W) : A ∈ β.selfAdjointSubmodule ↔ formAdjoint β hβ A = A := by
  rw [LinearMap.mem_selfAdjointSubmodule]
  change LinearMap.IsAdjointPair β β A A ↔ _
  exact (β.isAdjointPair_iff_eq_of_nondegenerate hβ A A).trans eq_comm

variable [CharZero K]

omit [FiniteDimensional K W] in
/-- Reflexivity makes the adjoint pairing symmetric in its two operators. -/
theorem adjoint_pair_swap_of_reflexive (β : LinearMap.BilinForm K W)
    (hβ : LinearMap.IsRefl β) {A B : Module.End K W}
    (hAB : LinearMap.IsAdjointPair β β A B) : LinearMap.IsAdjointPair β β B A := by
  rcases reflexive_form_symmetric_or_alternating β hβ with hs | ha
  · have hs' (x y : W) : β x y = β y x := hs.eq x y
    intro x y
    rw [hs' (B x) y, ← hAB y x, hs' (A y) x]
  · intro x y
    rw [← ha.neg y (B x), ← hAB y x, ha.neg (A y) x]

/-- The actual adjoint of a nondegenerate reflexive form is involutive. -/
@[simp] theorem form_adjoint_involutive (β : LinearMap.BilinForm K W)
    (hβ : β.Nondegenerate) (hr : LinearMap.IsRefl β) (A : Module.End K W) :
    formAdjoint β hβ (formAdjoint β hβ A) = A := by
  symm
  apply (β.isAdjointPair_iff_eq_of_nondegenerate hβ _ _).mp
  exact adjoint_pair_swap_of_reflexive β hr (form_adjoint_pair β hβ A)

/-- The actual adjoint can be transferred between factors of the trace
pairing, so its eigenspaces are orthogonal. -/
theorem trace_form_adjoint_transfer (β : LinearMap.BilinForm K W)
    (hβ : β.Nondegenerate) (hr : LinearMap.IsRefl β) (A B : Module.End K W) :
    LinearMap.trace K W (formAdjoint β hβ A * B) =
      LinearMap.trace K W (A * formAdjoint β hβ B) := by
  rw [← trace_form_adjoint β hβ (formAdjoint β hβ A * B), form_adjoint_mul,
    form_adjoint_involutive β hβ hr, LinearMap.trace_mul_comm]

end Adjoint

section TracePairing

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- The ordinary trace pairing on the actual endomorphism space. -/
def endTraceForm : LinearMap.BilinForm K (Module.End K W) :=
  (LinearMap.mul K (Module.End K W)).compr₂ (LinearMap.trace K W)

@[simp] theorem end_trace_form_apply (A B : Module.End K W) :
    endTraceForm (K := K) (W := W) A B = LinearMap.trace K W (A * B) := rfl

/-- Cyclicity makes the actual trace pairing symmetric. -/
theorem end_trace_form_symmetric : LinearMap.IsSymm (endTraceForm (K := K) (W := W)) :=
  ⟨LinearMap.trace_mul_comm K⟩

variable [FiniteDimensional K W]

/-- Rank-one operators detect every endomorphism through the ordinary
trace pairing, proving its nondegeneracy directly. -/
theorem end_trace_form_nondegenerate : (endTraceForm (K := K) (W := W)).Nondegenerate := by
  apply (end_trace_form_symmetric (K := K) (W := W)).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro A hA
  ext x
  apply (Module.forall_dual_apply_eq_zero_iff K (A x)).mp
  intro f
  have h := hA (f.smulRight x)
  change LinearMap.trace K W (A * f.smulRight x) = 0 at h
  have he : A * f.smulRight x = f.smulRight (A x) := by
    ext y
    exact A.map_smul (f y) x
  rw [he, LinearMap.trace_smulRight] at h
  exact h

/-- The actual trace pairing restricted to the self-adjoint subspace. -/
def selfAdjointTraceForm (β : LinearMap.BilinForm K W) :
    LinearMap.BilinForm K β.selfAdjointSubmodule :=
  (endTraceForm (K := K) (W := W)).restrict β.selfAdjointSubmodule

variable [CharZero K]

/-- The trace form on the actual self-adjoint subspace is nondegenerate.
Symmetrizing an arbitrary test operator reduces this to nondegeneracy on
the full endomorphism space. -/
theorem self_adjoint_trace_form_nondegenerate (β : LinearMap.BilinForm K W)
    (hβ : β.Nondegenerate) (hr : LinearMap.IsRefl β) :
    (selfAdjointTraceForm β).Nondegenerate := by
  have hs : LinearMap.IsSymm (selfAdjointTraceForm β) :=
    ⟨fun A B => LinearMap.trace_mul_comm K (A : Module.End K W) B⟩
  apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro A hA
  apply Subtype.ext
  apply (end_trace_form_nondegenerate (K := K) (W := W)).1 (A : Module.End K W)
  intro B
  have hB : B + formAdjoint β hβ B ∈ β.selfAdjointSubmodule := by
    apply (mem_selfAdjoint_iff_form_adjoint β hβ _).mpr
    rw [map_add, form_adjoint_involutive β hβ hr, add_comm]
  have h := hA ⟨B + formAdjoint β hβ B, hB⟩
  change LinearMap.trace K W ((A : Module.End K W) * (B + formAdjoint β hβ B)) = 0 at h
  have hfix := (mem_selfAdjoint_iff_form_adjoint β hβ (A : Module.End K W)).mp A.property
  have htransfer := trace_form_adjoint_transfer β hβ hr (A : Module.End K W) B
  rw [hfix] at htransfer
  rw [mul_add, map_add, ← htransfer] at h
  have htwo : (2 : K) * LinearMap.trace K W ((A : Module.End K W) * B) = 0 := by
    simpa only [two_mul] using h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The literal trace-zero part of the actual self-adjoint subspace. -/
def traceZeroSelfAdjointSubmodule (β : LinearMap.BilinForm K W) : Submodule K (Module.End K W) :=
  β.selfAdjointSubmodule ⊓ LinearMap.ker (LinearMap.trace K W)

omit [FiniteDimensional K W] [CharZero K] in
@[simp] theorem mem_traceZeroSelfAdjointSubmodule (β : LinearMap.BilinForm K W)
    (A : Module.End K W) : A ∈ traceZeroSelfAdjointSubmodule β ↔
      A ∈ β.selfAdjointSubmodule ∧ LinearMap.trace K W A = 0 := Iff.rfl

/-- The ordinary trace pairing on the actual trace-zero self-adjoint
operator subspace. -/
def traceZeroSelfAdjointTraceForm (β : LinearMap.BilinForm K W) :
    LinearMap.BilinForm K (traceZeroSelfAdjointSubmodule β) :=
  (endTraceForm (K := K) (W := W)).restrict (traceZeroSelfAdjointSubmodule β)

/-- Removing the scalar identity from the self-adjoint space preserves
nondegeneracy of the trace pairing in characteristic zero. The zero
dimensional defining module is covered as well. -/
theorem trace_zero_self_adjoint_trace_form_nondegenerate (β : LinearMap.BilinForm K W)
    (hβ : β.Nondegenerate) (hr : LinearMap.IsRefl β) :
    (traceZeroSelfAdjointTraceForm β).Nondegenerate := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · letI := hW
    exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  · letI := hW
    have hn : (finrank K W : K) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
    have hs : LinearMap.IsSymm (traceZeroSelfAdjointTraceForm β) :=
      ⟨fun A B => LinearMap.trace_mul_comm K (A : Module.End K W) B⟩
    apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
    intro A hA
    apply Subtype.ext
    have hzero : (⟨(A : Module.End K W), A.property.1⟩ : β.selfAdjointSubmodule) = 0 := by
      apply (self_adjoint_trace_form_nondegenerate β hβ hr).1
      intro B
      let c := LinearMap.trace K W (B : Module.End K W) / (finrank K W : K)
      have hOne : (1 : Module.End K W) ∈ β.selfAdjointSubmodule :=
        (LinearMap.mem_selfAdjointSubmodule _).mpr LinearMap.isAdjointPair_one
      have hC : (B : Module.End K W) - c • 1 ∈ β.selfAdjointSubmodule :=
        β.selfAdjointSubmodule.sub_mem B.property (β.selfAdjointSubmodule.smul_mem c hOne)
      have hC0 : LinearMap.trace K W ((B : Module.End K W) - c • 1) = 0 := by
        simp only [map_sub, map_smul, LinearMap.trace_one, smul_eq_mul]
        dsimp [c]
        rw [div_mul_cancel₀ _ hn, sub_self]
      have htest := hA ⟨(B : Module.End K W) - c • 1, ⟨hC, hC0⟩⟩
      change LinearMap.trace K W ((A : Module.End K W) * ((B : Module.End K W) - c • 1)) = 0
        at htest
      have hAz : LinearMap.trace K W (A : Module.End K W) = 0 := A.property.2
      change LinearMap.trace K W ((A : Module.End K W) * (B : Module.End K W)) = 0
      simpa only [mul_sub, mul_smul_comm, mul_one, map_sub, map_smul, hAz, smul_zero, sub_zero]
        using htest
    exact congrArg (fun B : β.selfAdjointSubmodule => (B : Module.End K W)) hzero

end TracePairing

section Invariance

variable {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

/-- The ordinary trace pairing is invariant for the standard action on
endomorphisms induced by any Lie representation. -/
theorem end_trace_form_invariant : (endTraceForm (K := K) (W := W)).lieInvariant L := by
  intro x A B
  change LinearMap.trace K W ((toEnd K L W x * A - A * toEnd K L W x) * B) =
    -LinearMap.trace K W (A * (toEnd K L W x * B - B * toEnd K L W x))
  simp only [sub_mul, mul_sub, map_sub, mul_assoc]
  rw [LinearMap.trace_mul_comm K (toEnd K L W x) (A * B), mul_assoc]
  abel

/-- The actual self-adjoint operator subspace is stable under an action
that preserves the original bilinear form. -/
def selfAdjointLieSubmodule (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    LieSubmodule K L (Module.End K W) where
  __ := β.selfAdjointSubmodule
  lie_mem := by
    intro x A hA
    have ha := (LinearMap.mem_selfAdjointSubmodule A).mp hA
    apply (LinearMap.mem_selfAdjointSubmodule _).mpr
    intro u v
    change β (⁅x, A u⁆ - A ⁅x, u⁆) v = β u (⁅x, A v⁆ - A ⁅x, v⁆)
    simp only [map_sub, LinearMap.sub_apply]
    rw [hβ x (A u) v, ha u ⁅x, v⁆, ha ⁅x, u⁆ v, hβ x u (A v)]
    abel

/-- The actual trace-zero self-adjoint operator subspace, with its
inherited standard endomorphism Lie action. -/
def traceZeroSelfAdjointLieSubmodule (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    LieSubmodule K L (Module.End K W) where
  __ := traceZeroSelfAdjointSubmodule β
  lie_mem := by
    intro x A hA
    refine ⟨(selfAdjointLieSubmodule β hβ).lie_mem hA.1, ?_⟩
    change LinearMap.trace K W ⁅toEnd K L W x, A⁆ = 0
    exact LinearMap.trace_lie _ _

/-- The actual self-adjoint module's ordinary trace pairing. -/
def selfAdjointModuleTraceForm (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    LinearMap.BilinForm K (selfAdjointLieSubmodule β hβ) :=
  (endTraceForm (K := K) (W := W)).restrict (selfAdjointLieSubmodule β hβ).toSubmodule

/-- The actual trace-zero self-adjoint module's ordinary trace pairing. -/
def traceZeroSelfAdjointModuleTraceForm (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    LinearMap.BilinForm K (traceZeroSelfAdjointLieSubmodule β hβ) :=
  (endTraceForm (K := K) (W := W)).restrict (traceZeroSelfAdjointLieSubmodule β hβ).toSubmodule

/-- Invariance of the actual self-adjoint trace pairing. -/
theorem self_adjoint_module_trace_form_invariant
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    (selfAdjointModuleTraceForm β hβ).lieInvariant L := by
  intro x A B
  exact end_trace_form_invariant (L := L) x (A : Module.End K W) (B : Module.End K W)

/-- Invariance of the actual trace-zero self-adjoint trace pairing. -/
theorem trace_zero_self_adjoint_module_trace_form_invariant
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L) :
    (traceZeroSelfAdjointModuleTraceForm β hβ).lieInvariant L := by
  intro x A B
  exact end_trace_form_invariant (L := L) x (A : Module.End K W) (B : Module.End K W)

variable [CharZero K] [FiniteDimensional K W]

/-- The invariant ordinary trace pairing on the actual self-adjoint Lie
module is nondegenerate, derived from the original defining form. -/
theorem self_adjoint_module_trace_form_nondegenerate
    (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate)
    (hr : LinearMap.IsRefl β) (hi : β.lieInvariant L) :
    (selfAdjointModuleTraceForm β hi).Nondegenerate :=
  self_adjoint_trace_form_nondegenerate β hβ hr

/-- The invariant trace pairing on the actual trace-zero self-adjoint Lie
module is nondegenerate, with no extra form witness supplied. -/
theorem trace_zero_self_adjoint_module_trace_form_nondegenerate
    (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate)
    (hr : LinearMap.IsRefl β) (hi : β.lieInvariant L) :
    (traceZeroSelfAdjointModuleTraceForm β hi).Nondegenerate :=
  trace_zero_self_adjoint_trace_form_nondegenerate β hβ hr

/-- Actual equivariant self-duality of the self-adjoint endomorphism
module follows from its derived invariant trace pairing. -/
theorem self_adjoint_self_dual (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate)
    (hr : LinearMap.IsRefl β) (hi : β.lieInvariant L) :
    Nonempty ((selfAdjointLieSubmodule β hi) ≃ₗ⁅K,L⁆
      Module.Dual K (selfAdjointLieSubmodule β hi)) :=
  invariant_nondegenerate_form_self_dual (selfAdjointModuleTraceForm β hi)
    (self_adjoint_module_trace_form_invariant β hi)
    (self_adjoint_module_trace_form_nondegenerate β hβ hr hi)

/-- Actual equivariant self-duality of the trace-zero self-adjoint
endomorphism module follows from its derived invariant trace pairing. -/
theorem trace_zero_self_adjoint_self_dual (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate)
    (hr : LinearMap.IsRefl β) (hi : β.lieInvariant L) :
    Nonempty ((traceZeroSelfAdjointLieSubmodule β hi) ≃ₗ⁅K,L⁆
      Module.Dual K (traceZeroSelfAdjointLieSubmodule β hi)) :=
  invariant_nondegenerate_form_self_dual (traceZeroSelfAdjointModuleTraceForm β hi)
    (trace_zero_self_adjoint_module_trace_form_invariant β hi)
    (trace_zero_self_adjoint_module_trace_form_nondegenerate β hβ hr hi)

end Invariance

end

end CubicAnomaly.Classification.AdjointTraceForms
