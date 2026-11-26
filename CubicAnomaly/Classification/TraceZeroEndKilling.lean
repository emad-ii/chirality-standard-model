import CubicAnomaly.Classification.AdjointTraceForms
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.LinearAlgebra.Contraction

/-!
# The Killing form of actual trace-zero endomorphisms

The Killing form is computed directly through the canonical tensor
description of endomorphisms. Its nondegeneracy on the actual trace-zero
ideal needs neither a classification of simple Lie algebras nor matrix
coordinates.
-/

namespace CubicAnomaly.Classification.TraceZeroEndKilling

open Module LieModule
open CubicAnomaly.Classification.AdjointTraceForms
open scoped TensorProduct

noncomputable section

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/-- Left and right multiplication by actual defining endomorphisms. -/
def sandwich (A B : Module.End K W) : Module.End K (Module.End K W) where
  toFun T := A * T * B
  map_add' T U := by simp only [mul_add, add_mul]
  map_smul' c T := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

omit [FiniteDimensional K W] in
@[simp] theorem sandwich_apply (A B T : Module.End K W) : sandwich A B T = A * T * B := rfl

/-- The trace of a two-sided multiplication operator factors into the two
ordinary traces. -/
theorem trace_sandwich (A B : Module.End K W) :
    LinearMap.trace K (Module.End K W) (sandwich A B) =
      LinearMap.trace K W A * LinearMap.trace K W B := by
  let E := dualTensorHomEquiv K W W
  have he : sandwich A B = E.conj (TensorProduct.map (Module.Dual.transpose B) A) := by
    apply LinearMap.ext
    intro T
    obtain ⟨t, rfl⟩ := E.surjective T
    change sandwich A B (E t) = E (TensorProduct.map (Module.Dual.transpose B) A (E.symm (E t)))
    rw [E.symm_apply_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul f w =>
      ext v
      simp only [sandwich_apply, Module.End.mul_apply, E, dualTensorHomEquiv,
        dualTensorHomEquivOfBasis_apply, dualTensorHom_apply, TensorProduct.map_tmul,
        Module.Dual.transpose_apply, LinearMap.coe_comp, Function.comp_apply, map_smul]
    | add t u ht hu => simp only [map_add, ht, hu]
  have ht : LinearMap.trace K (Module.End K W)
      (E.conj (TensorProduct.map (Module.Dual.transpose B) A)) =
      LinearMap.trace K (Module.Dual K W ⊗[K] W)
        (TensorProduct.map (Module.Dual.transpose B) A) :=
    @LinearMap.trace_conj' K inferInstance (Module.Dual K W ⊗[K] W)
      inferInstance inferInstance (Module.End K W) inferInstance inferInstance
      (TensorProduct.map (Module.Dual.transpose B) A) E
  rw [he, ht, LinearMap.trace_tensorProduct', LinearMap.trace_transpose']
  exact mul_comm _ _

/-- The actual endomorphism Lie algebra has its usual trace formula for
the Killing form, derived without a choice of basis. -/
theorem end_killing_form (A B : Module.End K W) :
    killingForm K (Module.End K W) A B =
      2 * (finrank K W : K) * LinearMap.trace K W (A * B) -
        2 * LinearMap.trace K W A * LinearMap.trace K W B := by
  have he : (LieAlgebra.ad K (Module.End K W) A).comp
      (LieAlgebra.ad K (Module.End K W) B) =
      sandwich (A * B) 1 - sandwich A B - sandwich B A + sandwich 1 (B * A) := by
    apply LinearMap.ext
    intro T
    change A * (B * T - T * B) - (B * T - T * B) * A =
      A * B * T * 1 - A * T * B - B * T * A + 1 * T * (B * A)
    noncomm_ring
  rw [killingForm_apply_apply, he, map_add, map_sub, map_sub,
    trace_sandwich, trace_sandwich, trace_sandwich, trace_sandwich,
    LinearMap.trace_one, LinearMap.trace_mul_comm K B A]
  ring

/-- The kernel of ordinary trace is an actual Lie ideal of all
endomorphisms. -/
def traceZeroEndIdeal : LieIdeal K (Module.End K W) where
  __ := LinearMap.ker (LinearMap.trace K W)
  lie_mem := by
    intro A B _
    change LinearMap.trace K W (A * B - B * A) = 0
    rw [map_sub, LinearMap.trace_mul_comm K A B, sub_self]

omit [FiniteDimensional K W] in
@[simp] theorem mem_traceZeroEndIdeal (A : Module.End K W) :
    A ∈ traceZeroEndIdeal (K := K) (W := W) ↔ LinearMap.trace K W A = 0 := Iff.rfl

/-- On actual trace-zero endomorphisms, the Killing form is a nonzero
dimension multiple of the ordinary trace pairing. -/
theorem trace_zero_end_killing_form
    (A B : traceZeroEndIdeal (K := K) (W := W)) :
    killingForm K (traceZeroEndIdeal (K := K) (W := W)) A B =
      2 * (finrank K W : K) * LinearMap.trace K W ((A : Module.End K W) * B) := by
  rw [LieIdeal.killingForm_eq]
  change killingForm K (Module.End K W) A B = _
  rw [end_killing_form, (mem_traceZeroEndIdeal _).mp A.property]
  ring

variable [CharZero K]

/-- The ordinary trace pairing restricts nondegenerately to the actual
trace-zero endomorphisms. The zero-dimensional defining space is included. -/
theorem trace_zero_end_trace_form_nondegenerate :
    ((endTraceForm (K := K) (W := W)).restrict
      (traceZeroEndIdeal (K := K) (W := W)).toSubmodule).Nondegenerate := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · letI := hW
    exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  · letI := hW
    have hn : (finrank K W : K) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
    have hs : LinearMap.IsSymm ((endTraceForm (K := K) (W := W)).restrict
        (traceZeroEndIdeal (K := K) (W := W)).toSubmodule) :=
      ⟨fun A B => LinearMap.trace_mul_comm K (A : Module.End K W) B⟩
    apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
    intro A hA
    apply Subtype.ext
    apply (end_trace_form_nondegenerate (K := K) (W := W)).1 (A : Module.End K W)
    intro B
    let c := LinearMap.trace K W B / (finrank K W : K)
    have hc : B - c • 1 ∈ traceZeroEndIdeal (K := K) (W := W) := by
      change LinearMap.trace K W (B - c • 1) = 0
      simp only [map_sub, map_smul, LinearMap.trace_one, smul_eq_mul]
      dsimp [c]
      rw [div_mul_cancel₀ _ hn, sub_self]
    have h := hA ⟨B - c • 1, hc⟩
    change LinearMap.trace K W ((A : Module.End K W) * (B - c • 1)) = 0 at h
    change LinearMap.trace K W ((A : Module.End K W) * B) = 0
    have hAz := (mem_traceZeroEndIdeal _).mp A.property
    simpa only [mul_sub, mul_smul_comm, mul_one, map_sub, map_smul, hAz,
      smul_zero, sub_zero] using h

/-- The actual trace-zero endomorphism Lie algebra is Killing in
characteristic zero, including the trivial low-dimensional cases. -/
theorem trace_zero_end_isKilling :
    LieAlgebra.IsKilling K (traceZeroEndIdeal (K := K) (W := W)) := by
  constructor
  apply le_antisymm _ bot_le
  intro A hA
  change A = 0
  rcases subsingleton_or_nontrivial W with hW | hW
  · letI := hW
    exact Subsingleton.elim _ _
  · letI := hW
    have hn : (2 : K) * (finrank K W : K) ≠ 0 :=
      mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
    apply trace_zero_end_trace_form_nondegenerate.1 A
    intro B
    have h := (LieIdeal.mem_killingCompl K _ ⊤).mp hA B (by trivial)
    rw [trace_zero_end_killing_form] at h
    change LinearMap.trace K W ((A : Module.End K W) * B) = 0
    rw [LinearMap.trace_mul_comm K (A : Module.End K W) B]
    exact (mul_eq_zero.mp h).resolve_left hn

end

end CubicAnomaly.Classification.TraceZeroEndKilling
