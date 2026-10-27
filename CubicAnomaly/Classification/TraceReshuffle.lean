import CubicAnomaly.Classification.AdjointTraceForms
import CubicAnomaly.Classification.SkewTraceComplement
import CubicAnomaly.Classification.TensorEndomorphismDescent

/-!
# Canonical trace reshuffling of actual endomorphisms

The trace pairing identifies an operator on `End(W)` with a tensor of
two actual endomorphisms of `W`. The same tensor acts on `W ⊗ W`.
This gives an actual equivariant equivalence, without coordinates or a
representation-classification witness. Trace adjoint becomes conjugation
by tensor interchange, so trace-skew operators become flip-odd operators.
-/

namespace CubicAnomaly.Classification.TraceReshuffle

open Module LieModule
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.SkewTraceComplement
open CubicAnomaly.Classification.IdealTensorDuality
open CubicAnomaly.Classification.TensorEndomorphisms
open CubicAnomaly.Classification.TensorEndomorphismDescent
open scoped TensorProduct

noncomputable section

section DualTensor

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

/-- The actual dual-tensor identification with endomorphisms respects
the contragredient and standard endomorphism actions. -/
def dualTensorEndLieEquiv : (Module.Dual K M ⊗[K] M) ≃ₗ⁅K,L⁆ Module.End K M := {
  dualTensorHomEquiv K M M with
  map_lie' := by
    intro x t
    change dualTensorHom K M M ⁅x, t⁆ = ⁅x, dualTensorHom K M M t⁆
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [lie_zero (M := Module.Dual K M ⊗[K] M) x, map_zero, lie_zero x]
    | tmul φ m =>
      apply LinearMap.ext
      intro n
      simp only [TensorProduct.LieModule.lie_tmul_right, map_add, LinearMap.add_apply,
        dualTensorHom_apply, Module.Dual.lie_apply, LieHom.lie_apply, lie_smul,
        neg_smul]
      abel
    | add t u ht hu => rw [lie_add x t u, map_add, ht, hu, map_add, lie_add] }

/-- The dual-tensor equivalence is the literal rank-one operator. -/
@[simp] theorem dual_tensor_end_lie_equiv_tmul
    (φ : Module.Dual K M) (m n : M) :
    dualTensorEndLieEquiv (K := K) (L := L) (M := M) (φ ⊗ₜ[K] m) n = φ n • m := rfl

end DualTensor

variable {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  [FiniteDimensional K W]

/-- The actual invariant trace pairing identifies `End(W)` with its
contragredient dual equivariantly. -/
def traceDualEquiv : Module.End K W ≃ₗ⁅K,L⁆ Module.Dual K (Module.End K W) := {
  (endTraceForm (K := K) (W := W)).toDual end_trace_form_nondegenerate with
  map_lie' := by
    intro x A
    apply LinearMap.ext
    intro B
    exact end_trace_form_invariant (L := L) x A B }

/-- The trace duality retains the literal trace pairing. -/
@[simp] theorem trace_dual_equiv_apply (A B : Module.End K W) :
    traceDualEquiv (K := K) (L := L) (W := W) A B = LinearMap.trace K W (A * B) := rfl

/-- A tensor of actual operators acts on the actual endomorphism space
by the corresponding rank-one trace operator. -/
def traceTensorEquiv :
    (Module.End K W ⊗[K] Module.End K W) ≃ₗ⁅K,L⁆ Module.End K (Module.End K W) :=
  (tensorCommLieEquiv (K := K) (L := L) (M := Module.End K W) (N := Module.End K W)).trans
    ((tensorLieEquiv (traceDualEquiv (K := K) (L := L) (W := W))
      (LieModuleEquiv.refl (R := K) (L := L) (M := Module.End K W))).trans
      (dualTensorEndLieEquiv (K := K) (L := L) (M := Module.End K W)))

/-- On pure tensors the trace identification is literal rank-one
evaluation against the second operator. -/
@[simp] theorem trace_tensor_equiv_tmul (A B X : Module.End K W) :
    traceTensorEquiv (K := K) (L := L) (W := W) (A ⊗ₜ[K] B) X = LinearMap.trace K W (B * X) • A := rfl

/-- The canonical actual trace reshuffle from operators on `End(W)` to
operators on `W ⊗ W`, equivariant for the original action. -/
def traceReshuffle : Module.End K (Module.End K W) ≃ₗ⁅K,L⁆ Module.End K (W ⊗[K] W) :=
  (traceTensorEquiv (K := K) (L := L) (W := W)).symm.trans
    (tensorEndomorphismEquiv (K := K) (L := L) (M := W) (N := W))

/-- The actual reshuffle sends a rank-one trace operator to the literal
tensor product of the two defining operators. -/
theorem trace_reshuffle_trace_tensor (t : Module.End K W ⊗[K] Module.End K W) :
    traceReshuffle (K := K) (L := L) (W := W) (traceTensorEquiv (K := K) (L := L) (W := W) t) =
      tensorEndomorphismEquiv (K := K) (L := L) (M := W) (N := W) t := by
  change tensorEndomorphismEquiv (K := K) (L := L) (M := W) (N := W)
    ((traceTensorEquiv (K := K) (L := L) (W := W)).symm
      (traceTensorEquiv (K := K) (L := L) (W := W) t)) = _
  rw [LieModuleEquiv.symm_apply_apply]

/-- Restricting the actual reshuffle to invariant endomorphisms gives a
linear equivalence between the two actual equivariant endomorphism spaces. -/
def equivariantTraceReshuffle :
    (Module.End K W →ₗ⁅K,L⁆ Module.End K W) ≃ₗ[K]
      ((W ⊗[K] W) →ₗ⁅K,L⁆ (W ⊗[K] W)) :=
  (maxTrivLinearMapEquivLieModuleHom
    (R := K) (L := L) (M := Module.End K W) (N := Module.End K W)).symm.trans
      ((maxTrivEquiv (traceReshuffle (K := K) (L := L) (W := W))).toLinearEquiv.trans
        (maxTrivLinearMapEquivLieModuleHom
          (R := K) (L := L) (M := W ⊗[K] W) (N := W ⊗[K] W)))

/-- Restriction to equivariant operators does not alter the underlying
canonical trace reshuffle. -/
theorem equivariant_trace_reshuffle_toLinearMap
    (D : Module.End K W →ₗ⁅K,L⁆ Module.End K W) :
    (equivariantTraceReshuffle (K := K) (L := L) (W := W) D).toLinearMap =
      traceReshuffle (K := K) (L := L) (W := W) D.toLinearMap := rfl

/-- The literal flip operator on the actual tensor square. -/
def tensorFlip : Module.End K (W ⊗[K] W) := (TensorProduct.comm K W W).toLinearMap

omit [FiniteDimensional K W] in
/-- The actual flip interchanges pure tensors. -/
@[simp] theorem tensor_flip_tmul (u v : W) :
    tensorFlip (K := K) (u ⊗ₜ[K] v) = v ⊗ₜ[K] u := rfl

omit [FiniteDimensional K W] in
/-- The literal flip is an involution. -/
theorem tensor_flip_mul_self :
    tensorFlip (K := K) (W := W) * tensorFlip = 1 := by
  apply TensorProduct.ext'
  intro u v
  rfl

/-- Conjugating a literal tensor operator by the flip interchanges its
two actual endomorphism factors. -/
theorem tensor_flip_conjugation (t : Module.End K W ⊗[K] Module.End K W) :
    tensorFlip (K := K) *
      tensorEndomorphismEquiv (K := K) (L := L) (M := W) (N := W) t * tensorFlip =
    tensorEndomorphismEquiv (K := K) (L := L) (M := W) (N := W)
      (tensorCommLieEquiv (K := K) (L := L) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul A B =>
    rw [tensor_comm_lie_equiv_tmul, tensor_endomorphism_equiv_tmul,
      tensor_endomorphism_equiv_tmul]
    apply TensorProduct.ext'
    intro u v
    rfl
  | add t u ht hu => simp only [map_add, mul_add, add_mul, ht, hu]

/-- The actual trace adjoint interchanges the two factors of the
rank-one trace representation. -/
theorem trace_tensor_equiv_adjoint
    (t : Module.End K W ⊗[K] Module.End K W) :
    formAdjoint (endTraceForm (K := K) (W := W)) end_trace_form_nondegenerate
      (traceTensorEquiv (K := K) (L := L) (W := W) t) =
    traceTensorEquiv (K := K) (L := L) (W := W) (tensorCommLieEquiv (K := K) (L := L) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul A B =>
    rw [tensor_comm_lie_equiv_tmul]
    symm
    apply ((endTraceForm (K := K) (W := W)).isAdjointPair_iff_eq_of_nondegenerate
      end_trace_form_nondegenerate _ _).mp
    intro X Y
    change LinearMap.trace K W
        (traceTensorEquiv (K := K) (L := L) (W := W) (B ⊗ₜ[K] A) X * Y) =
      LinearMap.trace K W (X * traceTensorEquiv (K := K) (L := L) (W := W) (A ⊗ₜ[K] B) Y)
    simp only [trace_tensor_equiv_tmul, smul_mul_assoc, mul_smul_comm, map_smul,
      smul_eq_mul]
    rw [LinearMap.trace_mul_comm K A X, mul_comm]
  | add t u ht hu => simp only [map_add, ht, hu]

/-- The canonical reshuffle carries the actual trace adjoint to
conjugation by the actual tensor flip. -/
theorem trace_reshuffle_adjoint (D : Module.End K (Module.End K W)) :
    traceReshuffle (K := K) (L := L) (W := W)
      (formAdjoint (endTraceForm (K := K) (W := W)) end_trace_form_nondegenerate D) =
      tensorFlip (K := K) * traceReshuffle (K := K) (L := L) (W := W) D * tensorFlip := by
  obtain ⟨t, rfl⟩ := (traceTensorEquiv (K := K) (L := L) (W := W)).surjective D
  rw [trace_tensor_equiv_adjoint, trace_reshuffle_trace_tensor,
    trace_reshuffle_trace_tensor, tensor_flip_conjugation]

omit [FiniteDimensional K W] in
/-- Negative flip-conjugation is equivalent to literal anticommutation
with the flip, because the flip squares to the identity. -/
theorem tensor_flip_conjugation_eq_neg_iff (T : Module.End K (W ⊗[K] W)) :
    tensorFlip (K := K) * T * tensorFlip = -T ↔
      tensorFlip (K := K) * T = -(T * tensorFlip) := by
  constructor
  · intro h
    have he := congrArg (fun A : Module.End K (W ⊗[K] W) => A * tensorFlip) h
    simpa only [mul_assoc, tensor_flip_mul_self, mul_one, neg_mul] using he
  · intro h
    calc
      tensorFlip * T * tensorFlip = -(T * tensorFlip) * tensorFlip :=
        congrArg (fun A : Module.End K (W ⊗[K] W) => A * tensorFlip) h
      _ = -((T * tensorFlip) * tensorFlip) := by
        apply LinearMap.ext
        intro z
        rfl
      _ = -(T * (tensorFlip * tensorFlip)) := congrArg Neg.neg (mul_assoc _ _ _)
      _ = -T := by rw [tensor_flip_mul_self, mul_one]

/-- Trace-skew operators on the actual endomorphism space correspond
exactly to operators on the actual tensor square that anticommute with
tensor interchange. The equivalence is the constructed trace reshuffle. -/
theorem trace_skew_iff_flip_odd (D : Module.End K (Module.End K W)) :
    (∀ A B : Module.End K W,
      LinearMap.trace K W (D A * B) = -LinearMap.trace K W (A * D B)) ↔
    tensorFlip (K := K) * traceReshuffle (K := K) (L := L) (W := W) D =
      -(traceReshuffle (K := K) (L := L) (W := W) D * tensorFlip) := by
  have hsk : (∀ A B : Module.End K W,
      LinearMap.trace K W (D A * B) = -LinearMap.trace K W (A * D B)) ↔
      formAdjoint (endTraceForm (K := K) (W := W)) end_trace_form_nondegenerate D = -D := by
    rw [← mem_skew_adjoint_iff_form_adjoint, LinearMap.mem_skewAdjointSubmodule]
    constructor <;> intro h A B
    · change LinearMap.trace K W (D A * B) = LinearMap.trace K W (A * (-D) B)
      simpa only [LinearMap.neg_apply, mul_neg, map_neg] using h A B
    · have he := h A B
      change LinearMap.trace K W (D A * B) = LinearMap.trace K W (A * (-D) B) at he
      simpa only [LinearMap.neg_apply, mul_neg, map_neg] using he
  rw [hsk, ← tensor_flip_conjugation_eq_neg_iff]
  constructor
  · intro h
    have he := congrArg (traceReshuffle (K := K) (L := L) (W := W)) h
    simpa only [trace_reshuffle_adjoint, map_neg] using he
  · intro h
    apply (traceReshuffle (K := K) (L := L) (W := W)).injective
    simpa only [trace_reshuffle_adjoint, map_neg] using h

/-- The same exact trace-skew/flip-odd correspondence on the actual
equivariant endomorphism spaces. -/
theorem equivariant_trace_skew_iff_flip_odd
    (D : Module.End K W →ₗ⁅K,L⁆ Module.End K W) :
    (∀ A B : Module.End K W,
      LinearMap.trace K W (D A * B) = -LinearMap.trace K W (A * D B)) ↔
    tensorFlip (K := K) * (equivariantTraceReshuffle (K := K) (L := L) (W := W) D).toLinearMap =
      -((equivariantTraceReshuffle (K := K) (L := L) (W := W) D).toLinearMap * tensorFlip) := by
  rw [equivariant_trace_reshuffle_toLinearMap]
  exact trace_skew_iff_flip_odd D.toLinearMap

/-- A nonzero line of actual equivariant trace-skew operators transports
to a nonzero line of actual equivariant flip-odd operators. Every map is
transported through the constructed linear equivalence. -/
theorem exists_flip_odd_line_of_trace_skew_line
    (D₀ : Module.End K W →ₗ⁅K,L⁆ Module.End K W) (hD₀ : D₀ ≠ 0)
    (hsk : ∀ A B : Module.End K W,
      LinearMap.trace K W (D₀ A * B) = -LinearMap.trace K W (A * D₀ B))
    (hline : ∀ D : Module.End K W →ₗ⁅K,L⁆ Module.End K W,
      (∀ A B : Module.End K W,
        LinearMap.trace K W (D A * B) = -LinearMap.trace K W (A * D B)) →
      ∃ c : K, D = c • D₀) :
    ∃ T : (W ⊗[K] W) →ₗ⁅K,L⁆ (W ⊗[K] W), T ≠ 0 ∧
      tensorFlip (K := K) * T.toLinearMap = -(T.toLinearMap * tensorFlip) ∧
      ∀ S : (W ⊗[K] W) →ₗ⁅K,L⁆ (W ⊗[K] W),
        tensorFlip (K := K) * S.toLinearMap = -(S.toLinearMap * tensorFlip) →
        ∃ c : K, S = c • T := by
  let E := equivariantTraceReshuffle (K := K) (L := L) (W := W)
  refine ⟨E D₀, ?_, (equivariant_trace_skew_iff_flip_odd D₀).mp hsk, ?_⟩
  · intro hzero
    apply hD₀
    apply E.injective
    simpa only [map_zero] using hzero
  · intro S hS
    have hs := (equivariant_trace_skew_iff_flip_odd (E.symm S)).mpr
      (by simpa only [show equivariantTraceReshuffle (K := K) (L := L) (W := W) = E from rfl,
        E.apply_symm_apply] using hS)
    obtain ⟨c, hc⟩ := hline (E.symm S) hs
    refine ⟨c, ?_⟩
    have he := congrArg E hc
    simpa only [E.apply_symm_apply, map_smul] using he

end

end CubicAnomaly.Classification.TraceReshuffle
