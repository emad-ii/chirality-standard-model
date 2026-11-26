import CubicAnomaly.Classification.ScalarAdjointDensity

/-!
# Removing the scalar term from a trace-zero action

The scalar-plus-action density conclusion becomes the full trace-zero
action once the original action is known to be traceless. This uses the
literal trace on the actual endomorphisms and no classification labels.
-/

namespace CubicAnomaly.Classification.ScalarTraceZeroDensity

open Module LieModule
open CubicAnomaly.Classification.ScalarAdjointDensity
open CubicAnomaly.Classification.AdjointTraceForms

noncomputable section

variable {K L W : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  [FiniteDimensional K W]

/-- Scalars plus a trace-zero action can span all operators only when
the actual action already spans every trace-zero operator. -/
theorem exists_action_eq_of_scalar_sup_eq_top [Nontrivial W]
    (hfull : (K ∙ (1 : Module.End K W)) ⊔ (toEnd K L W).toLinearMap.range = ⊤)
    (htrace : ∀ x : L, LinearMap.trace K W (toEnd K L W x) = 0)
    (A : Module.End K W) (hA : LinearMap.trace K W A = 0) :
    ∃ x : L, toEnd K L W x = A := by
  have hmem : A ∈ (K ∙ (1 : Module.End K W)) ⊔ (toEnd K L W).toLinearMap.range := by
    rw [hfull]
    exact Submodule.mem_top
  obtain ⟨s, hs, B, hB, hAB⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  obtain ⟨x, rfl⟩ := hB
  change c • (1 : Module.End K W) + toEnd K L W x = A at hAB
  have ht := congrArg (LinearMap.trace K W) hAB
  simp only [map_add, map_smul, LinearMap.trace_one, htrace x, hA,
    add_zero, smul_eq_mul] at ht
  have hn : (finrank K W : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hc : c = 0 := (mul_eq_zero.mp ht).resolve_right hn
  refine ⟨x, ?_⟩
  simpa only [hc, zero_smul, zero_add] using hAB

/-- If an actual irreducible trace-zero action preserves a bilinear
form with zero trace-zero self-adjoint space, it is the full trace-zero
endomorphism action. Nondegeneracy of the form is not an extra premise. -/
theorem action_range_eq_trace_zero_of_trace_zero_self_adjoint_eq_bot
    [IsAlgClosed K] [LieModule.IsIrreducible K L W]
    (β : LinearMap.BilinForm K W) (hi : β.lieInvariant L)
    (hzero : traceZeroSelfAdjointSubmodule β = ⊥)
    (htrace : ∀ x : L, LinearMap.trace K W (toEnd K L W x) = 0) :
    (toEnd K L W).toLinearMap.range = LinearMap.ker (LinearMap.trace K W) := by
  letI : Nontrivial W := LieModule.nontrivial_of_isIrreducible K L W
  have hfull := scalar_sup_action_range_eq_top β hi
    (self_adjoint_eq_smul_one_of_trace_zero_eq_bot β hzero)
  apply le_antisymm
  · rintro A ⟨x, rfl⟩
    exact htrace x
  · intro A hA
    exact exists_action_eq_of_scalar_sup_eq_top hfull htrace A hA

/-- The same conclusion accepts the actual invariant trace-zero
self-adjoint Lie submodule from the tensor and quotient arguments. -/
theorem action_range_eq_trace_zero_of_trace_zero_lie_submodule_eq_bot
    [IsAlgClosed K] [LieModule.IsIrreducible K L W]
    (β : LinearMap.BilinForm K W) (hi : β.lieInvariant L)
    (hzero : traceZeroSelfAdjointLieSubmodule β hi = ⊥)
    (htrace : ∀ x : L, LinearMap.trace K W (toEnd K L W x) = 0) :
    (toEnd K L W).toLinearMap.range = LinearMap.ker (LinearMap.trace K W) := by
  apply action_range_eq_trace_zero_of_trace_zero_self_adjoint_eq_bot β hi
    (congrArg LieSubmodule.toSubmodule hzero) htrace

end

end CubicAnomaly.Classification.ScalarTraceZeroDensity
