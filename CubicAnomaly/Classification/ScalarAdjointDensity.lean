import CubicAnomaly.Classification.AdjointTraceForms
import CubicAnomaly.Classification.LieDensity
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Tactic.Module

/-!
# Scalar self-adjoint operators force the full skew action

If the trace-zero self-adjoint subspace vanishes, every self-adjoint
operator is scalar. The sum of the scalar operators and an irreducible
form-preserving Lie action is then closed under multiplication: the
commutator is in the action, and the anticommutator is self-adjoint.
Associative density identifies this sum with the full endomorphism
algebra. Its skew part is exactly the original Lie action.

This avoids classifying the small-dimensional alternating factor.
-/

namespace CubicAnomaly.Classification.ScalarAdjointDensity

open Module LieModule
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.LieDensity

noncomputable section

section Scalar

variable {K W : Type*} [Field K] [CharZero K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/-- If the actual trace-zero self-adjoint subspace vanishes, every
self-adjoint operator is a scalar identity. -/
theorem self_adjoint_eq_smul_one_of_trace_zero_eq_bot
    (β : LinearMap.BilinForm K W)
    (hzero : traceZeroSelfAdjointSubmodule β = ⊥)
    (A : Module.End K W) (hA : A ∈ β.selfAdjointSubmodule) :
    ∃ c : K, A = c • (1 : Module.End K W) := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · letI := hW
    exact ⟨0, Subsingleton.elim _ _⟩
  · letI := hW
    have hn : (finrank K W : K) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
    let c := LinearMap.trace K W A / (finrank K W : K)
    refine ⟨c, ?_⟩
    have hOne : (1 : Module.End K W) ∈ β.selfAdjointSubmodule :=
      (LinearMap.mem_selfAdjointSubmodule _).mpr LinearMap.isAdjointPair_one
    have hC : A - c • 1 ∈ traceZeroSelfAdjointSubmodule β := by
      refine ⟨β.selfAdjointSubmodule.sub_mem hA (β.selfAdjointSubmodule.smul_mem c hOne), ?_⟩
      change LinearMap.trace K W (A - c • 1) = 0
      simp only [map_sub, map_smul, LinearMap.trace_one, smul_eq_mul]
      dsimp [c]
      rw [div_mul_cancel₀ _ hn, sub_self]
    rw [hzero, Submodule.mem_bot] at hC
    exact sub_eq_zero.mp hC

omit [CharZero K] [FiniteDimensional K W] in
/-- The anticommutator of two actual skew-adjoint operators is
self-adjoint for the original bilinear form. -/
theorem skew_anticommutator_self_adjoint (β : LinearMap.BilinForm K W)
    (A B : Module.End K W) (hA : A ∈ β.skewAdjointSubmodule)
    (hB : B ∈ β.skewAdjointSubmodule) : A * B + B * A ∈ β.selfAdjointSubmodule := by
  apply (LinearMap.mem_selfAdjointSubmodule _).mpr
  have ha := (LinearMap.mem_skewAdjointSubmodule _).mp hA
  have hb := (LinearMap.mem_skewAdjointSubmodule _).mp hB
  have hab : LinearMap.IsAdjointPair β β (A * B) (B * A) := by
    rw [← neg_mul_neg B A]
    exact hb.comp ha
  have hba : LinearMap.IsAdjointPair β β (B * A) (A * B) := by
    rw [← neg_mul_neg A B]
    exact ha.comp hb
  intro u v
  simpa only [LinearMap.add_apply, Pi.add_apply, add_comm] using (hab.add hba) u v

end Scalar

section Density

variable {K L W : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  [FiniteDimensional K W] [IsAlgClosed K] [LieModule.IsIrreducible K L W]

omit [CharZero K] [FiniteDimensional K W] [IsAlgClosed K]
    [LieModule.IsIrreducible K L W] in
private theorem action_skew (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (x : L) : toEnd K L W x ∈ β.skewAdjointSubmodule := by
  apply (LinearMap.mem_skewAdjointSubmodule _).mpr
  intro u v
  change β ⁅x, u⁆ v = β u (-⁅x, v⁆)
  rw [map_neg]
  exact hβ x u v

/-- If every self-adjoint operator is scalar, scalars together with the
actual irreducible form-preserving action span all endomorphisms. -/
theorem scalar_sup_action_range_eq_top
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (hscalar : ∀ A : Module.End K W, A ∈ β.selfAdjointSubmodule →
      ∃ c : K, A = c • (1 : Module.End K W)) :
    (K ∙ (1 : Module.End K W)) ⊔ (toEnd K L W).toLinearMap.range = ⊤ := by
  let U := (K ∙ (1 : Module.End K W)) ⊔ (toEnd K L W).toLinearMap.range
  have hOne : (1 : Module.End K W) ∈ U :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hAction (x : L) : toEnd K L W x ∈ U := Submodule.mem_sup_right ⟨x, rfl⟩
  have hprod (x y : L) : toEnd K L W x * toEnd K L W y ∈ U := by
    let A := toEnd K L W x
    let B := toEnd K L W y
    obtain ⟨c, hc⟩ := hscalar (A * B + B * A)
      (skew_anticommutator_self_adjoint β A B (action_skew β hβ x) (action_skew β hβ y))
    have hs : A * B + B * A ∈ U := hc ▸ U.smul_mem c hOne
    have hb : A * B - B * A ∈ U := by
      simpa only [LieHom.map_lie, Ring.lie_def] using hAction ⁅x, y⁆
    have he : A * B = (2 : K)⁻¹ • ((A * B + B * A) + (A * B - B * A)) := by module
    rw [he]
    exact U.smul_mem _ (U.add_mem hs hb)
  have hmul : ∀ A B, A ∈ U → B ∈ U → A * B ∈ U := by
    intro A B hA hB
    rcases Submodule.mem_sup.mp hA with ⟨s, hs, x, hx, rfl⟩
    rcases Submodule.mem_sup.mp hB with ⟨t, ht, y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp ht
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    rw [add_mul, mul_add, mul_add]
    apply U.add_mem
    · apply U.add_mem
      · simpa only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul] using U.smul_mem (d * c) hOne
      · simpa only [smul_mul_assoc, one_mul] using U.smul_mem c (hAction y)
    · apply U.add_mem
      · simpa only [mul_smul_comm, mul_one] using U.smul_mem d (hAction x)
      · exact hprod x y
  have hfull := subalgebra_eq_top_of_lie_action_mem (L := L)
    (U.toSubalgebra hOne hmul) hAction
  exact congrArg Subalgebra.toSubmodule hfull

/-- Vanishing of the actual trace-zero self-adjoint space forces an
irreducible form-preserving action to be the full skew-adjoint algebra.
No low-dimensional Lie classification or maximality premise is used. -/
theorem action_range_eq_skew_adjoint_of_trace_zero_eq_bot
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (hnd : β.Nondegenerate)
    (hzero : traceZeroSelfAdjointSubmodule β = ⊥) :
    (toEnd K L W).range = skewAdjointLieSubalgebra β := by
  have hfull := scalar_sup_action_range_eq_top β hβ
    (self_adjoint_eq_smul_one_of_trace_zero_eq_bot β hzero)
  apply le_antisymm
  · rintro A ⟨x, rfl⟩
    exact action_skew β hβ x
  · intro A hA
    have hmem : A ∈ (K ∙ (1 : Module.End K W)) ⊔ (toEnd K L W).toLinearMap.range := by
      rw [hfull]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hmem with ⟨s, hs, B, hB, hAB⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
    obtain ⟨x, rfl⟩ := hB
    have hscalar : c • (1 : Module.End K W) ∈ β.skewAdjointSubmodule := by
      have hm := β.skewAdjointSubmodule.sub_mem hA (action_skew β hβ x)
      rw [← hAB] at hm
      change c • 1 + toEnd K L W x - toEnd K L W x ∈ β.skewAdjointSubmodule at hm
      rw [add_sub_cancel_right] at hm
      exact hm
    have hc : c = 0 := by
      have hp := (LinearMap.mem_skewAdjointSubmodule _).mp hscalar
      letI : Nontrivial W := LieModule.nontrivial_of_isIrreducible K L W
      obtain ⟨u, hu⟩ := exists_ne (0 : W)
      obtain ⟨v, hv⟩ : ∃ v, β u v ≠ 0 := by
        by_contra! h
        exact hu (hnd.1 u h)
      have h := hp u v
      change β (c • u) v = β u (-(c • v)) at h
      simp only [map_neg, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
      have hz : (2 : K) * c * β u v = 0 := by linear_combination h
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hv)).resolve_left (by norm_num)
    subst c
    refine ⟨x, ?_⟩
    simpa only [zero_smul, zero_add] using hAB

/-- The same collapse accepts the actual invariant trace-zero
self-adjoint Lie submodule used by the tensor parity blocks. -/
theorem action_range_eq_skew_adjoint_of_trace_zero_lie_submodule_eq_bot
    (β : LinearMap.BilinForm K W) (hβ : β.lieInvariant L)
    (hnd : β.Nondegenerate)
    (hzero : traceZeroSelfAdjointLieSubmodule β hβ = ⊥) :
    (toEnd K L W).range = skewAdjointLieSubalgebra β := by
  apply action_range_eq_skew_adjoint_of_trace_zero_eq_bot β hβ hnd
  exact congrArg LieSubmodule.toSubmodule hzero

end Density

end

end CubicAnomaly.Classification.ScalarAdjointDensity
