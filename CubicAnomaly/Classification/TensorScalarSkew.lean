import CubicAnomaly.Classification.ScalarAdjointDensity
import CubicAnomaly.Classification.SkewTraceComplement
import CubicAnomaly.Classification.TensorEndomorphisms

/-!
# Exhausting tensor skew operators when both self-adjoint parts are scalar

If scalars and the two separate ideal actions span the factor endomorphism
spaces, every skew operator on the tensor product belongs to the actual
diagonal action. The proof projects the literal endomorphism tensor
decomposition onto its skew part; its even-parity terms vanish.
-/

namespace CubicAnomaly.Classification.TensorScalarSkew

open Module LieModule
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.SkewTraceComplement
open CubicAnomaly.Classification.ScalarAdjointDensity
open CubicAnomaly.Classification.TensorEndomorphisms
open scoped TensorProduct

noncomputable section

variable {K L M N : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [FiniteDimensional K M] [FiniteDimensional K N]

/-- Separate scalar-plus-action spans exhaust every actual skew operator
on the tensor product. This only assumes the literal tensor form and
the literal separate actions; no dimension classification is used. -/
theorem tensor_skew_range_le_diagonal_of_scalar_action_spans
    (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L)
    (hnd : (β.tmul γ).Nondegenerate)
    (I J : LieIdeal K L)
    (hIN : ∀ x : I, ∀ n : N, ⁅(x : L), n⁆ = 0)
    (hJM : ∀ y : J, ∀ m : M, ⁅(y : L), m⁆ = 0)
    (hM : ∀ A : Module.End K M, ∃ (c : K) (x : I),
      A = c • (1 : Module.End K M) + toEnd K L M (x : L))
    (hN : ∀ B : Module.End K N, ∃ (c : K) (y : J),
      B = c • (1 : Module.End K N) + toEnd K L N (y : L)) :
    skewAdjointLieSubalgebra (β.tmul γ) ≤ (toEnd K L (M ⊗[K] N)).range := by
  let Ψ : LinearMap.BilinForm K (M ⊗[K] N) := β.tmul γ
  let p : Module.End K (Module.End K (M ⊗[K] N)) :=
    (2 : K)⁻¹ • (LinearMap.id - formAdjoint Ψ hnd)
  have hp0 (A : Module.End K (M ⊗[K] N)) (hA : A ∈ Ψ.selfAdjointSubmodule) : p A = 0 := by
    have ha := (mem_selfAdjoint_iff_form_adjoint Ψ hnd A).mp hA
    change (2 : K)⁻¹ • (A - formAdjoint Ψ hnd A) = 0
    rw [ha, sub_self, smul_zero]
  have hp1 (A : Module.End K (M ⊗[K] N)) (hA : A ∈ Ψ.skewAdjointSubmodule) : p A = A := by
    have ha := (mem_skew_adjoint_iff_form_adjoint Ψ hnd A).mp hA
    change (2 : K)⁻¹ • (A - formAdjoint Ψ hnd A) = A
    rw [ha]
    module
  have hleft (x : I) :
      TensorProduct.map (toEnd K L M (x : L)) (1 : Module.End K N) =
        toEnd K L (M ⊗[K] N) (x : L) := by
    apply TensorProduct.ext'
    intro m n
    change ⁅(x : L), m⁆ ⊗ₜ[K] n =
      ⁅(x : L), m⁆ ⊗ₜ[K] n + m ⊗ₜ[K] ⁅(x : L), n⁆
    rw [hIN, TensorProduct.tmul_zero, add_zero]
  have hright (y : J) :
      TensorProduct.map (1 : Module.End K M) (toEnd K L N (y : L)) =
        toEnd K L (M ⊗[K] N) (y : L) := by
    apply TensorProduct.ext'
    intro m n
    change m ⊗ₜ[K] ⁅(y : L), n⁆ =
      ⁅(y : L), m⁆ ⊗ₜ[K] n + m ⊗ₜ[K] ⁅(y : L), n⁆
    rw [hJM, TensorProduct.zero_tmul, zero_add]
  have hsingleLeft (x : I) :
      TensorProduct.map (toEnd K L M (x : L)) (1 : Module.End K N) ∈ Ψ.skewAdjointSubmodule := by
    apply (LinearMap.mem_skewAdjointSubmodule _).mpr
    intro u v
    change Ψ (TensorProduct.map _ _ u) v = Ψ u (-TensorProduct.map _ _ v)
    rw [map_neg]
    exact tensor_skew_self_adjoint_operator β γ _ _ (hβ (x : L)) (fun _ _ => rfl) u v
  have hsingleRight (y : J) :
      TensorProduct.map (1 : Module.End K M) (toEnd K L N (y : L)) ∈ Ψ.skewAdjointSubmodule := by
    apply (LinearMap.mem_skewAdjointSubmodule _).mpr
    intro u v
    change Ψ (TensorProduct.map _ _ u) v = Ψ u (-TensorProduct.map _ _ v)
    rw [map_neg]
    exact tensor_self_adjoint_skew_operator β γ _ _ (fun _ _ => rfl) (hγ (y : L)) u v
  have hdouble (x : I) (y : J) :
      TensorProduct.map (toEnd K L M (x : L)) (toEnd K L N (y : L)) ∈ Ψ.selfAdjointSubmodule := by
    apply (LinearMap.mem_selfAdjointSubmodule _).mpr
    intro u v
    simpa only [neg_mul_neg, one_mul, mul_one] using
      tensor_operator_adjointness_signs β γ _ _ (-1) (-1)
        (by simpa only [neg_one_mul] using hβ (x : L))
        (by simpa only [neg_one_mul] using hγ (y : L)) u v
  let U := (toEnd K L (M ⊗[K] N)).toLinearMap.range
  have hpure (A : Module.End K M) (B : Module.End K N) :
      p (TensorProduct.map A B) ∈ U := by
    obtain ⟨c, x, rfl⟩ := hM A
    obtain ⟨d, y, rfl⟩ := hN B
    rw [TensorProduct.map_add_left, TensorProduct.map_add_right,
      TensorProduct.map_add_right, TensorProduct.map_smul_left,
      TensorProduct.map_smul_right, TensorProduct.map_smul_left,
      TensorProduct.map_smul_right]
    rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      hp0 _ (by simpa only [TensorProduct.map_one] using
        (show (1 : Module.End K (M ⊗[K] N)) ∈ Ψ.selfAdjointSubmodule from
          (LinearMap.mem_selfAdjointSubmodule _).mpr LinearMap.isAdjointPair_one)),
      hp1 _ (hsingleRight y), hp1 _ (hsingleLeft x), hp0 _ (hdouble x y),
      smul_zero, smul_zero, zero_add, add_zero, hleft, hright]
    exact U.add_mem (U.smul_mem c ⟨(y : L), rfl⟩) (U.smul_mem d ⟨(x : L), rfl⟩)
  have hall (A : Module.End K (M ⊗[K] N)) : p A ∈ U := by
    obtain ⟨t, rfl⟩ := (homTensorHomEquiv K M N M N).surjective A
    induction t using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using U.zero_mem
    | tmul A B => simpa only [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply] using hpure A B
    | add t u ht hu => simpa only [map_add] using U.add_mem ht hu
  intro A hA
  have ha := hall A
  rwa [hp1 A hA] at ha

/-- When both actual trace-zero self-adjoint parts vanish, associative
density supplies the scalar-plus-action spans and every tensor-form
preserver belongs to the original diagonal action. -/
theorem tensor_skew_range_le_diagonal_of_trace_zero_parts_eq_bot
    [IsAlgClosed K]
    (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L)
    (hnd : (β.tmul γ).Nondegenerate)
    (I J : LieIdeal K L)
    [LieModule.IsIrreducible K I M] [LieModule.IsIrreducible K J N]
    (hIN : ∀ x : I, ∀ n : N, ⁅(x : L), n⁆ = 0)
    (hJM : ∀ y : J, ∀ m : M, ⁅(y : L), m⁆ = 0)
    (hM : traceZeroSelfAdjointSubmodule β = ⊥)
    (hN : traceZeroSelfAdjointSubmodule γ = ⊥) :
    skewAdjointLieSubalgebra (β.tmul γ) ≤ (toEnd K L (M ⊗[K] N)).range := by
  apply tensor_skew_range_le_diagonal_of_scalar_action_spans β hβ γ hγ hnd I J hIN hJM
  · have hf := scalar_sup_action_range_eq_top (L := I) β (fun x => hβ (x : L))
      (self_adjoint_eq_smul_one_of_trace_zero_eq_bot β hM)
    intro A
    have ha : A ∈ (K ∙ (1 : Module.End K M)) ⊔ (toEnd K I M).toLinearMap.range := by
      rw [hf]
      trivial
    obtain ⟨s, hs, T, hT, he⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
    obtain ⟨x, rfl⟩ := hT
    exact ⟨c, x, he.symm⟩

  · have hf := scalar_sup_action_range_eq_top (L := J) γ (fun x => hγ (x : L))
      (self_adjoint_eq_smul_one_of_trace_zero_eq_bot γ hN)
    intro A
    have ha : A ∈ (K ∙ (1 : Module.End K N)) ⊔ (toEnd K J N).toLinearMap.range := by
      rw [hf]
      trivial
    obtain ⟨s, hs, T, hT, he⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
    obtain ⟨x, rfl⟩ := hT
    exact ⟨c, x, he.symm⟩

/-- The same tensor exhaustion uses irreducibility of the supplied
ambient factor actions. Spanning ideals and trivial cross actions select
the needed separate ideal operators without changing action instances. -/
theorem tensor_skew_range_le_diagonal_of_irreducible_factors
    [IsAlgClosed K] [LieModule.IsIrreducible K L M] [LieModule.IsIrreducible K L N]
    (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L)
    (hnd : (β.tmul γ).Nondegenerate)
    (I J : LieIdeal K L) (htop : I ⊔ J = ⊤)
    (hIN : ∀ x : I, ∀ n : N, ⁅(x : L), n⁆ = 0)
    (hJM : ∀ y : J, ∀ m : M, ⁅(y : L), m⁆ = 0)
    (hM : traceZeroSelfAdjointSubmodule β = ⊥)
    (hN : traceZeroSelfAdjointSubmodule γ = ⊥) :
    skewAdjointLieSubalgebra (β.tmul γ) ≤ (toEnd K L (M ⊗[K] N)).range := by
  apply tensor_skew_range_le_diagonal_of_scalar_action_spans β hβ γ hγ hnd I J hIN hJM
  · have hf := scalar_sup_action_range_eq_top β hβ
      (self_adjoint_eq_smul_one_of_trace_zero_eq_bot β hM)
    intro A
    have ha : A ∈ (K ∙ (1 : Module.End K M)) ⊔ (toEnd K L M).toLinearMap.range := by
      rw [hf]
      trivial
    obtain ⟨s, hs, T, hT, he⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
    obtain ⟨z, rfl⟩ := hT
    have hz : z ∈ I ⊔ J := by rw [htop]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := (LieSubmodule.mem_sup I J z).mp hz
    have hy0 : toEnd K L M y = 0 := by
      apply LinearMap.ext
      intro m
      exact hJM ⟨y, hy⟩ m
    refine ⟨c, ⟨x, hx⟩, ?_⟩
    change c • (1 : Module.End K M) + toEnd K L M (x + y) = A at he
    rw [map_add, hy0, add_zero] at he
    exact he.symm
  · have hf := scalar_sup_action_range_eq_top γ hγ
      (self_adjoint_eq_smul_one_of_trace_zero_eq_bot γ hN)
    intro A
    have ha : A ∈ (K ∙ (1 : Module.End K N)) ⊔ (toEnd K L N).toLinearMap.range := by
      rw [hf]
      trivial
    obtain ⟨s, hs, T, hT, he⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
    obtain ⟨z, rfl⟩ := hT
    have hz : z ∈ I ⊔ J := by rw [htop]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := (LieSubmodule.mem_sup I J z).mp hz
    have hx0 : toEnd K L N x = 0 := by
      apply LinearMap.ext
      intro n
      exact hIN ⟨x, hx⟩ n
    refine ⟨c, ⟨y, hy⟩, ?_⟩
    change c • (1 : Module.End K N) + toEnd K L N (x + y) = A at he
    rw [map_add, hx0, zero_add] at he
    exact he.symm

end

end CubicAnomaly.Classification.TensorScalarSkew
