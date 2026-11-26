import CubicAnomaly.Classification.CompactTensorSaturation
import CubicAnomaly.Classification.CompactQuotientSkew
import CubicAnomaly.Classification.TensorEndomorphismDescent
import CubicAnomaly.Classification.TensorInvariantForms
import CubicAnomaly.Classification.TensorScalarSkew
import CubicAnomaly.Classification.TraceZeroSymmetricPair
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Excluding two actual tensor factors in a complex-type compact quotient

A nonzero parity block fills the quotient and forces the other factor's
action to be the full skew algebra. The quotient's nonzero equivariant
sign operator descends through the irreducible ideal tensor factor to a
trace-skew equivariant operator on the actual traceless self-adjoint
space. The trace-zero symmetric-pair derivation argument forces that
operator to vanish, a contradiction. This avoids highest-weight
classification, low-dimensional identifications, and maximality.
-/

namespace CubicAnomaly.Classification.CompactTensorExclusion

open Module LieModule
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactOperatorModel
open CubicAnomaly.Classification.EquivariantOperatorTransport
open CubicAnomaly.Classification.CompactTensorSaturation
open CubicAnomaly.Classification.CompactQuotientSkew
open CubicAnomaly.Classification.TensorFixedVectors
open CubicAnomaly.Classification.TensorEndomorphismDescent
open CubicAnomaly.Classification.TensorInvariantForms
open CubicAnomaly.Classification.TensorScalarSkew
open CubicAnomaly.Classification.TraceZeroSymmetricPair
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.IdealTensorDuality
open scoped TensorProduct

noncomputable section

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  {h : LieSubalgebra ℝ g}
  {W M N : Type*}
  [AddCommGroup W] [Module ℂ W]
  [LieRingModule (ℂ ⊗[ℝ] h) W] [LieModule ℂ (ℂ ⊗[ℝ] h) W]
  [AddCommGroup M] [Module ℂ M]
  [LieRingModule (ℂ ⊗[ℝ] h) M] [LieModule ℂ (ℂ ⊗[ℝ] h) M]
  [AddCommGroup N] [Module ℂ N]
  [LieRingModule (ℂ ⊗[ℝ] h) N] [LieModule ℂ (ℂ ⊗[ℝ] h) N]
  [FiniteDimensional ℂ M] [FiniteDimensional ℂ N] [Nontrivial M]
  [LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) N]
  [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)]
  {Φ : LinearMap.BilinForm ℂ W}

set_option maxHeartbeats 800000 in
/-- Any actual tensor factor paired with a faithfully acting atomic
ideal has zero trace-zero self-adjoint space in a complex-type compact
quotient. This derives the vanishing without classifying the factor. -/
theorem compact_tensor_right_trace_zero_eq_bot
    (B : CompactForm g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (A : Model h Φ) (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W)
    (I : LieIdeal ℂ (ℂ ⊗[ℝ] h)) (hI : IsAtom I)
    (β : LinearMap.BilinForm ℂ M) (hiβ : β.lieInvariant (ℂ ⊗[ℝ] h))
    (γ : LinearMap.BilinForm ℂ N) (hiγ : γ.lieInvariant (ℂ ⊗[ℝ] h))
    (hβ : β.Nondegenerate) (hγ : γ.Nondegenerate) (hrγ : LinearMap.IsRefl γ)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    (hMI : Function.Injective (fun x : I => toEnd ℂ (ℂ ⊗[ℝ] h) M (x : ℂ ⊗[ℝ] h)))
    (hN : ∀ (x : I) (n : N), ⁅(x : ℂ ⊗[ℝ] h), n⁆ = 0) :
    traceZeroSelfAdjointLieSubmodule γ hiγ = ⊥ := by
  by_contra hP
  letI : Nontrivial N := LieModule.nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) N
  letI : Nontrivial I := (LieSubmodule.nontrivial_iff_ne_bot ℂ _ _).mpr hI.ne_bot
  letI : LieAlgebra.IsSimple ℂ I := LieAlgebra.IsSemisimple.isSimple_of_isAtom I hI
  have hcenter : LieAlgebra.center ℂ I = ⊥ := LieAlgebra.center_eq_bot ℂ I
  have hfull := right_factor_action_full_of_left_parity_nonzero B hproper e A E I hI hcenter
    β hiβ γ hiγ hβ hγ hrγ hform hMI hN hP
  let f := leftParityQuotientMap B A E I β hiβ γ hiγ hform
  have hbij : Function.Bijective f := left_parity_quotient_map_bijective B hproper e A E I hI
    β hiβ γ hiγ hβ hγ hrγ hform hMI hP
  let F : (I ⊗[ℂ] traceZeroSelfAdjointLieSubmodule γ hiγ) ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆
      (ℂ ⊗[ℝ] orthogonalComplement B h) :=
    { f, LinearEquiv.ofBijective f.toLinearMap hbij with }
  obtain ⟨D, hD, hskew⟩ := compact_equivalent_source_exists_skew_end B h hproper e F
  have hκ : idealKillingForm I ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : I)
    apply hx
    apply (atomic_ideal_killing_form_nondegenerate I hI).1 x
    intro y
    rw [hz]
    rfl
  have htrace := trace_zero_self_adjoint_module_trace_form_invariant γ hiγ
  have hinv := tensor_bilin_form_invariant (idealKillingForm I)
    (ideal_killing_form_invariant I) (traceZeroSelfAdjointModuleTraceForm γ hiγ) htrace
  obtain ⟨d, hd, _, hdskew⟩ := exists_nonzero_skew_right_equivariant_factor I
    (trace_zero_self_adjoint_ideal_action_eq_zero I γ hiγ hN)
    (idealKillingForm I) hκ (traceZeroSelfAdjointModuleTraceForm γ hiγ) D hD
    (hskew _ hinv)
  exact hd (full_skew_trace_zero_self_adjoint_skew_end_eq_zero
    γ hiγ hγ hrγ hfull d hdskew)

set_option maxHeartbeats 1000000 in
/-- Two complementary atomic ideals acting through actual irreducible
tensor factors are impossible in a proper compact form-preserving pair
with complex commutant. Every tensor and form witness here is concrete;
the classical applications construct all of them from the original pair. -/
theorem compact_two_ideal_tensor_impossible
    [LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) M]
    (B : CompactForm g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (A : Model h Φ) (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W)
    (I J : LieIdeal ℂ (ℂ ⊗[ℝ] h)) (hI : IsAtom I) (hJ : IsAtom J)
    (htop : I ⊔ J = ⊤)
    (β : LinearMap.BilinForm ℂ M) (hiβ : β.lieInvariant (ℂ ⊗[ℝ] h))
    (γ : LinearMap.BilinForm ℂ N) (hiγ : γ.lieInvariant (ℂ ⊗[ℝ] h))
    (hβ : β.Nondegenerate) (hγ : γ.Nondegenerate)
    (hrβ : LinearMap.IsRefl β) (hrγ : LinearMap.IsRefl γ)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    (hMI : Function.Injective (fun x : I => toEnd ℂ (ℂ ⊗[ℝ] h) M (x : ℂ ⊗[ℝ] h)))
    (hNJ : Function.Injective (fun x : J => toEnd ℂ (ℂ ⊗[ℝ] h) N (x : ℂ ⊗[ℝ] h)))
    (hIN : ∀ (x : I) (n : N), ⁅(x : ℂ ⊗[ℝ] h), n⁆ = 0)
    (hJM : ∀ (x : J) (m : M), ⁅(x : ℂ ⊗[ℝ] h), m⁆ = 0) : False := by
  letI : Nontrivial N := LieModule.nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) N
  have hNzero := compact_tensor_right_trace_zero_eq_bot B hproper e A E I hI
    β hiβ γ hiγ hβ hγ hrγ hform hMI hIN
  have hMzero := compact_tensor_right_trace_zero_eq_bot B hproper e A
    ((tensorCommLieEquiv (M := N) (N := M)).trans E) J hJ
    γ hiγ β hiβ hγ hβ hrβ (tensor_form_isometry_swap Φ E β γ hform) hNJ hJM
  have hM0 : traceZeroSelfAdjointSubmodule β = ⊥ :=
    congrArg LieSubmodule.toSubmodule hMzero
  have hN0 : traceZeroSelfAdjointSubmodule γ = ⊥ :=
    congrArg LieSubmodule.toSubmodule hNzero
  have hfull := tensor_skew_range_le_diagonal_of_irreducible_factors β hiβ γ hiγ
    (tensor_bilin_form_nondegenerate β hβ γ hγ) I J htop hIN hJM hM0 hN0
  have hall (z : ℂ ⊗[ℝ] g) : z ∈ h.toSubmodule.baseChange ℂ := by
    let T := (operatorConjugation E).symm (A.operatorMap z)
    have hT : T ∈ skewAdjointLieSubalgebra (β.tmul γ) := by
      apply (operator_conjugation_mem_skew_iff E Φ (β.tmul γ) hform T).mp
      change operatorConjugation E ((operatorConjugation E).symm (A.operatorMap z)) ∈ _
      rw [LieModuleEquiv.apply_symm_apply]
      exact (A.range_iff (A.operatorMap z)).mp ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := hfull hT
    apply (A.mem_isotropy_iff z).mpr
    refine ⟨x, ?_⟩
    calc
      toEnd ℂ (ℂ ⊗[ℝ] h) W x =
          operatorConjugation E (toEnd ℂ (ℂ ⊗[ℝ] h) (M ⊗[ℂ] N) x) :=
        (operator_conjugation_action E x).symm
      _ = operatorConjugation E T := congrArg (operatorConjugation E) hx
      _ = A.operatorMap z := (operatorConjugation E).apply_symm_apply _
  apply hproper
  apply top_unique
  intro x _
  exact (complexification_real_mem_baseChange_iff g h.toSubmodule x).mp (hall (1 ⊗ₜ[ℝ] x))

end

end CubicAnomaly.Classification.CompactTensorExclusion
