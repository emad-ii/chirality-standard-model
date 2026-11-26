import CubicAnomaly.Classification.CompactTensorParity
import CubicAnomaly.Classification.TensorFixedVectors

/-!
# A surviving tensor block saturates the other factor action

A nonzero ideal/trace-zero-self-adjoint block injects into the actual
compact quotient and is self-dual, so it fills that quotient. Since the
ideal is centerless and acts trivially on the other factor, this quotient
has no ideal-fixed vectors. Every extra form-preserving operator in that
other factor has an ideal-fixed quotient class, hence lies in isotropy.
Partial trace then identifies the other factor action with its full
form-preserving algebra. No real or complex maximality is used.
-/

namespace CubicAnomaly.Classification.CompactTensorSaturation

open Module LieModule
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.CompactOperatorModel
open CubicAnomaly.Classification.EquivariantOperatorTransport
open CubicAnomaly.Classification.SelfDualQuotientObstruction
open CubicAnomaly.Classification.CompactTensorParity
open CubicAnomaly.Classification.TensorParitySeparation
open CubicAnomaly.Classification.TensorParityBlocks
open CubicAnomaly.Classification.TensorEndomorphisms
open CubicAnomaly.Classification.TensorFixedVectors
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.ExternalTensor
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
  [FiniteDimensional ℂ M] [FiniteDimensional ℂ N]
  {Φ : LinearMap.BilinForm ℂ W}

/-- The actual left parity block followed by the actual compact quotient
projection. Its source and every action remain the constructed modules. -/
def leftParityQuotientMap
    (B : CompactForm g) (A : Model h Φ)
    (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W) (I : LieIdeal ℂ (ℂ ⊗[ℝ] h))
    (β : LinearMap.BilinForm ℂ M) (hiβ : β.lieInvariant (ℂ ⊗[ℝ] h))
    (γ : LinearMap.BilinForm ℂ N) (hiγ : γ.lieInvariant (ℂ ⊗[ℝ] h))
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ) :
    (I ⊗[ℂ] traceZeroSelfAdjointLieSubmodule γ hiγ) →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆
      (ℂ ⊗[ℝ] orthogonalComplement B h) :=
  (complexifiedComplementProjection B h).comp
    (tensorAmbientLift A E β γ hform (leftParityBlock I γ hiγ)
      (left_parity_block_mem_skewAdjointLieSubalgebra I β hiβ γ hiγ))

variable [Nontrivial M] [Nontrivial N]

/-- The surviving parity block injects into the actual quotient. This
requires only a faithful ideal action, not irreducibility of the block. -/
theorem left_parity_quotient_map_injective
    (B : CompactForm g) (A : Model h Φ)
    (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W) (I : LieIdeal ℂ (ℂ ⊗[ℝ] h))
    (β : LinearMap.BilinForm ℂ M) (hiβ : β.lieInvariant (ℂ ⊗[ℝ] h))
    (γ : LinearMap.BilinForm ℂ N) (hiγ : γ.lieInvariant (ℂ ⊗[ℝ] h))
    (hβ : β.Nondegenerate) (hγ : γ.Nondegenerate)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    (hMI : Function.Injective (fun x : I => toEnd ℂ (ℂ ⊗[ℝ] h) M (x : ℂ ⊗[ℝ] h))) :
    Function.Injective (leftParityQuotientMap B A E I β hiβ γ hiγ hform) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro t ht
  have hmem := (complexified_complement_projection_eq_zero_iff B h _).mp ht
  obtain ⟨x, hx⟩ := (tensor_ambient_lift_mem_isotropy_iff A E β γ hform
    (leftParityBlock I γ hiγ)
    (left_parity_block_mem_skewAdjointLieSubalgebra I β hiβ γ hiγ) t).mp hmem
  have he : leftParityBlock (M := M) I γ hiγ t +
      rightParityBlock (N := N) I β hiβ 0 =
      TensorProduct.map (toEnd ℂ (ℂ ⊗[ℝ] h) M x) 1 +
        TensorProduct.map 1 (toEnd ℂ (ℂ ⊗[ℝ] h) N x) := by
    rw [map_zero, add_zero, ← tensor_action_eq_sum]
    exact hx.symm
  have hz := (parity_blocks_tensor_sum_separation I I β hβ hiβ γ hγ hiγ t 0
    _ _ (hiβ x) (hiγ x) he).1
  apply left_parity_block_injective I γ hiγ hMI
  simpa only [map_zero] using hz

variable [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)]

/-- A nonzero atomic parity block is exactly the whole actual quotient,
through its literal operator map and complement projection. -/
theorem left_parity_quotient_map_bijective
    (B : CompactForm g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (A : Model h Φ) (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W)
    (I : LieIdeal ℂ (ℂ ⊗[ℝ] h)) (hI : IsAtom I)
    (β : LinearMap.BilinForm ℂ M) (hiβ : β.lieInvariant (ℂ ⊗[ℝ] h))
    (γ : LinearMap.BilinForm ℂ N) (hiγ : γ.lieInvariant (ℂ ⊗[ℝ] h))
    (hβ : β.Nondegenerate) (hγ : γ.Nondegenerate) (hrγ : LinearMap.IsRefl γ)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    (hMI : Function.Injective (fun x : I => toEnd ℂ (ℂ ⊗[ℝ] h) M (x : ℂ ⊗[ℝ] h)))
    (hP : traceZeroSelfAdjointLieSubmodule γ hiγ ≠ ⊥) :
    Function.Bijective (leftParityQuotientMap B A E I β hiβ γ hiγ hform) := by
  letI : Nontrivial I := (LieSubmodule.nontrivial_iff_ne_bot ℂ _ _).mpr hI.ne_bot
  letI : Nontrivial (traceZeroSelfAdjointLieSubmodule γ hiγ) :=
    (LieSubmodule.nontrivial_iff_ne_bot ℂ _ _).mpr hP
  letI : Nontrivial (I ⊗[ℂ] traceZeroSelfAdjointLieSubmodule γ hiγ) := tensor_product_nontrivial
  have hinj := left_parity_quotient_map_injective B A E I β hiβ γ hiγ hβ hγ hform hMI
  exact ⟨hinj, self_dual_embedding_surjective
    (SelfDualAbsorption.compact_complement_self_dual_submodule_eq_bot_or_top B h hproper e)
    _ hinj (atomic_left_parity_source_self_dual I hI γ hγ hrγ hiγ)⟩

/-- A surviving atomic parity block forces the other factor action to
be the full algebra preserving its actual bilinear form. The argument
uses fixed vectors in the actual quotient, without any maximality step. -/
theorem right_factor_action_full_of_left_parity_nonzero
    (B : CompactForm g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (A : Model h Φ) (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W)
    (I : LieIdeal ℂ (ℂ ⊗[ℝ] h)) (hI : IsAtom I)
    (hcenter : LieAlgebra.center ℂ I = ⊥)
    (β : LinearMap.BilinForm ℂ M) (hiβ : β.lieInvariant (ℂ ⊗[ℝ] h))
    (γ : LinearMap.BilinForm ℂ N) (hiγ : γ.lieInvariant (ℂ ⊗[ℝ] h))
    (hβ : β.Nondegenerate) (hγ : γ.Nondegenerate) (hrγ : LinearMap.IsRefl γ)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    (hMI : Function.Injective (fun x : I => toEnd ℂ (ℂ ⊗[ℝ] h) M (x : ℂ ⊗[ℝ] h)))
    (hN : ∀ (x : I) (n : N), ⁅(x : ℂ ⊗[ℝ] h), n⁆ = 0)
    (hP : traceZeroSelfAdjointLieSubmodule γ hiγ ≠ ⊥) :
    (toEnd ℂ (ℂ ⊗[ℝ] h) N).range = skewAdjointLieSubalgebra γ := by
  have hbij := left_parity_quotient_map_bijective B hproper e A E I hI
    β hiβ γ hiγ hβ hγ hrγ hform hMI hP
  have hfix (q : ℂ ⊗[ℝ] orthogonalComplement B h)
      (hq : ∀ x : I, ⁅(x : ℂ ⊗[ℝ] h), q⁆ = 0) : q = 0 :=
    fixed_eq_zero_of_bijective I _ hbij
      (left_parity_source_fixed_eq_zero I hcenter γ hiγ hN) q hq
  apply le_antisymm
  · rintro b ⟨x, rfl⟩
    apply (LinearMap.mem_skewAdjointSubmodule _).mpr
    intro n n'
    change γ ⁅x, n⁆ n' = γ n (-⁅x, n'⁆)
    rw [map_neg]
    exact hiγ x n n'
  · intro b hb
    have hb' (n n' : N) : γ (b n) n' = -γ n (b n') := by
      simpa only [Pi.neg_apply, map_neg] using
        (LinearMap.mem_skewAdjointSubmodule _).mp hb n n'
    let T : Module.End ℂ (M ⊗[ℂ] N) := TensorProduct.map 1 b
    have hT : T ∈ skewAdjointLieSubalgebra (β.tmul γ) := by
      apply (LinearMap.mem_skewAdjointSubmodule _).mpr
      intro u v
      simpa only [Pi.neg_apply, map_neg] using
        tensor_self_adjoint_skew_operator β γ 1 b (fun _ _ => rfl) hb' u v
    obtain ⟨z, hz⟩ := (A.range_iff (operatorConjugation E T)).mpr
      ((operator_conjugation_mem_skew_iff E Φ (β.tmul γ) hform T).mpr hT)
    have hzfix (x : I) : ⁅(x : ℂ ⊗[ℝ] h), z⁆ = 0 := by
      have hTf : ⁅(x : ℂ ⊗[ℝ] h), T⁆ = 0 := by
        apply TensorProduct.ext'
        intro m n
        rw [LieHom.lie_apply]
        simp only [T, TensorProduct.map_tmul, Module.End.one_apply,
          TensorProduct.LieModule.lie_tmul_right, hN,
          TensorProduct.tmul_zero, add_zero, sub_self, LinearMap.zero_apply]
      apply A.injective
      rw [A.operatorMap.map_lie, hz, map_zero]
      change ⁅(x : ℂ ⊗[ℝ] h), (operatorConjugation E).toLieModuleHom T⁆ = 0
      rw [← (operatorConjugation E).toLieModuleHom.map_lie, hTf, map_zero]
    have hzin : z ∈ h.toSubmodule.baseChange ℂ := by
      apply (complexified_complement_projection_eq_zero_iff B h z).mp
      apply hfix
      intro x
      rw [← (complexifiedComplementProjection B h).map_lie, hzfix, map_zero]
    obtain ⟨x, hx⟩ := (A.mem_isotropy_iff z).mp hzin
    have hTx : T = toEnd ℂ (ℂ ⊗[ℝ] h) (M ⊗[ℂ] N) x := by
      apply (operator_conjugation_eq_action_iff E T x).mp
      exact hz.symm.trans hx.symm
    have ht := congrArg (rightPartialTrace (L := ℂ ⊗[ℝ] h)) hTx
    rw [tensor_action_eq_sum] at ht
    change rightPartialTrace (L := ℂ ⊗[ℝ] h) (TensorProduct.map 1 b) = _ at ht
    simp only [map_add, right_partial_trace_map, LinearMap.trace_one,
      invariant_action_trace_zero β hβ hiβ, zero_smul, zero_add] at ht
    have hdim : (finrank ℂ M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
    exact ⟨x, ((smul_right_inj hdim).mp ht).symm⟩

end

end CubicAnomaly.Classification.CompactTensorSaturation
