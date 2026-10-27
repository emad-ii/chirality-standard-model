import CubicAnomaly.Classification.CompactOperatorModel
import CubicAnomaly.Classification.EquivariantOperatorTransport
import CubicAnomaly.Classification.TensorParitySeparation

/-!
# Tensor parity in the actual compact quotient

The literal tensor form isometry and actual ambient operator model lift
the two parity blocks to the original complexified Lie algebra. Partial
traces and adjoint parity prove that their sum injects modulo the actual
isotropy. The complex-type quotient then forces one of the two traceless
self-adjoint factor spaces to vanish.
-/

namespace CubicAnomaly.Classification.CompactTensorParity

open Module LieModule
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.CompactOperatorModel
open CubicAnomaly.Classification.EquivariantOperatorTransport
open CubicAnomaly.Classification.SelfDualQuotientObstruction
open CubicAnomaly.Classification.TensorParitySeparation
open CubicAnomaly.Classification.TensorParityBlocks
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.ExternalTensor
open scoped TensorProduct

noncomputable section

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]
  {h : LieSubalgebra ℝ g}
  {W M N : Type*}
  [AddCommGroup W] [Module ℂ W]
  [LieRingModule (ℂ ⊗[ℝ] h) W] [LieModule ℂ (ℂ ⊗[ℝ] h) W]
  [AddCommGroup M] [Module ℂ M]
  [LieRingModule (ℂ ⊗[ℝ] h) M] [LieModule ℂ (ℂ ⊗[ℝ] h) M]
  [AddCommGroup N] [Module ℂ N]
  [LieRingModule (ℂ ⊗[ℝ] h) N] [LieModule ℂ (ℂ ⊗[ℝ] h) N]
  {Φ : LinearMap.BilinForm ℂ W}

/-- Transport a tensor operator through the actual defining equivalence,
then lift it through the actual form-preserving ambient realization. -/
def tensorAmbientLift (A : Model h Φ) (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W)
    (β : LinearMap.BilinForm ℂ M) (γ : LinearMap.BilinForm ℂ N)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ (M ⊗[ℂ] N))
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra (β.tmul γ)) :
    S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] g) :=
  A.lift ((operatorConjugation E).toLieModuleHom.comp f)
    (fun s => (operator_conjugation_mem_skew_iff E Φ (β.tmul γ) hform (f s)).mpr (hf s))

/-- Tensor lifting retains the literal conjugated operator. -/
@[simp] theorem tensor_ambient_lift_operator
    (A : Model h Φ) (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W)
    (β : LinearMap.BilinForm ℂ M) (γ : LinearMap.BilinForm ℂ N)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ (M ⊗[ℂ] N))
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra (β.tmul γ)) (s : S) :
    A.operatorMap (tensorAmbientLift A E β γ hform f hf s) = operatorConjugation E (f s) :=
  A.lift_operator _ _ s

/-- The actual ambient tensor lift lies in isotropy exactly when its
original tensor operator belongs to the actual diagonal action image. -/
theorem tensor_ambient_lift_mem_isotropy_iff
    (A : Model h Φ) (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W)
    (β : LinearMap.BilinForm ℂ M) (γ : LinearMap.BilinForm ℂ N)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ (M ⊗[ℂ] N))
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra (β.tmul γ)) (s : S) :
    tensorAmbientLift A E β γ hform f hf s ∈ h.toSubmodule.baseChange ℂ ↔
      f s ∈ (toEnd ℂ (ℂ ⊗[ℝ] h) (M ⊗[ℂ] N)).range := by
  rw [A.mem_isotropy_iff, tensor_ambient_lift_operator]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, ((operator_conjugation_eq_action_iff E (f s) x).mp hx.symm).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, ((operator_conjugation_eq_action_iff E (f s) x).mpr hx.symm).symm⟩

variable [Module.Finite ℝ g]

/-- Joint separation from the diagonal action transfers to the actual
compact quotient. A nonzero self-dual first source rules out a second
nonzero source; the sources need not be irreducible. -/
theorem compact_tensor_blocks_obstruction
    (B : CompactForm g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (A : Model h Φ) (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W)
    (β : LinearMap.BilinForm ℂ M) (γ : LinearMap.BilinForm ℂ N)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    {S T : Type*} [AddCommGroup S] [Module ℂ S] [Nontrivial S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    [AddCommGroup T] [Module ℂ T] [Nontrivial T]
    [LieRingModule (ℂ ⊗[ℝ] h) T] [LieModule ℂ (ℂ ⊗[ℝ] h) T]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ (M ⊗[ℂ] N))
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra (β.tmul γ))
    (f' : T →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ (M ⊗[ℂ] N))
    (hf' : ∀ t, f' t ∈ skewAdjointLieSubalgebra (β.tmul γ))
    (hs : Nonempty (S ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ S))
    (hsep : ∀ s t x, f s + f' t = toEnd ℂ (ℂ ⊗[ℝ] h) (M ⊗[ℂ] N) x →
      s = 0 ∧ t = 0) : False := by
  apply compact_two_ambient_blocks_obstruction B h hproper e
    (tensorAmbientLift A E β γ hform f hf)
    (tensorAmbientLift A E β γ hform f' hf') hs
  intro s t hst
  obtain ⟨x, hx⟩ := (A.mem_isotropy_iff _).mp hst
  have he : operatorConjugation E (f s + f' t) = toEnd ℂ (ℂ ⊗[ℝ] h) W x := by
    simpa only [map_add, tensor_ambient_lift_operator] using hx.symm
  exact hsep s t x ((operator_conjugation_eq_action_iff E _ x).mp he)

variable [FiniteDimensional ℂ M] [FiniteDimensional ℂ N] [Nontrivial M] [Nontrivial N]
  [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)]

/-- Two faithful tensor factors in an actual classical compact model
cannot both have nonzero traceless self-adjoint operator spaces. This
conclusion is about the actual factor forms, in arbitrary dimension. -/
theorem compact_tensor_parity_one_factor_eq_bot
    (B : CompactForm g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (A : Model h Φ) (E : M ⊗[ℂ] N ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ W)
    (I J : LieIdeal ℂ (ℂ ⊗[ℝ] h)) (hI : IsAtom I) (hJ : J ≠ ⊥)
    (β : LinearMap.BilinForm ℂ M) (hiβ : β.lieInvariant (ℂ ⊗[ℝ] h))
    (γ : LinearMap.BilinForm ℂ N) (hiγ : γ.lieInvariant (ℂ ⊗[ℝ] h))
    (hβ : β.Nondegenerate) (hγ : γ.Nondegenerate) (hrγ : LinearMap.IsRefl γ)
    (hform : Φ.compl₁₂ E.toLinearMap E.toLinearMap = β.tmul γ)
    (hMI : Function.Injective (fun x : I => toEnd ℂ (ℂ ⊗[ℝ] h) M (x : ℂ ⊗[ℝ] h)))
    (hNJ : Function.Injective (fun x : J => toEnd ℂ (ℂ ⊗[ℝ] h) N (x : ℂ ⊗[ℝ] h))) :
    traceZeroSelfAdjointLieSubmodule β hiβ = ⊥ ∨
      traceZeroSelfAdjointLieSubmodule γ hiγ = ⊥ := by
  by_contra! hP
  letI : Nontrivial I := (LieSubmodule.nontrivial_iff_ne_bot ℂ _ _).mpr hI.ne_bot
  letI : Nontrivial J := (LieSubmodule.nontrivial_iff_ne_bot ℂ _ _).mpr hJ
  letI : Nontrivial (traceZeroSelfAdjointLieSubmodule β hiβ) :=
    (LieSubmodule.nontrivial_iff_ne_bot ℂ _ _).mpr hP.1
  letI : Nontrivial (traceZeroSelfAdjointLieSubmodule γ hiγ) :=
    (LieSubmodule.nontrivial_iff_ne_bot ℂ _ _).mpr hP.2
  letI : Nontrivial (I ⊗[ℂ] traceZeroSelfAdjointLieSubmodule γ hiγ) := tensor_product_nontrivial
  letI : Nontrivial (traceZeroSelfAdjointLieSubmodule β hiβ ⊗[ℂ] J) := tensor_product_nontrivial
  exact compact_tensor_blocks_obstruction B hproper e A E β γ hform
    (leftParityBlock I γ hiγ)
    (left_parity_block_mem_skewAdjointLieSubalgebra I β hiβ γ hiγ)
    (rightParityBlock J β hiβ)
    (right_parity_block_mem_skewAdjointLieSubalgebra J β hiβ γ hiγ)
    (atomic_left_parity_source_self_dual I hI γ hγ hrγ hiγ)
    (parity_blocks_eq_diagonal_action I J β hβ hiβ γ hγ hiγ hMI hNJ)

end

end CubicAnomaly.Classification.CompactTensorParity
