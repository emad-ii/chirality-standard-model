import CubicAnomaly.Classification.TensorFactorActions
import CubicAnomaly.Classification.TensorFormFactorization

/-!
# Actual tensor factors and forms for two complementary ideals

Starting with a faithful irreducible representation and its actual
nondegenerate invariant bilinear form, complementary ideals determine an
actual atomic first factor and its equivariant-map multiplicity space.
The canonical evaluation equivalence carries the original form to an
exact tensor product of constructed nondegenerate invariant reflexive
factor forms.  No factorization or factor-form witness is an input.
-/

namespace CubicAnomaly.Classification.TwoIdealTensorForms

open CubicAnomaly.Classification.TensorEvaluation
open CubicAnomaly.Classification.TensorFactorActions
open CubicAnomaly.Classification.TensorFormFactorization
open scoped TensorProduct

noncomputable section

section Pullback

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

omit [LieAlgebra K L] [LieModule K L M] [LieModule K L N] in
private theorem pullback_form_invariant
    (B : LinearMap.BilinForm K N) (hB : B.lieInvariant L) (f : M →ₗ⁅K,L⁆ N) :
    LinearMap.BilinForm.lieInvariant L (B.compl₁₂ f.toLinearMap f.toLinearMap) := by
  intro x m n
  change B (f ⁅x, m⁆) (f n) = -B (f m) (f ⁅x, n⁆)
  rw [f.map_lie, f.map_lie]
  exact hB x (f m) (f n)

private theorem pullback_form_nondegenerate
    (B : LinearMap.BilinForm K N) (hB : B.Nondegenerate) (e : M ≃ₗ[K] N) :
    (B.compl₁₂ e.toLinearMap e.toLinearMap).Nondegenerate := by
  constructor
  · intro m hm
    apply e.injective
    rw [map_zero]
    apply hB.1
    intro n
    obtain ⟨u, rfl⟩ := e.surjective n
    exact hm u
  · intro m hm
    apply e.injective
    rw [map_zero]
    apply hB.2
    intro n
    obtain ⟨u, rfl⟩ := e.surjective n
    exact hm u

end Pullback

section RestrictedEvaluation

variable {K L W U : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)
  [AddCommGroup U] [Module K U] [LieRingModule I U] [LieModule K I U]

private def leftEvaluationLieHom
    [LieRingModule I (U →ₗ⁅K,I⁆ W)] [LieModule K I (U →ₗ⁅K,I⁆ W)]
    [LieModule.IsTrivial I (U →ₗ⁅K,I⁆ W)] :
    U ⊗[K] (U →ₗ⁅K,I⁆ W) →ₗ⁅K,I⁆ W where
  toLinearMap := lieHomEvaluation
  map_lie' := by
    intro x t
    change lieHomEvaluation ⁅x, t⁆ = ⁅x, lieHomEvaluation t⁆
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u f =>
      simp only [TensorProduct.LieModule.lie_tmul_right, trivial_lie_zero,
        TensorProduct.tmul_zero, add_zero, lieHomEvaluation_tmul]
      exact f.map_lie x u
    | add t s ht hs => simp only [lie_add, map_add, ht, hs]

private def rightEvaluationLieHom
    [LieRingModule J U] [LieModule K J U] [LieModule.IsTrivial J U] :
    letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
    letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
    U ⊗[K] (U →ₗ⁅K,I⁆ W) →ₗ⁅K,J⁆ W := by
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
  refine { toLinearMap := lieHomEvaluation, map_lie' := ?_ }
  intro x t
  change lieHomEvaluation ⁅x, t⁆ = ⁅x, lieHomEvaluation t⁆
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u f =>
    simp only [TensorProduct.LieModule.lie_tmul_right, trivial_lie_zero,
      TensorProduct.zero_tmul, zero_add, lieHomEvaluation_tmul]
    rfl
  | add t s ht hs => simp only [lie_add, map_add, ht, hs]

end RestrictedEvaluation

section ActualPackage

variable {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

/-- The exact constructed two-ideal tensor package.  Its first factor is
an actual restricted submodule; its second factor consists of actual
equivariant maps into the original representation.  All ideal and ambient
actions are the original actions or their actual projection inflations. -/
def ActualTwoIdealTensorForms
    (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)
    (B : LinearMap.BilinForm K W) (U : LieSubmodule K I W) : Prop :=
  letI : LieRingModule I U := inferInstance
  letI : LieModule K I U := inferInstance
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
  letI := idealInflationLieRingModule (M := U) I J hIJ htop
  letI := idealInflationLieModule (M := U) I J hIJ htop
  letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
  letI := multiplicityAmbientLieModule (U := U) (W := W) I J hIJ htop
  LieModule.IsIrreducible K I U ∧ LieModule.IsFaithful K I U ∧
  LieModule.IsIrreducible K J (U →ₗ⁅K,I⁆ W) ∧ LieModule.IsFaithful K J (U →ₗ⁅K,I⁆ W) ∧
  LieModule.IsIrreducible K L U ∧ LieModule.IsIrreducible K L (U →ₗ⁅K,I⁆ W) ∧
  Module.Finite K (U →ₗ⁅K,I⁆ W) ∧
  ∃ E : U ⊗[K] (U →ₗ⁅K,I⁆ W) ≃ₗ⁅K,L⁆ W,
    E.toLinearEquiv.toLinearMap = lieHomEvaluation ∧
    ∃ β : LinearMap.BilinForm K U, ∃ γ : LinearMap.BilinForm K (U →ₗ⁅K,I⁆ W),
      β.lieInvariant L ∧ γ.lieInvariant L ∧ β.Nondegenerate ∧ γ.Nondegenerate ∧
      LinearMap.IsRefl β ∧ LinearMap.IsRefl γ ∧
      B.compl₁₂ E.toLinearEquiv.toLinearMap E.toLinearEquiv.toLinearMap = β.tmul γ

set_option maxHeartbeats 800000 in
/-- Faithful irreducibility and an actual invariant nondegenerate form
produce actual faithful irreducible tensor factors, their constructed
invariant reflexive forms, and an exact equivariant isometry of tensor forms. -/
theorem exists_atomic_two_ideal_tensor_forms
    [IsAlgClosed K] [Module.Finite K W] [LieModule.IsIrreducible K L W]
    [LieModule.IsFaithful K L W]
    (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)
    (B : LinearMap.BilinForm K W) (hInv : B.lieInvariant L) (hNd : B.Nondegenerate) :
    ∃ U : LieSubmodule K I W, IsAtom U ∧ ActualTwoIdealTensorForms I J hIJ htop B U := by
  obtain ⟨U, hU, hIrred, hbij⟩ :=
    exists_atomic_evaluation_factorization (W := W) I J hIJ htop
  refine ⟨U, hU, ?_⟩
  letI : LieRingModule I U := inferInstance
  letI : LieModule K I U := inferInstance
  letI : LieModule.IsIrreducible K I U := hIrred
  have hne : ∃ f : U →ₗ⁅K,I⁆ W, f ≠ 0 := by
    refine ⟨U.incl, ?_⟩
    intro he
    apply hU.ne_bot
    apply (LieSubmodule.eq_bot_iff U).mpr
    intro u hu
    exact LieModuleHom.congr_fun he ⟨u, hu⟩
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
  letI : LieModule.IsIrreducible K J (U →ₗ⁅K,I⁆ W) :=
    commutingIdealHom_irreducible I J hIJ htop hne
  letI : LieModule.IsFaithful K I W := by
    apply (LieModule.isFaithful_iff' K I W).mpr
    intro x hx
    apply Subtype.ext
    exact (LieModule.isFaithful_iff' K L W).mp inferInstance (x : L) hx
  letI : LieModule.IsFaithful K I U := lieHomEvaluation_left_faithful hbij.2
  letI : LieModule.IsFaithful K J (U →ₗ⁅K,I⁆ W) :=
    commutingIdealHom_faithful I J hIJ htop hne
  letI := idealInflationLieRingModule (M := U) I J hIJ htop
  letI := idealInflationLieModule (M := U) I J hIJ htop
  letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
  letI := multiplicityAmbientLieModule (U := U) (W := W) I J hIJ htop
  letI : LieModule.IsTrivial I (U →ₗ⁅K,I⁆ W) :=
    multiplicityAmbient_first_trivial I J hIJ htop
  letI : LieModule.IsTrivial J U := idealInflation_complement_trivial I J hIJ htop
  letI : LieModule.IsIrreducible K L U := idealInflation_irreducible I J hIJ htop
  letI : LieModule.IsIrreducible K L (U →ₗ⁅K,I⁆ W) :=
    multiplicityAmbient_irreducible I J hIJ htop hne
  letI : Module.Finite K (U →ₗ⁅K,I⁆ W) := lieHom_space_finite
  letI : Nontrivial (U →ₗ⁅K,I⁆ W) :=
    LieModule.nontrivial_of_isIrreducible K J (U →ₗ⁅K,I⁆ W)
  letI : LieRingModule I (U ⊗[K] (U →ₗ⁅K,I⁆ W)) :=
    TensorProduct.LieModule.lieRingModule (R := K)
  letI : LieModule K I (U ⊗[K] (U →ₗ⁅K,I⁆ W)) :=
    TensorProduct.LieModule.lieModule
  letI : LieRingModule J (U ⊗[K] (U →ₗ⁅K,I⁆ W)) :=
    TensorProduct.LieModule.lieRingModule (R := K)
  letI : LieModule K J (U ⊗[K] (U →ₗ⁅K,I⁆ W)) :=
    TensorProduct.LieModule.lieModule
  let E : U ⊗[K] (U →ₗ⁅K,I⁆ W) ≃ₗ⁅K,L⁆ W :=
    { ambientTensorEvaluationLieHom I J hIJ htop,
      LinearEquiv.ofBijective lieHomEvaluation hbij with }
  let P : LinearMap.BilinForm K (U ⊗[K] (U →ₗ⁅K,I⁆ W)) :=
    B.compl₁₂ E.toLinearEquiv.toLinearMap E.toLinearEquiv.toLinearMap
  have hPI : P.lieInvariant I :=
    pullback_form_invariant (L := I) B (fun x => hInv (x : L))
      (leftEvaluationLieHom (U := U) (W := W) I)
  have hPJ : P.lieInvariant J :=
    pullback_form_invariant (L := J) B (fun x => hInv (x : L))
      (rightEvaluationLieHom (U := U) (W := W) I J hIJ)
  have hPNd : P.Nondegenerate := pullback_form_nondegenerate B hNd E.toLinearEquiv
  obtain ⟨β, γ, hβI, hγJ, hβNd, hγNd, hfactor⟩ :=
    exists_nondegenerate_invariant_factorization P hPI hPJ hPNd
  have hβL : β.lieInvariant L := by
    intro x u v
    exact hβI (complementaryIdealProjection I J hIJ htop x) u v
  have hγL : γ.lieInvariant L := by
    intro x f g
    exact hγJ (complementaryIdealProjection J I hIJ.symm
      (by simpa only [sup_comm] using htop) x) f g
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, E, rfl, β, γ,
    hβL, hγL, hβNd, hγNd, invariant_form_isRefl β hβI,
    invariant_form_isRefl γ hγJ, hfactor⟩

end ActualPackage

end

end CubicAnomaly.Classification.TwoIdealTensorForms
