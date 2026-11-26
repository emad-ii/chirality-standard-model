import CubicAnomaly.Classification.TensorEvaluation
import Mathlib.LinearAlgebra.Projection

/-!
# Ambient actions on the actual tensor factors

Complementary ideals determine actual Lie algebra projections. Pulling
the factor actions back along these projections makes canonical evaluation
an equivariant tensor factorization for the full ambient Lie algebra.
-/

namespace CubicAnomaly.Classification.TensorFactorActions

open LieModule Module
open scoped TensorProduct
open CubicAnomaly.Classification.ExternalTensor
open CubicAnomaly.Classification.TensorEvaluation

noncomputable section

section Projections

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)

private theorem actualIdealIsCompl (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤) :
    IsCompl I.toSubmodule J.toSubmodule := by
  apply LieSubmodule.isCompl_toSubmodule.mpr
  exact ⟨hIJ, codisjoint_iff.mpr htop⟩

/-- Projection onto an actual ideal along its complementary ideal preserves
the Lie bracket because the two ideals commute. -/
def complementaryIdealProjection : L →ₗ⁅K⁆ I where
  toLinearMap := I.toSubmodule.linearProjOfIsCompl J.toSubmodule (actualIdealIsCompl I J hIJ htop)
  map_lie' := by
    intro x y
    let hC := actualIdealIsCompl I J hIJ htop
    let p : L →ₗ[K] I := I.toSubmodule.linearProjOfIsCompl J.toSubmodule hC
    obtain ⟨⟨a, b⟩, rfl⟩ := (I.toSubmodule.prodEquivOfIsCompl J.toSubmodule hC).surjective x
    obtain ⟨⟨c, d⟩, rfl⟩ := (I.toSubmodule.prodEquivOfIsCompl J.toSubmodule hC).surjective y
    change I at a c
    change J at b d
    change p ⁅(a : L) + (b : L), (c : L) + (d : L)⁆ =
      ⁅p ((a : L) + (b : L)), p ((c : L) + (d : L))⁆
    rw [add_lie, lie_add, lie_add, disjoint_ideal_bracket_eq_zero I J hIJ a d,
      disjoint_ideal_bracket_eq_zero J I hIJ.symm b c, add_zero, zero_add]
    rw [map_add]
    change p ((⁅a, c⁆ : I) : L) + p ((⁅b, d⁆ : J) : L) =
      ⁅p ((a : L) + (b : L)), p ((c : L) + (d : L))⁆
    have hpI (u : I) : p (u : L) = u := Submodule.linearProjOfIsCompl_apply_left hC u
    have hpJ (v : J) : p (v : L) = 0 := Submodule.linearProjOfIsCompl_apply_right hC v
    simp only [map_add, hpI, hpJ, add_zero]

/-- The ideal projection restricts to the identity on its own ideal. -/
@[simp] theorem complementaryIdealProjection_left (x : I) :
    complementaryIdealProjection I J hIJ htop (x : L) = x :=
  Submodule.linearProjOfIsCompl_apply_left (actualIdealIsCompl I J hIJ htop) x

/-- The ideal projection vanishes on the complementary ideal. -/
@[simp] theorem complementaryIdealProjection_right (y : J) :
    complementaryIdealProjection I J hIJ htop (y : L) = 0 :=
  Submodule.linearProjOfIsCompl_apply_right (actualIdealIsCompl I J hIJ htop) y

/-- Every ambient element is the sum of its two actual ideal projections. -/
theorem complementaryIdealProjection_add (x : L) :
    (complementaryIdealProjection I J hIJ htop x : L) +
      (complementaryIdealProjection J I hIJ.symm (by simpa only [sup_comm] using htop) x : L) = x :=
  Submodule.IsCompl.projection_add_projection_eq_self (actualIdealIsCompl I J hIJ htop) x

end Projections

section Inflation

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)
  [AddCommGroup M] [LieRingModule I M]

/-- Inflate an ideal action to the ambient algebra through the actual projection. -/
def idealInflationLieRingModule : LieRingModule L M :=
  LieRingModule.compLieHom M (complementaryIdealProjection I J hIJ htop)

/-- Inflated actions are the given ideal action evaluated at the projection. -/
theorem idealInflation_action (x : L) (m : M) :
    letI := idealInflationLieRingModule (M := M) I J hIJ htop
    ⁅x, m⁆ = ⁅complementaryIdealProjection I J hIJ htop x, m⁆ := rfl

/-- Inflation preserves linearity of the action. -/
theorem idealInflationLieModule [Module K M] [LieModule K I M] :
    letI := idealInflationLieRingModule (M := M) I J hIJ htop
    LieModule K L M :=
  LieModule.compLieHom M (complementaryIdealProjection I J hIJ htop)

/-- The complementary ideal acts trivially in the inflated factor. -/
theorem idealInflation_complement_trivial :
    letI := idealInflationLieRingModule (M := M) I J hIJ htop
    LieModule.IsTrivial J M := by
  letI := idealInflationLieRingModule (M := M) I J hIJ htop
  constructor
  intro y m
  change ⁅complementaryIdealProjection I J hIJ htop (y : L), m⁆ = 0
  rw [complementaryIdealProjection_right, zero_lie]

/-- Inflation of an irreducible ideal module remains irreducible for the
ambient algebra, since its original ideal action is unchanged. -/
theorem idealInflation_irreducible [Module K M] [LieModule.IsIrreducible K I M] :
    letI := idealInflationLieRingModule (M := M) I J hIJ htop
    LieModule.IsIrreducible K L M := by
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible K I M
  letI := idealInflationLieRingModule (M := M) I J hIJ htop
  apply LieModule.IsIrreducible.mk
  intro S hS
  let T : LieSubmodule K I M :=
    { S.toSubmodule with
      lie_mem := by
        intro x m hm
        have h := S.lie_mem (x := (x : L)) hm
        change ⁅complementaryIdealProjection I J hIJ htop (x : L), m⁆ ∈ S at h
        simpa only [complementaryIdealProjection_left] using h }
  have hT : T ≠ ⊥ := by
    intro he
    apply hS
    apply LieSubmodule.toSubmodule_injective
    exact congrArg (fun Q : LieSubmodule K I M => Q.toSubmodule) he
  have he : T = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top T).resolve_left hT
  apply LieSubmodule.toSubmodule_injective
  exact congrArg (fun Q : LieSubmodule K I M => Q.toSubmodule) he

end Inflation

section EvaluationActions

variable {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)
  {U : Type*} [AddCommGroup U] [Module K U] [LieRingModule I U] [LieModule K I U]

/-- The multiplicity factor carries the actual commuting-ideal action,
inflated to the full ambient algebra through its complementary projection. -/
def multiplicityAmbientLieRingModule : LieRingModule L (U →ₗ⁅K,I⁆ W) := by
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  exact idealInflationLieRingModule J I hIJ.symm (by simpa only [sup_comm] using htop)

omit [LieModule K I U] in
/-- The ambient multiplicity action is linear. -/
theorem multiplicityAmbientLieModule :
    letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
    LieModule K L (U →ₗ⁅K,I⁆ W) := by
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
  exact idealInflationLieModule J I hIJ.symm (by simpa only [sup_comm] using htop)

omit [LieModule K I U] in
/-- The actual ambient multiplicity action evaluates by postcomposition. -/
theorem multiplicityAmbient_action_apply (x : L) (f : U →ₗ⁅K,I⁆ W) (u : U) :
    letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
    (⁅x, f⁆ : U →ₗ⁅K,I⁆ W) u =
      ⁅(complementaryIdealProjection J I hIJ.symm
        (by simpa only [sup_comm] using htop) x : L), f u⁆ := rfl

omit [LieModule K I U] in
/-- The first ideal acts trivially on the actual ambient multiplicity factor. -/
theorem multiplicityAmbient_first_trivial :
    letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
    LieModule.IsTrivial I (U →ₗ⁅K,I⁆ W) := by
  letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
  constructor
  intro x f
  apply LieModuleHom.ext
  intro u
  change ⁅(complementaryIdealProjection J I hIJ.symm
    (by simpa only [sup_comm] using htop) (x : L) : L), f u⁆ = 0
  rw [complementaryIdealProjection_right]
  exact zero_lie _

/-- The actual multiplicity factor is irreducible for its inflated ambient
action, as well as for its original commuting-ideal action. -/
theorem multiplicityAmbient_irreducible [IsAlgClosed K] [Module.Finite K U]
    [LieModule.IsIrreducible K I U] [LieModule.IsIrreducible K L W]
    (hne : ∃ f : U →ₗ⁅K,I⁆ W, f ≠ 0) :
    letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
    LieModule.IsIrreducible K L (U →ₗ⁅K,I⁆ W) := by
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  letI := commutingIdealHom_irreducible I J hIJ htop hne
  exact idealInflation_irreducible J I hIJ.symm (by simpa only [sup_comm] using htop)

/-- Actual evaluation intertwines the full ambient action with the standard
diagonal tensor action on the two inflated factors. -/
def ambientTensorEvaluationLieHom :
    letI := idealInflationLieRingModule (M := U) I J hIJ htop
    letI := idealInflationLieModule (M := U) I J hIJ htop
    letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
    letI := multiplicityAmbientLieModule (U := U) (W := W) I J hIJ htop
    U ⊗[K] (U →ₗ⁅K,I⁆ W) →ₗ⁅K,L⁆ W := by
  letI := idealInflationLieRingModule (M := U) I J hIJ htop
  letI := idealInflationLieModule (M := U) I J hIJ htop
  letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
  letI := multiplicityAmbientLieModule (U := U) (W := W) I J hIJ htop
  refine { toLinearMap := lieHomEvaluation, map_lie' := ?_ }
  intro x z
  change lieHomEvaluation ⁅x, z⁆ = ⁅x, lieHomEvaluation z⁆
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u f =>
    change f ⁅complementaryIdealProjection I J hIJ htop x, u⁆ +
      ⁅(complementaryIdealProjection J I hIJ.symm
        (by simpa only [sup_comm] using htop) x : L), f u⁆ = ⁅x, f u⁆
    rw [f.map_lie]
    change ⁅(complementaryIdealProjection I J hIJ htop x : L), f u⁆ + _ = _
    rw [← add_lie, complementaryIdealProjection_add]
  | add z t hz ht => simp only [lie_add, map_add, hz, ht]

/-- Canonical evaluation is an equivalence for the full ambient Lie action;
the factor actions are derived from the actual complementary ideals. -/
def ambientTensorEvaluationLieEquiv [IsAlgClosed K] [Module.Finite K U]
    [LieModule.IsIrreducible K I U] [LieModule.IsIrreducible K L W]
    (hne : ∃ f : U →ₗ⁅K,I⁆ W, f ≠ 0) :
    letI := idealInflationLieRingModule (M := U) I J hIJ htop
    letI := idealInflationLieModule (M := U) I J hIJ htop
    letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
    letI := multiplicityAmbientLieModule (U := U) (W := W) I J hIJ htop
    U ⊗[K] (U →ₗ⁅K,I⁆ W) ≃ₗ⁅K,L⁆ W := by
  letI := idealInflationLieRingModule (M := U) I J hIJ htop
  letI := idealInflationLieModule (M := U) I J hIJ htop
  letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
  letI := multiplicityAmbientLieModule (U := U) (W := W) I J hIJ htop
  exact { ambientTensorEvaluationLieHom I J hIJ htop,
    commutingIdealEvaluationEquiv I J hIJ htop hne with }

/-- The ambient equivariant tensor factorization remains literal evaluation
on pure tensors. -/
@[simp] theorem ambientTensorEvaluationLieEquiv_tmul [IsAlgClosed K] [Module.Finite K U]
    [LieModule.IsIrreducible K I U] [LieModule.IsIrreducible K L W]
    (hne : ∃ f : U →ₗ⁅K,I⁆ W, f ≠ 0) (u : U) (f : U →ₗ⁅K,I⁆ W) :
    letI := idealInflationLieRingModule (M := U) I J hIJ htop
    letI := idealInflationLieModule (M := U) I J hIJ htop
    letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
    letI := multiplicityAmbientLieModule (U := U) (W := W) I J hIJ htop
    ambientTensorEvaluationLieEquiv I J hIJ htop hne (u ⊗ₜ[K] f) = f u := rfl

end EvaluationActions

section ActualAmbientFactorization

variable {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

/-- The actual atomic-submodule choice yields an equivariant tensor
factorization for the full ambient algebra. Its actions and evaluation
equivalence are constructed from the original representation. -/
theorem exists_atomic_ambient_tensor_factorization
    [IsAlgClosed K] [Module.Finite K W] [LieModule.IsIrreducible K L W]
    (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤) :
    ∃ S : LieSubmodule K I W, IsAtom S ∧ LieModule.IsIrreducible K I S ∧
      letI : LieRingModule I S := inferInstance
      letI : LieModule K I S := inferInstance
      letI := idealInflationLieRingModule (M := S) I J hIJ htop
      letI := idealInflationLieModule (M := S) I J hIJ htop
      letI := multiplicityAmbientLieRingModule (U := S) (W := W) I J hIJ htop
      letI := multiplicityAmbientLieModule (U := S) (W := W) I J hIJ htop
      Nonempty (S ⊗[K] (S →ₗ⁅K,I⁆ W) ≃ₗ⁅K,L⁆ W) := by
  obtain ⟨S, hS, hIrred, hbij⟩ :=
    exists_atomic_evaluation_factorization (W := W) I J hIJ htop
  refine ⟨S, hS, hIrred, ?_⟩
  letI : LieRingModule I S := inferInstance
  letI : LieModule K I S := inferInstance
  letI := idealInflationLieRingModule (M := S) I J hIJ htop
  letI := idealInflationLieModule (M := S) I J hIJ htop
  letI := multiplicityAmbientLieRingModule (U := S) (W := W) I J hIJ htop
  letI := multiplicityAmbientLieModule (U := S) (W := W) I J hIJ htop
  exact ⟨{ ambientTensorEvaluationLieHom I J hIJ htop,
    LinearEquiv.ofBijective lieHomEvaluation hbij with }⟩

end ActualAmbientFactorization

end

end CubicAnomaly.Classification.TensorFactorActions
