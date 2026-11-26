import CubicAnomaly.Classification.UnitaryModuleBridge
import CubicAnomaly.Classification.SelfDualQuotientObstruction
import CubicAnomaly.Classification.TraceZeroEndKilling

/-!
# Actual scalar, isotropy, and complement blocks in defining endomorphisms

The actual special-unitary complexification supplies the trace-zero part
of every defining endomorphism. The original compact orthogonal splitting
then separates that part into the actual isotropy and actual complement.
All inclusions, projections, and retractions are constructed explicitly.
-/

namespace CubicAnomaly.Classification.UnitaryEndDecomposition

open Module LieModule Submodule
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.UnitaryDefining
open CubicAnomaly.Classification.UnitaryComplexification
open CubicAnomaly.Classification.UnitaryModuleBridge
open CubicAnomaly.Classification.SelfDualQuotientObstruction
open scoped TensorProduct

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] [Nontrivial W]

variable (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))

local instance : LieRingModule (ℂ ⊗[ℝ] h) W :=
  complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)

local instance : LieModule ℂ (ℂ ⊗[ℝ] h) W :=
  complexified_defining_lieModule (specialUnitaryDefiningRepresentation h)

/-- The actual scalar operators, with the trivial isotropy action. -/
def scalarInsertion :
    TrivialLieModule ℂ (ℂ ⊗[ℝ] h) ℂ →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W where
  toLinearMap := (TrivialLieModule.equiv ℂ (ℂ ⊗[ℝ] h) ℂ).toLinearMap.smulRight 1
  map_lie' := by
    intro x c
    change (TrivialLieModule.equiv ℂ (ℂ ⊗[ℝ] h) ℂ ⁅x, c⁆) • (1 : Module.End ℂ W) =
      ⁅x, (TrivialLieModule.equiv ℂ (ℂ ⊗[ℝ] h) ℂ c) • (1 : Module.End ℂ W)⁆
    rw [trivial_lie_zero, map_zero, zero_smul]
    ext w
    change 0 = ⁅x, (show ℂ from c) • w⁆ - (show ℂ from c) • ⁅x, w⁆
    rw [lie_smul, sub_self]

/-- Normalized trace is the actual equivariant scalar projection. -/
def scalarProjection :
    Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ TrivialLieModule ℂ (ℂ ⊗[ℝ] h) ℂ where
  toLinearMap := (TrivialLieModule.equiv ℂ (ℂ ⊗[ℝ] h) ℂ).symm.toLinearMap.comp
    ((finrank ℂ W : ℂ)⁻¹ • LinearMap.trace ℂ W)
  map_lie' := by
    intro x A
    change (finrank ℂ W : ℂ)⁻¹ *
      LinearMap.trace ℂ W (toEnd ℂ (ℂ ⊗[ℝ] h) W x * A -
        A * toEnd ℂ (ℂ ⊗[ℝ] h) W x) = 0
    rw [map_sub, LinearMap.trace_mul_comm, sub_self, mul_zero]

/-- Removing its normalized scalar part is equivariant. -/
def traceZeroPart : Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W :=
  LieModuleHom.id - (scalarInsertion h).comp (scalarProjection h)

private theorem trace_zero_part_trace (A : Module.End ℂ W) :
    LinearMap.trace ℂ W (traceZeroPart h A) = 0 := by
  have hn : (finrank ℂ W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  change LinearMap.trace ℂ W (A -
    ((finrank ℂ W : ℂ)⁻¹ * LinearMap.trace ℂ W A) • 1) = 0
  simp only [map_sub, map_smul, LinearMap.trace_one, smul_eq_mul]
  field_simp
  ring

/-- The actual trace-zero part lifted into the original ambient complexification. -/
def traceZeroLift : Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆
    (ℂ ⊗[ℝ] specialUnitaryAlgebra W) :=
  liftTraceZeroEquivariant h (traceZeroPart h) (trace_zero_part_trace h)

/-- The actual complexified isotropy action, as an equivariant inclusion. -/
def isotropyInsertion :
    (ℂ ⊗[ℝ] h) →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W :=
  (specialUnitaryAmbientOperatorMap h).comp (complexifiedHom h.toLieSubmodule.incl)

/-- The actual compact complement acts by its literal defining operators. -/
def complementInsertion (B : CompactForm (specialUnitaryAlgebra W)) :
    (ℂ ⊗[ℝ] orthogonalComplement B h) →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W :=
  (specialUnitaryAmbientOperatorMap h).comp
    (complexifiedHom (orthogonalComplement B h).incl)

/-- The original compact orthogonal isotropy projection after taking trace zero. -/
def isotropyProjection (B : CompactForm (specialUnitaryAlgebra W)) :
    Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] h) :=
  (complexifiedHom (invariantProjection h.toLieSubmodule (orthogonalComplement B h)
    (compact_orthogonal_complement_isCompl B h))).comp (traceZeroLift h)

/-- The original compact orthogonal complement projection after taking trace zero. -/
def complementProjection (B : CompactForm (specialUnitaryAlgebra W)) :
    Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] orthogonalComplement B h) :=
  (complexifiedComplementProjection B h).comp (traceZeroLift h)

/-- The scalar inclusion has its literal normalized-trace retraction. -/
theorem scalar_projection_insertion :
    (scalarProjection h).comp (scalarInsertion h) = LieModuleHom.id := by
  ext c
  change (finrank ℂ W : ℂ)⁻¹ * LinearMap.trace ℂ W ((show ℂ from c) • 1) =
    (show ℂ from c)
  have hn : (finrank ℂ W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [map_smul, LinearMap.trace_one]
  change (finrank ℂ W : ℂ)⁻¹ * ((show ℂ from c) * (finrank ℂ W : ℂ)) =
    (show ℂ from c)
  field_simp

private theorem trace_zero_lift_ambient (z : ℂ ⊗[ℝ] specialUnitaryAlgebra W) :
    traceZeroLift h (specialUnitaryAmbientOperatorMap h z) = z := by
  apply special_unitary_ambient_operator_map_injective h
  rw [traceZeroLift, lift_trace_zero_equivariant_operator]
  have ht : LinearMap.trace ℂ W (specialUnitaryAmbientOperatorMap h z) = 0 :=
    (specialUnitaryComplexificationEquiv z).property
  change specialUnitaryAmbientOperatorMap h z -
    ((finrank ℂ W : ℂ)⁻¹ * LinearMap.trace ℂ W (specialUnitaryAmbientOperatorMap h z)) • 1 = _
  rw [ht, mul_zero, zero_smul, sub_zero]

/-- The actual isotropy inclusion has its original compact retraction. -/
theorem isotropy_projection_insertion (B : CompactForm (specialUnitaryAlgebra W)) :
    (isotropyProjection h B).comp (isotropyInsertion h) = LieModuleHom.id := by
  ext x
  change complexifiedHom (invariantProjection h.toLieSubmodule (orthogonalComplement B h)
      (compact_orthogonal_complement_isCompl B h))
    (traceZeroLift h (specialUnitaryAmbientOperatorMap h
      (complexifiedHom h.toLieSubmodule.incl x))) = x
  rw [trace_zero_lift_ambient]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change a ⊗ₜ[ℝ] ((invariantProjection h.toLieSubmodule (orthogonalComplement B h)
      (compact_orthogonal_complement_isCompl B h)) x.val) = a ⊗ₜ[ℝ] x
    rw [show (invariantProjection h.toLieSubmodule (orthogonalComplement B h)
      (compact_orthogonal_complement_isCompl B h)) x.val = x from
      Submodule.linearProjOfIsCompl_apply_left _ x]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual complement inclusion has its original compact retraction. -/
theorem complement_projection_insertion (B : CompactForm (specialUnitaryAlgebra W)) :
    (complementProjection h B).comp (complementInsertion h B) = LieModuleHom.id := by
  ext x
  change complexifiedComplementProjection B h
    (traceZeroLift h (specialUnitaryAmbientOperatorMap h
      (complexifiedHom (orthogonalComplement B h).incl x))) = x
  rw [trace_zero_lift_ambient]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change a ⊗ₜ[ℝ] ((invariantProjection (orthogonalComplement B h) h.toLieSubmodule
      (compact_orthogonal_complement_isCompl B h).symm) x.val) = a ⊗ₜ[ℝ] x
    rw [show (invariantProjection (orthogonalComplement B h) h.toLieSubmodule
      (compact_orthogonal_complement_isCompl B h).symm) x.val = x from
      Submodule.linearProjOfIsCompl_apply_left _ x]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Nontrivial W] in
set_option maxHeartbeats 1000000 in
private theorem ambient_projection_sum (B : CompactForm (specialUnitaryAlgebra W))
    (z : ℂ ⊗[ℝ] specialUnitaryAlgebra W) :
    complexifiedHom h.toLieSubmodule.incl
        (complexifiedHom (invariantProjection h.toLieSubmodule (orthogonalComplement B h)
          (compact_orthogonal_complement_isCompl B h)) z) +
      complexifiedHom (orthogonalComplement B h).incl
        (complexifiedComplementProjection B h z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
    change a ⊗ₜ[ℝ] ((compact_orthogonal_complement_isCompl B h).projection z) +
      a ⊗ₜ[ℝ] ((compact_orthogonal_complement_isCompl B h).symm.projection z) = a ⊗ₜ[ℝ] z
    rw [← TensorProduct.tmul_add, Submodule.IsCompl.projection_add_projection_eq_self]
  | add z w hz hw => simp only [map_add]; rw [add_add_add_comm, hz, hw]

set_option maxHeartbeats 1000000 in
/-- Every actual defining operator is exactly its scalar, isotropy, and
compact-complement parts. -/
theorem scalar_isotropy_complement_sum (B : CompactForm (specialUnitaryAlgebra W))
    (A : Module.End ℂ W) :
    scalarInsertion h (scalarProjection h A) +
      isotropyInsertion h (isotropyProjection h B A) +
      complementInsertion h B (complementProjection h B A) = A := by
  have hs := congrArg (specialUnitaryAmbientOperatorMap h)
    (ambient_projection_sum h B (traceZeroLift h A))
  rw [map_add] at hs
  have ht : specialUnitaryAmbientOperatorMap h (traceZeroLift h A) = traceZeroPart h A :=
    lift_trace_zero_equivariant_operator h (traceZeroPart h) (trace_zero_part_trace h) A
  rw [ht] at hs
  change isotropyInsertion h (isotropyProjection h B A) +
      complementInsertion h B (complementProjection h B A) =
    A - scalarInsertion h (scalarProjection h A) at hs
  rw [add_assoc, hs, add_sub_cancel]

end

end CubicAnomaly.Classification.UnitaryEndDecomposition
