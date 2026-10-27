import CubicAnomaly.Classification.UnitaryDefining
import CubicAnomaly.Classification.UnitaryComplexification
import CubicAnomaly.Classification.CompactGeometry

/-!
# The actual special-unitary ambient module inside defining endomorphisms

The complexified defining inclusion is equivariant for the actual isotropy
action. Its range is precisely the trace-zero endomorphisms, and its
restriction to the actual isotropy inclusion is the actual defining action.
Thus a trace-zero equivariant map can be lifted to the original ambient
complexification without supplying an intertwining or identification witness.
-/

namespace CubicAnomaly.Classification.UnitaryModuleBridge

open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.UnitaryDefining
open CubicAnomaly.Classification.UnitaryComplexification
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open scoped TensorProduct

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- Scalar extension of the defining inclusion agrees with the defining
representation after the literal complexified isotropy inclusion. -/
theorem special_unitary_complexified_inclusion_natural
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W)) (x : ℂ ⊗[ℝ] h) :
    complexifyEndRepresentation (specialUnitaryAlgebra W).incl
        (complexifiedLieHom h.incl x) =
      complexifyEndRepresentation (specialUnitaryDefiningRepresentation h) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))

local instance : LieRingModule (ℂ ⊗[ℝ] h) W :=
  complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)

local instance : LieModule ℂ (ℂ ⊗[ℝ] h) W :=
  complexified_defining_lieModule (specialUnitaryDefiningRepresentation h)

/-- The actual ambient complexification acts faithfully on the same
defining space, equivariantly for the actual isotropy action. -/
def specialUnitaryAmbientOperatorMap :
    (ℂ ⊗[ℝ] specialUnitaryAlgebra W) →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W where
  __ := (complexifyEndRepresentation (specialUnitaryAlgebra W).incl).toLinearMap
  map_lie' := by
    intro x y
    change complexifyEndRepresentation (specialUnitaryAlgebra W).incl ⁅x, y⁆ = _
    rw [← complexifiedLieHom_inclusion_action h x y, LieHom.map_lie,
      special_unitary_complexified_inclusion_natural]
    ext w
    rfl

/-- The ambient operator map is the literal defining scalar extension. -/
theorem special_unitary_ambient_operator_map_apply
    (x : ℂ ⊗[ℝ] specialUnitaryAlgebra W) :
    specialUnitaryAmbientOperatorMap h x =
      complexifyEndRepresentation (specialUnitaryAlgebra W).incl x := rfl

/-- No ambient vector is lost by its actual defining action. -/
theorem special_unitary_ambient_operator_map_injective :
    Function.Injective (specialUnitaryAmbientOperatorMap h) :=
  complexify_skew_map_injective (specialUnitaryAlgebra W).incl.toLinearMap
    Subtype.val_injective (fun x => x.property.1)

/-- The original complexified isotropy inclusion maps to its actual
defining action operator. -/
theorem special_unitary_ambient_operator_map_inclusion (x : ℂ ⊗[ℝ] h) :
    specialUnitaryAmbientOperatorMap h (complexifiedLieHom h.incl x) =
      LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) W x :=
  special_unitary_complexified_inclusion_natural h x

/-- The actual complexified defining isotropy action is faithful. -/
theorem special_unitary_complexified_defining_faithful :
    LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) W := by
  apply (LieModule.isFaithful_iff ℂ (ℂ ⊗[ℝ] h) W).mpr
  exact complexify_skew_map_injective (specialUnitaryDefiningRepresentation h).toLinearMap
    (fun x y he => Subtype.ext (Subtype.ext he)) (fun x => x.val.property.1)

/-- A trace-zero equivariant endomorphism map lifts to the actual ambient
complexification through its constructed special-unitary equivalence. -/
def liftTraceZeroEquivariant
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W)
    (hf : ∀ s, LinearMap.trace ℂ W (f s) = 0) :
    S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] specialUnitaryAlgebra W) where
  __ := specialUnitaryComplexificationEquiv.symm.toLinearEquiv.toLinearMap.comp
    (f.toLinearMap.codRestrict (specialLinearEnd W).toSubmodule hf)
  map_lie' := by
    intro x s
    apply special_unitary_ambient_operator_map_injective h
    change specialUnitaryAmbientOperatorMap h
      (specialUnitaryComplexificationEquiv.symm ⟨f ⁅x, s⁆, hf _⟩) = _
    rw [(specialUnitaryAmbientOperatorMap h).map_lie]
    have he (t : S) : specialUnitaryAmbientOperatorMap h
        (specialUnitaryComplexificationEquiv.symm ⟨f t, hf t⟩) = f t := by
      exact congrArg Subtype.val
        (specialUnitaryComplexificationEquiv.apply_symm_apply ⟨f t, hf t⟩)
    change specialUnitaryAmbientOperatorMap h
      (specialUnitaryComplexificationEquiv.symm ⟨f ⁅x, s⁆, hf _⟩) =
      ⁅x, specialUnitaryAmbientOperatorMap h
        (specialUnitaryComplexificationEquiv.symm ⟨f s, hf s⟩)⁆
    rw [he, he, f.map_lie]

/-- Lifting preserves the actual defining endomorphism exactly. -/
theorem lift_trace_zero_equivariant_operator
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W)
    (hf : ∀ s, LinearMap.trace ℂ W (f s) = 0) (s : S) :
    specialUnitaryAmbientOperatorMap h (liftTraceZeroEquivariant h f hf s) = f s :=
  congrArg Subtype.val (specialUnitaryComplexificationEquiv.apply_symm_apply ⟨f s, hf s⟩)

/-- Absorption of the actual lifted map into the isotropy implies
containment of the original operators in the actual isotropy action. -/
theorem lift_trace_zero_range_le_action_range
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W)
    (hf : ∀ s, LinearMap.trace ℂ W (f s) = 0)
    (habs : (liftTraceZeroEquivariant h f hf).range.toSubmodule ≤
      h.toSubmodule.baseChange ℂ) :
    f.range.toSubmodule ≤ (LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) W).range.toSubmodule := by
  rintro z ⟨s, rfl⟩
  have hs := habs (show liftTraceZeroEquivariant h f hf s ∈
    (liftTraceZeroEquivariant h f hf).range.toSubmodule from ⟨s, rfl⟩)
  change liftTraceZeroEquivariant h f hf s ∈ complexifiedSubalgebra h at hs
  obtain ⟨x, hx⟩ := (LieHom.mem_range (complexifiedLieHom h.incl) _).mp hs
  refine ⟨x, ?_⟩
  calc
    LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) W x =
        specialUnitaryAmbientOperatorMap h (complexifiedLieHom h.incl x) :=
      (special_unitary_ambient_operator_map_inclusion h x).symm
    _ = specialUnitaryAmbientOperatorMap h (liftTraceZeroEquivariant h f hf s) :=
      congrArg _ hx
    _ = f s := lift_trace_zero_equivariant_operator h f hf s

end

end CubicAnomaly.Classification.UnitaryModuleBridge
