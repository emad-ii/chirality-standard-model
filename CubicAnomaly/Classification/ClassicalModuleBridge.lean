import CubicAnomaly.Classification.OrthogonalComplexification
import CubicAnomaly.Classification.SymplecticComplexification
import CubicAnomaly.Classification.CompactGeometry

/-!
# Actual orthogonal and symplectic ambient modules in endomorphisms

The actual complexified defining actions identify the orthogonal and
symplectic ambient algebras with the operators preserving their defining
bilinear forms.  These identifications are equivariant for the original
complexified isotropy actions and retain the literal isotropy inclusions.
Consequently every equivariant map taking values in the relevant form
preserver lifts to the original ambient complexification.
-/

namespace CubicAnomaly.Classification.ClassicalModuleBridge

open CubicAnomaly.Classification.OrthogonalDefining
open CubicAnomaly.Classification.OrthogonalComplexification
open CubicAnomaly.Classification.SymplecticGeometry
open CubicAnomaly.Classification.SymplecticDefining
open CubicAnomaly.Classification.SymplecticForm
open CubicAnomaly.Classification.SymplecticComplexification
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open scoped TensorProduct

noncomputable section

section Orthogonal

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The actual scalar-extended orthogonal action restricts to the actual
scalar-extended defining action of the isotropy. -/
theorem orthogonal_complexified_inclusion_natural
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) (x : ℂ ⊗[ℝ] h) :
    LieModule.toEnd ℂ (ℂ ⊗[ℝ] orthogonalAlgebra W) (ℂ ⊗[ℝ] W)
        (complexifiedLieHom h.incl x) =
      LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    apply TensorProduct.AlgebraTensorModule.ext
    intro b w
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (h : LieSubalgebra ℝ (orthogonalAlgebra W))

/-- The actual orthogonal ambient action is an equivariant map into the
endomorphisms of the actual scalar-extended real defining space. -/
def orthogonalAmbientOperatorMap :
    (ℂ ⊗[ℝ] orthogonalAlgebra W) →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆
      Module.End ℂ (ℂ ⊗[ℝ] W) where
  __ := (LieModule.toEnd ℂ (ℂ ⊗[ℝ] orthogonalAlgebra W) (ℂ ⊗[ℝ] W)).toLinearMap
  map_lie' := by
    intro x y
    change LieModule.toEnd ℂ (ℂ ⊗[ℝ] orthogonalAlgebra W) (ℂ ⊗[ℝ] W) ⁅x, y⁆ = _
    rw [← complexifiedLieHom_inclusion_action h x y, LieHom.map_lie,
      orthogonal_complexified_inclusion_natural]
    ext w
    rfl

/-- The orthogonal ambient map is the literal scalar-extended defining action. -/
theorem orthogonal_ambient_operator_map_apply (x : ℂ ⊗[ℝ] orthogonalAlgebra W) :
    orthogonalAmbientOperatorMap h x =
      LieModule.toEnd ℂ (ℂ ⊗[ℝ] orthogonalAlgebra W) (ℂ ⊗[ℝ] W) x := rfl

/-- The actual orthogonal ambient defining action is injective. -/
theorem orthogonal_ambient_operator_map_injective :
    Function.Injective (orthogonalAmbientOperatorMap h) := by
  intro x y he
  apply orthogonal_complexification_injective
  exact Subtype.ext he

/-- The original complexified orthogonal isotropy inclusion maps to its
actual defining action operator. -/
theorem orthogonal_ambient_operator_map_inclusion (x : ℂ ⊗[ℝ] h) :
    orthogonalAmbientOperatorMap h (complexifiedLieHom h.incl x) =
      LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) x :=
  orthogonal_complexified_inclusion_natural h x

/-- The actual complexified orthogonal defining isotropy action is faithful. -/
theorem orthogonal_complexified_defining_faithful :
    LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) := by
  apply (LieModule.isFaithful_iff ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W)).mpr
  intro x y he
  apply complexification_linearMap_injective h.incl.toLinearMap Subtype.val_injective
  apply orthogonal_ambient_operator_map_injective h
  change orthogonalAmbientOperatorMap h (complexifiedLieHom h.incl x) =
    orthogonalAmbientOperatorMap h (complexifiedLieHom h.incl y)
  rw [orthogonal_ambient_operator_map_inclusion,
    orthogonal_ambient_operator_map_inclusion, he]

/-- The actual extended inner product is invariant under the actual
complexified defining isotropy action. -/
theorem orthogonal_complexified_defining_form_invariant :
    (orthogonalExtendedForm (W := W)).lieInvariant (ℂ ⊗[ℝ] h) := by
  apply ComplexDuality.complexified_invariantForm_invariant (innerₗ W)
  intro x u v
  have hx := (LinearMap.mem_skewAdjointSubmodule (B := innerₗ W) x.val.val).mp
    x.val.property u v
  simpa only [Pi.neg_apply, map_neg] using hx

/-- An equivariant map preserving the actual extended inner product lifts
through the constructed equivalence to the actual orthogonal ambient algebra. -/
def liftOrthogonalEquivariant
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ (ℂ ⊗[ℝ] W))
    (hf : ∀ s, f s ∈ orthogonalExtendedAlgebra (W := W)) :
    S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] orthogonalAlgebra W) where
  __ := orthogonalComplexificationEquiv.symm.toLinearEquiv.toLinearMap.comp
    (f.toLinearMap.codRestrict (orthogonalExtendedAlgebra (W := W)).toSubmodule hf)
  map_lie' := by
    intro x s
    apply orthogonal_ambient_operator_map_injective h
    change orthogonalAmbientOperatorMap h
      (orthogonalComplexificationEquiv.symm ⟨f ⁅x, s⁆, hf _⟩) = _
    rw [(orthogonalAmbientOperatorMap h).map_lie]
    have he (t : S) : orthogonalAmbientOperatorMap h
        (orthogonalComplexificationEquiv.symm ⟨f t, hf t⟩) = f t := by
      exact congrArg Subtype.val
        (orthogonalComplexificationEquiv.apply_symm_apply ⟨f t, hf t⟩)
    change orthogonalAmbientOperatorMap h
      (orthogonalComplexificationEquiv.symm ⟨f ⁅x, s⁆, hf _⟩) =
      ⁅x, orthogonalAmbientOperatorMap h
        (orthogonalComplexificationEquiv.symm ⟨f s, hf s⟩)⁆
    rw [he, he, f.map_lie]

/-- Lifting to the orthogonal ambient algebra preserves the actual operator. -/
theorem lift_orthogonal_equivariant_operator
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ (ℂ ⊗[ℝ] W))
    (hf : ∀ s, f s ∈ orthogonalExtendedAlgebra (W := W)) (s : S) :
    orthogonalAmbientOperatorMap h (liftOrthogonalEquivariant h f hf s) = f s :=
  congrArg Subtype.val (orthogonalComplexificationEquiv.apply_symm_apply ⟨f s, hf s⟩)

/-- Absorption of the orthogonal lift into the original isotropy implies
containment of the original operators in the actual defining isotropy action. -/
theorem lift_orthogonal_range_le_action_range
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ (ℂ ⊗[ℝ] W))
    (hf : ∀ s, f s ∈ orthogonalExtendedAlgebra (W := W))
    (habs : (liftOrthogonalEquivariant h f hf).range.toSubmodule ≤
      h.toSubmodule.baseChange ℂ) :
    f.range.toSubmodule ≤
      (LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W)).range.toSubmodule := by
  rintro z ⟨s, rfl⟩
  have hs := habs (show liftOrthogonalEquivariant h f hf s ∈
    (liftOrthogonalEquivariant h f hf).range.toSubmodule from ⟨s, rfl⟩)
  change liftOrthogonalEquivariant h f hf s ∈ complexifiedSubalgebra h at hs
  obtain ⟨x, hx⟩ := (LieHom.mem_range (complexifiedLieHom h.incl) _).mp hs
  refine ⟨x, ?_⟩
  calc
    LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) x =
        orthogonalAmbientOperatorMap h (complexifiedLieHom h.incl x) :=
      (orthogonal_ambient_operator_map_inclusion h x).symm
    _ = orthogonalAmbientOperatorMap h (liftOrthogonalEquivariant h f hf s) :=
      congrArg _ hx
    _ = f s := lift_orthogonal_equivariant_operator h f hf s

end Orthogonal

section Symplectic

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
/-- The scalar-extended symplectic defining inclusion agrees with the
actual defining isotropy representation after the literal inclusion. -/
theorem symplectic_complexified_inclusion_natural
    (J : QuaternionicStructure W) (h : LieSubalgebra ℝ (symplecticAlgebra J))
    (x : ℂ ⊗[ℝ] h) :
    complexifyEndRepresentation (symplecticAlgebra J).incl
        (complexifiedLieHom h.incl x) =
      complexifyEndRepresentation (symplecticDefiningRepresentation J h) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (J : QuaternionicStructure W) (h : LieSubalgebra ℝ (symplecticAlgebra J))

local instance : LieRingModule (ℂ ⊗[ℝ] h) W :=
  complexifiedDefiningAction (symplecticDefiningRepresentation J h)

local instance : LieModule ℂ (ℂ ⊗[ℝ] h) W :=
  complexified_defining_lieModule (symplecticDefiningRepresentation J h)

/-- The actual symplectic ambient defining action is equivariant for the
actual complexified isotropy action on the same defining complex space. -/
def symplecticAmbientOperatorMap :
    (ℂ ⊗[ℝ] symplecticAlgebra J) →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W where
  __ := (complexifyEndRepresentation (symplecticAlgebra J).incl).toLinearMap
  map_lie' := by
    intro x y
    change complexifyEndRepresentation (symplecticAlgebra J).incl ⁅x, y⁆ = _
    rw [← complexifiedLieHom_inclusion_action h x y, LieHom.map_lie,
      symplectic_complexified_inclusion_natural]
    ext w
    rfl

omit [FiniteDimensional ℂ W] in
/-- The symplectic ambient map is the literal scalar-extended defining inclusion. -/
theorem symplectic_ambient_operator_map_apply (x : ℂ ⊗[ℝ] symplecticAlgebra J) :
    symplecticAmbientOperatorMap J h x =
      complexifyEndRepresentation (symplecticAlgebra J).incl x := rfl

/-- The actual symplectic ambient defining action is injective. -/
theorem symplectic_ambient_operator_map_injective :
    Function.Injective (symplecticAmbientOperatorMap J h) := by
  intro x y he
  apply symplectic_complexification_injective J
  exact Subtype.ext he

omit [FiniteDimensional ℂ W] in
/-- The original complexified symplectic isotropy inclusion maps to its
actual defining action operator. -/
theorem symplectic_ambient_operator_map_inclusion (x : ℂ ⊗[ℝ] h) :
    symplecticAmbientOperatorMap J h (complexifiedLieHom h.incl x) =
      LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) W x :=
  symplectic_complexified_inclusion_natural J h x

/-- The actual complexified symplectic defining isotropy action is faithful. -/
theorem symplectic_complexified_defining_faithful :
    LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) W := by
  apply (LieModule.isFaithful_iff ℂ (ℂ ⊗[ℝ] h) W).mpr
  intro x y he
  apply complexification_linearMap_injective h.incl.toLinearMap Subtype.val_injective
  apply symplectic_ambient_operator_map_injective J h
  change symplecticAmbientOperatorMap J h (complexifiedLieHom h.incl x) =
    symplecticAmbientOperatorMap J h (complexifiedLieHom h.incl y)
  rw [symplectic_ambient_operator_map_inclusion,
    symplectic_ambient_operator_map_inclusion, he]

/-- An equivariant map preserving the actual quaternionic bilinear form
lifts through the constructed equivalence to the actual symplectic ambient algebra. -/
def liftSymplecticEquivariant
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W)
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra (quaternionicForm J)) :
    S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] symplecticAlgebra J) where
  __ := (symplecticComplexificationEquiv J).symm.toLinearEquiv.toLinearMap.comp
    (f.toLinearMap.codRestrict (skewAdjointLieSubalgebra (quaternionicForm J)).toSubmodule hf)
  map_lie' := by
    intro x s
    apply symplectic_ambient_operator_map_injective J h
    change symplecticAmbientOperatorMap J h
      ((symplecticComplexificationEquiv J).symm ⟨f ⁅x, s⁆, hf _⟩) = _
    rw [(symplecticAmbientOperatorMap J h).map_lie]
    have he (t : S) : symplecticAmbientOperatorMap J h
        ((symplecticComplexificationEquiv J).symm ⟨f t, hf t⟩) = f t := by
      exact congrArg Subtype.val
        ((symplecticComplexificationEquiv J).apply_symm_apply ⟨f t, hf t⟩)
    change symplecticAmbientOperatorMap J h
      ((symplecticComplexificationEquiv J).symm ⟨f ⁅x, s⁆, hf _⟩) =
      ⁅x, symplecticAmbientOperatorMap J h
        ((symplecticComplexificationEquiv J).symm ⟨f s, hf s⟩)⁆
    rw [he, he, f.map_lie]

/-- Lifting to the symplectic ambient algebra preserves the actual operator. -/
theorem lift_symplectic_equivariant_operator
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W)
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra (quaternionicForm J)) (s : S) :
    symplecticAmbientOperatorMap J h (liftSymplecticEquivariant J h f hf s) = f s :=
  congrArg Subtype.val ((symplecticComplexificationEquiv J).apply_symm_apply ⟨f s, hf s⟩)

/-- Absorption of the symplectic lift into the original isotropy implies
containment of the original operators in the actual defining isotropy action. -/
theorem lift_symplectic_range_le_action_range
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W)
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra (quaternionicForm J))
    (habs : (liftSymplecticEquivariant J h f hf).range.toSubmodule ≤
      h.toSubmodule.baseChange ℂ) :
    f.range.toSubmodule ≤ (LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) W).range.toSubmodule := by
  rintro z ⟨s, rfl⟩
  have hs := habs (show liftSymplecticEquivariant J h f hf s ∈
    (liftSymplecticEquivariant J h f hf).range.toSubmodule from ⟨s, rfl⟩)
  change liftSymplecticEquivariant J h f hf s ∈ complexifiedSubalgebra h at hs
  obtain ⟨x, hx⟩ := (LieHom.mem_range (complexifiedLieHom h.incl) _).mp hs
  refine ⟨x, ?_⟩
  calc
    LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) W x =
        symplecticAmbientOperatorMap J h (complexifiedLieHom h.incl x) :=
      (symplectic_ambient_operator_map_inclusion J h x).symm
    _ = symplecticAmbientOperatorMap J h (liftSymplecticEquivariant J h f hf s) :=
      congrArg _ hx
    _ = f s := lift_symplectic_equivariant_operator J h f hf s

end Symplectic

end

end CubicAnomaly.Classification.ClassicalModuleBridge
