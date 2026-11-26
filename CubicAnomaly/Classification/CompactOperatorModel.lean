import CubicAnomaly.Classification.ClassicalModuleBridge
import CubicAnomaly.Classification.SelfDualQuotientObstruction

/-!
# Actual compact ambient form-preserver models

This interface records an actual faithful ambient operator map, its exact
form-preserving range, and its literal isotropy inclusion. The orthogonal
and symplectic models are constructed from the already proved actual
complexification equivalences. Equivariant form-preserving operators can
then be lifted uniformly without introducing a classification witness.
-/

namespace CubicAnomaly.Classification.CompactOperatorModel

open Module LieModule
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.ClassicalModuleBridge
open CubicAnomaly.Classification.SelfDualQuotientObstruction
open CubicAnomaly.Classification.OrthogonalDefining
open CubicAnomaly.Classification.OrthogonalComplexification
open CubicAnomaly.Classification.SymplecticGeometry
open CubicAnomaly.Classification.SymplecticDefining
open CubicAnomaly.Classification.SymplecticForm
open CubicAnomaly.Classification.SymplecticComplexification
open CubicAnomaly.Classification.ComplexDefining
open scoped TensorProduct

noncomputable section

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]
  (h : LieSubalgebra ℝ g)
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  [LieRingModule (ℂ ⊗[ℝ] h) W] [LieModule ℂ (ℂ ⊗[ℝ] h) W]

/-- An exact operator realization of the original complexified ambient
algebra, retaining the actual isotropy action and actual bilinear form. -/
structure Model (Φ : LinearMap.BilinForm ℂ W) where
  operatorMap : (ℂ ⊗[ℝ] g) →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W
  injective : Function.Injective operatorMap
  range_iff : ∀ A, A ∈ operatorMap.range ↔ A ∈ skewAdjointLieSubalgebra Φ
  inclusion : ∀ x, operatorMap (complexifiedLieHom h.incl x) = toEnd ℂ (ℂ ⊗[ℝ] h) W x

variable {h} {Φ : LinearMap.BilinForm ℂ W}

/-- Lift actual equivariant form-preserving operators through the
constructed ambient realization. -/
def Model.lift (A : Model h Φ)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W)
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra Φ) :
    S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] g) :=
  (equivariantRangeEquiv A.operatorMap A.injective).symm.toLieModuleHom.comp
    (f.codRestrict A.operatorMap.range (fun s => (A.range_iff (f s)).mpr (hf s)))

/-- The lift retains the literal operator, rather than only its
isomorphism class or character. -/
@[simp] theorem Model.lift_operator (A : Model h Φ)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W)
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra Φ) (s : S) :
    A.operatorMap (A.lift f hf s) = f s := by
  exact congrArg Subtype.val
    ((equivariantRangeEquiv A.operatorMap A.injective).apply_symm_apply
      (⟨f s, (A.range_iff (f s)).mpr (hf s)⟩ : A.operatorMap.range))

/-- Faithfulness of a form-preserving operator block survives its lift
to the actual ambient complexification. -/
theorem Model.lift_injective (A : Model h Φ)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (f : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W)
    (hf : ∀ s, f s ∈ skewAdjointLieSubalgebra Φ) (hinj : Function.Injective f) :
    Function.Injective (A.lift f hf) := by
  intro s t hst
  apply hinj
  have he := congrArg A.operatorMap hst
  simpa only [Model.lift_operator] using he

/-- Actual isotropy membership is equivalent to membership of the
literal ambient operator in the actual defining action image. -/
theorem Model.mem_isotropy_iff (A : Model h Φ) (z : ℂ ⊗[ℝ] g) :
    z ∈ h.toSubmodule.baseChange ℂ ↔
      A.operatorMap z ∈ (toEnd ℂ (ℂ ⊗[ℝ] h) W).range := by
  change z ∈ complexifiedSubalgebra h ↔ _
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (A.inclusion x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, A.injective ?_⟩
    exact (A.inclusion x).trans hx

/-- The orthogonal operator model is supplied by the actual scalar
extension of the real defining representation. -/
def orthogonalModel
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (h : LieSubalgebra ℝ (orthogonalAlgebra V)) :
    Model h (orthogonalExtendedForm (W := V)) where
  operatorMap := orthogonalAmbientOperatorMap h
  injective := orthogonal_ambient_operator_map_injective h
  range_iff A := by
    constructor
    · rintro ⟨z, rfl⟩
      exact (orthogonalComplexificationEquiv z).property
    · intro hA
      refine ⟨orthogonalComplexificationEquiv.symm ⟨A, hA⟩, ?_⟩
      exact congrArg Subtype.val
        (orthogonalComplexificationEquiv.apply_symm_apply ⟨A, hA⟩)
  inclusion := orthogonal_ambient_operator_map_inclusion h

/-- The symplectic model preserves the original quaternionic form and
the original complexified defining action. -/
def symplecticModel
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (Q : QuaternionicStructure V)
    (h : LieSubalgebra ℝ (symplecticAlgebra Q)) :
    letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
    letI := complexified_defining_lieModule (symplecticDefiningRepresentation Q h)
    Model h (quaternionicForm Q) := by
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
  letI := complexified_defining_lieModule (symplecticDefiningRepresentation Q h)
  refine {
    operatorMap := symplecticAmbientOperatorMap Q h
    injective := symplectic_ambient_operator_map_injective Q h
    inclusion := symplectic_ambient_operator_map_inclusion Q h
    range_iff := ?_ }
  intro A
  constructor
  · rintro ⟨z, rfl⟩
    exact (symplecticComplexificationEquiv Q z).property
  · intro hA
    refine ⟨(symplecticComplexificationEquiv Q).symm ⟨A, hA⟩, ?_⟩
    exact congrArg Subtype.val
      ((symplecticComplexificationEquiv Q).apply_symm_apply ⟨A, hA⟩)

end

end CubicAnomaly.Classification.CompactOperatorModel
