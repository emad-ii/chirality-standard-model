import CubicAnomaly.Classification.ClassicalIsotropyFactors
import CubicAnomaly.Classification.TwoIdealTensorForms

/-!
# Actual tensor forms in the remaining classical two-factor branch

The original orthogonal and symplectic hypotheses give either simple
complexified isotropy or two disjoint simple isotropy ideals. In the
second case, actual evaluation constructs the defining tensor module,
faithful irreducible factor actions, and invariant nondegenerate reflexive
factor forms whose tensor product is the original defining form.

Thus neither the representation factorization nor its form factorization
is a remaining input witness. Excluding the resulting two-factor case is
a separate step and is not asserted here.
-/

namespace CubicAnomaly.Classification.ClassicalTwoFactorReduction

open LieAlgebra LieModule
open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.ComplexDuality
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.OrthogonalDefining
open CubicAnomaly.Classification.OrthogonalComplexification
open CubicAnomaly.Classification.SymplecticGeometry
open CubicAnomaly.Classification.SymplecticDefining
open CubicAnomaly.Classification.SymplecticForm
open CubicAnomaly.Classification.ClassicalModuleBridge
open CubicAnomaly.Classification.ClassicalIsotropyFactors
open CubicAnomaly.Classification.TwoIdealTensorForms

section Orthogonal

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

set_option maxHeartbeats 1000000 in
/-- The original orthogonal hypotheses derive every defining-module and
form witness in the possible two-ideal case, in arbitrary dimension. -/
theorem all_rank_orthogonal_isotropy_simple_or_actual_tensor_forms
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h) ∨
      ∃ (I J : LieIdeal ℂ (ℂ ⊗[ℝ] h)) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤),
        IsAtom I ∧ IsAtom J ∧
        ∃ U : LieSubmodule ℂ I (ℂ ⊗[ℝ] W), IsAtom U ∧
          ActualTwoIdealTensorForms I J hIJ htop (orthogonalExtendedForm (W := W)) U := by
  rcases all_rank_orthogonal_isotropy_simple_or_two_atoms B h heff hproper e hradical with
    hsimple | ⟨I, J, hI, hJ, hIJ, htop⟩
  · exact Or.inl hsimple
  · right
    refine ⟨I, J, hIJ, htop, hI, hJ, ?_⟩
    letI : LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) :=
      orthogonal_complexified_defining_faithful h
    letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) :=
      all_rank_orthogonal_defining_complex_irreducible B h heff hproper e hradical
    have hnd : (orthogonalExtendedForm (W := W)).Nondegenerate := by
      apply complexified_bilinForm_nondegenerate (innerₗ W)
      constructor <;> intro w hw <;> exact inner_self_eq_zero.mp (hw w)
    exact exists_atomic_two_ideal_tensor_forms I J hIJ htop
      (orthogonalExtendedForm (W := W))
      (orthogonal_complexified_defining_form_invariant h) hnd

end Orthogonal

section Symplectic

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

set_option maxHeartbeats 1000000 in
/-- The original symplectic hypotheses derive the actual defining tensor
factors and their invariant forms from the given quaternionic form. -/
theorem all_rank_symplectic_isotropy_simple_or_actual_tensor_forms
    (Q : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra Q))
    (h : LieSubalgebra ℝ (symplecticAlgebra Q))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
    letI := complexified_defining_lieModule (symplecticDefiningRepresentation Q h)
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h) ∨
      ∃ (I J : LieIdeal ℂ (ℂ ⊗[ℝ] h)) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤),
        IsAtom I ∧ IsAtom J ∧
        ∃ U : LieSubmodule ℂ I W, IsAtom U ∧
          ActualTwoIdealTensorForms I J hIJ htop (quaternionicForm Q) U := by
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
  letI := complexified_defining_lieModule (symplecticDefiningRepresentation Q h)
  rcases all_rank_symplectic_isotropy_simple_or_two_atoms Q B h heff hproper e hradical with
    hsimple | ⟨I, J, hI, hJ, hIJ, htop⟩
  · exact Or.inl hsimple
  · right
    refine ⟨I, J, hIJ, htop, hI, hJ, ?_⟩
    letI : LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) W :=
      symplectic_complexified_defining_faithful Q h
    letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) W :=
      all_rank_symplectic_complexified_defining_irreducible Q B h heff hproper e hradical
    exact exists_atomic_two_ideal_tensor_forms I J hIJ htop
      (quaternionicForm Q) (quaternionic_form_complexified_invariant Q h)
      (quaternionic_form_nondegenerate Q)

end Symplectic

end CubicAnomaly.Classification.ClassicalTwoFactorReduction
