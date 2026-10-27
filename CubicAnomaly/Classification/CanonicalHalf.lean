import CubicAnomaly.Classification.ComplexHalf
import CubicAnomaly.Classification.HermitianRealization
import CubicAnomaly.Classification.AnomalyComplexification

/-!
# The canonical Hermitian model is the actual positive complex half

The canonical coordinates preserve the complex structure supplied by the
commutant.  Composing them with the inverse real projection of the positive
eigenspace therefore gives a complex-linear equivalence.  Its equivariance
is proved for every element of the complexified isotropy algebra and the
actual matrix representation used in the anomaly calculation.
-/

namespace CubicAnomaly.Classification.CanonicalHalf

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.AllRank
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.AnomalyComplexification
open Matrix
open scoped TensorProduct

private theorem real_linear_preserving_I_map_smul
    {U W : Type*} [AddCommGroup U] [Module ℂ U] [Module ℝ U] [IsScalarTower ℝ ℂ U]
    [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
    (f : U →ₗ[ℝ] W) (hI : ∀ u, f (Complex.I • u) = Complex.I • f u)
    (a : ℂ) (u : U) : f (a • u) = a • f u := by
  have hU (r : ℝ) (v : U) : (r : ℂ) • v = r • v :=
    IsScalarTower.algebraMap_smul ℂ r v
  have hW (r : ℝ) (v : W) : (r : ℂ) • v = r • v :=
    IsScalarTower.algebraMap_smul ℂ r v
  conv_lhs => rw [← Complex.re_add_im a]
  rw [add_smul, SemigroupAction.mul_smul, hU, hU,
    map_add, map_smul, map_smul, hI]
  conv_rhs => rw [← Complex.re_add_im a]
  rw [add_smul, SemigroupAction.mul_smul, hW, hW]

private noncomputable def complexEquivOfRealPreservingI
    {U W : Type*} [AddCommGroup U] [Module ℂ U] [Module ℝ U] [IsScalarTower ℝ ℂ U]
    [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
    (f : U ≃ₗ[ℝ] W) (hI : ∀ u, f (Complex.I • u) = Complex.I • f u) : U ≃ₗ[ℂ] W where
  toFun := f
  invFun := f.symm
  map_add' := f.map_add
  map_smul' := real_linear_preserving_I_map_smul f.toLinearMap hI
  left_inv := f.symm_apply_apply
  right_inv := f.apply_symm_apply

section CompatibleHalf

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]
  {h : LieSubalgebra ℝ g} {q : LieSubmodule ℝ h g}

/-- Coordinates compatible with `J` identify the actual positive complex
eigenspace with the matrix coordinate space over `ℂ`. -/
noncomputable def positiveHermitianEquiv (V : HermitianHalf h q)
    (J : q →ₗ⁅ℝ,h⁆ q) (hJ : ∀ m, J (J m) = -m)
    (hcompat : ∀ m, V.coordinates (J m) = Complex.I • V.coordinates m) :
    invariantEigenspace (complexifiedEnd J) Complex.I ≃ₗ[ℂ] (Fin V.dimension → ℂ) :=
  complexEquivOfRealPreservingI ((positiveHalfRealEquiv J hJ).symm.trans V.coordinates) (by
    intro z
    obtain ⟨m, rfl⟩ := (positiveHalfRealEquiv J hJ).surjective z
    change V.coordinates ((positiveHalfRealEquiv J hJ).symm
        (Complex.I • positiveHalfRealEquiv J hJ m)) =
      Complex.I • V.coordinates ((positiveHalfRealEquiv J hJ).symm
        (positiveHalfRealEquiv J hJ m))
    rw [← positiveHalfRealEquiv_map_complexStructure, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, hcompat])

/-- On a vector coming from the original real module, this equivalence
is exactly the originally chosen Hermitian coordinate map. -/
theorem positiveHermitianEquiv_on_real_half (V : HermitianHalf h q)
    (J : q →ₗ⁅ℝ,h⁆ q) (hJ : ∀ m, J (J m) = -m)
    (hcompat : ∀ m, V.coordinates (J m) = Complex.I • V.coordinates m) (m : q) :
    positiveHermitianEquiv V J hJ hcompat (positiveHalfRealEquiv J hJ m) =
      V.coordinates m := by
  change V.coordinates ((positiveHalfRealEquiv J hJ).symm
    (positiveHalfRealEquiv J hJ m)) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem positiveHermitianEquiv_real_action (V : HermitianHalf h q)
    (J : q →ₗ⁅ℝ,h⁆ q) (hJ : ∀ m, J (J m) = -m)
    (hcompat : ∀ m, V.coordinates (J m) = Complex.I • V.coordinates m)
    (x : h) (z : invariantEigenspace (complexifiedEnd J) Complex.I) :
    positiveHermitianEquiv V J hJ hcompat ⁅(1 ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] h), z⁆ =
      (complexHermitianRepresentation V (1 ⊗ₜ[ℝ] x)) *ᵥ
        positiveHermitianEquiv V J hJ hcompat z := by
  obtain ⟨m, rfl⟩ := (positiveHalfRealEquiv J hJ).surjective z
  rw [← positiveHalfRealEquiv_map_lie, positiveHermitianEquiv_on_real_half,
    positiveHermitianEquiv_on_real_half]
  change V.coordinates ⁅x, m⁆ = ((1 : ℂ) • (Complex.I • V.generators x)) *ᵥ V.coordinates m
  simpa only [one_smul, Matrix.smul_mulVec] using V.action x m

/-- The complex-linear equivalence intertwines the complete complexified
Lie action with the same matrix representation used by the anomaly radical. -/
theorem positiveHermitianEquiv_intertwines (V : HermitianHalf h q)
    (J : q →ₗ⁅ℝ,h⁆ q) (hJ : ∀ m, J (J m) = -m)
    (hcompat : ∀ m, V.coordinates (J m) = Complex.I • V.coordinates m)
    (x : ℂ ⊗[ℝ] h) (z : invariantEigenspace (complexifiedEnd J) Complex.I) :
    positiveHermitianEquiv V J hJ hcompat ⁅x, z⁆ =
      (complexHermitianRepresentation V x) *ᵥ positiveHermitianEquiv V J hJ hcompat z := by
  change positiveHermitianEquiv V J hJ hcompat
      ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] h)
        (invariantEigenspace (complexifiedEnd J) Complex.I) x) z) = _
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have ht : a ⊗ₜ[ℝ] x = a • (1 ⊗ₜ[ℝ] x) := by
      rw [TensorProduct.smul_tmul']; simp
    rw [ht]
    simp only [map_smul, LinearMap.smul_apply, Matrix.smul_mulVec]
    exact congrArg (fun v => a • v) (positiveHermitianEquiv_real_action V J hJ hcompat x z)
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Matrix.add_mulVec, hx, hy]

end CompatibleHalf

section Canonical

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The canonical Hermitian realization is complex-linearly equivalent to
the actual positive eigenspace of the commutant complex structure. -/
noncomputable def canonicalPositiveHalfEquiv (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I ≃ₗ[ℂ]
      (Fin (hermitianHalfOfCommutant B h e).dimension → ℂ) :=
  positiveHermitianEquiv (hermitianHalfOfCommutant B h e) (commutantComplexStructure e)
    (commutant_complex_structure_square e) (hermitian_half_coordinates_complexStructure B h e)

/-- The canonical matrix action is the actual positive-half action of
the complexified isotropy algebra under the canonical equivalence. -/
theorem canonicalPositiveHalfEquiv_intertwines (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (x : ℂ ⊗[ℝ] h)
    (z : invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I) :
    canonicalPositiveHalfEquiv B h e ⁅x, z⁆ =
      (complexHermitianRepresentation (hermitianHalfOfCommutant B h e) x) *ᵥ
        canonicalPositiveHalfEquiv B h e z :=
  positiveHermitianEquiv_intertwines _ _ _ _ x z

end Canonical

end CubicAnomaly.Classification.CanonicalHalf
