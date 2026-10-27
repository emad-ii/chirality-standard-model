import CubicAnomaly.Classification.SymplecticForm
import CubicAnomaly.Classification.UnitaryComplexification
import Mathlib.Algebra.Lie.SkewAdjoint

/-!
# The actual compact symplectic complexification

The complexification of the actual compact quaternionic algebra is the
actual complex Lie algebra preserving its alternating form.  Injectivity
comes from the skew-Hermitian real structure, and surjectivity from an
explicit decomposition into two compact symplectic endomorphisms.
-/

namespace CubicAnomaly.Classification.SymplecticComplexification

open CubicAnomaly.Classification.SymplecticGeometry
open CubicAnomaly.Classification.SymplecticForm
open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.UnitaryComplexification
open CubicAnomaly.Classification.ComplexDefining
open scoped ComplexConjugate TensorProduct

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

private theorem symplectic_form_skew_adjoint_relation (J : QuaternionicStructure W)
    (A : skewAdjointLieSubalgebra (quaternionicForm J)) (u : W) :
    J (A.val u) = -A.val.adjoint (J u) := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_neg_left, LinearMap.adjoint_inner_left]
  have hA := (LinearMap.mem_skewAdjointSubmodule (B := quaternionicForm J) A.val).mp
    A.property u v
  simpa only [quaternionic_form_apply, Pi.neg_apply, inner_neg_right] using hA

omit [FiniteDimensional ℂ W] in
private theorem symplectic_extension_mem (J : QuaternionicStructure W)
    (z : ℂ ⊗[ℝ] symplecticAlgebra J) :
    complexifyEndRepresentation (symplecticAlgebra J).incl z ∈
      skewAdjointLieSubalgebra (quaternionicForm J) := by
  induction z using TensorProduct.induction_on with
  | zero => exact (skewAdjointLieSubalgebra (quaternionicForm J)).zero_mem
  | tmul a x =>
    change a • x.val ∈ skewAdjointLieSubalgebra (quaternionicForm J)
    apply (skewAdjointLieSubalgebra (quaternionicForm J)).smul_mem
    apply (LinearMap.mem_skewAdjointSubmodule (B := quaternionicForm J) x.val).mpr
    intro u v
    change quaternionicForm J (x.val u) v = quaternionicForm J u (-x.val v)
    rw [map_neg]
    exact quaternionic_form_invariant J x u v
  | add x y hx hy =>
    rw [map_add]
    exact (skewAdjointLieSubalgebra (quaternionicForm J)).add_mem hx hy

/-- The actual scalar-extended defining inclusion, with the alternating-form
preserving complex algebra as codomain. -/
def symplecticComplexificationHom (J : QuaternionicStructure W) :
    (ℂ ⊗[ℝ] symplecticAlgebra J) →ₗ⁅ℂ⁆
      skewAdjointLieSubalgebra (quaternionicForm J) := {
  (complexifyEndRepresentation (symplecticAlgebra J).incl).toLinearMap.codRestrict
    (skewAdjointLieSubalgebra (quaternionicForm J)).toSubmodule
    (symplectic_extension_mem J) with
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact (complexifyEndRepresentation (symplecticAlgebra J).incl).map_lie x y }

/-- The actual complexified symplectic defining inclusion is injective. -/
theorem symplectic_complexification_injective (J : QuaternionicStructure W) :
    Function.Injective (symplecticComplexificationHom J) := by
  intro x y h
  exact complexify_skew_map_injective (symplecticAlgebra J).incl.toLinearMap
    Subtype.val_injective (fun x => (unitary_mem_iff x.val).mpr x.property.1)
    (congrArg Subtype.val h)

private theorem complex_symplectic_skew_decomposition (J : QuaternionicStructure W)
    (A : skewAdjointLieSubalgebra (quaternionicForm J)) :
    ∃ X Y : symplecticAlgebra J, A.val = X.val + Complex.I • Y.val := by
  let X : Module.End ℂ W := (2 : ℂ)⁻¹ • (A.val - A.val.adjoint)
  let Y : Module.End ℂ W := (-Complex.I * (2 : ℂ)⁻¹) • (A.val + A.val.adjoint)
  have hX : X.adjoint = -X := by
    dsimp [X]
    rw [map_smulₛₗ, map_sub, LinearMap.adjoint_adjoint]
    simp only [map_inv₀, map_ofNat]
    module
  have hY : Y.adjoint = -Y := by
    dsimp [Y]
    rw [map_smulₛₗ, map_add, LinearMap.adjoint_adjoint]
    simp only [map_mul, map_neg, Complex.conj_I, neg_neg, map_inv₀, map_ofNat]
    module
  have hAJ := symplectic_form_skew_adjoint_relation J A
  have hAadj (u : W) : J (A.val.adjoint u) = -A.val (J u) := by
    have h := hAJ (J u)
    rw [J.square, map_neg, neg_neg] at h
    rw [← h, J.square]
  have hXJ (u : W) : X (J u) = J (X u) := by
    dsimp only [X]
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, J.apply_smul,
      J.apply_sub, hAJ, hAadj, map_inv₀, map_ofNat]
    module
  have hYJ (u : W) : Y (J u) = J (Y u) := by
    dsimp only [Y]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, J.apply_smul,
      J.apply_add, hAJ, hAadj, map_mul, map_neg, Complex.conj_I,
      neg_neg, map_inv₀, map_ofNat]
    module
  refine ⟨⟨X, (unitary_mem_iff X).mp hX, hXJ⟩,
    ⟨Y, (unitary_mem_iff Y).mp hY, hYJ⟩, ?_⟩
  dsimp [X, Y]
  rw [smul_smul]
  have hi : Complex.I * (-Complex.I * (2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  rw [hi]
  module

/-- Every complex endomorphism preserving the actual alternating form is
in the actual scalar extension of the compact symplectic algebra. -/
theorem symplectic_complexification_surjective (J : QuaternionicStructure W) :
    Function.Surjective (symplecticComplexificationHom J) := by
  intro A
  obtain ⟨X, Y, h⟩ := complex_symplectic_skew_decomposition J A
  refine ⟨1 ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y, ?_⟩
  apply Subtype.ext
  change complexifyEndRepresentation (symplecticAlgebra J).incl
    (1 ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y) = A.val
  rw [map_add]
  change (1 : ℂ) • X.val + Complex.I • Y.val = A.val
  rw [one_smul]
  exact h.symm

/-- An actual Lie equivalence from the compact symplectic complexification
to the complex endomorphisms preserving the constructed alternating form. -/
def symplecticComplexificationEquiv (J : QuaternionicStructure W) :
    (ℂ ⊗[ℝ] symplecticAlgebra J) ≃ₗ⁅ℂ⁆
      skewAdjointLieSubalgebra (quaternionicForm J) :=
  LieEquiv.ofBijective (symplecticComplexificationHom J)
    ⟨symplectic_complexification_injective J, symplectic_complexification_surjective J⟩

/-- The Lie equivalence has the literal scalar-extended defining action. -/
theorem symplectic_complexification_equiv_tmul (J : QuaternionicStructure W)
    (a : ℂ) (x : symplecticAlgebra J) :
    (symplecticComplexificationEquiv J (a ⊗ₜ[ℝ] x)).val = a • x.val := rfl

end

end CubicAnomaly.Classification.SymplecticComplexification
