import CubicAnomaly.Classification.UnitaryGeometry
import CubicAnomaly.Classification.ComplexDefining
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Algebra.Lie.Classical

/-!
# The actual special-unitary complexification

The actual scalar extension of `su(W)` is identified with all traceless
complex endomorphisms of `W`.  Injectivity follows from skew-adjoint real
and imaginary parts; surjectivity uses the explicit skew-adjoint
decomposition of a complex operator.  No classified Lie-type equivalence
is assumed.
-/

namespace CubicAnomaly.Classification.UnitaryComplexification

open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.Complexification
open scoped TensorProduct Matrix

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- Complex scalar extension of an injective skew-Hermitian real action
is injective.  This applies to arbitrary compact matrix subalgebras. -/
theorem complexify_skew_map_injective {L : Type*} [AddCommGroup L] [Module ℝ L]
    (ρ : L →ₗ[ℝ] Module.End ℂ W) (hρ : Function.Injective ρ)
    (hsk : ∀ x, (ρ x).adjoint = -ρ x) :
    Function.Injective (complexifyEndMap ρ) := by
  have hz (z : ℂ ⊗[ℝ] L) (hz : complexifyEndMap ρ z = 0) : z = 0 := by
    let x := tensorRealPart L z
    let y := tensorImagPart L z
    have he : ρ x + Complex.I • ρ y = 0 := by
      rw [complexification_real_imag_decomposition L z, map_add,
        complexify_end_map_tmul, complexify_end_map_tmul, one_smul] at hz
      exact hz
    have he' : -ρ x + Complex.I • ρ y = 0 := by
      have hh := congrArg LinearMap.adjoint he
      simpa only [map_add, map_smulₛₗ, hsk, map_zero, Complex.conj_I,
        neg_smul, smul_neg, neg_neg] using hh
    have hx2 : (2 : ℂ) • ρ x = 0 := by
      calc
        (2 : ℂ) • ρ x = (ρ x + Complex.I • ρ y) - (-ρ x + Complex.I • ρ y) := by module
        _ = 0 := by rw [he, he', sub_self]
    have hx : ρ x = 0 := (smul_eq_zero.mp hx2).resolve_left (by norm_num)
    have hy : ρ y = 0 := by
      rw [hx, zero_add] at he
      exact (smul_eq_zero.mp he).resolve_left Complex.I_ne_zero
    apply (complexification_zero_iff_parts L z).mpr
    exact ⟨hρ (hx.trans (map_zero ρ).symm), hρ (hy.trans (map_zero ρ).symm)⟩
  intro z w h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

/-- The trace of the adjoint is the conjugate trace, for actual operators. -/
theorem trace_adjoint_eq_conj (A : Module.End ℂ W) :
    LinearMap.trace ℂ W A.adjoint = star (LinearMap.trace ℂ W A) := by
  let b := stdOrthonormalBasis ℂ W
  rw [A.adjoint.trace_eq_sum_inner b, A.trace_eq_sum_inner b, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.adjoint_inner_right]
  exact (inner_conj_symm (A (b i)) (b i)).symm

/-- The actual complex Lie algebra of traceless defining endomorphisms. -/
def specialLinearEnd (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] : LieSubalgebra ℂ (Module.End ℂ W) where
  __ := LinearMap.ker (LinearMap.trace ℂ W)
  lie_mem' := by
    intro A B _ _
    change LinearMap.trace ℂ W (A ∘ₗ B - B ∘ₗ A) = 0
    rw [map_sub, LinearMap.trace_comp_comm', sub_self]

private theorem special_unitary_extension_trace_zero (z : ℂ ⊗[ℝ] specialUnitaryAlgebra W) :
    LinearMap.trace ℂ W
      (complexifyEndRepresentation (specialUnitaryAlgebra W).incl z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change LinearMap.trace ℂ W (a • x.val) = 0
    rw [map_smul, x.property.2, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- The literal complexified defining inclusion, with trace-zero codomain. -/
def specialUnitaryComplexificationHom :
    (ℂ ⊗[ℝ] specialUnitaryAlgebra W) →ₗ⁅ℂ⁆ specialLinearEnd W := {
  (complexifyEndRepresentation (specialUnitaryAlgebra W).incl).toLinearMap.codRestrict
    (specialLinearEnd W).toSubmodule special_unitary_extension_trace_zero with
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact (complexifyEndRepresentation (specialUnitaryAlgebra W).incl).map_lie x y }

/-- The complexified defining inclusion is injective. -/
theorem special_unitary_complexification_injective :
    Function.Injective (specialUnitaryComplexificationHom (W := W)) := by
  intro x y h
  exact complexify_skew_map_injective (specialUnitaryAlgebra W).incl.toLinearMap
    Subtype.val_injective (fun x => x.property.1) (congrArg Subtype.val h)

private theorem traceless_skew_decomposition (A : specialLinearEnd W) :
    ∃ X Y : specialUnitaryAlgebra W, A.val = X.val + Complex.I • Y.val := by
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
  have hAt : LinearMap.trace ℂ W A.val = 0 := A.property
  have hAat : LinearMap.trace ℂ W A.val.adjoint = 0 := by
    rw [trace_adjoint_eq_conj, hAt, star_zero]
  have hXt : LinearMap.trace ℂ W X = 0 := by simp [X, hAt, hAat]
  have hYt : LinearMap.trace ℂ W Y = 0 := by simp [Y, hAt, hAat]
  refine ⟨⟨X, hX, hXt⟩, ⟨Y, hY, hYt⟩, ?_⟩
  dsimp [X, Y]
  rw [smul_smul]
  have hi : Complex.I * (-Complex.I * (2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  rw [hi]
  module

/-- Every actual traceless complex endomorphism lies in the scalar extension
of the actual special-unitary algebra. -/
theorem special_unitary_complexification_surjective :
    Function.Surjective (specialUnitaryComplexificationHom (W := W)) := by
  intro A
  obtain ⟨X, Y, h⟩ := traceless_skew_decomposition A
  refine ⟨1 ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y, ?_⟩
  apply Subtype.ext
  change complexifyEndRepresentation (specialUnitaryAlgebra W).incl
    (1 ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y) = A.val
  rw [map_add]
  change (1 : ℂ) • X.val + Complex.I • Y.val = A.val
  rw [one_smul]
  exact h.symm

/-- The actual special-unitary complexification is the actual traceless
complex endomorphism Lie algebra. -/
def specialUnitaryComplexificationEquiv :
    (ℂ ⊗[ℝ] specialUnitaryAlgebra W) ≃ₗ⁅ℂ⁆ specialLinearEnd W :=
  LieEquiv.ofBijective specialUnitaryComplexificationHom
    ⟨special_unitary_complexification_injective, special_unitary_complexification_surjective⟩

/-- The resulting Lie equivalence preserves the literal defining action. -/
theorem special_unitary_complexification_equiv_tmul (a : ℂ)
    (x : specialUnitaryAlgebra W) :
    (specialUnitaryComplexificationEquiv (a ⊗ₜ[ℝ] x)).val = a • x.val := rfl

/-- Choosing an actual complex basis identifies traceless endomorphisms
with Mathlib's special-linear matrix Lie algebra. -/
def specialLinearMatrixEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) :
    specialLinearEnd W ≃ₗ⁅ℂ⁆ LieAlgebra.SpecialLinear.sl ι ℂ :=
  (LinearMap.toMatrixAlgEquiv b).toLieEquiv.ofSubalgebras _ _ (by
    ext A
    constructor
    · rintro ⟨f, hf, rfl⟩
      change Matrix.trace (LinearMap.toMatrix b b f) = 0
      rw [← LinearMap.trace_eq_matrix_trace ℂ b f]
      exact hf
    · intro hA
      obtain ⟨f, rfl⟩ := (LinearMap.toMatrixAlgEquiv b).surjective A
      refine ⟨f, ?_, rfl⟩
      change LinearMap.trace ℂ W f = 0
      rw [LinearMap.trace_eq_matrix_trace ℂ b f]
      exact hA)

/-- The actual compact special-unitary complexification is Mathlib's
special-linear matrix algebra in any actual defining basis. -/
def specialUnitaryMatrixEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) :
    (ℂ ⊗[ℝ] specialUnitaryAlgebra W) ≃ₗ⁅ℂ⁆ LieAlgebra.SpecialLinear.sl ι ℂ :=
  specialUnitaryComplexificationEquiv.trans (specialLinearMatrixEquiv b)

/-- The matrix identification agrees with scalar extension of the original
defining operators on every pure tensor. -/
theorem special_unitary_matrix_equiv_tmul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) (a : ℂ) (x : specialUnitaryAlgebra W) :
    (specialUnitaryMatrixEquiv b (a ⊗ₜ[ℝ] x)).val = a • LinearMap.toMatrix b b x.val := by
  change LinearMap.toMatrix b b (a • x.val) = _
  exact map_smul _ _ _

/-- The Lie-algebra identification intertwines the actual defining action
with matrix multiplication in the chosen basis. -/
theorem special_unitary_matrix_equiv_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) (z : ℂ ⊗[ℝ] specialUnitaryAlgebra W) (w : W) :
    (specialUnitaryMatrixEquiv b z).val *ᵥ b.repr w =
      b.repr ((complexifyEndRepresentation (specialUnitaryAlgebra W).incl z) w) := by
  exact LinearMap.toMatrix_mulVec_repr b b _ w

/-- Finite dimensionality supplies an actual basis, giving the standard
matrix algebra without an additional coordinate witness. -/
def standardSpecialUnitaryMatrixEquiv :
    (ℂ ⊗[ℝ] specialUnitaryAlgebra W) ≃ₗ⁅ℂ⁆
      LieAlgebra.SpecialLinear.sl (Fin (Module.finrank ℂ W)) ℂ :=
  specialUnitaryMatrixEquiv (Module.finBasis ℂ W)

end

end CubicAnomaly.Classification.UnitaryComplexification
