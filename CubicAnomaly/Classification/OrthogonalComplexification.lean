import CubicAnomaly.Classification.OrthogonalDefining
import Mathlib.Algebra.Lie.Classical

/-!
# The actual orthogonal complexification

The scalar extension of the real orthogonal algebra is the algebra of
endomorphisms skew for the scalar extension of the real inner product.
Real and imaginary parts of actual operators prove surjectivity directly.
-/

namespace CubicAnomaly.Classification.OrthogonalComplexification

open CubicAnomaly.Classification.OrthogonalDefining
open CubicAnomaly.Classification.Complexification
open scoped TensorProduct Matrix

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The complex bilinear extension of the real defining inner product. -/
abbrev orthogonalExtendedForm : LinearMap.BilinForm ℂ (ℂ ⊗[ℝ] W) :=
  LinearMap.BilinForm.baseChange ℂ (innerₗ W)

/-- The actual complex orthogonal algebra for the extended defining form. -/
abbrev orthogonalExtendedAlgebra := skewAdjointLieSubalgebra (orthogonalExtendedForm (W := W))

private theorem baseChange_orthogonal_mem (A : orthogonalAlgebra W) :
    A.val.baseChange ℂ ∈ orthogonalExtendedAlgebra (W := W) := by
  apply (LinearMap.mem_skewAdjointSubmodule (B := orthogonalExtendedForm) _).mpr
  intro u v
  have hA := (LinearMap.mem_skewAdjointSubmodule (B := innerₗ W) A.val).mp A.property
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul b v =>
      change LinearMap.BilinForm.baseChange ℂ (innerₗ W) (a ⊗ₜ[ℝ] A.val u) (b ⊗ₜ[ℝ] v) =
        LinearMap.BilinForm.baseChange ℂ (innerₗ W) (a ⊗ₜ[ℝ] u) (-(b ⊗ₜ[ℝ] A.val v))
      rw [← TensorProduct.tmul_neg]
      simp only [LinearMap.BilinForm.baseChange_tmul]
      exact congrArg (fun t : ℝ => t • (a * b)) (hA u v)
    | add v w hv hw => simp only [Pi.neg_apply, map_add, neg_add, hv, hw]
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]

private theorem complexified_orthogonal_action_mem (z : ℂ ⊗[ℝ] orthogonalAlgebra W) :
    LieModule.toEnd ℂ (ℂ ⊗[ℝ] orthogonalAlgebra W) (ℂ ⊗[ℝ] W) z ∈
      orthogonalExtendedAlgebra (W := W) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have ht : a ⊗ₜ[ℝ] x = a • (1 ⊗ₜ[ℝ] x) := by
      rw [TensorProduct.smul_tmul']
      simp
    rw [ht, map_smul, LieModule.toEnd_baseChange]
    exact (orthogonalExtendedAlgebra (W := W)).smul_mem a (baseChange_orthogonal_mem x)
  | add x y hx hy => simpa only [map_add] using
      (orthogonalExtendedAlgebra (W := W)).add_mem hx hy

/-- The actual complexified defining action, with orthogonal codomain. -/
def orthogonalComplexificationHom :
    (ℂ ⊗[ℝ] orthogonalAlgebra W) →ₗ⁅ℂ⁆ orthogonalExtendedAlgebra (W := W) := {
  (LieModule.toEnd ℂ (ℂ ⊗[ℝ] orthogonalAlgebra W) (ℂ ⊗[ℝ] W)).toLinearMap.codRestrict
    (orthogonalExtendedAlgebra (W := W)).toSubmodule complexified_orthogonal_action_mem with
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact (LieModule.toEnd ℂ (ℂ ⊗[ℝ] orthogonalAlgebra W) (ℂ ⊗[ℝ] W)).map_lie x y }

/-- The pure-tensor action is the literal scalar extension of the real action. -/
theorem orthogonal_complexification_action_tmul (a b : ℂ)
    (A : orthogonalAlgebra W) (w : W) :
    (orthogonalComplexificationHom (a ⊗ₜ[ℝ] A)).val (b ⊗ₜ[ℝ] w) =
      (a * b) ⊗ₜ[ℝ] A.val w := rfl

/-- The actual scalar-extended orthogonal defining action is faithful. -/
theorem orthogonal_complexification_injective :
    Function.Injective (orthogonalComplexificationHom (W := W)) := by
  have hz (z : ℂ ⊗[ℝ] orthogonalAlgebra W)
      (hz : orthogonalComplexificationHom z = 0) : z = 0 := by
    let x := tensorRealPart (orthogonalAlgebra W) z
    let y := tensorImagPart (orthogonalAlgebra W) z
    have he (w : W) : 1 ⊗ₜ[ℝ] x.val w + Complex.I ⊗ₜ[ℝ] y.val w = 0 := by
      have h := congrArg (fun A : orthogonalExtendedAlgebra (W := W) => A.val (1 ⊗ₜ[ℝ] w)) hz
      rw [complexification_real_imag_decomposition (orthogonalAlgebra W) z,
        map_add] at h
      change (orthogonalComplexificationHom (1 ⊗ₜ[ℝ] x)).val (1 ⊗ₜ[ℝ] w) +
        (orthogonalComplexificationHom (Complex.I ⊗ₜ[ℝ] y)).val (1 ⊗ₜ[ℝ] w) = 0 at h
      simpa only [orthogonal_complexification_action_tmul, mul_one] using h
    have hx : x = 0 := by
      apply Subtype.ext
      ext w
      have h := congrArg (tensorRealPart W) (he w)
      simpa [tensorRealPart] using h
    have hy : y = 0 := by
      apply Subtype.ext
      ext w
      have h := congrArg (tensorImagPart W) (he w)
      simpa [tensorImagPart] using h
    exact (complexification_zero_iff_parts _ z).mpr ⟨hx, hy⟩
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

private def operatorRealPart (A : Module.End ℂ (ℂ ⊗[ℝ] W)) : Module.End ℝ W :=
  (tensorRealPart W).comp ((A.restrictScalars ℝ).comp (TensorProduct.mk ℝ ℂ W 1))

private def operatorImagPart (A : Module.End ℂ (ℂ ⊗[ℝ] W)) : Module.End ℝ W :=
  (tensorImagPart W).comp ((A.restrictScalars ℝ).comp (TensorProduct.mk ℝ ℂ W 1))

private theorem extended_form_re_left (z : ℂ ⊗[ℝ] W) (w : W) :
    (orthogonalExtendedForm z (1 ⊗ₜ[ℝ] w)).re = inner ℝ (tensorRealPart W z) w := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [orthogonalExtendedForm, tensorRealPart, innerₗ_apply_apply,
      inner_smul_left, mul_comm]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, Complex.add_re,
      inner_add_left, hx, hy]

private theorem extended_form_im_left (z : ℂ ⊗[ℝ] W) (w : W) :
    (orthogonalExtendedForm z (1 ⊗ₜ[ℝ] w)).im = inner ℝ (tensorImagPart W z) w := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [orthogonalExtendedForm, tensorImagPart, innerₗ_apply_apply,
      inner_smul_left, mul_comm]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, Complex.add_im,
      inner_add_left, hx, hy]

private theorem extended_form_re_right (w : W) (z : ℂ ⊗[ℝ] W) :
    (orthogonalExtendedForm (1 ⊗ₜ[ℝ] w) z).re = inner ℝ w (tensorRealPart W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [orthogonalExtendedForm, tensorRealPart, innerₗ_apply_apply,
      inner_smul_right, mul_comm]
  | add x y hx hy => simp only [map_add, Complex.add_re, inner_add_right, hx, hy]

private theorem extended_form_im_right (w : W) (z : ℂ ⊗[ℝ] W) :
    (orthogonalExtendedForm (1 ⊗ₜ[ℝ] w) z).im = inner ℝ w (tensorImagPart W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [orthogonalExtendedForm, tensorImagPart, innerₗ_apply_apply,
      inner_smul_right, mul_comm]
  | add x y hx hy => simp only [map_add, Complex.add_im, inner_add_right, hx, hy]

private theorem orthogonal_operator_parts (A : orthogonalExtendedAlgebra (W := W)) :
    operatorRealPart A.val ∈ orthogonalAlgebra W ∧
      operatorImagPart A.val ∈ orthogonalAlgebra W := by
  have hA := (LinearMap.mem_skewAdjointSubmodule (B := orthogonalExtendedForm) A.val).mp A.property
  constructor
  · apply (LinearMap.mem_skewAdjointSubmodule (B := innerₗ W) _).mpr
    intro u v
    have h := congrArg Complex.re (hA (1 ⊗ₜ[ℝ] u) (1 ⊗ₜ[ℝ] v))
    simp only [Pi.neg_apply] at h
    rw [map_neg, Complex.neg_re, extended_form_re_left, extended_form_re_right] at h
    simpa only [operatorRealPart, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.restrictScalars_apply, TensorProduct.mk_apply, innerₗ_apply_apply,
      Pi.neg_apply, inner_neg_right] using h
  · apply (LinearMap.mem_skewAdjointSubmodule (B := innerₗ W) _).mpr
    intro u v
    have h := congrArg Complex.im (hA (1 ⊗ₜ[ℝ] u) (1 ⊗ₜ[ℝ] v))
    simp only [Pi.neg_apply] at h
    rw [map_neg, Complex.neg_im, extended_form_im_left, extended_form_im_right] at h
    simpa only [operatorImagPart, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.restrictScalars_apply, TensorProduct.mk_apply, innerₗ_apply_apply,
      Pi.neg_apply, inner_neg_right] using h

/-- Every skew operator for the extended bilinear form is the complex
linear combination of two actual real orthogonal operators. -/
theorem orthogonal_complexification_surjective :
    Function.Surjective (orthogonalComplexificationHom (W := W)) := by
  intro A
  obtain ⟨hr, hi⟩ := orthogonal_operator_parts A
  let X : orthogonalAlgebra W := ⟨operatorRealPart A.val, hr⟩
  let Y : orthogonalAlgebra W := ⟨operatorImagPart A.val, hi⟩
  refine ⟨1 ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y, ?_⟩
  apply Subtype.ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro a w
  have h := complexification_real_imag_decomposition W (A.val (1 ⊗ₜ[ℝ] w))
  have ht : a ⊗ₜ[ℝ] w = a • (1 ⊗ₜ[ℝ] w) := by
    rw [TensorProduct.smul_tmul']
    simp
  rw [ht]
  simp only [map_smul]
  congr 1
  rw [map_add]
  change (orthogonalComplexificationHom (1 ⊗ₜ[ℝ] X)).val (1 ⊗ₜ[ℝ] w) +
    (orthogonalComplexificationHom (Complex.I ⊗ₜ[ℝ] Y)).val (1 ⊗ₜ[ℝ] w) = A.val (1 ⊗ₜ[ℝ] w)
  simpa only [orthogonal_complexification_action_tmul, mul_one] using h.symm

/-- The actual real orthogonal complexification is the full orthogonal
algebra for the actual scalar-extended defining form. -/
def orthogonalComplexificationEquiv :
    (ℂ ⊗[ℝ] orthogonalAlgebra W) ≃ₗ⁅ℂ⁆ orthogonalExtendedAlgebra (W := W) :=
  LieEquiv.ofBijective orthogonalComplexificationHom
    ⟨orthogonal_complexification_injective, orthogonal_complexification_surjective⟩

/-- The equivalence retains the actual defining action on pure tensors. -/
theorem orthogonal_complexification_equiv_action (a b : ℂ)
    (A : orthogonalAlgebra W) (w : W) :
    (orthogonalComplexificationEquiv (a ⊗ₜ[ℝ] A)).val (b ⊗ₜ[ℝ] w) =
      (a * b) ⊗ₜ[ℝ] A.val w := rfl

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem extended_orthonormal_basis_left (b : OrthonormalBasis ι ℝ W)
    (i : ι) (z : ℂ ⊗[ℝ] W) :
    orthogonalExtendedForm ((b.toBasis.baseChange ℂ) i) z =
      (b.toBasis.baseChange ℂ).repr z i := by
  rw [Module.Basis.baseChange_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a w =>
    simp [orthogonalExtendedForm, b.coe_toBasis_repr_apply, b.repr_apply_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

omit [DecidableEq ι] in
private theorem extended_orthonormal_basis_right (b : OrthonormalBasis ι ℝ W)
    (i : ι) (z : ℂ ⊗[ℝ] W) :
    orthogonalExtendedForm z ((b.toBasis.baseChange ℂ) i) =
      (b.toBasis.baseChange ℂ).repr z i := by
  rw [Module.Basis.baseChange_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a w =>
    simp [orthogonalExtendedForm, b.coe_toBasis_repr_apply, b.repr_apply_apply,
      real_inner_comm]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hy]

private theorem orthogonal_matrix_mem_iff (b : OrthonormalBasis ι ℝ W)
    (A : Module.End ℂ (ℂ ⊗[ℝ] W)) :
    LinearMap.toMatrix (b.toBasis.baseChange ℂ) (b.toBasis.baseChange ℂ) A ∈
      LieAlgebra.Orthogonal.so ι ℂ ↔ A ∈ orthogonalExtendedAlgebra (W := W) := by
  rw [LieAlgebra.Orthogonal.mem_so]
  constructor
  · intro h
    apply (LinearMap.mem_skewAdjointSubmodule (B := orthogonalExtendedForm) _).mpr
    have hf :
        (orthogonalExtendedForm (W := W)).compl₁₂ A LinearMap.id =
        (orthogonalExtendedForm (W := W)).compl₁₂ LinearMap.id (-A) := by
      apply (b.toBasis.baseChange ℂ).ext
      intro i
      apply (b.toBasis.baseChange ℂ).ext
      intro j
      change orthogonalExtendedForm (A ((b.toBasis.baseChange ℂ) i))
          ((b.toBasis.baseChange ℂ) j) =
        orthogonalExtendedForm ((b.toBasis.baseChange ℂ) i)
          (-A ((b.toBasis.baseChange ℂ) j))
      rw [extended_orthonormal_basis_right, map_neg, extended_orthonormal_basis_left]
      have hh := congrArg (fun M : Matrix ι ι ℂ => M i j) h
      simpa only [Matrix.transpose_apply, Matrix.neg_apply, LinearMap.toMatrix_apply] using hh
    intro u v
    exact congrArg (fun F : LinearMap.BilinForm ℂ (ℂ ⊗[ℝ] W) => F u v) hf
  · intro h
    have hA := (LinearMap.mem_skewAdjointSubmodule (B := orthogonalExtendedForm) A).mp h
    ext i j
    have hh := hA ((b.toBasis.baseChange ℂ) i) ((b.toBasis.baseChange ℂ) j)
    change orthogonalExtendedForm (A ((b.toBasis.baseChange ℂ) i))
        ((b.toBasis.baseChange ℂ) j) =
      orthogonalExtendedForm ((b.toBasis.baseChange ℂ) i)
        (-A ((b.toBasis.baseChange ℂ) j)) at hh
    rw [extended_orthonormal_basis_right, map_neg, extended_orthonormal_basis_left] at hh
    simpa only [Matrix.transpose_apply, Matrix.neg_apply, LinearMap.toMatrix_apply] using hh

/-- An actual real orthonormal basis, extended by scalars, identifies the
complex orthogonal algebra with Mathlib's orthogonal matrix Lie algebra. -/
def orthogonalExtendedMatrixEquiv (b : OrthonormalBasis ι ℝ W) :
    orthogonalExtendedAlgebra (W := W) ≃ₗ⁅ℂ⁆ LieAlgebra.Orthogonal.so ι ℂ :=
  (LinearMap.toMatrixAlgEquiv (b.toBasis.baseChange ℂ)).toLieEquiv.ofSubalgebras _ _ (by
    ext A
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (orthogonal_matrix_mem_iff b f).mpr hf
    · intro hA
      obtain ⟨f, rfl⟩ := (LinearMap.toMatrixAlgEquiv (b.toBasis.baseChange ℂ)).surjective A
      exact ⟨f, (orthogonal_matrix_mem_iff b f).mp hA, rfl⟩)

/-- The actual real orthogonal complexification is Mathlib's orthogonal
matrix algebra in any actual real orthonormal defining basis. -/
def orthogonalMatrixEquiv (b : OrthonormalBasis ι ℝ W) :
    (ℂ ⊗[ℝ] orthogonalAlgebra W) ≃ₗ⁅ℂ⁆ LieAlgebra.Orthogonal.so ι ℂ :=
  orthogonalComplexificationEquiv.trans (orthogonalExtendedMatrixEquiv b)

/-- The matrix identification intertwines the actual complexified defining
action with matrix multiplication in the extended basis. -/
theorem orthogonal_matrix_equiv_action (b : OrthonormalBasis ι ℝ W)
    (z : ℂ ⊗[ℝ] orthogonalAlgebra W) (w : ℂ ⊗[ℝ] W) :
    (orthogonalMatrixEquiv b z).val *ᵥ (b.toBasis.baseChange ℂ).repr w =
      (b.toBasis.baseChange ℂ).repr ⁅z, w⁆ := by
  change LinearMap.toMatrix (b.toBasis.baseChange ℂ) (b.toBasis.baseChange ℂ)
      (orthogonalComplexificationHom z).val *ᵥ (b.toBasis.baseChange ℂ).repr w =
    (b.toBasis.baseChange ℂ).repr ((orthogonalComplexificationHom z).val w)
  exact LinearMap.toMatrix_mulVec_repr (b.toBasis.baseChange ℂ) (b.toBasis.baseChange ℂ)
    (orthogonalComplexificationHom z).val w

end Matrix

/-- A finite-dimensional real defining space supplies its own orthonormal
basis, so no coordinate witness is required for the matrix identification. -/
def standardOrthogonalMatrixEquiv [FiniteDimensional ℝ W] :
    (ℂ ⊗[ℝ] orthogonalAlgebra W) ≃ₗ⁅ℂ⁆
      LieAlgebra.Orthogonal.so (Fin (Module.finrank ℝ W)) ℂ :=
  orthogonalMatrixEquiv (stdOrthonormalBasis ℝ W)

end

end CubicAnomaly.Classification.OrthogonalComplexification
