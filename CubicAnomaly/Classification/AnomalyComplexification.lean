import CubicAnomaly.Classification.CartanTrace
import CubicAnomaly.Classification.Complexification
import CubicAnomaly.Classification.AllRank

/-!
# The Hermitian anomaly after actual scalar extension

The Hermitian generators determine the genuine Lie representation
`ρ(x) = I • T(x)`.  We extend this representation to `ℂ ⊗[ℝ] h` and compare
its full trace-cubic radical with the original real radical.  This supplies
the representation needed by the Cartan matrix criterion.
-/

namespace CubicAnomaly.Classification.AnomalyComplexification

set_option maxHeartbeats 800000

open Matrix
open scoped TensorProduct
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanCubic
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.AllRank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex-linear extension of a real-linear map into complex matrices. -/
noncomputable def complexifyMatrixMap {L : Type*} [AddCommGroup L] [Module ℝ L]
    (T : L →ₗ[ℝ] Matrix n n ℂ) : (ℂ ⊗[ℝ] L) →ₗ[ℂ] Matrix n n ℂ :=
  TensorProduct.AlgebraTensorModule.lift {
    toFun := fun a : ℂ => a • T
    map_add' := fun a b => add_smul a b T
    map_smul' := fun a b => mul_smul a b T }

omit [Fintype n] [DecidableEq n] in
/-- The extended matrix action on pure tensors is scalar multiplication. -/
theorem complexify_matrix_map_tmul {L : Type*} [AddCommGroup L] [Module ℝ L]
    (T : L →ₗ[ℝ] Matrix n n ℂ) (a : ℂ) (x : L) :
    complexifyMatrixMap T (a ⊗ₜ[ℝ] x) = a • T x := rfl

/-- Scalar extension preserves the actual matrix Lie representation law. -/
noncomputable def complexifyMatrixRepresentation {L : Type*}
    [LieRing L] [LieAlgebra ℝ L] (ρ : L →ₗ⁅ℝ⁆ Matrix n n ℂ) :
    (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Matrix n n ℂ := {
  complexifyMatrixMap ρ.toLinearMap with
  map_lie' := by
    intro x y
    change complexifyMatrixMap ρ.toLinearMap
        ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L) x) y) =
      (LieModule.toEnd ℂ (Matrix n n ℂ) (Matrix n n ℂ)
        (complexifyMatrixMap ρ.toLinearMap x)) (complexifyMatrixMap ρ.toLinearMap y)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
        simp [LieModule.toEnd_apply_apply, complexify_matrix_map_tmul,
          LieHom.map_lie, smul_smul, mul_comm]
      | add y z hy hz => simp only [map_add, hy, hz]
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz] }

private theorem matrixTraceCubic_smul_all (a b c : ℂ) (A B C : Matrix n n ℂ) :
    matrixTraceCubic (a • A) (b • B) (c • C) =
      a * b * c * matrixTraceCubic A B C := by
  change complexTraceCubicForm (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (a • A) (b • B) (c • C) = _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  change c * (b * (a * matrixTraceCubic A B C)) = _
  ring

omit [DecidableEq n] in
/-- For Hermitian generators the symmetrized cubic is real. -/
theorem hermitian_matrix_trace_cubic_real (A B C : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (matrixTraceCubic A B C).im = 0 := by
  have hstar : star (matrixTraceCubic A B C) = matrixTraceCubic A B C := by
    simp only [matrixTraceCubic, StarMul.star_mul, star_div₀, star_one, star_ofNat,
      ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_add,
      hA.eq, hB.eq, hC.eq]
    rw [Matrix.trace_mul_comm]
    rw [add_comm (C * B) (B * C)]
    exact mul_comm _ _
  have him := congrArg Complex.im hstar
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

private theorem tmul_eq_smul_one {M : Type*} [AddCommGroup M] [Module ℝ M]
    (a : ℂ) (x : M) : a ⊗ₜ[ℝ] x = a • (1 ⊗ₜ[ℝ] x) := by
  rw [TensorProduct.smul_tmul']
  simp

private theorem bilinear_tensor_test {M : Type*} [AddCommGroup M] [Module ℝ M]
    (f : (ℂ ⊗[ℝ] M) →ₗ[ℂ] (ℂ ⊗[ℝ] M) →ₗ[ℂ] ℂ) :
    (∀ y z, f y z = 0) ↔ ∀ y z : M, f (1 ⊗ₜ[ℝ] y) (1 ⊗ₜ[ℝ] z) = 0 := by
  constructor
  · intro hf y z
    exact hf _ _
  · intro hf y z
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b z =>
        rw [tmul_eq_smul_one a y, tmul_eq_smul_one b z]
        simp only [map_smul, LinearMap.smul_apply, hf, smul_zero]
      | add z w hz hw => simp only [map_add, hz, hw, add_zero]
    | add y w hy hw => simp only [map_add, LinearMap.add_apply, hy, hw, add_zero]

section HermitianHalf

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]
  {h : LieSubalgebra ℝ g} {q : LieSubmodule ℝ h g}

/-- The Hermitian convention gives an actual, skew-Hermitian matrix action. -/
noncomputable def hermitianLieRepresentation (V : HermitianHalf h q) :
    h →ₗ⁅ℝ⁆ Matrix (Fin V.dimension) (Fin V.dimension) ℂ := {
  Complex.I • V.generators with
  map_lie' := by
    intro x y
    change Complex.I • V.generators ⁅x, y⁆ =
      ⁅Complex.I • V.generators x, Complex.I • V.generators y⁆
    rw [scaled_commutator_of_action V.coordinates V.generators V.action]
    simp only [Ring.lie_def, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I, smul_sub] }

/-- The actual complex Lie representation associated to the Hermitian half. -/
noncomputable def complexHermitianRepresentation (V : HermitianHalf h q) :
    (ℂ ⊗[ℝ] h) →ₗ⁅ℂ⁆ Matrix (Fin V.dimension) (Fin V.dimension) ℂ :=
  complexifyMatrixRepresentation (n := Fin V.dimension) (hermitianLieRepresentation V)

private theorem complexHermitianRepresentation_tmul (V : HermitianHalf h q)
    (a : ℂ) (x : h) :
    complexHermitianRepresentation V (a ⊗ₜ[ℝ] x) = a • (Complex.I • V.generators x) := rfl

/-- Passing from Hermitian generators to the Lie action multiplies the cubic
on real inputs by the nonzero scalar `-I`. -/
theorem hermitian_complex_cubic_real_inputs (V : HermitianHalf h q) (x y z : h) :
    complexTraceCubicForm (complexHermitianRepresentation V).toLinearMap
        (1 ⊗ₜ[ℝ] x) (1 ⊗ₜ[ℝ] y) (1 ⊗ₜ[ℝ] z) =
      -Complex.I * matrixTraceCubic (V.generators x) (V.generators y) (V.generators z) := by
  change matrixTraceCubic (complexHermitianRepresentation V (1 ⊗ₜ[ℝ] x))
    (complexHermitianRepresentation V (1 ⊗ₜ[ℝ] y))
    (complexHermitianRepresentation V (1 ⊗ₜ[ℝ] z)) = _
  simp only [complexHermitianRepresentation_tmul, one_smul, matrixTraceCubic_smul_all,
    Complex.I_mul_I, neg_one_mul]

private theorem hermitian_complex_cubic_parts (V : HermitianHalf h q)
    (x : ℂ ⊗[ℝ] h) (y z : h) :
    complexTraceCubicForm (complexHermitianRepresentation V).toLinearMap
        x (1 ⊗ₜ[ℝ] y) (1 ⊗ₜ[ℝ] z) =
      -Complex.I * matrixTraceCubic (V.generators (tensorRealPart h x))
        (V.generators y) (V.generators z) +
      matrixTraceCubic (V.generators (tensorImagPart h x))
        (V.generators y) (V.generators z) := by
  conv_lhs => rw [complexification_real_imag_decomposition h x]
  rw [tmul_eq_smul_one Complex.I (tensorImagPart h x)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hermitian_complex_cubic_real_inputs, smul_eq_mul]
  rw [← mul_assoc Complex.I, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

/-- A complex vector is in the full trace radical exactly when its real and
imaginary coordinates are in the original Hermitian anomaly radical. -/
theorem hermitian_complex_radical_membership (V : HermitianHalf h q)
    (x : ℂ ⊗[ℝ] h) :
    x ∈ complexTraceRadical (complexHermitianRepresentation V) ↔
      tensorRealPart h x ∈ V.cubicRadical ∧ tensorImagPart h x ∈ V.cubicRadical := by
  rw [complexTraceRadical, mem_radical_iff, bilinear_tensor_test,
    hermitian_half_cubic_radical_membership, hermitian_half_cubic_radical_membership]
  constructor
  · intro hx
    have hparts (y z : h) := hx y z
    simp only [hermitian_complex_cubic_parts] at hparts
    have hreal (w y z : h) := hermitian_matrix_trace_cubic_real
      (V.generators w) (V.generators y) (V.generators z)
      (V.hermitian w) (V.hermitian y) (V.hermitian z)
    constructor
    · intro y z
      apply Complex.ext
      · have hh := congrArg Complex.im (hparts y z)
        simpa [Complex.mul_im, hreal] using hh
      · exact hreal _ _ _
    · intro y z
      apply Complex.ext
      · have hh := congrArg Complex.re (hparts y z)
        simpa [Complex.mul_re, hreal] using hh
      · exact hreal _ _ _
  · rintro ⟨hr, hi⟩ y z
    rw [hermitian_complex_cubic_parts, hr, hi, mul_zero, add_zero]

/-- The entire radical, as a subspace, is exactly the scalar extension of the
real radical.  This compares all mixed insertions, not only diagonal cubics. -/
theorem hermitian_complex_radical_eq_baseChange (V : HermitianHalf h q) :
    (complexTraceRadical (complexHermitianRepresentation V)).toSubmodule =
      V.cubicRadical.toSubmodule.baseChange ℂ := by
  ext x
  exact (hermitian_complex_radical_membership V x).trans
    (complexification_mem_baseChange_iff_parts h V.cubicRadical.toSubmodule x).symm

/-- Nonvanishing of the full anomaly radical is preserved and reflected by
complexification of the actual Hermitian representation. -/
theorem hermitian_complex_radical_ne_bot_iff (V : HermitianHalf h q) :
    complexTraceRadical (complexHermitianRepresentation V) ≠ ⊥ ↔ V.cubicRadical ≠ ⊥ := by
  constructor
  · intro hc hr
    apply hc
    apply le_antisymm _ bot_le
    intro x hx
    have hp := (hermitian_complex_radical_membership V x).mp hx
    rw [hr] at hp
    change x = 0
    exact (complexification_zero_iff_parts h x).mpr hp
  · intro hr hc
    apply hr
    apply le_antisymm _ bot_le
    intro x hx
    have hxC : 1 ⊗ₜ[ℝ] x ∈ complexTraceRadical (complexHermitianRepresentation V) := by
      apply (hermitian_complex_radical_membership V _).mpr
      simpa [tensorRealPart, tensorImagPart] using
        (show x ∈ V.cubicRadical ∧ (0 : h) ∈ V.cubicRadical from
          ⟨hx, V.cubicRadical.zero_mem⟩)
    rw [hc] at hxC
    have hx0 : (1 : ℂ) ⊗ₜ[ℝ] x = 0 := hxC
    have hh := congrArg (tensorRealPart h) hx0
    simpa [tensorRealPart] using hh

/-- For a centreless compact isotropy algebra, the original full Hermitian
anomaly condition is equivalent to a finite matrix kernel on any Cartan
subalgebra of its actual complexification. -/
theorem hermitian_radical_ne_bot_iff_cartan_matrix_kernel
    [Module.Finite ℝ h] (B : Structural.CompactForm h)
    (hcenter : LieAlgebra.center ℝ h = ⊥) (V : HermitianHalf h q)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ H) :
    V.cubicRadical ≠ ⊥ ↔
      ∃ v : ι → ℂ, v ≠ 0 ∧
        cartanCubicMatrix H b
          (complexTraceCubicForm (complexHermitianRepresentation V).toLinearMap) *ᵥ v = 0 := by
  letI := compact_complexification_isKilling B hcenter
  rw [← hermitian_complex_radical_ne_bot_iff V]
  exact complex_trace_radical_ne_bot_iff_matrix_kernel H b (complexHermitianRepresentation V)

end HermitianHalf

end CubicAnomaly.Classification.AnomalyComplexification
