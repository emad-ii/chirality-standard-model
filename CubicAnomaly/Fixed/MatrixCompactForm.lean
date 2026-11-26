import CubicAnomaly.Classification.UnitaryComplexification
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Compact real forms of adjoint-closed operator algebras

For an actual complex Lie subalgebra of finite-dimensional operators, its
skew-adjoint real part carries the positive invariant negative real trace
form. If the algebra is closed under the actual Hermitian adjoint, explicit
real and imaginary skew parts identify its complexification with the
original complex algebra.
-/

namespace CubicAnomaly.Fixed.MatrixCompactForm

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.UnitaryComplexification
open CubicAnomaly.Classification.ComplexDefining
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- The actual real skew-adjoint part of a complex operator Lie algebra. -/
def realForm (L : LieSubalgebra ℂ (Module.End ℂ W)) :
    LieSubalgebra ℝ (Module.End ℂ W) where
  carrier := {A | A ∈ L ∧ A.adjoint = -A}
  zero_mem' := ⟨L.zero_mem, by simp⟩
  add_mem' := fun hA hB => ⟨L.add_mem hA.1 hB.1,
    (unitaryAlgebra W).add_mem hA.2 hB.2⟩
  smul_mem' := by
    intro r A hA
    exact ⟨by simpa only [Complex.coe_smul] using L.smul_mem (r : ℂ) hA.1,
      (unitaryAlgebra W).smul_mem r hA.2⟩
  lie_mem' := fun hA hB => ⟨L.lie_mem hA.1 hB.1,
    (unitaryAlgebra W).lie_mem hA.2 hB.2⟩

/-- The actual negative real trace pairing on complex operators. -/
def negativeTraceForm : LinearMap.BilinForm ℝ (Module.End ℂ W) :=
  -((LinearMap.mul ℝ (Module.End ℂ W)).compr₂
    (Complex.reLm.comp ((LinearMap.trace ℂ W).restrictScalars ℝ)))

omit [FiniteDimensional ℂ W] in
theorem negative_trace_form_apply (A B : Module.End ℂ W) :
    negativeTraceForm A B = -(LinearMap.trace ℂ W (A * B)).re := rfl

omit [FiniteDimensional ℂ W] in
private theorem negative_trace_form_symmetric (A B : Module.End ℂ W) :
    negativeTraceForm A B = negativeTraceForm B A := by
  rw [negative_trace_form_apply, negative_trace_form_apply,
    LinearMap.trace_mul_comm]

omit [FiniteDimensional ℂ W] in
private theorem negative_trace_form_invariant (A X Y : Module.End ℂ W) :
    negativeTraceForm ⁅A, X⁆ Y = -negativeTraceForm X ⁅A, Y⁆ := by
  change -(LinearMap.trace ℂ W ((A * X - X * A) * Y)).re =
    -(-(LinearMap.trace ℂ W (X * (A * Y - Y * A))).re)
  simp only [sub_mul, mul_sub, map_sub, mul_assoc]
  rw [LinearMap.trace_mul_comm ℂ A (X * Y), mul_assoc]
  simp only [Complex.sub_re]
  ring

private theorem negative_trace_form_positive (A : Module.End ℂ W)
    (hA : A.adjoint = -A) (hne : A ≠ 0) : 0 < negativeTraceForm A A := by
  classical
  let b := stdOrthonormalBasis ℂ W
  have htrace : negativeTraceForm A A =
      ∑ i, (inner ℂ (A (b i)) (A (b i))).re := by
    rw [negative_trace_form_apply, LinearMap.trace_eq_sum_inner _ b]
    rw [Complex.re_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h := (unitary_mem_iff A).mp hA (b i) (A (b i))
    simpa only [Complex.neg_re] using (congrArg Complex.re h).symm
  rw [htrace]
  have hex : ∃ i, A (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    apply b.toBasis.ext
    exact h
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos' (fun j _ => (inner_self_nonneg (𝕜 := ℂ) (x := A (b j))))
  exact ⟨i, Finset.mem_univ i, re_inner_self_pos.mpr hi⟩

/-- The negative real trace is an actual compactness form on the skew part. -/
def compactForm (L : LieSubalgebra ℂ (Module.End ℂ W)) : CompactForm (realForm L) where
  form := negativeTraceForm.restrict (realForm L).toSubmodule
  symmetric x y := negative_trace_form_symmetric x.val y.val
  positive x hx := negative_trace_form_positive x.val x.property.2
    (fun hz => hx (Subtype.ext hz))
  invariant x y z := negative_trace_form_invariant x.val y.val z.val

/-- The form is literally the negative real trace of the two operators. -/
theorem compact_form_trace (L : LieSubalgebra ℂ (Module.End ℂ W))
    (x y : realForm L) :
    (compactForm L).form x y = -(LinearMap.trace ℂ W (x.val * y.val)).re := rfl

instance realForm_finiteDimensional (L : LieSubalgebra ℂ (Module.End ℂ W)) :
    FiniteDimensional ℝ (realForm L) := by
  letI : Module.Finite ℝ (Module.End ℂ W) := Module.Finite.trans ℂ (Module.End ℂ W)
  infer_instance

private theorem extension_mem (L : LieSubalgebra ℂ (Module.End ℂ W))
    (z : ℂ ⊗[ℝ] realForm L) :
    complexifyEndRepresentation (realForm L).incl z ∈ L := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact L.smul_mem a x.property.1
  | add x y hx hy => simpa only [map_add] using L.add_mem hx hy

/-- The literal scalar extension of the inclusion of the real skew part. -/
def complexificationHom (L : LieSubalgebra ℂ (Module.End ℂ W)) :
    (ℂ ⊗[ℝ] realForm L) →ₗ⁅ℂ⁆ L := {
  (complexifyEndRepresentation (realForm L).incl).toLinearMap.codRestrict
    L.toSubmodule (extension_mem L) with
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact (complexifyEndRepresentation (realForm L).incl).map_lie x y }

theorem compact_complexification_injective
    (L : LieSubalgebra ℂ (Module.End ℂ W)) :
    Function.Injective (complexificationHom L) := by
  intro x y h
  exact complexify_skew_map_injective (realForm L).incl.toLinearMap
    Subtype.val_injective (fun x => x.property.2) (congrArg Subtype.val h)

/-- Adjoint closure supplies explicit skew real and imaginary parts. -/
theorem compact_skew_parts (L : LieSubalgebra ℂ (Module.End ℂ W))
    (hadj : ∀ A ∈ L, A.adjoint ∈ L) (A : L) :
    ∃ X Y : realForm L, A.val = X.val + Complex.I • Y.val := by
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
  have hXL : X ∈ L := L.smul_mem _ (L.sub_mem A.property (hadj _ A.property))
  have hYL : Y ∈ L := L.smul_mem _ (L.add_mem A.property (hadj _ A.property))
  refine ⟨⟨X, hXL, hX⟩, ⟨Y, hYL, hY⟩, ?_⟩
  dsimp [X, Y]
  rw [smul_smul]
  have hi : Complex.I * (-Complex.I * (2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  rw [hi]
  module

theorem compact_complexification_surjective
    (L : LieSubalgebra ℂ (Module.End ℂ W))
    (hadj : ∀ A ∈ L, A.adjoint ∈ L) :
    Function.Surjective (complexificationHom L) := by
  intro A
  obtain ⟨X, Y, h⟩ := compact_skew_parts L hadj A
  refine ⟨1 ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y, ?_⟩
  apply Subtype.ext
  change complexifyEndRepresentation (realForm L).incl
    (1 ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y) = A.val
  rw [map_add]
  change (1 : ℂ) • X.val + Complex.I • Y.val = A.val
  rw [one_smul]
  exact h.symm

/-- An adjoint-closed operator Lie algebra is the complexification of its
constructed compact real skew part. -/
def complexificationEquiv (L : LieSubalgebra ℂ (Module.End ℂ W))
    (hadj : ∀ A ∈ L, A.adjoint ∈ L) :
    (ℂ ⊗[ℝ] realForm L) ≃ₗ⁅ℂ⁆ L :=
  LieEquiv.ofBijective (complexificationHom L)
    ⟨compact_complexification_injective L, compact_complexification_surjective L hadj⟩

theorem compact_complexification_equiv_tmul
    (L : LieSubalgebra ℂ (Module.End ℂ W))
    (hadj : ∀ A ∈ L, A.adjoint ∈ L) (a : ℂ) (x : realForm L) :
    (complexificationEquiv L hadj (a ⊗ₜ[ℝ] x)).val = a • x.val := rfl

end

section WeightedMatrices

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A copy of the coordinate space carrying the specified positive Hermitian metric. -/
def MetricSpace (J : Matrix n n ℂ) (_hJ : J.PosDef) := n → ℂ

instance metricSpaceAddCommGroup (J : Matrix n n ℂ) (hJ : J.PosDef) :
    AddCommGroup (MetricSpace J hJ) := inferInstanceAs (AddCommGroup (n → ℂ))

instance metricSpaceModule (J : Matrix n n ℂ) (hJ : J.PosDef) :
    Module ℂ (MetricSpace J hJ) := inferInstanceAs (Module ℂ (n → ℂ))

instance metricSpaceFiniteDimensional (J : Matrix n n ℂ) (hJ : J.PosDef) :
    FiniteDimensional ℂ (MetricSpace J hJ) :=
  inferInstanceAs (FiniteDimensional ℂ (n → ℂ))

/-- The positive matrix gives the literal Hermitian inner-product core. -/
noncomputable def metricInnerCore (J : Matrix n n ℂ) (hJ : J.PosDef) :
    InnerProductSpace.Core ℂ (MetricSpace J hJ) where
  inner x y := star x ⬝ᵥ (J *ᵥ y)
  conj_inner_symm x y := by
    change star (star y ⬝ᵥ (J *ᵥ x)) = star x ⬝ᵥ (J *ᵥ y)
    rw [← star_dotProduct_star, star_star, star_mulVec, hJ.isHermitian]
    exact (dotProduct_mulVec _ _ _).symm
  re_inner_nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (Complex.pos_iff.mp (hJ.dotProduct_mulVec_pos hx)).1.le
  add_left x y z := by
    rw [star_add, add_dotProduct]
  smul_left x y r := by
    change star (r • x) ⬝ᵥ (J *ᵥ y) = _
    rw [star_smul, smul_dotProduct]
    rfl
  definite x hx := by
    by_contra hne
    exact (ne_of_gt (hJ.dotProduct_mulVec_pos hne)) hx

noncomputable instance metricSpaceNormedAddCommGroup
    (J : Matrix n n ℂ) (hJ : J.PosDef) : NormedAddCommGroup (MetricSpace J hJ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (MetricSpace J hJ) _ _ _
    (metricInnerCore J hJ)

noncomputable instance metricSpaceInnerProductSpace
    (J : Matrix n n ℂ) (hJ : J.PosDef) : InnerProductSpace ℂ (MetricSpace J hJ) :=
  InnerProductSpace.ofCore (metricInnerCore J hJ).toCore

omit [DecidableEq n] in
theorem metric_space_inner (J : Matrix n n ℂ) (hJ : J.PosDef)
    (x y : MetricSpace J hJ) :
    inner ℂ x y = star x ⬝ᵥ (J *ᵥ y) := rfl

/-- The actual matrix action on the positively metrized coordinate space. -/
noncomputable def matrixOperatorEquiv (J : Matrix n n ℂ) (hJ : J.PosDef) :
    Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (MetricSpace J hJ) :=
  Matrix.toLinAlgEquiv'

theorem metric_matrix_action (J : Matrix n n ℂ) (hJ : J.PosDef)
    (A : Matrix n n ℂ) (x : MetricSpace J hJ) :
    matrixOperatorEquiv J hJ A x = A *ᵥ x := rfl

/-- A literal weighted conjugate-transpose identity identifies the actual
adjoint of the corresponding operator. -/
theorem metric_matrix_adjoint (J : Matrix n n ℂ) (hJ : J.PosDef)
    (A B : Matrix n n ℂ) (hAB : Aᴴ * J = J * B) :
    (matrixOperatorEquiv J hJ A).adjoint = matrixOperatorEquiv J hJ B := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change star (B *ᵥ x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ (A *ᵥ y))
  have hBA : Bᴴ * J = J * A := by
    have h := congrArg Matrix.conjTranspose hAB
    simpa only [conjTranspose_mul, hJ.isHermitian.eq, conjTranspose_conjTranspose] using h.symm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hBA, ← mulVec_mulVec]

end WeightedMatrices

end CubicAnomaly.Fixed.MatrixCompactForm
