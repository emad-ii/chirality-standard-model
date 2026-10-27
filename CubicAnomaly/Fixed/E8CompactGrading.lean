import CubicAnomaly.Fixed.E8Compact
import CubicAnomaly.Fixed.E8Grading
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Compact conjugation reverses the actual exceptional grading

Homogeneity is first recognized by the support of the actual adjoint matrices.
The positive metric and its inverse have degree zero. Thus the weighted
Hermitian adjoint reverses matrix degree and, by the faithful adjoint
identification, reverses the actual Lie algebra grading.
-/

namespace CubicAnomaly.Fixed.E8CompactGrading

open Matrix
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8Metric
open CubicAnomaly.Fixed.E8Compact
open scoped BigOperators

noncomputable section

instance lieAlgebraReal : LieAlgebra ℝ E8Geck.lieAlgebra where
  lie_smul r x y := by
    apply Subtype.ext
    exact lie_smul r x.val y.val

instance operatorAlgebraReal : LieAlgebra ℝ operatorAlgebra where
  lie_smul r x y := by
    apply Subtype.ext
    exact lie_smul r x.val y.val

/-- Operators whose nonzero entries shift the coordinate degree by `a`. -/
def matrixGrade (a : ZMod 3) : Submodule ℂ (Matrix Index Index ℂ) where
  carrier := {A | ∀ i j, indexGrade i ≠ a + indexGrade j → A i j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i j hij
    simp [hA i j hij, hB i j hij]
  smul_mem' := by
    intro c A hA i j hij
    simp [hA i j hij]

/-- Extract the entries having a prescribed degree shift. -/
def matrixProjection (a : ZMod 3) :
    Matrix Index Index ℂ →ₗ[ℂ] Matrix Index Index ℂ where
  toFun A i j := if indexGrade i = a + indexGrade j then A i j else 0
  map_add' := by
    intro A B
    ext i j
    by_cases h : indexGrade i = a + indexGrade j <;> simp [h]
  map_smul' := by
    intro c A
    ext i j
    by_cases h : indexGrade i = a + indexGrade j <;> simp [h]

theorem matrix_projection_mem (a : ZMod 3) (A : Matrix Index Index ℂ) :
    matrixProjection a A ∈ matrixGrade a := by
  intro i j hij
  exact if_neg hij

theorem matrix_projection_of_homogeneous (a b : ZMod 3)
    (A : Matrix Index Index ℂ) (hA : A ∈ matrixGrade b) :
    matrixProjection a A = if a = b then A else 0 := by
  classical
  ext i j
  by_cases hab : a = b
  · subst b
    by_cases hij : indexGrade i = a + indexGrade j
    · simp [matrixProjection, hij]
    · simp [matrixProjection, hij, hA i j hij]
  · have hzero (hij : indexGrade i = a + indexGrade j) : A i j = 0 := by
      apply hA i j
      intro hbj
      exact hab (add_right_cancel (hij.symm.trans hbj))
    by_cases hij : indexGrade i = a + indexGrade j <;>
      simp [matrixProjection, hab, hij, hzero]

theorem grade_projection_of_homogeneous (a b : ZMod 3)
    (v : E8Geck.DefiningSpace) (hv : v ∈ gradeSpace b) :
    gradeProjection a v = if a = b then v else 0 := by
  classical
  ext i
  by_cases hab : a = b
  · subst b
    by_cases hi : indexGrade i = a <;> simp [gradeProjection, hi, hv i]
  · by_cases hi : indexGrade i = a
    · have hbi : indexGrade i ≠ b := fun hb => hab (hi.symm.trans hb)
      simp [gradeProjection, hi, hab, hv i hbi]
    · simp [gradeProjection, hi, hab]

/-- The actual adjoint of a homogeneous vector has the corresponding matrix shift. -/
theorem e8_bracketMatrixMap_homogeneous (a : ZMod 3)
    (v : E8Geck.DefiningSpace) (hv : v ∈ gradeSpace a) :
    bracketMatrixMap v ∈ matrixGrade a := by
  classical
  intro i j hij
  have hj : Pi.single j (1 : ℂ) ∈ gradeSpace (indexGrade j) := by
    simpa only [indexGrade, e8_basisVector_dataIndex] using
      e8_basisVector_homogeneous (dataIndex j)
  have h := e8_bilinear_map_graded candidateBracket
    (fun i j => e8_candidateBracket_labels _ _ (e8_dataIndex_mem_basisList i)
      (e8_dataIndex_mem_basisList j)) a (indexGrade j) v (Pi.single j 1) hv hj
  have hz := h i hij
  rw [← e8_bracketMatrixMap_mulVec] at hz
  simpa only [Matrix.mulVec_single_one] using hz

/-- Coordinate and matrix projections agree under the actual faithful adjoint map. -/
theorem e8_matrixProjection_bracketMatrixMap (a : ZMod 3)
    (v : E8Geck.DefiningSpace) :
    matrixProjection a (bracketMatrixMap v) =
      bracketMatrixMap (gradeProjection a v) := by
  classical
  have he : v = ∑ i : Index, v i • basisVector (dataIndex i) := by
    simp only [e8_basisVector_dataIndex]
    exact pi_eq_sum_univ' v
  rw [he]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  have hi := e8_basisVector_homogeneous (dataIndex i)
  rw [matrix_projection_of_homogeneous _ _ _ (e8_bracketMatrixMap_homogeneous _ _ hi),
    grade_projection_of_homogeneous _ _ _ hi]
  split_ifs <;> simp

/-- Matrix support recognizes actual homogeneous elements, in both directions. -/
theorem e8_actualGrade_iff_matrixGrade (a : ZMod 3) (x : E8Geck.lieAlgebra) :
    x ∈ actualGrade a ↔ x.val ∈ matrixGrade a := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact e8_bracketMatrixMap_homogeneous a v hv
  · intro hx
    let v := adjointEquiv.symm x
    have hproj : gradeProjection a v = v := by
      apply e8_bracketMatrixMap_injective
      rw [← e8_matrixProjection_bracketMatrixMap]
      have hm : bracketMatrixMap v ∈ matrixGrade a := by
        change (adjointEquiv v).val ∈ matrixGrade a
        simpa only [v, adjointEquiv.apply_symm_apply] using hx
      simpa only [if_pos rfl] using matrix_projection_of_homogeneous a a _ hm
    refine ⟨v, ?_, adjointEquiv.apply_symm_apply x⟩
    rw [← hproj]
    exact e8_gradeProjection_homogeneous a v

theorem matrix_grade_mul (a b : ZMod 3) (A B : Matrix Index Index ℂ)
    (hA : A ∈ matrixGrade a) (hB : B ∈ matrixGrade b) :
    A * B ∈ matrixGrade (a + b) := by
  classical
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : indexGrade i = a + indexGrade k
  · have hkj : indexGrade k ≠ b + indexGrade j := by
      intro hkj
      apply hij
      rw [hik, hkj, add_assoc]
    rw [hB k j hkj, mul_zero]
  · rw [hA i k hik, zero_mul]

theorem matrix_grade_conjTranspose (a : ZMod 3) (A : Matrix Index Index ℂ)
    (hA : A ∈ matrixGrade a) : Aᴴ ∈ matrixGrade (-a) := by
  intro i j hij
  change star (A j i) = 0
  rw [hA j i, star_zero]
  intro hji
  apply hij
  rw [hji, ← add_assoc, neg_add_cancel, zero_add]

private theorem gram_blocks_homogeneous (S : Matrix base.support base.support ℂ) :
    Matrix.fromBlocks S 0 0 1 ∈ matrixGrade 0 := by
  classical
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => exact False.elim (hij (by rfl))
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j =>
      change (1 : Matrix _ _ ℂ) i j = 0
      apply Matrix.one_apply_ne
      intro h
      subst j
      exact hij (zero_add _).symm

theorem e8_gramMatrix_homogeneous : gramMatrix ∈ matrixGrade 0 :=
  gram_blocks_homogeneous simpleGram

theorem e8_gramMatrix_inverse_homogeneous : gramMatrix⁻¹ ∈ matrixGrade 0 := by
  have hS : IsUnit simpleGram :=
    (Matrix.isUnit_fromBlocks_zero₂₁.mp gramMatrix_isUnit).1
  have hiff : IsUnit simpleGram ↔ IsUnit (1 : Matrix E8RootPairing.Root E8RootPairing.Root ℂ) :=
    ⟨fun _ => isUnit_one, fun _ => hS⟩
  rw [gramMatrix, Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ hiff]
  simpa only [Matrix.mul_zero, Matrix.zero_mul, neg_zero, inv_one] using
    gram_blocks_homogeneous simpleGram⁻¹

/-- The literal weighted Hermitian adjoint of an actual matrix. -/
def weightedAdjoint (A : Matrix Index Index ℂ) : Matrix Index Index ℂ :=
  gramMatrix⁻¹ * Aᴴ * gramMatrix

theorem e8_weightedAdjoint_operator (A : Matrix Index Index ℂ) :
    operatorEquiv (weightedAdjoint A) = (operatorEquiv A).adjoint := by
  symm
  apply MatrixCompactForm.metric_matrix_adjoint
  change Aᴴ * gramMatrix = gramMatrix * (gramMatrix⁻¹ * Aᴴ * gramMatrix)
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left]
  exact (Matrix.isUnit_iff_isUnit_det _).mp gramMatrix_isUnit

theorem e8_weightedAdjoint_homogeneous (a : ZMod 3) (A : Matrix Index Index ℂ)
    (hA : A ∈ matrixGrade a) : weightedAdjoint A ∈ matrixGrade (-a) := by
  simpa only [zero_add, add_zero] using
    matrix_grade_mul (0 + -a) 0 (gramMatrix⁻¹ * Aᴴ) gramMatrix
      (matrix_grade_mul 0 (-a) _ _ e8_gramMatrix_inverse_homogeneous
        (matrix_grade_conjTranspose a A hA)) e8_gramMatrix_homogeneous

private def operatorConjugation : operatorAlgebra →ₗ⁅ℝ⁆ operatorAlgebra where
  toFun A := ⟨-A.val.adjoint, operatorAlgebra.neg_mem (e8_operator_adjoint_closed _ A.property)⟩
  map_add' A B := by
    apply Subtype.ext
    change -(A.val + B.val).adjoint = -A.val.adjoint + -B.val.adjoint
    rw [map_add]
    abel
  map_smul' r A := by
    apply Subtype.ext
    change -((r : ℂ) • A.val).adjoint = (r : ℂ) • -A.val.adjoint
    rw [map_smulₛₗ]
    simp only [Complex.conj_ofReal, smul_neg]
  map_lie' := by
    intro A B
    apply Subtype.ext
    change -((A.val.comp B.val - B.val.comp A.val).adjoint) =
      (-A.val.adjoint).comp (-B.val.adjoint) - (-B.val.adjoint).comp (-A.val.adjoint)
    rw [map_sub, LinearMap.adjoint_comp, LinearMap.adjoint_comp]
    simp only [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]
    abel

private theorem operatorConjugation_involutive : Function.Involutive operatorConjugation := by
  intro A
  apply Subtype.ext
  change -(-A.val.adjoint).adjoint = A.val
  simp

/-- The actual operator identification, with scalars restricted to the reals. -/
def operatorAlgebraEquivReal : E8Geck.lieAlgebra ≃ₗ⁅ℝ⁆ operatorAlgebra := {
  operatorAlgebraEquiv.toLinearEquiv.restrictScalars ℝ with
  map_lie' := by intro x y; exact operatorAlgebraEquiv.map_lie x y }

/-- Compact conjugation of the actual exceptional algebra: minus the metric adjoint. -/
def compactConjugation : E8Geck.lieAlgebra ≃ₗ⁅ℝ⁆ E8Geck.lieAlgebra :=
  (operatorAlgebraEquivReal.trans
    (LieEquiv.ofBijective operatorConjugation operatorConjugation_involutive.bijective)).trans
      operatorAlgebraEquivReal.symm

theorem e8_compact_conjugation_operator (x : E8Geck.lieAlgebra) :
    operatorEquiv (compactConjugation x).val = -(operatorEquiv x.val).adjoint := by
  change operatorEquiv (operatorEquiv.symm (-(operatorEquiv x.val).adjoint)) = _
  exact operatorEquiv.apply_symm_apply _

theorem e8_compact_conjugation_matrix (x : E8Geck.lieAlgebra) :
    (compactConjugation x).val = -weightedAdjoint x.val := by
  apply operatorEquiv.injective
  rw [e8_compact_conjugation_operator, map_neg, e8_weightedAdjoint_operator]

theorem e8_compact_conjugation_involutive : Function.Involutive compactConjugation := by
  intro x
  apply Subtype.ext
  apply operatorEquiv.injective
  rw [e8_compact_conjugation_operator, e8_compact_conjugation_operator]
  simp

theorem e8_compact_conjugation_smul (c : ℂ) (x : E8Geck.lieAlgebra) :
    compactConjugation (c • x) = star c • compactConjugation x := by
  apply Subtype.ext
  apply operatorEquiv.injective
  change operatorEquiv (compactConjugation (c • x)).val =
    operatorEquiv (star c • (compactConjugation x).val)
  rw [e8_compact_conjugation_operator, map_smul, e8_compact_conjugation_operator]
  change -(operatorEquiv (c • x.val)).adjoint = _
  rw [map_smul, map_smulₛₗ]
  simp only [smul_neg]
  rfl

/-- Compact conjugation exchanges degree one and degree two, and preserves degree zero. -/
theorem e8_compact_conjugation_graded (a : ZMod 3) (x : E8Geck.lieAlgebra)
    (hx : x ∈ actualGrade a) : compactConjugation x ∈ actualGrade (-a) := by
  apply (e8_actualGrade_iff_matrixGrade _ _).mpr
  rw [e8_compact_conjugation_matrix]
  exact (matrixGrade (-a)).neg_mem
    (e8_weightedAdjoint_homogeneous a x.val ((e8_actualGrade_iff_matrixGrade a x).mp hx))

/-- The literal inclusion of the existing compact real form into the complex algebra. -/
def compactToComplex : compactRealAlgebra →ₗ⁅ℝ⁆ E8Geck.lieAlgebra where
  toFun x := operatorAlgebraEquiv.symm ⟨x.val, x.property.1⟩
  map_add' x y := by apply Subtype.ext; exact map_add operatorEquiv.symm x.val y.val
  map_smul' r x := by
    apply Subtype.ext
    change operatorEquiv.symm ((r : ℂ) • x.val) = (r : ℂ) • operatorEquiv.symm x.val
    exact map_smul operatorEquiv.symm (r : ℂ) x.val
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact operatorEquiv.symm.toLieEquiv.map_lie x.val y.val

theorem e8_compactToComplex_injective : Function.Injective compactToComplex := by
  intro x y h
  apply Subtype.ext
  exact operatorEquiv.symm.injective (congrArg Subtype.val h)

theorem e8_compactToComplex_operator (x : compactRealAlgebra) :
    operatorEquiv (compactToComplex x).val = x.val :=
  operatorEquiv.apply_symm_apply x.val

theorem e8_compactToComplex_fixed (x : compactRealAlgebra) :
    compactConjugation (compactToComplex x) = compactToComplex x := by
  apply Subtype.ext
  apply operatorEquiv.injective
  rw [e8_compact_conjugation_operator, e8_compactToComplex_operator, x.property.2, neg_neg]

/-- Every fixed point of compact conjugation is an element of the existing real form. -/
def compactOfFixed (x : E8Geck.lieAlgebra) (hx : compactConjugation x = x) :
    compactRealAlgebra :=
  ⟨operatorEquiv x.val, ⟨x.val, x.property, rfl⟩, by
    have h := congrArg (fun z : E8Geck.lieAlgebra => operatorEquiv z.val) hx
    change operatorEquiv (compactConjugation x).val = operatorEquiv x.val at h
    rw [e8_compact_conjugation_operator] at h
    exact neg_eq_iff_eq_neg.mp h⟩

theorem e8_compactToComplex_ofFixed (x : E8Geck.lieAlgebra)
    (hx : compactConjugation x = x) : compactToComplex (compactOfFixed x hx) = x := by
  apply Subtype.ext
  exact operatorEquiv.symm_apply_apply x.val

end

end CubicAnomaly.Fixed.E8CompactGrading
