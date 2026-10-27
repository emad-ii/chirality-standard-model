import CubicAnomaly.Fixed.E8PairComplexType
import CubicAnomaly.Fixed.E8FullCubic
import CubicAnomaly.Classification.HermitianRealization

set_option Elab.async false

/-!
# The original compact-pair hypotheses for the fixed exceptional algebra

The actual degree-one module and the canonical Hermitian half are complex
linearly equivalent, with the orientation fixed by the proved commutant.
Conjugating their matrices preserves the complete trace cubic. The actual
compact coroots `i * h_a` therefore give nonzero elements of the canonical
Hermitian cubic radical.

This closes the original compact-pair hypotheses on the exact orthogonal
complement used by the universal structural theorem. No representation,
irreducibility, or radical assumption is introduced as input.
-/

namespace CubicAnomaly.Fixed.E8CanonicalPair

open Matrix
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.AllRank
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8Compact
open CubicAnomaly.Fixed.E8CompactGrading
open CubicAnomaly.Fixed.E8CompactPair
open CubicAnomaly.Fixed.E8PairComplexType
open CubicAnomaly.Fixed.E8MatterMatching
open CubicAnomaly.Fixed.E8Matter
open CubicAnomaly.Fixed.E8FullCubic
open CubicAnomaly.Fixed.E8FullCubicData

noncomputable section

set_option maxHeartbeats 800000

/-- The canonical Hermitian half of the actual compact exceptional pair. -/
def canonicalHalf :
    HermitianHalf compactZero (orthogonalComplement compactForm compactZero) :=
  hermitianHalfOfCommutant compactForm compactZero pairCommutantEquivComplex

private def canonicalRealCoordinates :
    ActualMatter ≃ₗ[ℝ] (Fin canonicalHalf.dimension → ℂ) :=
  canonicalRealificationLieEquiv.toLinearEquiv.trans canonicalHalf.coordinates

private theorem canonical_coordinates_I (v : ActualMatter) :
    canonicalRealCoordinates (Complex.I • v) =
      Complex.I • canonicalRealCoordinates v := by
  change canonicalHalf.coordinates (canonicalRealificationLieEquiv (Complex.I • v)) = _
  rw [← e8_canonical_realification_complex_structure]
  exact hermitian_half_coordinates_complexStructure compactForm compactZero
    pairCommutantEquivComplex (canonicalRealificationLieEquiv v)

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

/-- The canonical half has the existing degree-one complex structure. -/
def canonicalMatterCoordinates :
    ActualMatter ≃ₗ[ℂ] (Fin canonicalHalf.dimension → ℂ) where
  toFun := canonicalRealCoordinates
  invFun := canonicalRealCoordinates.symm
  map_add' := canonicalRealCoordinates.map_add
  map_smul' := real_linear_preserving_I_map_smul
    canonicalRealCoordinates.toLinearMap canonical_coordinates_I
  left_inv := canonicalRealCoordinates.symm_apply_apply
  right_inv := canonicalRealCoordinates.apply_symm_apply

/-- The canonical half has exactly the eighty-one constructed complex coordinates. -/
theorem e8_canonical_half_dimension : canonicalHalf.dimension = 81 := by
  have hdim := canonicalMatterCoordinates.finrank_eq
  rw [e8_actual_matter_finrank, Module.finrank_fin_fun] at hdim
  exact hdim.symm

/-- These complex coordinates intertwine the literal compact isotropy action. -/
theorem e8_canonical_matter_action (x : compactZero) (v : ActualMatter) :
    canonicalMatterCoordinates ⁅x, v⁆ =
      Complex.I • (canonicalHalf.generators x *ᵥ canonicalMatterCoordinates v) := by
  change canonicalHalf.coordinates (canonicalRealificationLieEquiv ⁅x, v⁆) =
    Complex.I • (canonicalHalf.generators x *ᵥ
      canonicalHalf.coordinates (canonicalRealificationLieEquiv v))
  have he : canonicalRealificationLieEquiv ⁅x, v⁆ =
      ⁅x, canonicalRealificationLieEquiv v⁆ :=
    canonicalRealificationLieEquiv.map_lie x v
  exact (congrArg canonicalHalf.coordinates he).trans
    (canonicalHalf.action x (canonicalRealificationLieEquiv v))

private theorem full_matrix_operator (x : zeroSubalgebra) :
    (fullMatrixRepresentation x).toLin' =
      actualCoordinates.conj (LieModule.toEnd ℂ zeroSubalgebra ActualMatter x) := by
  simp [fullMatrixRepresentation, LinearEquiv.lieConj_apply]

private def matrixCoordinateChange {U n m : Type*}
    [AddCommGroup U] [Module ℂ U] [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (e : U ≃ₗ[ℂ] (n → ℂ)) (f : U ≃ₗ[ℂ] (m → ℂ)) :
    Matrix n n ℂ ≃ₐ[ℂ] Matrix m m ℂ :=
  Matrix.toLinAlgEquiv'.trans ((e.symm.conjAlgEquiv ℂ).trans
    ((f.conjAlgEquiv ℂ).trans Matrix.toLinAlgEquiv'.symm))

private theorem matrix_coordinate_change_of_action {U n m : Type*}
    [AddCommGroup U] [Module ℂ U] [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (e : U ≃ₗ[ℂ] (n → ℂ)) (f : U ≃ₗ[ℂ] (m → ℂ))
    (T : Module.End ℂ U) (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.toLin' = e.conj T) (hB : ∀ u, f (T u) = B *ᵥ f u) :
    matrixCoordinateChange e f A = B := by
  apply Matrix.toLin'.injective
  change Matrix.toLin' (LinearMap.toMatrix' (f.conj (e.symm.conj A.toLin'))) = _
  rw [Matrix.toLin'_toMatrix', hA, LinearEquiv.conj_symm_conj]
  apply LinearMap.ext
  intro v
  change f (T (f.symm v)) = B *ᵥ v
  rw [hB, f.apply_symm_apply]

private def canonicalMatrixChange :
    Matrix (Fin 27 × Fin 3) (Fin 27 × Fin 3) ℂ ≃ₐ[ℂ]
      Matrix (Fin canonicalHalf.dimension) (Fin canonicalHalf.dimension) ℂ :=
  matrixCoordinateChange actualCoordinates canonicalMatterCoordinates

set_option maxRecDepth 2048 in
private theorem canonical_matrix_change_action (x : compactZero) :
    canonicalMatrixChange (fullMatrixRepresentation (compactZeroToComplex x)) =
      Complex.I • canonicalHalf.generators x := by
  unfold canonicalMatrixChange
  apply matrix_coordinate_change_of_action actualCoordinates canonicalMatterCoordinates
    (LieModule.toEnd ℂ zeroSubalgebra ActualMatter (compactZeroToComplex x))
    (fullMatrixRepresentation (compactZeroToComplex x))
    (Complex.I • canonicalHalf.generators x) (full_matrix_operator _)
  intro v
  change canonicalMatterCoordinates ⁅x, v⁆ =
    (Complex.I • canonicalHalf.generators x) *ᵥ canonicalMatterCoordinates v
  exact (e8_canonical_matter_action x v).trans
    (Matrix.smul_mulVec Complex.I (canonicalHalf.generators x)
      (canonicalMatterCoordinates v)).symm

private theorem canonical_cubic_coordinate_invariance
    (A B C : Matrix (Fin 27 × Fin 3) (Fin 27 × Fin 3) ℂ) :
    matrixTraceCubic (canonicalMatrixChange A) (canonicalMatrixChange B)
      (canonicalMatrixChange C) = matrixTraceCubic A B C :=
  matrix_trace_cubic_algEquiv canonicalMatrixChange A B C

private theorem matrix_trace_cubic_smul_all {n : Type*} [Fintype n]
    (a b c : ℂ) (A B C : Matrix n n ℂ) :
    matrixTraceCubic (a • A) (b • B) (c • C) =
      (a * b * c) * matrixTraceCubic A B C := by
  simp only [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The canonical Hermitian cubic is the full actual cubic, with the
explicit `i³ = -i` normalization of Hermitian generators. -/
theorem e8_canonical_full_cubic (x y z : compactZero) :
    matrixTraceCubic (fullMatrixRepresentation (compactZeroToComplex x))
      (fullMatrixRepresentation (compactZeroToComplex y))
      (fullMatrixRepresentation (compactZeroToComplex z)) =
      (-Complex.I) * matrixTraceCubic (canonicalHalf.generators x)
        (canonicalHalf.generators y) (canonicalHalf.generators z) := by
  rw [← canonical_cubic_coordinate_invariance]
  simp only [canonical_matrix_change_action, matrix_trace_cubic_smul_all,
    Complex.I_mul_I, neg_one_mul]

private theorem imaginary_cartan_fixed (i : Fin 8) :
    compactConjugation (Complex.I • (cartan i).val) =
      Complex.I • (cartan i).val := by
  have hself : (operatorEquiv (cartan i).val.val).adjoint =
      operatorEquiv (cartan i).val.val := by
    rw [e8_full_cartan_matrix]
    exact MatrixCompactForm.metric_matrix_adjoint _ _ _ _
      (E8Adjoints.geck_cartan_weighted_adjoint _)
  apply Subtype.ext
  apply operatorEquiv.injective
  rw [e8_compact_conjugation_operator]
  change -(operatorEquiv (Complex.I • (cartan i).val.val)).adjoint =
    operatorEquiv (Complex.I • (cartan i).val.val)
  simp only [map_smul, map_smulₛₗ, hself]
  simp

/-- The actual compact element `i * h_i`, inside the compact zero algebra. -/
def compactCartan (i : Fin 8) : compactZero :=
  ⟨compactOfFixed (Complex.I • (cartan i).val) (imaginary_cartan_fixed i), by
    change compactToComplex (compactOfFixed _ (imaginary_cartan_fixed i)) ∈ actualGrade 0
    rw [e8_compactToComplex_ofFixed]
    exact (actualGrade 0).smul_mem Complex.I (cartan i).property⟩

theorem e8_compact_cartan_image (i : Fin 8) :
    compactZeroToComplex (compactCartan i) = Complex.I • cartan i := by
  apply Subtype.ext
  exact e8_compactToComplex_ofFixed _ (imaginary_cartan_fixed i)

theorem e8_compact_cartan_ne_zero (i : Fin 8) : compactCartan i ≠ 0 := by
  intro hi
  have hh := congrArg compactZeroToComplex hi
  rw [e8_compact_cartan_image, map_zero] at hh
  exact (smul_ne_zero Complex.I_ne_zero (e8_full_cartan_ne_zero i)) hh

/-- Each of the six actual compact E6 coroots annihilates all mixed
insertions from the entire compact isotropy algebra in the canonical half. -/
theorem e8_canonical_cartan_mem_cubicRadical (a : Fin 6) :
    compactCartan (e6SimpleIndex a) ∈ canonicalHalf.cubicRadical := by
  apply (hermitian_half_cubic_radical_membership canonicalHalf _).mpr
  have hm : compactZeroToComplex (compactCartan (e6SimpleIndex a)) ∈ fullRadical := by
    rw [e8_compact_cartan_image]
    exact fullRadical.smul_mem Complex.I (e8_full_radical_cartan a)
  have hz := (mem_radical_iff (complexTraceCubicForm fullMatrixRepresentation.toLinearMap)
    (complex_trace_cubic_invariant fullMatrixRepresentation) _).mp hm
  intro y z
  have htest := hz (compactZeroToComplex y) (compactZeroToComplex z)
  change matrixTraceCubic
    (fullMatrixRepresentation (compactZeroToComplex (compactCartan (e6SimpleIndex a))))
    (fullMatrixRepresentation (compactZeroToComplex y))
    (fullMatrixRepresentation (compactZeroToComplex z)) = 0 at htest
  rw [e8_canonical_full_cubic] at htest
  exact (mul_eq_zero.mp htest).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)

/-- The original canonical Hermitian half has nonzero full cubic radical. -/
theorem e8_canonical_half_cubicRadical_ne_bot : canonicalHalf.cubicRadical ≠ ⊥ := by
  intro hbot
  have hm := e8_canonical_cartan_mem_cubicRadical (0 : Fin 6)
  rw [hbot, LieSubmodule.mem_bot] at hm
  exact e8_compact_cartan_ne_zero _ hm

/-- The literal original pair hypotheses all hold for the constructed pair. -/
theorem e8_original_pair_hypotheses :
    Effective compactZero ∧ compactZero ≠ ⊤ ∧
      Nonempty (lieCommutant (L := compactZero)
        (M := orthogonalComplement compactForm compactZero) ≃ₐ[ℝ] ℂ) ∧
      (hermitianHalfOfCommutant compactForm compactZero
        pairCommutantEquivComplex).cubicRadical ≠ ⊥ :=
  ⟨e8_compact_pair_effective, e8_compactZero_ne_top,
    ⟨pairCommutantEquivComplex⟩, e8_canonical_half_cubicRadical_ne_bot⟩

/-- Applying the all-rank theorem to the actual pair supplies all five
structural conclusions, including semisimplicity of the compact isotropy. -/
theorem e8_canonical_pair_structural_conclusions :
    LieModule.IsIrreducible ℝ compactZero (orthogonalComplement compactForm compactZero) ∧
      LieModule.IsFaithful ℝ compactZero (orthogonalComplement compactForm compactZero) ∧
      LieAlgebra.IsSimple ℝ compactRealAlgebra ∧
      LieAlgebra.IsSemisimple ℝ compactZero ∧ IsCoatom compactZero :=
  all_rank_structural_reduction compactForm compactZero e8_compact_pair_effective
    e8_compactZero_ne_top pairCommutantEquivComplex canonicalHalf
    e8_canonical_half_cubicRadical_ne_bot

end

end CubicAnomaly.Fixed.E8CanonicalPair
