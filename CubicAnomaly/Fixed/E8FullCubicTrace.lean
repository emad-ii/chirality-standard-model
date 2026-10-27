import CubicAnomaly.Fixed.E8FullCubicCoordinates
import Mathlib.LinearAlgebra.Trace

/-! Exact trace-cubic binding in the actual homogeneous root coordinates. -/

namespace CubicAnomaly.Fixed.E8FullCubic

open Matrix
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8BracketBinding
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8FullCubicData
open CubicAnomaly.Fixed.E8MatterMatching
open CubicAnomaly.Fixed.E8Matter
open CubicAnomaly.Fixed.E8ClassicalEmbedding
open CubicAnomaly.Fixed.MatterFamilyAnomaly
open CubicAnomaly.Fixed.FamilyAnomaly
open CubicAnomaly.Fixed.TensorAnomaly
open scoped BigOperators

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 200000
set_option Elab.async false

private theorem full_matrix_operator (x : zeroSubalgebra) :
    (fullMatrixRepresentation x).toLin' =
      actualCoordinates.conj (LieModule.toEnd ℂ zeroSubalgebra ActualMatter x) := by
  simp [fullMatrixRepresentation, LinearEquiv.lieConj_apply]

private def cubicCoordinateChange :
    Matrix (Fin 27 × Fin 3) (Fin 27 × Fin 3) ℂ ≃ₐ[ℂ]
      Matrix (GradeLabel 1) (GradeLabel 1) ℂ :=
  Matrix.toLinAlgEquiv'.trans ((actualCoordinates.symm.conjAlgEquiv ℂ).trans
    (LinearMap.toMatrixAlgEquiv (gradeBasis 1)))

private theorem cubicCoordinateChange_apply (x : zeroSubalgebra) :
    cubicCoordinateChange (fullMatrixRepresentation x) =
      LinearMap.toMatrix (gradeBasis 1) (gradeBasis 1)
        (LieModule.toEnd ℂ zeroSubalgebra ActualMatter x) := by
  change LinearMap.toMatrix (gradeBasis 1) (gradeBasis 1)
    (actualCoordinates.symm.conj ((fullMatrixRepresentation x).toLin')) = _
  simp only [full_matrix_operator, LinearEquiv.conj_symm_conj]

/-- A complex matrix-algebra equivalence preserves the entire mixed trace cubic. -/
theorem matrix_trace_cubic_algEquiv {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (e : Matrix n n ℂ ≃ₐ[ℂ] Matrix m m ℂ) (A B C : Matrix n n ℂ) :
    matrixTraceCubic (e A) (e B) (e C) = matrixTraceCubic A B C := by
  unfold matrixTraceCubic
  simp only [← map_mul, ← map_add, Matrix.trace_map]

private theorem cubic_coordinate_invariance
    (A B C : Matrix (Fin 27 × Fin 3) (Fin 27 × Fin 3) ℂ) :
    matrixTraceCubic (cubicCoordinateChange A) (cubicCoordinateChange B)
      (cubicCoordinateChange C) = matrixTraceCubic A B C :=
  matrix_trace_cubic_algEquiv cubicCoordinateChange A B C

private theorem matrix_of_eigenbasis {n V : Type*} [Fintype n] [DecidableEq n]
    [AddCommGroup V] [Module ℂ V] (b : Module.Basis n ℂ V)
    (T : Module.End ℂ V) (w : n → ℂ)
    (hw : ∀ i, T (b i) = w i • b i) :
    LinearMap.toMatrix b b T = Matrix.diagonal w := by
  ext i j
  rw [LinearMap.toMatrix_apply, hw]
  by_cases hij : i = j
  · subst j
    simp
  · simp [Matrix.diagonal, hij]

private theorem cartan_matrix_diagonal (i : Fin 8) :
    LinearMap.toMatrix (gradeBasis 1) (gradeBasis 1)
      (LieModule.toEnd ℂ zeroSubalgebra ActualMatter (cartan i)) =
      Matrix.diagonal (fun d : GradeLabel 1 => (labelWeight d.val i : ℂ)) :=
  matrix_of_eigenbasis (gradeBasis 1)
    (LieModule.toEnd ℂ zeroSubalgebra ActualMatter (cartan i))
    (fun d => (labelWeight d.val i : ℂ)) (e8_full_cartan_basis_action i 1)

private theorem matrixTraceCubic_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (u v w : n → ℂ) :
    matrixTraceCubic (Matrix.diagonal u) (Matrix.diagonal v) (Matrix.diagonal w) =
      ∑ d, u d * v d * w d := by
  unfold matrixTraceCubic
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.trace_diagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  change (1 / 2 : ℂ) * (u d * (v d * w d + w d * v d)) = u d * v d * w d
  ring

private theorem integral_cubic_sum {α : Type*} (s : Finset α)
    {F : Fintype {a : α // a ∈ s}} (u v w : α → ℤ) :
    (∑ a : {a : α // a ∈ s}, (u a.val : ℂ) * (v a.val : ℂ) * (w a.val : ℂ)) =
      ((∑ a ∈ s, u a * v a * w a : ℤ) : ℂ) := by
  classical
  rw [← Finset.sum_subtype (F := F) s (fun _ => Iff.rfl)
    (fun a => (u a : ℂ) * (v a : ℂ) * (w a : ℂ))]
  simp only [Int.cast_sum, Int.cast_mul]

/-- The checked integral tensor is the Cartan restriction of the actual full action. -/
theorem e8_full_cubic_cartan_tensor (i j k : Fin 8) :
    matrixTraceCubic (fullMatrixRepresentation (cartan i))
      (fullMatrixRepresentation (cartan j)) (fullMatrixRepresentation (cartan k)) =
      (cartanTensor i j k : ℂ) := by
  classical
  rw [← cubic_coordinate_invariance]
  simp only [cubicCoordinateChange_apply, cartan_matrix_diagonal]
  rw [matrixTraceCubic_diagonal]
  exact integral_cubic_sum (gradeLabels 1)
    (fun d => labelWeight d i) (fun d => labelWeight d j) (fun d => labelWeight d k)

end

end CubicAnomaly.Fixed.E8FullCubic
