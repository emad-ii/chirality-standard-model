import CubicAnomaly.Fixed.E8Geck
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic

/-!
# A positive Hermitian metric for the actual E8 matrix construction

An explicit rational Gram factor for the unsigned E8 Cartan matrix gives
the positive form on the eight simple-root coordinates. The remaining
240 root coordinates carry the identity form. Positivity is deduced from
a proved inverse of the factor, with no positivity or compactness premise.
-/

namespace CubicAnomaly.Fixed.E8Metric

open Matrix
open scoped ComplexOrder
open CubicAnomaly.Fixed.E8RootPairing
open CubicAnomaly.Fixed.E8Geck

/-- A rational Gram factor for the unsigned E8 Cartan matrix. -/
def rationalFactor : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1/2, -1, 1, 0, 0, 0, 0, 0;
     -1/2, -1, -1, -1, 0, 0, 0, 0;
     -1/2, 0, 0, 1, 1, 0, 0, 0;
     -1/2, 0, 0, 0, -1, -1, 0, 0;
     -1/2, 0, 0, 0, 0, 1, 1, 0;
     -1/2, 0, 0, 0, 0, 0, -1, -1;
     -1/2, 0, 0, 0, 0, 0, 0, 1;
     1/2, 0, 0, 0, 0, 0, 0, 0]

/-- An explicit inverse for the rational Gram factor. -/
def rationalFactorInverse : Matrix (Fin 8) (Fin 8) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 2;
     -1/2, -1/2, -1/2, -1/2, -1/2, -1/2, -1/2, -5/2;
     1/2, -1/2, -1/2, -1/2, -1/2, -1/2, -1/2, -7/2;
     0, 0, 1, 1, 1, 1, 1, 5;
     0, 0, 0, -1, -1, -1, -1, -4;
     0, 0, 0, 0, 1, 1, 1, 3;
     0, 0, 0, 0, 0, -1, -1, -2;
     0, 0, 0, 0, 0, 0, 1, 1]

theorem rational_factor_left_inverse : rationalFactorInverse * rationalFactor = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rationalFactorInverse, rationalFactor, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rational_factor_gram :
    rationalFactorᵀ * rationalFactor = (4 - CartanMatrix.E₈).map (Int.castRingHom ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rationalFactor, Matrix.mul_apply, Fin.sum_univ_succ, CartanMatrix.E₈,
      Matrix.ofNat_apply]

noncomputable section

/-- The same factor over the complex numbers. -/
def coordinateFactor : Matrix (Fin 8) (Fin 8) ℂ :=
  rationalFactor.map (algebraMap ℚ ℂ)

private def coordinateFactorInverse : Matrix (Fin 8) (Fin 8) ℂ :=
  rationalFactorInverse.map (algebraMap ℚ ℂ)

private theorem coordinate_factor_left_inverse :
    coordinateFactorInverse * coordinateFactor = 1 := by
  have h := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℚ => A.map (algebraMap ℚ ℂ))
    rational_factor_left_inverse
  simpa [coordinateFactorInverse, coordinateFactor, Matrix.map_mul] using h

theorem coordinate_factor_gram :
    coordinateFactorᴴ * coordinateFactor =
      (4 - CartanMatrix.E₈).map (Int.castRingHom ℂ) := by
  have ht : coordinateFactorᴴ = rationalFactorᵀ.map (algebraMap ℚ ℂ) := by
    ext i j
    simp [coordinateFactor, Matrix.conjTranspose_apply]
  rw [ht, coordinateFactor, ← Matrix.map_mul, rational_factor_gram]
  ext i j
  simp

/-- The unsigned Cartan block on the actual simple-root index type. -/
def simpleGram : Matrix base.support base.support ℂ :=
  (4 - base.cartanMatrix).map (Int.castRingHom ℂ)

private def simpleFactor : Matrix base.support base.support ℂ :=
  coordinateFactor.submatrix simpleIndexEquiv.symm simpleIndexEquiv.symm

private def simpleFactorInverse : Matrix base.support base.support ℂ :=
  coordinateFactorInverse.submatrix simpleIndexEquiv.symm simpleIndexEquiv.symm

private theorem simple_factor_left_inverse : simpleFactorInverse * simpleFactor = 1 := by
  simp [simpleFactorInverse, simpleFactor, Matrix.submatrix_mul_equiv,
    coordinate_factor_left_inverse]

private theorem simple_factor_gram : simpleFactorᴴ * simpleFactor = simpleGram := by
  rw [simpleFactor, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    coordinate_factor_gram]
  ext i j
  obtain ⟨i, rfl⟩ := simpleIndexEquiv.surjective i
  obtain ⟨j, rfl⟩ := simpleIndexEquiv.surjective j
  simp [simpleGram, base, simpleBase_cartanMatrix, simpleIndexEquiv,
    Matrix.ofNat_apply, simpleIndex_bijective.1.eq_iff]

/-- The actual positive Hermitian metric on the 248-dimensional defining space. -/
def gramMatrix : Matrix Index Index ℂ := fromBlocks simpleGram 0 0 1

private def fullFactor : Matrix Index Index ℂ := fromBlocks simpleFactor 0 0 1

private def fullFactorInverse : Matrix Index Index ℂ := fromBlocks simpleFactorInverse 0 0 1

private theorem full_factor_left_inverse : fullFactorInverse * fullFactor = 1 := by
  simp [fullFactorInverse, fullFactor, fromBlocks_multiply, simple_factor_left_inverse]

private theorem full_factor_gram : fullFactorᴴ * fullFactor = gramMatrix := by
  simp [fullFactor, gramMatrix, fromBlocks_conjTranspose, fromBlocks_multiply,
    simple_factor_gram]

/-- Positivity follows from an explicit invertible Gram factor. -/
theorem gramMatrix_posDef : gramMatrix.PosDef := by
  rw [← full_factor_gram]
  apply Matrix.PosDef.conjTranspose_mul_self
  intro x y h
  have hx := congrArg (fun z => fullFactorInverse *ᵥ z) h
  simpa [Matrix.mulVec_mulVec, full_factor_left_inverse] using hx

theorem gramMatrix_hermitian : gramMatrix.IsHermitian := gramMatrix_posDef.1

theorem gramMatrix_isUnit : IsUnit gramMatrix := gramMatrix_posDef.isUnit

end

end CubicAnomaly.Fixed.E8Metric
