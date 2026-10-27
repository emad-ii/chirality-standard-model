import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Complex.Basic

/-!
# Descent of nonzero matrix kernels

A matrix over a field has a nonzero kernel after scalar extension exactly
when it already has one over the original field.  A linear functional on
the extension field extracts a nonzero original-field solution from an
extended solution.  The proof needs neither elimination nor a rank formula.

In particular, an integer anomaly matrix has nonzero complex kernel exactly
when it has nonzero rational kernel.  There is no bound on either matrix
dimension; only the column index must be finite to form the row sums.
-/

namespace CubicAnomaly.Classification.RationalKernel

open Matrix Module

variable {K E m n : Type*} [Field K] [Field E] [Algebra K E] [Fintype n]

/-- A nonzero kernel vector over an extension field exists exactly when a
nonzero kernel vector exists over the original field. -/
theorem nonzero_kernel_map_iff (A : Matrix m n K) :
    (∃ v : n → E, v ≠ 0 ∧ (A.map (algebraMap K E)) *ᵥ v = 0) ↔
      ∃ v : n → K, v ≠ 0 ∧ A *ᵥ v = 0 := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hj
    refine ⟨fun i => f (v i), ?_, ?_⟩
    · intro hz
      have h := congrFun hz j
      change f (v j) = 0 at h
      rw [hf] at h
      exact one_ne_zero h
    · funext i
      have h := congrArg f (congrFun hAv i)
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
        ← Algebra.smul_def, map_smul, smul_eq_mul, Pi.zero_apply, map_zero] using h
  · rintro ⟨v, hv, hAv⟩
    refine ⟨fun i => algebraMap K E (v i), ?_, ?_⟩
    · intro hz
      apply hv
      funext i
      apply (algebraMap K E).injective
      simpa only [Pi.zero_apply, map_zero] using congrFun hz i
    · funext i
      have h := congrArg (algebraMap K E) (congrFun hAv i)
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
        map_mul, Pi.zero_apply, map_zero] using h

/-- The complex and rational kernel tests agree for every rectangular
integer matrix. -/
theorem integer_matrix_complex_kernel_iff_rational (A : Matrix m n ℤ) :
    (∃ v : n → ℂ, v ≠ 0 ∧ (A.map (Int.cast : ℤ → ℂ)) *ᵥ v = 0) ↔
      ∃ v : n → ℚ, v ≠ 0 ∧ (A.map (Int.cast : ℤ → ℚ)) *ᵥ v = 0 := by
  simpa only [Matrix.map_map, Function.comp_def, map_intCast] using
    (nonzero_kernel_map_iff (E := ℂ) (A.map (Int.cast : ℤ → ℚ)))

end CubicAnomaly.Classification.RationalKernel
