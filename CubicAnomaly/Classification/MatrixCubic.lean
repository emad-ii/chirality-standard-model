import CubicAnomaly.Classification.CartanTrace
import CubicAnomaly.Classification.WeightCubic

/-!
# Basis-independent meaning of the matrix trace cubic

An actual intertwining coordinate equivalence identifies the matrix cubic
with the trace of the corresponding product of Lie-module endomorphisms.
This connects the finite matrix test with weight calculations on the actual
module, independently of the chosen Hermitian basis.
-/

namespace CubicAnomaly.Classification.MatrixCubic

open Matrix
open CubicAnomaly.Classification.CubicRadical

variable {L M n : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [Fintype n] [DecidableEq n]

/-- The matrix cubic of an intertwined action is the basis-independent
trace cubic of the actual Lie module. -/
theorem matrix_trace_cubic_of_intertwining
    (e : M ≃ₗ[ℂ] (n → ℂ)) (T : L → Matrix n n ℂ)
    (haction : ∀ x m, e ⁅x, m⁆ = T x *ᵥ e m) (x y z : L) :
    matrixTraceCubic (T x) (T y) (T z) =
      (1 / 2 : ℂ) * LinearMap.trace ℂ M
        (LieModule.toEnd ℂ L M x *
          (LieModule.toEnd ℂ L M y * LieModule.toEnd ℂ L M z +
            LieModule.toEnd ℂ L M z * LieModule.toEnd ℂ L M y)) := by
  have h (a : L) : (T a).toLin' = e.conj (LieModule.toEnd ℂ L M a) := by
    apply LinearMap.ext
    intro v
    change T a *ᵥ v = e ⁅a, e.symm v⁆
    rw [haction, e.apply_symm_apply]
  have hc : (T x * (T y * T z + T z * T y)).toLin' =
      e.conj (LieModule.toEnd ℂ L M x *
        (LieModule.toEnd ℂ L M y * LieModule.toEnd ℂ L M z +
          LieModule.toEnd ℂ L M z * LieModule.toEnd ℂ L M y)) := by
    simp only [Matrix.toLin'_mul, map_add, h, Module.End.mul_eq_comp, LinearEquiv.conj_comp]
  rw [matrixTraceCubic, ← Matrix.trace_toLin'_eq, hc, LinearMap.trace_conj']

/-- The finite matrix cubic of an abelian action equals the sum over its
actual generalized weights, counted with their multiplicities. -/
theorem matrix_trace_cubic_eq_actual_weight_sum
    [IsLieAbelian L] [FiniteDimensional ℂ M]
    (e : M ≃ₗ[ℂ] (n → ℂ)) (T : L → Matrix n n ℂ)
    (haction : ∀ x m, e ⁅x, m⁆ = T x *ᵥ e m) (x y z : L) :
    matrixTraceCubic (T x) (T y) (T z) =
      ∑ χ : LieModule.Weight ℂ L M,
        Module.finrank ℂ (LieModule.genWeightSpace M χ) • (χ x * χ y * χ z) := by
  rw [matrix_trace_cubic_of_intertwining e T haction]
  exact WeightCubic.symmetrized_trace_cubic_eq_sum_weights (M := M) x y z

end CubicAnomaly.Classification.MatrixCubic
