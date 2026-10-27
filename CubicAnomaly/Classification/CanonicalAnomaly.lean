import CubicAnomaly.Classification.CanonicalHalf
import CubicAnomaly.Classification.MatrixCubic

/-!
# The canonical anomaly as an actual Cartan weight matrix

The positive eigenspace, its canonical Hermitian coordinates, the complexified
Lie action, and the full mixed anomaly radical are connected here to one finite
matrix of actual weight sums.  The weights and multiplicities come from the
module itself; they are not an input table or a classification label.
-/

namespace CubicAnomaly.Classification.CanonicalAnomaly

open Matrix
open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CanonicalHalf
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanCubic
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Classification.AnomalyComplexification
open CubicAnomaly.Classification.MatrixCubic

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- On a Cartan subalgebra, the canonical anomaly representation's cubic is
the sum of the actual positive-half weights, with their actual multiplicities. -/
theorem canonical_cubic_cartan_weight_sum
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    (x y z : H) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    matrixTraceCubic
        (complexHermitianRepresentation (hermitianHalfOfCommutant B h e) x)
        (complexHermitianRepresentation (hermitianHalfOfCommutant B h e) y)
        (complexHermitianRepresentation (hermitianHalfOfCommutant B h e) z) =
      ∑ χ : LieModule.Weight ℂ H V,
        Module.finrank ℂ (LieModule.genWeightSpace V χ) • (χ x * χ y * χ z) := by
  exact matrix_trace_cubic_eq_actual_weight_sum (canonicalPositiveHalfEquiv B h e)
    (fun x : H => complexHermitianRepresentation (hermitianHalfOfCommutant B h e) x)
    (fun x m => canonicalPositiveHalfEquiv_intertwines B h e x m) x y z

/-- The Cartan tensor matrix computed from actual positive-half weights and
generalized weight multiplicities. -/
noncomputable def canonicalCartanWeightMatrix
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    {ι : Type*} (b : Module.Basis ι ℂ H) : Matrix (ι × ι) ι ℂ :=
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  fun jk i => ∑ χ : LieModule.Weight ℂ H V,
    Module.finrank ℂ (LieModule.genWeightSpace V χ) • (χ (b i) * χ (b jk.1) * χ (b jk.2))

/-- The trace matrix and the actual weight matrix agree entry by entry. -/
theorem canonical_cartan_cubic_matrix_eq_weight_matrix
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    {ι : Type*} (b : Module.Basis ι ℂ H) :
    cartanCubicMatrix H b
        (complexTraceCubicForm
          (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)).toLinearMap) =
      canonicalCartanWeightMatrix B h e H b := by
  ext jk i
  exact canonical_cubic_cartan_weight_sum B h e H (b i) (b jk.1) (b jk.2)

/-- The original full mixed anomaly radical is nonzero exactly when the matrix of
actual Cartan weights has a nonzero kernel.  The compact centreless assumption
supplies the complex Killing form required by Cartan detection. -/
theorem canonical_anomaly_iff_cartan_weight_kernel
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ H) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔
      ∃ v : ι → ℂ, v ≠ 0 ∧ canonicalCartanWeightMatrix B h e H b *ᵥ v = 0 := by
  letI := compact_complexification_isKilling (B.restrict h) hcenter
  rw [hermitian_radical_ne_bot_iff_cartan_matrix_kernel
    (B.restrict h) hcenter (hermitianHalfOfCommutant B h e) H b,
    canonical_cartan_cubic_matrix_eq_weight_matrix B h e H b]

end CubicAnomaly.Classification.CanonicalAnomaly
