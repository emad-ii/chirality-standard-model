import CubicAnomaly.Classification.CoordinateCubic
import CubicAnomaly.Classification.RationalKernel

/-!
# The full original anomaly as a rational integer-coordinate kernel

Once the actual positive half is identified with grade one of an actual
root-lattice character, the full anomaly is equivalent to a nonzero
rational kernel of its finite integer-coordinate cubic matrix. All bases,
root multiplicities and scalar-extension comparisons are constructed.
-/

namespace CubicAnomaly.Classification.IntrinsicAnomaly

open Matrix Module
open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.ToralCharacter
open CubicAnomaly.Classification.RootLatticeBasis
open CubicAnomaly.Classification.IntrinsicCartanBasis
open CubicAnomaly.Classification.RootCubicKernel
open CubicAnomaly.Classification.CoordinateCubic
open CubicAnomaly.Classification.RationalKernel

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The original full mixed anomaly is nonzero exactly when the finite
integer root-coordinate cubic has a nonzero rational kernel. The character
and grade identity here are constructed by the original-hypothesis toral
endpoint; they are not a classification or census-membership assumption. -/
theorem canonical_anomaly_iff_intrinsic_rational_kernel
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h)
    (character : rootLattice H →+ ZMod 3)
    (hone : rootCharacterGrade H character 1 =
      (ambientComplexifiedHalf (orthogonalComplement B h)
        (commutantComplexStructure e) Complex.I).toSubmodule) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔
      ∃ v : Fin (finrank ℂ H) → ℚ, v ≠ 0 ∧
        (intrinsicCoordinateCubicMatrix H
          (fun i => character (intrinsicRootBasis H i)) 1).map (Int.cast : ℤ → ℚ) *ᵥ v = 0 := by
  rw [canonical_anomaly_iff_actual_root_kernel B h heff hproper e hcenter
    H hH (intrinsicCartanBasis H), ← hone,
    actual_root_cubic_matrix_eq_intrinsic_coordinates H character 1]
  exact integer_matrix_complex_kernel_iff_rational _

end CubicAnomaly.Classification.IntrinsicAnomaly
