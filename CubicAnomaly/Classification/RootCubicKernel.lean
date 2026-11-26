import CubicAnomaly.Classification.CommonCartanAnomaly
import CubicAnomaly.Classification.CanonicalRootCubic

/-!
# The original full anomaly as the actual grade-one root cubic

The canonical representation and its full mixed radical are connected to
the unweighted ambient root sum on the same common Cartan. This identifies
the mathematical cubic and finite kernel tested by a toral census, without
supplying a representation table or changing the Cartan.
-/

namespace CubicAnomaly.Classification.RootCubicKernel

open Matrix Module
open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.RootSupportTrace
open CubicAnomaly.Classification.CommonCartanAnomaly
open CubicAnomaly.Classification.CanonicalRootCubic

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The finite matrix of the actual ambient root cubic. Every supported
root is counted once; no multiplicities are supplied. -/
noncomputable def actualRootCubicMatrix
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (N : Submodule K L) {ι : Type*} (b : Basis ι K H) : Matrix (ι × ι) ι K :=
  fun jk i => actualRootCubic H N (b i) (b jk.1) (b jk.2)

/-- Every canonical trace-cubic matrix entry is the actual grade-one
root-cubic entry in the same Cartan basis. -/
theorem common_cartan_matrix_eq_actual_root_matrix
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h)
    {ι : Type*} (b : Basis ι ℂ H) :
    commonCartanCubicMatrix B h e H hH b =
      actualRootCubicMatrix H
        (ambientComplexifiedHalf (orthogonalComplement B h)
          (commutantComplexStructure e) Complex.I).toSubmodule b := by
  ext jk i
  exact canonical_matrix_cubic_eq_actual_root_sum B h heff hproper e H hH
    (b i) (b jk.1) (b jk.2)

/-- The original full mixed radical is nonzero exactly when the actual
grade-one root-cubic matrix has a nonzero kernel. Centrelessness is the
structural consequence used for the Cartan detection equivalence. -/
theorem canonical_anomaly_iff_actual_root_kernel
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h)
    {ι : Type*} [Fintype ι] (b : Basis ι ℂ H) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔
      ∃ v : ι → ℂ, v ≠ 0 ∧
        actualRootCubicMatrix H
          (ambientComplexifiedHalf (orthogonalComplement B h)
            (commutantComplexStructure e) Complex.I).toSubmodule b *ᵥ v = 0 := by
  rw [canonical_anomaly_iff_common_cartan_kernel B h e hcenter H hH b,
    common_cartan_matrix_eq_actual_root_matrix B h heff hproper e H hH b]

/-- The full original anomaly condition is the actual grade-one root sum
vanishing on a nonzero Cartan vector against every remaining Cartan pair. -/
theorem canonical_anomaly_iff_actual_root_cubic
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔
      ∃ x : H, x ≠ 0 ∧ ∀ y z : H,
        actualRootCubic H
          (ambientComplexifiedHalf (orthogonalComplement B h)
            (commutantComplexStructure e) Complex.I).toSubmodule x y z = 0 := by
  rw [canonical_anomaly_iff_common_cartan_cubic B h e hcenter H hH]
  simp_rw [canonical_matrix_cubic_eq_actual_root_sum B h heff hproper e H hH]

end CubicAnomaly.Classification.RootCubicKernel
