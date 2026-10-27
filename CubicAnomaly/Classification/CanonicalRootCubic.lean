import CubicAnomaly.Classification.RootSupportTrace
import CubicAnomaly.Classification.CanonicalHalf
import CubicAnomaly.Classification.MatrixCubic
import CubicAnomaly.Classification.ContainedCartan

/-!
# The canonical anomaly cubic as an actual ambient root sum

For a common Cartan, the canonical positive-half matrix representation has
exactly the cubic obtained by summing its actual ambient roots, each once.
The Cartan elements are lifted through the actual complexified inclusion of
the isotropy algebra. The equality uses the canonical equivariant half
coordinates and the one-dimensionality of the ambient root spaces.

The root sum and the matrix cubic refer to the same Cartan and the same
actual positive half. No root coordinate table or multiplicity assumption
is part of the statement.
-/

namespace CubicAnomaly.Classification.CanonicalRootCubic

open Matrix
open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.AnomalyComplexification
open CubicAnomaly.Classification.CanonicalHalf
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.ContainedCartan
open CubicAnomaly.Classification.EqualRank
open CubicAnomaly.Classification.RootSupportTrace

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The actual canonical matrix cubic is the unweighted sum of the cubic
root evaluations on the actual positive ambient half, on the same common
Cartan. No anomaly hypothesis or authored root realization is needed. -/
theorem canonical_matrix_cubic_eq_actual_root_sum
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) (x y z : H) :
    matrixTraceCubic
        (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
          (commonCartanLift h H hH x))
        (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
          (commonCartanLift h H hH y))
        (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
          (commonCartanLift h H hH z)) =
      actualRootCubic H
        (ambientComplexifiedHalf (orthogonalComplement B h)
          (commutantComplexStructure e) Complex.I).toSubmodule x y z := by
  let q := orthogonalComplement B h
  let J := commutantComplexStructure e
  let P₀ := ambientComplexifiedHalf q J Complex.I
  let Q₀ := ambientComplexifiedHalf q J (-Complex.I)
  let S := complexifiedSubalgebra h
  let P := imageActionSubmodule h P₀
  let Q := imageActionSubmodule h Q₀
  let N := restrictCartanSubmodule H S hH P
  have hgcenter := (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) :=
    compact_complexification_isKilling B hgcenter
  have hPQ : P.toSubmodule ⊔ Q.toSubmodule = q.toSubmodule.baseChange ℂ :=
    congrArg LieSubmodule.toSubmodule
      (ambient_complex_halves_sup q J (commutant_complex_structure_square e))
  have hdis : Disjoint S.toSubmodule (P.toSubmodule ⊔ Q.toSubmodule) := by
    rw [hPQ]
    exact (compact_pair_complexification_isCompl B h).disjoint
  have hHS : H.toSubmodule ≤ S.toSubmodule := hH
  have hN : Disjoint H.toSubmodule N.toSubmodule :=
    (hdis.mono_left hHS).mono_right le_sup_left
  let D := ambientHalfEquiv q J Complex.I
  let E : N ≃ₗ[ℂ] (Fin (hermitianHalfOfCommutant B h e).dimension → ℂ) :=
    D.symm.toLinearEquiv.trans (canonicalPositiveHalfEquiv B h e)
  let T := fun a : H => complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
    (commonCartanLift h H hH a)
  have haction : ∀ a m, E ⁅a, m⁆ = T a *ᵥ E m := by
    intro a m
    have ha : (⁅a, m⁆ : N) = (⁅commonCartanLift h H hH a, (m : P₀)⁆ : P₀) := by
      apply Subtype.ext
      exact (commonCartanLift_action h H hH a (m : ℂ ⊗[ℝ] g)).symm
    change canonicalPositiveHalfEquiv B h e (D.symm (⁅a, m⁆ : N)) =
      T a *ᵥ canonicalPositiveHalfEquiv B h e (D.symm m)
    rw [ha]
    exact (congrArg (canonicalPositiveHalfEquiv B h e)
      (D.symm.map_lie (commonCartanLift h H hH a) (m : P₀))).trans
        (canonicalPositiveHalfEquiv_intertwines B h e _ _)
  exact (MatrixCubic.matrix_trace_cubic_of_intertwining E T haction x y z).trans
    (symmetrized_trace_cubic_eq_actual_root_sum H N hN x y z)

end CubicAnomaly.Classification.CanonicalRootCubic
