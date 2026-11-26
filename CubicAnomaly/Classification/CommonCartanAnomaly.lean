import CubicAnomaly.Classification.CanonicalAnomaly
import CubicAnomaly.Classification.ContainedCartan

/-!
# The full anomaly on the same ambient Cartan

The literal lift of a common ambient Cartan to the actual isotropy
complexification transports the full anomaly criterion. No second Cartan,
conjugacy witness, or representation identification is supplied.
-/

namespace CubicAnomaly.Classification.CommonCartanAnomaly

open Matrix Module
open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanCubic
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Classification.AnomalyComplexification
open CubicAnomaly.Classification.ContainedCartan

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The finite trace-cubic matrix on the same ambient common Cartan. -/
noncomputable def commonCartanCubicMatrix
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
    (hH : H ≤ complexifiedSubalgebra h)
    {ι : Type*} (b : Basis ι ℂ H) : Matrix (ι × ι) ι ℂ :=
  fun jk i => matrixTraceCubic
    (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
      (commonCartanLift h H hH (b i)))
    (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
      (commonCartanLift h H hH (b jk.1)))
    (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
      (commonCartanLift h H hH (b jk.2)))

/-- Transport to the literal isotropy Cartan preserves every matrix entry. -/
theorem common_cartan_cubic_matrix_eq_isotropy_matrix
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
    (hH : H ≤ complexifiedSubalgebra h)
    {ι : Type*} (b : Basis ι ℂ H) :
    commonCartanCubicMatrix B h e H hH b =
      cartanCubicMatrix (commonCartanInIsotropy h H)
        (b.map (commonCartanIsotropyEquiv h H hH).toLinearEquiv)
        (complexTraceCubicForm
          (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)).toLinearMap) := rfl

/-- The original full mixed anomaly is equivalent to a nonzero finite
kernel on the very same ambient Cartan used by the root grading. -/
theorem canonical_anomaly_iff_common_cartan_kernel
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h)
    {ι : Type*} [Fintype ι] (b : Basis ι ℂ H) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔
      ∃ v : ι → ℂ, v ≠ 0 ∧ commonCartanCubicMatrix B h e H hH b *ᵥ v = 0 := by
  letI := commonCartanInIsotropy_isCartan h H hH
  rw [common_cartan_cubic_matrix_eq_isotropy_matrix]
  exact hermitian_radical_ne_bot_iff_cartan_matrix_kernel (B.restrict h) hcenter
    (hermitianHalfOfCommutant B h e) (commonCartanInIsotropy h H)
    (b.map (commonCartanIsotropyEquiv h H hH).toLinearEquiv)

/-- The original radical is nonzero exactly when the common ambient
Cartan contains a nonzero vector annihilating every remaining Cartan pair.
The full non-Cartan mixed insertions are discharged by Cartan detection. -/
theorem canonical_anomaly_iff_common_cartan_cubic
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔
      ∃ x : H, x ≠ 0 ∧ ∀ y z : H,
        matrixTraceCubic
          (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
            (commonCartanLift h H hH x))
          (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
            (commonCartanLift h H hH y))
          (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
            (commonCartanLift h H hH z)) = 0 := by
  letI := commonCartanInIsotropy_isCartan h H hH
  letI := compact_complexification_isKilling (B.restrict h) hcenter
  let E := commonCartanIsotropyEquiv h H hH
  let ρ := complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
  rw [← hermitian_complex_radical_ne_bot_iff]
  change CubicRadical.radical (complexTraceCubicForm ρ.toLinearMap)
      (complex_trace_cubic_invariant ρ) ≠ ⊥ ↔ _
  rw [radical_ne_bot_iff_cartan (commonCartanInIsotropy h H)
    (complexTraceCubicForm ρ.toLinearMap) (complex_trace_cubic_invariant ρ)
    (complex_trace_cubic_symmetric ρ.toLinearMap)]
  constructor
  · rintro ⟨x, hx, hc⟩
    refine ⟨E.symm x, fun hz => hx ?_, ?_⟩
    · simpa using congrArg E hz
    · intro y z
      change complexTraceCubicForm ρ.toLinearMap
        (E (E.symm x)) (E y) (E z) = 0
      rw [E.apply_symm_apply]
      exact hc (E y) (E z)
  · rintro ⟨x, hx, hc⟩
    refine ⟨E x, fun hz => hx (E.injective (hz.trans (map_zero E).symm)), ?_⟩
    intro y z
    have hh := hc (E.symm y) (E.symm z)
    change complexTraceCubicForm ρ.toLinearMap
      (E x) (E (E.symm y)) (E (E.symm z)) = 0 at hh
    simpa only [E.apply_symm_apply] using hh

end CubicAnomaly.Classification.CommonCartanAnomaly
