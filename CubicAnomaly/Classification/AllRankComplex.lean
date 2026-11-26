import CubicAnomaly.Classification.ComplexDuality
import CubicAnomaly.Classification.AnomalyComplexification
import CubicAnomaly.Classification.CanonicalAnomaly
import Mathlib.Algebra.Lie.CartanExists

/-!
# Structural reduction in the original real and actual complex domains

The original compact-pair hypotheses now produce absolute simplicity,
nondegenerate Killing forms, an irreducible inequivalent dual pair in the
actual scalar extension, and a nonsymmetric complement.  The same original
anomaly hypothesis supplies an actual Cartan subalgebra and a nonzero kernel
vector for its finite cubic tensor matrix.

These are structural conclusions in arbitrary rank.  No classification,
equal-rank, root-datum identification, or finite-census membership is assumed
or claimed here.
-/

namespace CubicAnomaly.Classification.AllRankComplex

open Matrix
open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.AbsoluteSimplicity
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.ComplexDuality
open CubicAnomaly.Classification.CyclicBracket
open CubicAnomaly.Classification.CartanCubic
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Classification.AnomalyComplexification
open CubicAnomaly.Classification.CanonicalAnomaly

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The real structural reduction, absolute simplicity, complex Killing
forms, nonsymmetry, and the actual irreducible inequivalent dual-pair
decomposition follow from the original hypotheses, in every rank. -/
theorem all_rank_complex_structural_reduction
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    (LieModule.IsIrreducible ℝ h (orthogonalComplement B h) ∧
      LieModule.IsFaithful ℝ h (orthogonalComplement B h) ∧
      LieAlgebra.IsSimple ℝ g ∧ LieAlgebra.IsSemisimple ℝ h ∧ IsCoatom h) ∧
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g) ∧
    LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) ∧
    LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) ∧
    (∃ x y : orthogonalComplement B h, ⁅x.val, y.val⁆ ∉ h) ∧
    (let J := complexifiedEnd (commutantComplexStructure e)
     let V := invariantEigenspace J Complex.I
     let Vbar := invariantEigenspace J (-Complex.I)
     IsCompl V Vbar ∧
       LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) V ∧
       LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) Vbar ∧
       Nonempty (Vbar ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ V) ∧
       ¬Nonempty (V ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Vbar)) := by
  have hreal := all_rank_structural_reduction_of_commutant B h heff hproper e hradical
  letI : LieAlgebra.IsSemisimple ℝ h := hreal.2.2.2.1
  have hgcenter := (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).2.2.1
  have hhcenter := LieAlgebra.center_eq_bot ℝ h
  exact ⟨hreal, compact_pair_complexification_simple B h heff hproper e,
    compact_complexification_isKilling B hgcenter,
    compact_complexification_isKilling (B.restrict h) hhcenter,
    compact_complex_complement_nonsymmetric B h heff hproper e hhcenter,
    compact_complement_complex_type_decomposition B h hproper e⟩

/-- The original nonzero anomaly radical yields an actual Cartan subalgebra and a
nonzero vector in its finite trace-cubic tensor kernel.  Both the Cartan and
the representation are constructed; neither is a classification witness. -/
theorem all_rank_nonzero_cartan_anomaly_kernel
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    ∃ H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h), H.IsCartanSubalgebra ∧
      ∃ v : Fin (Module.finrank ℂ H) → ℂ, v ≠ 0 ∧
        cartanCubicMatrix H (Module.finBasis ℂ H)
          (complexTraceCubicForm
            (complexHermitianRepresentation (hermitianHalfOfCommutant B h e)).toLinearMap)
          *ᵥ v = 0 := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℂ (ℂ ⊗[ℝ] h)
  let H := LieSubalgebra.engel ℂ x
  letI : H.IsCartanSubalgebra := hx
  refine ⟨H, hx, ?_⟩
  exact (hermitian_radical_ne_bot_iff_cartan_matrix_kernel
    (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
    (hermitianHalfOfCommutant B h e) H (Module.finBasis ℂ H)).mp hradical

/-- The all-rank original hypotheses yield a finite kernel witness expressed
entirely in the actual positive-half Cartan weights and their multiplicities. -/
theorem all_rank_nonzero_cartan_weight_kernel
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    ∃ (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) (hH : H.IsCartanSubalgebra),
      letI := hH
      ∃ v : Fin (Module.finrank ℂ H) → ℂ, v ≠ 0 ∧
        canonicalCartanWeightMatrix B h e H (Module.finBasis ℂ H) *ᵥ v = 0 := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℂ (ℂ ⊗[ℝ] h)
  let H := LieSubalgebra.engel ℂ x
  letI : H.IsCartanSubalgebra := hx
  refine ⟨H, hx, ?_⟩
  exact (canonical_anomaly_iff_cartan_weight_kernel B h e
    (LieAlgebra.center_eq_bot ℝ h) H (Module.finBasis ℂ H)).mp hradical

end CubicAnomaly.Classification.AllRankComplex
