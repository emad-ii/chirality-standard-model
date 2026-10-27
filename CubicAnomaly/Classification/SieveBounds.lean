import CubicAnomaly.Classification.KillingDimension
import CubicAnomaly.Classification.CanonicalCoroot
import CubicAnomaly.Classification.QuadraticRestriction

/-!
# Actual finite search bounds from the original compact-pair hypotheses

The nonzero anomaly radical supplies an actual nonzero isotropy coroot.
The classification-free dimension and parity bounds for Killing algebras
therefore bound the isotropy dimension below. Combined with the actual
adjoint-complement dimension equation, this bounds the canonical complex
half above. Numerical ambient dimensions enter only as dimension equalities;
no highest-weight, type label, sieve bound, or classification witness is used.
-/

namespace CubicAnomaly.Classification.SieveBounds

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.CanonicalCoroot
open CubicAnomaly.Classification.KillingDimension
open CubicAnomaly.Classification.QuadraticRestriction
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The original anomaly condition forces actual isotropy dimension at least
three, and at least six when that dimension is even. -/
theorem all_rank_isotropy_dimension_bounds
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    3 ≤ finrank ℝ h ∧ (Even (finrank ℝ h) → 6 ≤ finrank ℝ h) := by
  obtain ⟨hK, H, hH, α, hα, _⟩ := all_rank_exists_null_coroot B h heff hproper e hradical
  letI := hK
  letI := hH
  letI : Nontrivial (ℂ ⊗[ℝ] h) := ⟨⟨coroot α.val, 0, hα⟩⟩
  have hbase : finrank ℂ (ℂ ⊗[ℝ] h) = finrank ℝ h := Module.finrank_baseChange
  have hthree := nonzero_killing_dimension_ge_three H
  have hsix := nonzero_even_killing_dimension_ge_six H
  rw [hbase] at hthree hsix
  exact ⟨hthree, hsix⟩

/-- The isotropy of an original anomalous compact pair is nonzero. -/
theorem all_rank_isotropy_ne_bot
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) : h ≠ ⊥ := by
  intro hh
  have hb := (all_rank_isotropy_dimension_bounds B h heff hproper e hradical).1
  rw [hh] at hb
  change 3 ≤ finrank ℝ (⊥ : Submodule ℝ g) at hb
  norm_num only [finrank_bot] at hb

/-- The actual complex half leaves at least three isotropy dimensions,
and at least six when the ambient dimension is even. -/
theorem all_rank_half_dimension_inequalities
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    2 * finrank ℂ V + 3 ≤ finrank ℝ g ∧
      (Even (finrank ℝ g) → 2 * finrank ℂ V + 6 ≤ finrank ℝ g) := by
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  have hdim := compact_pair_dimension_equation B h hproper e
  change finrank ℝ g = finrank ℝ h + 2 * finrank ℂ V at hdim
  have hb := all_rank_isotropy_dimension_bounds B h heff hproper e hradical
  change 2 * finrank ℂ V + 3 ≤ finrank ℝ g ∧
    (Even (finrank ℝ g) → 2 * finrank ℂ V + 6 ≤ finrank ℝ g)
  constructor
  · omega
  · rintro ⟨k, hk⟩
    have heven : Even (finrank ℝ h) := ⟨finrank ℝ h / 2, by omega⟩
    have hsix := hb.2 heven
    omega

/-- The finite half-dimension cutoffs at ambient dimensions 52, 78, 133
and 248 follow from the original pair hypotheses. This theorem assigns
no Lie-type names to those dimensions and assumes no search-bound witness. -/
theorem all_rank_exceptional_size_half_bounds
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    (finrank ℝ g = 52 → finrank ℂ V ≤ 23) ∧
    (finrank ℝ g = 78 → finrank ℂ V ≤ 36) ∧
    (finrank ℝ g = 133 → finrank ℂ V ≤ 65) ∧
    (finrank ℝ g = 248 → finrank ℂ V ≤ 121) := by
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  have hb := all_rank_half_dimension_inequalities B h heff hproper e hradical
  change 2 * finrank ℂ V + 3 ≤ finrank ℝ g ∧
    (Even (finrank ℝ g) → 2 * finrank ℂ V + 6 ≤ finrank ℝ g) at hb
  change (finrank ℝ g = 52 → finrank ℂ V ≤ 23) ∧
    (finrank ℝ g = 78 → finrank ℂ V ≤ 36) ∧
    (finrank ℝ g = 133 → finrank ℂ V ≤ 65) ∧
    (finrank ℝ g = 248 → finrank ℂ V ≤ 121)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hg
    have hsix := hb.2 ⟨26, by omega⟩
    omega
  · intro hg
    have hsix := hb.2 ⟨39, by omega⟩
    omega
  · omega
  · intro hg
    have hsix := hb.2 ⟨124, by omega⟩
    omega

end CubicAnomaly.Classification.SieveBounds
