import CubicAnomaly.Classification.CompactCartan
import CubicAnomaly.Classification.ToralCharacter

/-!
# The actual all-rank geometric branch reduction

Under the original compact-pair hypotheses, either the isotropy has strictly
smaller abelian rank, or the actual ambient complex algebra has the canonical
order-three root grading.  In the latter branch the Cartan, the closed root
subsystem, the lattice quotient, and the identifications of all three grades
are derived.  None is an input witness.

`abelianRank` means the explicitly defined maximum dimension of an actual
abelian Lie subalgebra.  This module does not assume or assert its equality
with Mathlib's separately defined characteristic-polynomial rank.
-/

namespace CubicAnomaly.Classification.AllRankGrading

open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.CompactCartan
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.ToralCharacter

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The explicit geometric conclusion: an actual ambient Cartan, a nonzero
character of its actual integer root lattice modulo three, and an internal
grading with the given isotropy and the actual two complex halves as its
three components.  This predicate is only a conclusion of the reduction. -/
def CanonicalCyclicGrading (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) : Prop :=
  ∃ (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H.IsCartanSubalgebra),
    letI := hH
    H ≤ complexifiedSubalgebra h ∧ Module.finrank ℂ H = abelianRank ℝ g ∧
    (let q := orthogonalComplement B h
     let J := commutantComplexStructure e
     ∃ character : rootLattice H →+ ZMod 3,
       character ≠ 0 ∧
       DirectSum.IsInternal (rootCharacterGrade H character) ∧
       rootCharacterGrade H character 0 = h.toSubmodule.baseChange ℂ ∧
       rootCharacterGrade H character 1 =
         (ambientComplexifiedHalf q J Complex.I).toSubmodule ∧
       rootCharacterGrade H character (-1) =
         (ambientComplexifiedHalf q J (-Complex.I)).toSubmodule ∧
       ∀ (i j : ZMod 3) (x y : ℂ ⊗[ℝ] g),
         x ∈ rootCharacterGrade H character i →
         y ∈ rootCharacterGrade H character j →
         ⁅x, y⁆ ∈ rootCharacterGrade H character (i + j))

/-- Equal actual abelian ranks produce the canonical cyclic grading from
the original hypotheses.  In particular the common Cartan is constructed. -/
theorem equal_abelianRank_canonical_cyclic_grading
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (hrank : abelianRank ℝ h = abelianRank ℝ g) :
    CanonicalCyclicGrading B h e := by
  obtain ⟨H, hH, hContained, hdim⟩ :=
    compact_equal_abelianRank_exists_complex_cartan B h hrank
  letI := hH
  refine ⟨H, hH, hContained, hdim, ?_⟩
  exact compact_common_cartan_root_character B h heff hproper e hradical H hContained

/-- The original hypotheses give the actual rank-deficient-or-cyclic-grading
split in every rank.  All hypotheses specific to the grading construction
are discharged in its branch. -/
theorem all_rank_rank_deficient_or_cyclic_grading
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    abelianRank ℝ h < abelianRank ℝ g ∨ CanonicalCyclicGrading B h e := by
  rcases (abelianRank_subalgebra_le ℝ g h).lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr (equal_abelianRank_canonical_cyclic_grading B h heff hproper e hradical heq)

end CubicAnomaly.Classification.AllRankGrading
