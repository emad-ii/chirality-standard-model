import CubicAnomaly.Fixed.AmbientClassification
import CubicAnomaly.Fixed.OrientedPairRadical
import CubicAnomaly.Classification.ClassicalOrthogonalRecognition
import CubicAnomaly.Classification.ClassicalConstituentOrthogonalExclusion

/-! # Uniqueness of the compact Lie-algebra pair

For every finite-dimensional effective proper compact Lie-algebra pair
with complex commutant on the entire adjoint complement, the canonical
mixed cubic has a nonzero radical exactly when the pair and its two
matter eigenspaces are isomorphic to the constructed compact E₈ pair.
The same ambient isomorphism identifies its 78-dimensional radical.
-/

namespace CubicAnomaly.Fixed.GlobalClassification

open LieAlgebra LieModule Module
open Classification Classification.Structural Classification.HermitianRealization
open Classification.CompactGeometry Classification.CompactCartan Classification.CompactPairTransport
open E8Compact E8CompactPair E8PairComplexType E8CanonicalPair E8CompactFactors
open E8EqualRankComplexPair E8EqualRankRealPair E8EqualRankConverse
open AmbientClassification OrientedPairRadical
open scoped TensorProduct

attribute [local instance] E8Compact.e8_compact_real_finiteDimensional

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]

/-- At every rank a nonzero full mixed cubic radical identifies the
oriented compact E₈ pair. Conversely that pair has a nonzero radical. -/
theorem anomaly_iff_fixed_pair (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔ IsOrientedFixedPair B h e := by
  refine ⟨fun hr => ?_, fixed_pair_has_nonzero_radical B h e⟩
  letI : IsKilling ℂ (ℂ ⊗[ℝ] g) :=
    (AllRankComplex.all_rank_complex_structural_reduction B h ha hp e hr).2.2.1
  rcases fixed_or_orthogonal_cartan B h ha hp e hr with hf | ⟨D, hD, b, n, s, hm⟩
  · exact hf
  letI := hD
  obtain ⟨ι, hι, ⟨f⟩⟩ := ClassicalOrthogonalRecognition.exists_orthogonal_model B h ha hp e hr D b s hm
  letI := hι
  letI : FiniteDimensional ℝ (OrthogonalDefining.orthogonalAlgebra (EuclideanSpace ℝ ι)) :=
    Module.Finite.equiv f.toLinearEquiv
  obtain ⟨C, l, c, _, hla, hlp, hlr⟩ := transport_pair_hypotheses f B h e ha hp hr
  exact (hlr (ClassicalConstituentOrthogonalExclusion.all_rank_orthogonal_cubic_radical_eq_bot (W := EuclideanSpace ℝ ι) C l hla hlp c)).elim

/-- One real ambient isomorphism identifies the isotropy subalgebra, the
full cubic radical inside it, and the two oriented ambient matter spaces. -/
theorem compact_pair_classification (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔
      ∃ (f : g ≃ₗ⁅ℝ⁆ compactRealAlgebra) (hf : h.map f.toLieHom = compactZero),
        (hermitianHalfOfCommutant B h e).cubicRadical.toLieSubalgebra.map
          (f.ofSubalgebras h compactZero hf).toLieHom = compactRadical.toLieSubalgebra ∧
        ∀ z ∈ ({Complex.I, -Complex.I} : Set ℂ),
          (orientedHalfSpace B h e z).map (f.toLinearMap.baseChange ℂ) =
            orientedHalfSpace compactForm compactZero pairCommutantEquivComplex z := by
  rw [anomaly_iff_fixed_pair B h ha hp e]
  constructor
  · rintro ⟨f, hf, hm⟩
    exact ⟨f, hf, radical_map_eq B h e f hf (hm _ (Set.mem_insert _ _)), hm⟩
  · rintro ⟨f, hf, _, hm⟩
    exact ⟨f, hf, hm⟩

end CubicAnomaly.Fixed.GlobalClassification
