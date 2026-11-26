import CubicAnomaly.Fixed.E8EqualRankRealPair
import CubicAnomaly.Classification.CanonicalHalfTransport

/-! # The converse for the oriented compact pair

An isomorphism identifying the actual positive matter spaces intertwines
the complex matrices of the real isotropy action. Conjugation preserves
their full mixed trace cubic, including the common factor from the
Hermitian generator convention.
-/

namespace CubicAnomaly.Fixed.E8EqualRankConverse

open Matrix LieAlgebra LieModule
open Classification.Structural Classification.HermitianRealization Classification.Complexification
open Classification.CompactCartan Classification.AllRank Classification.CubicRadical
open Classification.AnomalyComplexification Classification.CanonicalHalfTransport
open E8Compact E8CompactPair E8PairComplexType E8CanonicalPair E8FixedCommonCartan
open E8EqualRankComplexPair E8EqualRankRealPair E8FullCubic
open scoped TensorProduct

variable {g k : Type*} [LieRing g] [LieAlgebra ℝ g] [LieRing k] [LieAlgebra ℝ k]

variable [Module.Finite ℝ g] [Module.Finite ℝ k]

/-- Carrying the positive ambient matter by a real pair equivalence carries
nonvanishing of its full Hermitian cubic radical back to the source. -/
theorem radical_of_positive_pair_equiv (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (C : CompactForm k) (l : LieSubalgebra ℝ k)
    (c : lieCommutant (L := l) (M := orthogonalComplement C l) ≃ₐ[ℝ] ℂ)
    (f : g ≃ₗ⁅ℝ⁆ k) (hf : h.map f.toLieHom = l)
    (hpos : (orientedHalfSpace B h e Complex.I).map (f.toLinearMap.baseChange ℂ) =
      orientedHalfSpace C l c Complex.I)
    (hc : (hermitianHalfOfCommutant C l c).cubicRadical ≠ ⊥) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ := by
  obtain ⟨θ, R, hR⟩ := exists_positive_matrix_equiv B h e C l c f hf hpos
  exact radical_of_matched_real_actions _ _ θ R hR hc

attribute [local instance] E8Compact.e8_compact_real_finiteDimensional

/-- Identification with the oriented compact E₈ pair forces a nonzero
cubic radical even before any rank comparison. -/
theorem fixed_pair_has_nonzero_radical (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hf : IsOrientedFixedPair B h e) : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ := by
  obtain ⟨f, hl, hpos⟩ := hf
  exact radical_of_positive_pair_equiv B h e compactForm compactZero pairCommutantEquivComplex
    f hl (hpos Complex.I (Set.mem_insert _ _)) e8_canonical_half_cubicRadical_ne_bot

/-- At equal abelian rank, a nonzero full anomaly radical is equivalent
to a real Lie isomorphism to the explicit exceptional pair which identifies
the isotropy and both oriented matter eigenspaces. -/
theorem equal_rank_anomaly_iff_fixed_pair
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (rank_eq : abelianRank ℝ h = abelianRank ℝ g) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔ IsOrientedFixedPair B h e :=
  ⟨fun hr => equal_rank_real_equiv_to_fixed_pair B h ha hp e hr rank_eq,
    fixed_pair_has_nonzero_radical B h e⟩

end CubicAnomaly.Fixed.E8EqualRankConverse
