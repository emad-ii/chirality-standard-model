import CubicAnomaly.Classification.CompactEqualRankPair
import CubicAnomaly.Fixed.E8EqualRankComplexPair

/-! # Identification with the constructed compact exceptional pair

For equal abelian ranks, a real Lie isomorphism identifies the original
ambient algebra and its isotropy with the explicit compact E₈ construction.
Its scalar extension carries both matter halves to their specified partners.
-/

namespace CubicAnomaly.Fixed.E8EqualRankRealPair

open LieAlgebra LieModule
open Classification.Structural Classification.HermitianRealization
open Classification.CompactGeometry Classification.Complexification
open Classification.CompactCartan Classification.CompactEqualRankPair
open E8EqualRankComplexPair E8Compact E8CompactPair E8PairComplexType E8CanonicalPair E8FixedCommonCartan
open scoped TensorProduct

attribute [local instance] E8Compact.e8_compact_real_finiteDimensional

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- An actual real Lie isomorphism to the constructed pair, carrying both
chosen eigenspaces under its complex scalar extension. -/
def IsOrientedFixedPair (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) : Prop :=
  ∃ f : g ≃ₗ⁅ℝ⁆ compactRealAlgebra, h.map f.toLieHom = compactZero ∧
    ∀ z ∈ ({Complex.I, -Complex.I} : Set ℂ),
      (orientedHalfSpace B h e z).map (f.toLinearMap.baseChange ℂ) =
        orientedHalfSpace compactForm compactZero pairCommutantEquivComplex z

/-- The equal-rank branch identifies the concrete real pair and both
oriented matter spaces from the original cubic-radical hypotheses. -/
theorem equal_rank_real_equiv_to_fixed_pair
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (rank_eq : abelianRank ℝ h = abelianRank ℝ g) : IsOrientedFixedPair B h e := by
  obtain ⟨A, hA, abA, cartanA, _⟩ := compact_equal_abelianRank_exists_real_cartan B h rank_eq
  letI := abA
  letI := cartanA
  letI := complexified_abelian_cartan A
  letI : (complexifiedSubalgebra fixedRealCartan).IsCartanSubalgebra :=
    complexified_fixedRealCartan_eq.symm ▸ fixedCartan_isCartanSubalgebra
  exact compact_common_cartan_pairs_real_equiv B h ha hp e hr A hA compactForm compactZero
    e8_compact_pair_effective e8_compactZero_ne_top pairCommutantEquivComplex
    e8_canonical_half_cubicRadical_ne_bot fixedRealCartan fixedRealCartan_le_compactZero

/-- In all ranks, a pair satisfying the original hypotheses has strictly
smaller isotropy rank or is isomorphic to the constructed oriented pair. -/
theorem all_rank_deficient_or_fixed_pair
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    abelianRank ℝ h < abelianRank ℝ g ∨ IsOrientedFixedPair B h e :=
  (abelianRank_subalgebra_le ℝ g h).lt_or_eq.imp id
    (equal_rank_real_equiv_to_fixed_pair B h ha hp e hr)

end CubicAnomaly.Fixed.E8EqualRankRealPair
