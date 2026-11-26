import CubicAnomaly.Classification.EqualRankPairConjugacy
import CubicAnomaly.Fixed.E8FixedCommonCartan

/-! # Identification with the constructed exceptional complex pair

For equal geometric rank, the selected compact pair has a complexification
isomorphic to the concrete compact E₈ pair's scalar extension. The
isomorphism preserves the complexified real Cartans, isotropy, and the
original two oriented halves.
-/

namespace CubicAnomaly.Fixed.E8EqualRankComplexPair

open LieAlgebra LieModule
open Classification.Structural Classification.HermitianRealization
open Classification.CompactGeometry Classification.Complexification
open Classification.CompactCartan Classification.AllRankComplex
open Classification.EqualRankPairConjugacy
open E8Compact E8CompactPair E8PairComplexType E8CanonicalPair
open E8FixedCommonCartan
open scoped TensorProduct

attribute [local instance] E8Compact.e8_compact_real_finiteDimensional

/-- Either oriented isotropy eigenspace as a subspace of the ambient complexification. -/
noncomputable def orientedHalfSpace {g : Type*} [LieRing g] [LieAlgebra ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (z : ℂ) : Submodule ℂ (ℂ ⊗[ℝ] g) :=
  (ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) z).toSubmodule

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- At equal rank, the single ambient complex Lie equivalence identifies
the selected pair and its oriented matter spaces with the constructed pair,
and sends a complexified real Cartan to the concrete Geck Cartan. -/
theorem equal_rank_complex_equiv_to_fixed_pair
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (rank_eq : abelianRank ℝ h = abelianRank ℝ g) :
    ∃ A : LieSubalgebra ℝ g, A ≤ h ∧ (complexifiedSubalgebra A).IsCartanSubalgebra ∧
      ∃ Ψ : (ℂ ⊗[ℝ] g) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] compactRealAlgebra),
        (∀ x, Ψ x ∈ complexifiedSubalgebra fixedRealCartan ↔ x ∈ complexifiedSubalgebra A) ∧
        (h.toSubmodule.baseChange ℂ).map Ψ.toLinearMap = compactZero.toSubmodule.baseChange ℂ ∧
        ∀ z ∈ ({Complex.I, -Complex.I} : Set ℂ),
          (orientedHalfSpace B h e z).map Ψ.toLinearMap =
            orientedHalfSpace compactForm compactZero pairCommutantEquivComplex z := by
  obtain ⟨A, hA, abA, cartanA, _⟩ := compact_equal_abelianRank_exists_real_cartan B h rank_eq
  letI := abA
  letI := cartanA
  letI := complexified_abelian_cartan A
  letI : (complexifiedSubalgebra fixedRealCartan).IsCartanSubalgebra :=
    complexified_fixedRealCartan_eq.symm ▸ fixedCartan_isCartanSubalgebra
  exact ⟨A, hA, inferInstance, compact_real_cartan_pairs_complex_equiv B h ha hp e hr A hA
    compactForm compactZero e8_compact_pair_effective e8_compactZero_ne_top pairCommutantEquivComplex
    e8_canonical_half_cubicRadical_ne_bot fixedRealCartan fixedRealCartan_le_compactZero⟩

end CubicAnomaly.Fixed.E8EqualRankComplexPair
