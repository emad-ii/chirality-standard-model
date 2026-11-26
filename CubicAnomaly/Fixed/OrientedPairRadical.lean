import CubicAnomaly.Fixed.E8EqualRankConverse
import CubicAnomaly.Fixed.E8CompactIsotropy

/-! The isomorphism identifying the two matter spaces restricts to an
isomorphism of the full cubic radicals. Its target is the compact simple
factor whose complexification is the E₆ lattice algebra. -/

namespace CubicAnomaly.Fixed.OrientedPairRadical

open LieAlgebra LieModule Module
open Classification.Structural Classification.HermitianRealization Classification.CanonicalHalfTransport
open Classification.CompactGeometry Classification.CubicRadical
open E8Compact E8CompactPair E8PairComplexType E8CanonicalPair E8EqualRankRealPair
open E8CompactFactors E8CompactIsotropy E8EqualRankComplexPair
open scoped TensorProduct

attribute [local instance] E8Compact.e8_compact_real_finiteDimensional

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]

/-- The restriction of the given ambient map carries precisely the null
ideal of the original mixed cubic to the compact E₆ radical. -/
theorem radical_map_eq (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (f : g ≃ₗ⁅ℝ⁆ compactRealAlgebra) (hf : h.map f.toLieHom = compactZero)
    (hpos : (orientedHalfSpace B h e Complex.I).map (f.toLinearMap.baseChange ℂ) =
      orientedHalfSpace compactForm compactZero pairCommutantEquivComplex Complex.I) :
    (hermitianHalfOfCommutant B h e).cubicRadical.toLieSubalgebra.map
      (f.ofSubalgebras h compactZero hf).toLieHom = compactRadical.toLieSubalgebra := by
  obtain ⟨R, hR⟩ := positive_matrix_equiv_for_restriction B h e compactForm compactZero
    pairCommutantEquivComplex f hf hpos
  let θ := f.ofSubalgebras h compactZero hf
  have hm := mem_radical_iff_of_matched_real_actions (hermitianHalfOfCommutant B h e) canonicalHalf θ R hR
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hm x).mp hx
  · obtain ⟨x, rfl⟩ := θ.surjective y
    intro hx
    exact ⟨x, (hm x).mpr hx, rfl⟩

/-- The original radical embeds in the isotropy as the compact E₆ factor.
The radical has real dimension 78 and the isotropy has dimension 86. -/
theorem fixed_pair_radical_invariants (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hfix : IsOrientedFixedPair B h e) :
    (∃ r : (hermitianHalfOfCommutant B h e).cubicRadical ≃ₗ⁅ℝ⁆ compactRadical,
      ∃ θ : h ≃ₗ⁅ℝ⁆ compactZero, ∀ x, θ x.val = (r x).val) ∧
      finrank ℝ (hermitianHalfOfCommutant B h e).cubicRadical = 78 ∧ finrank ℝ h = 86 := by
  obtain ⟨f, hf, hm⟩ := hfix
  let θ := f.ofSubalgebras h compactZero hf
  let r := θ.ofSubalgebras _ _ (radical_map_eq B h e f hf (hm _ (Set.mem_insert _ _)))
  exact ⟨⟨r, θ, fun _ => rfl⟩, r.toLinearEquiv.finrank_eq.trans e8_canonical_radical_real_finrank,
    θ.toLinearEquiv.finrank_eq.trans e8_compactZero_finrank⟩

/-- Scalar extension of the original radical recovers the independently
constructed six-node E₆ algebra with its lattice bracket. -/
theorem fixed_pair_radical_complex_equiv (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hfix : IsOrientedFixedPair B h e) :
    Nonempty ((ℂ ⊗[ℝ] (hermitianHalfOfCommutant B h e).cubicRadical) ≃ₗ⁅ℂ⁆ E6Lattice.Algebra) := by
  obtain ⟨⟨r, _, _⟩, _⟩ := fixed_pair_radical_invariants B h e hfix
  let t : (ℂ ⊗[ℝ] (hermitianHalfOfCommutant B h e).cubicRadical) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] compactRadical) :=
    { LinearEquiv.baseChange ℝ ℂ _ _ r.toLinearEquiv with
      map_lie' := fun {x y} => (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) r.toLieHom).map_lie x y }
  exact ⟨t.trans compactRadicalComplexEquiv⟩

end CubicAnomaly.Fixed.OrientedPairRadical
