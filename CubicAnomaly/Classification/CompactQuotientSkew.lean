import CubicAnomaly.Classification.DualPairSkew

/-!
# Actual skew endomorphisms of the complex-type complement

The two actual complex halves of the original compact complement provide
a nonzero equivariant sign operator. It is skew for every invariant
bilinear form, and the same property transports through any actual
equivariant equivalence to a source module.
-/

namespace CubicAnomaly.Classification.CompactQuotientSkew

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.ComplexDuality
open CubicAnomaly.Classification.DualPairSkew
open scoped TensorProduct

noncomputable section

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The actual complexified complement carries a nonzero equivariant
endomorphism skew for every invariant bilinear form. -/
theorem compact_complement_exists_skew_end
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    ∃ D : (ℂ ⊗[ℝ] orthogonalComplement B h)
        →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] orthogonalComplement B h), D ≠ 0 ∧
      ∀ (Φ : LinearMap.BilinForm ℂ (ℂ ⊗[ℝ] orthogonalComplement B h)),
        Φ.lieInvariant (ℂ ⊗[ℝ] h) → ∀ x y, Φ (D x) y = -Φ x (D y) := by
  obtain ⟨hc, hP, hQ, ⟨d⟩, hne⟩ :=
    compact_complement_complex_type_decomposition B h hproper e
  letI := hP
  letI := hQ
  exact inequivalent_dual_pair_exists_skew_end _ _ hc d hne

/-- An actual equivariant identification with the original complexified
complement transfers its nonzero skew operator to the source module.
No decomposition or form is assumed on that source. -/
theorem compact_equivalent_source_exists_skew_end
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    [LieRingModule (ℂ ⊗[ℝ] h) S] [LieModule ℂ (ℂ ⊗[ℝ] h) S]
    (E : S ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] orthogonalComplement B h)) :
    ∃ D : S →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ S, D ≠ 0 ∧
      ∀ (Φ : LinearMap.BilinForm ℂ S), Φ.lieInvariant (ℂ ⊗[ℝ] h) →
        ∀ x y, Φ (D x) y = -Φ x (D y) :=
  exists_skew_end_of_equiv E (compact_complement_exists_skew_end B h hproper e)

end

end CubicAnomaly.Classification.CompactQuotientSkew
