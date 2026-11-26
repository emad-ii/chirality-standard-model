import CubicAnomaly.Classification.CompactCartanStraightening
import CubicAnomaly.Classification.EqualRankPairConjugacy

/-!
# Real isomorphism of the selected compact pairs

Two pairs satisfying the anomalous irreducible complex-type hypotheses and
admitting common compact Cartans have isomorphic real ambient Lie algebras.
The real isomorphism takes one isotropy subalgebra onto the other, and its
scalar extension preserves the choices of positive and negative matter.
-/

namespace CubicAnomaly.Classification.CompactEqualRankPair

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open Structural HermitianRealization Complexification CompactGeometry
open CompactCartan CompactCartanStraightening CompactChevalleyDescent EqualRankPairConjugacy
open ToralCharacter CommonCartan EqualRankSelection AllRankComplex Selection
open scoped TensorProduct

variable {g k : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  [LieRing k] [LieAlgebra ℝ k] [Module.Finite ℝ k]

/-- A common Cartan obtained from a real subalgebra is sufficient to
identify the two real compact pairs and their oriented matter halves. -/
theorem compact_common_cartan_pairs_real_equiv
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (A : LieSubalgebra ℝ g) [(complexifiedSubalgebra A).IsCartanSubalgebra] (hA : A ≤ h)
    (D : CompactForm k) (l : LieSubalgebra ℝ k) (la : Effective l) (lp : l ≠ ⊤)
    (c : lieCommutant (L := l) (M := orthogonalComplement D l) ≃ₐ[ℝ] ℂ)
    (lr : (hermitianHalfOfCommutant D l c).cubicRadical ≠ ⊥)
    (C : LieSubalgebra ℝ k) [(complexifiedSubalgebra C).IsCartanSubalgebra] (lC : C ≤ l) :
    ∃ f : g ≃ₗ⁅ℝ⁆ k, h.map f.toLieHom = l ∧ ∀ z ∈ ({Complex.I, -Complex.I} : Set ℂ),
      (ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) z
        ).toSubmodule.map (f.toLinearMap.baseChange ℂ) =
      (ambientComplexifiedHalf (orthogonalComplement D l) (commutantComplexStructure c) z
        ).toSubmodule := by
  classical
  let H := complexifiedSubalgebra A
  let J := complexifiedSubalgebra C
  have hH : H ≤ complexifiedSubalgebra h := complexified_subalgebra_mono hA
  have lJ : J ≤ complexifiedSubalgebra l := complexified_subalgebra_mono lC
  have hstruct := all_rank_complex_structural_reduction B h ha hp e hr
  letI : IsSimple ℂ (ℂ ⊗[ℝ] g) := hstruct.2.1
  letI : IsKilling ℂ (ℂ ⊗[ℝ] g) := hstruct.2.2.1
  letI : IsKilling ℂ (ℂ ⊗[ℝ] k) := (all_rank_complex_structural_reduction D l la lp c lr).2.2.1
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  obtain ⟨d⟩ := (rootSystem J).nonempty_base
  obtain ⟨⟨s, _⟩, _⟩ := compact_common_cartan_forces_eight B h ha hp e hr H hH b
  letI : Nontrivial (complexifiedSubalgebra A) := Module.nontrivial_of_finrank_pos (R := ℂ) (by
    change 0 < finrank ℂ H
    rw [finrank_eq_card_basis (b.toCoweightBasis.reindex s.symm), Fintype.card_fin]
    decide)
  obtain ⟨Φ, hCartan, h₀, hZ⟩ := compact_common_cartan_pairs_complex_equiv B h ha hp e hr H hH b
    D l la lp c lr J lJ d
  have hmap : H.toSubmodule.map Φ.toLinearMap = J.toSubmodule := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hCartan x).mpr hx
    · intro hy
      exact ⟨Φ.symm y, (hCartan _).mp (by simpa using hy), Φ.apply_symm_apply y⟩
  let T : H ≃ₗ[ℂ] J := Φ.toLinearEquiv.ofSubmodules H.toSubmodule J.toSubmodule hmap
  obtain ⟨Ψ, hΨ, _, hgrades⟩ := exists_compact_equiv_preserving_grade_images A C B D Φ T
    (fun _ => rfl) b
  obtain ⟨χ, _, _, g₀, g₁, g₂, _⟩ := compact_common_cartan_root_character B h ha hp e hr H hH
  have hg₀ := hgrades χ 0
  rw [g₀, h₀] at hg₀
  obtain ⟨f, hf, hreal⟩ := exists_real_pair_equiv_of_conjugation h l Ψ hΨ hg₀
  have hext : f.toLinearMap.baseChange ℂ = Ψ.toLinearMap := by
    ext x
    simpa only [LinearMap.baseChange_tmul] using hreal x
  refine ⟨f, hf, ?_⟩
  intro z hz
  rw [hext, ← hZ z hz]
  rcases hz with rfl | hz
  · rw [← g₁]
    exact hgrades χ 1
  · obtain rfl : z = -Complex.I := hz
    rw [← g₂]
    exact hgrades χ (-1)

/-- Equality of the maximal abelian dimensions in each pair supplies both
real Cartans required for the real pair isomorphism. -/
theorem compact_equal_rank_pairs_real_equiv
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (rankH : abelianRank ℝ h = abelianRank ℝ g)
    (D : CompactForm k) (l : LieSubalgebra ℝ k) (la : Effective l) (lp : l ≠ ⊤)
    (c : lieCommutant (L := l) (M := orthogonalComplement D l) ≃ₐ[ℝ] ℂ)
    (lr : (hermitianHalfOfCommutant D l c).cubicRadical ≠ ⊥)
    (rankL : abelianRank ℝ l = abelianRank ℝ k) :
    ∃ f : g ≃ₗ⁅ℝ⁆ k, h.map f.toLieHom = l ∧ ∀ z ∈ ({Complex.I, -Complex.I} : Set ℂ),
      (ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) z
        ).toSubmodule.map (f.toLinearMap.baseChange ℂ) =
      (ambientComplexifiedHalf (orthogonalComplement D l) (commutantComplexStructure c) z
        ).toSubmodule := by
  obtain ⟨A, hA, hAb, hAc, _⟩ := compact_equal_abelianRank_exists_real_cartan B h rankH
  obtain ⟨C, lC, hCb, hCc, _⟩ := compact_equal_abelianRank_exists_real_cartan D l rankL
  letI := hAb
  letI := hAc
  letI := hCb
  letI := hCc
  letI := complexified_abelian_cartan A
  letI := complexified_abelian_cartan C
  exact compact_common_cartan_pairs_real_equiv B h ha hp e hr A hA D l la lp c lr C lC

end CubicAnomaly.Classification.CompactEqualRankPair
