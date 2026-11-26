import CubicAnomaly.Classification.EqualRankConjugacy
import CubicAnomaly.Classification.ChevalleyRecognition
import CubicAnomaly.Classification.ChevalleyGradingTransport

/-! # Isomorphism between the complexifications of equal-rank compact pairs

The two Weyl automorphisms and the isomorphism matching the labeled Cartans
compose to give a single ambient Lie equivalence carrying the Cartan, the
isotropy, and each oriented half of the first pair to those of the second.
-/

namespace CubicAnomaly.Classification.EqualRankPairConjugacy

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ChevalleyCartanMatching ChevalleyRecognition ChevalleyGradingTransport
open RootClassificationExceptional RootClassificationOrbit Exceptional EqualRankConjugacy
open Structural HermitianRealization Complexification CompactGeometry RootGrading
open ToralCharacter CommonCartan Selection AllRankComplex
open scoped TensorProduct

variable {g p : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  [LieRing p] [LieAlgebra ℝ p] [Module.Finite ℝ p]

/-- Two anomalous compact pairs admitting common Cartans have Lie-isomorphic
ambient complexifications, with the isomorphism respecting their Cartans,
isotropies, and original choices of positive and negative matter. -/
theorem compact_common_cartan_pairs_complex_equiv
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] g)] (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
    [H.IsCartanSubalgebra] (hH : H ≤ complexifiedSubalgebra h) (b : (rootSystem H).Base)
    (C : CompactForm p) (l : LieSubalgebra ℝ p) (la : Effective l) (lp : l ≠ ⊤)
    (c : lieCommutant (L := l) (M := orthogonalComplement C l) ≃ₐ[ℝ] ℂ)
    (lr : (hermitianHalfOfCommutant C l c).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] p)] (J : LieSubalgebra ℂ (ℂ ⊗[ℝ] p))
    [J.IsCartanSubalgebra] (lJ : J ≤ complexifiedSubalgebra l) (d : (rootSystem J).Base) :
    ∃ Ψ : (ℂ ⊗[ℝ] g) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] p),
      (∀ x, Ψ x ∈ J ↔ x ∈ H) ∧
      (h.toSubmodule.baseChange ℂ).map Ψ.toLinearMap = l.toSubmodule.baseChange ℂ ∧
      ∀ z ∈ ({Complex.I, -Complex.I} : Set ℂ),
        (ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) z
          ).toSubmodule.map Ψ.toLinearMap =
        (ambientComplexifiedHalf (orthogonalComplement C l) (commutantComplexStructure c) z
          ).toSubmodule := by
  classical
  obtain ⟨s₁, m₁, σ, σH, h₀, h₁, h₂⟩ :=
    compact_common_cartan_canonical_lie_conjugacy B h ha hp e hr H hH b
  obtain ⟨s₂, m₂, τ, τJ, l₀, l₁, l₂⟩ :=
    compact_common_cartan_canonical_lie_conjugacy C l la lp c lr J lJ d
  letI : IsSimple ℂ (ℂ ⊗[ℝ] g) := (all_rank_complex_structural_reduction B h ha hp e hr).2.1
  letI : IsSimple ℂ (ℂ ⊗[ℝ] p) := (all_rank_complex_structural_reduction C l la lp c lr).2.1
  letI : Nontrivial H := Module.nontrivial_of_finrank_pos (R := ℂ) (by
    rw [finrank_eq_card_basis (b.toCoweightBasis.reindex s₁.symm), Fintype.card_fin]
    decide)
  let s := s₁.symm.trans s₂
  let T := cartanEquiv H b J d s
  have hm (i j : b.support) : b.cartanMatrix i j = d.cartanMatrix (s i) (s j) := by
    simpa [s] using (m₁ (s₁.symm i) (s₁.symm j)).trans (m₂ (s₁.symm i) (s₁.symm j)).symm
  obtain ⟨Φ, hΦ⟩ := lie_equiv_of_matching_cartan_matrix H b J d s hm
  have mapGrade := map_labeled_character_grade H b J d s₁ s₂ T (by
    intro i x
    simpa [s, T] using matched_simple_root_value H b J d s hm (s₁ i) x) Φ hΦ canonical
  let Ψ := (σ.trans Φ).trans τ.symm
  have maps (A : Submodule ℂ (ℂ ⊗[ℝ] g)) (U : Submodule ℂ (ℂ ⊗[ℝ] p)) (k : ZMod 3)
      (hA : A.map σ.toLinearMap = rootCharacterGrade H ((simpleCharacterEquiv H b s₁).symm canonical) k)
      (hU : U.map τ.toLinearMap = rootCharacterGrade J ((simpleCharacterEquiv J d s₂).symm canonical) k) :
      A.map Ψ.toLinearMap = U := by
    calc
      _ = ((A.map σ.toLinearMap).map Φ.toLinearMap).map τ.symm.toLinearMap := by
        rw [← Submodule.map_comp, ← Submodule.map_comp]
        rfl
      _ = U := by
        rw [hA, mapGrade, ← hU, ← Submodule.map_comp]
        change U.map (τ.toLinearEquiv.symm.toLinearMap.comp τ.toLinearEquiv.toLinearMap) = U
        simp
  refine ⟨Ψ, ?_, maps _ _ 0 h₀ l₀, ?_⟩
  · intro x
    change τ.symm (Φ (σ x)) ∈ J ↔ x ∈ H
    have hτ : τ.symm (Φ (σ x)) ∈ J ↔ Φ (σ x) ∈ J := by
      simpa only [LieEquiv.apply_symm_apply] using (τJ (τ.symm (Φ (σ x)))).symm
    rw [hτ, ← σH x]
    constructor
    · intro hi
      let v : J := ⟨Φ (σ x), hi⟩
      have hh : Φ (T.symm v).val = Φ (σ x) := (hΦ _).trans
        (congrArg Subtype.val (T.apply_symm_apply v))
      exact Φ.injective hh ▸ (T.symm v).property
    · intro hi
      exact hΦ ⟨σ x, hi⟩ ▸ (T ⟨σ x, hi⟩).property
  · rintro z (rfl | hz)
    · exact maps _ _ 1 h₁ l₁
    · obtain rfl : z = -Complex.I := hz
      exact maps _ _ (-1) h₂ l₂

/-- Real common Cartans supply the required bases of both complex root systems. -/
theorem compact_real_cartan_pairs_complex_equiv
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (A : LieSubalgebra ℝ g) [(complexifiedSubalgebra A).IsCartanSubalgebra] (hA : A ≤ h)
    (C : CompactForm p) (l : LieSubalgebra ℝ p) (la : Effective l) (lp : l ≠ ⊤)
    (c : lieCommutant (L := l) (M := orthogonalComplement C l) ≃ₐ[ℝ] ℂ)
    (lr : (hermitianHalfOfCommutant C l c).cubicRadical ≠ ⊥)
    (C₀ : LieSubalgebra ℝ p) [(complexifiedSubalgebra C₀).IsCartanSubalgebra] (lC : C₀ ≤ l) :
    ∃ Ψ : (ℂ ⊗[ℝ] g) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] p),
      (∀ x, Ψ x ∈ complexifiedSubalgebra C₀ ↔ x ∈ complexifiedSubalgebra A) ∧
      (h.toSubmodule.baseChange ℂ).map Ψ.toLinearMap = l.toSubmodule.baseChange ℂ ∧
      ∀ z ∈ ({Complex.I, -Complex.I} : Set ℂ),
        (ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) z
          ).toSubmodule.map Ψ.toLinearMap =
        (ambientComplexifiedHalf (orthogonalComplement C l) (commutantComplexStructure c) z
          ).toSubmodule := by
  letI : IsKilling ℂ (ℂ ⊗[ℝ] g) := (all_rank_complex_structural_reduction B h ha hp e hr).2.2.1
  letI : IsKilling ℂ (ℂ ⊗[ℝ] p) := (all_rank_complex_structural_reduction C l la lp c lr).2.2.1
  obtain ⟨b⟩ := (rootSystem (complexifiedSubalgebra A)).nonempty_base
  obtain ⟨d⟩ := (rootSystem (complexifiedSubalgebra C₀)).nonempty_base
  exact compact_common_cartan_pairs_complex_equiv B h ha hp e hr (complexifiedSubalgebra A)
    (CompactCartan.complexified_subalgebra_mono hA) b C l la lp c lr (complexifiedSubalgebra C₀)
    (CompactCartan.complexified_subalgebra_mono lC) d

end CubicAnomaly.Classification.EqualRankPairConjugacy
