import CubicAnomaly.Fixed.NestedPairReduction
import CubicAnomaly.Classification.ExceptionalSieveAssembly
import CubicAnomaly.Classification.TypeACompactExclusion
import CubicAnomaly.Classification.TypeCCompactRecognition

/-! The original pair hypotheses force the oriented exceptional pair or an
ambient orthogonal Dynkin diagram. The rank comparison and the diagram
are derived from the pair. -/

namespace CubicAnomaly.Fixed.AmbientClassification

open LieAlgebra LieAlgebra.IsKilling LieModule Module
open Classification Classification.CompactGeometry Classification.Structural
open Classification.HermitianRealization Classification.CompactCartan
open Classification.RootClassificationExceptional Classification.Exceptional
open Classification.ExceptionalSieveProducts Classification.ExceptionalSieve
open E8EqualRankRealPair NestedPairReduction
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]

/-- If the anomaly radical is nonzero, only the fixed pair and the two
orthogonal diagrams survive the simple Dynkin classification. In the
orthogonal branch the diagram is that of a scalar-extended real Cartan. -/
theorem fixed_or_orthogonal_cartan (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] g)] :
    IsOrientedFixedPair B h e ∨ ∃ (D : LieSubalgebra ℝ g)
      (_ : (complexifiedSubalgebra D).IsCartanSubalgebra)
      (b : (rootSystem (complexifiedSubalgebra D)).Base) (n : ℕ) (s : b.support ≃ Fin n),
      b.cartanMatrix.reindex s s = CartanMatrix.B n ∨
      b.cartanMatrix.reindex s s = CartanMatrix.D n := by
  rcases fixed_or_strict_nested_cartans B h ha hp e hr with hfix | ⟨T, D, hT, hD, hlt, hn⟩
  · exact Or.inl hfix
  letI := hT
  letI := hD
  have struc := AllRankComplex.all_rank_complex_structural_reduction B h ha hp e hr
  letI : IsSimple ℂ (ℂ ⊗[ℝ] g) := struc.2.1
  letI : IsKilling ℂ (ℂ ⊗[ℝ] h) := struc.2.2.2.1
  let H := complexifiedSubalgebra D
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  rcases simple_lie_classical_or_exceptional_census H b with hc | ⟨d, hd, s, hs, _⟩
  · rcases hc with ⟨n, s, hA⟩ | ⟨n, s, hB⟩ | ⟨n, s, hC⟩ | ⟨n, s, hDD⟩
    · exact (hr (TypeACompactRecognition.type_A_cubic_radical_eq_bot B h ha hp e D b s hA)).elim
    · exact Or.inr ⟨D, hD, b, n, s, Or.inl hB⟩
    · exact (hr (TypeCCompactRecognition.type_C_cubic_radical_eq_bot B h ha hp e D b s hC)).elim
    · exact Or.inr ⟨D, hD, b, n, s, Or.inr hDD⟩
  · exfalso
    have hsz : finrank ℂ H = d.cartan.size :=
      (finrank_eq_card_basis (b.toCoweightBasis.reindex s.symm)).trans (Fintype.card_fin _)
    have impossible (G : Ambient) (hdG : d = ambientDatum G) (hsize : (ambientDatum G).cartan.size = G.rank) :
        False := by
      subst d
      have hbound := ExceptionalSieveAssembly.compact_pair_exceptional_rank_bound B h ha hp e hr
        (complexifiedSubalgebra T) H hn G b s hs
      exact (not_lt_of_ge (hsz.trans hsize ▸ hbound)) hlt
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact impossible .g2 rfl rfl
    · exact impossible .f4 rfl rfl
    · exact impossible .e6 rfl rfl
    · exact impossible .e7 rfl rfl
    · exact impossible .e8 rfl rfl

end CubicAnomaly.Fixed.AmbientClassification
