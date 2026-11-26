import CubicAnomaly.Classification.TypeBCompactRecognition
import CubicAnomaly.Classification.TypeDCompactRecognition
import CubicAnomaly.Classification.TypeACompactExclusion

/-! A surviving B or D diagram of an original compact pair produces a
real orthogonal model, across the entire range of diagram parameters. -/
namespace CubicAnomaly.Classification.ClassicalOrthogonalRecognition

open LieAlgebra LieAlgebra.IsKilling CompactGeometry Structural HermitianRealization OrthogonalDefining
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
  [IsKilling ℂ (ℂ ⊗[ℝ] g)]

/-- The surviving B and D branches carry actual compact orthogonal Lie
equivalences. The anomalous hypothesis excludes the degenerate D₁
diagram through its identification with A₁. -/
theorem exists_orthogonal_model (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (A : LieSubalgebra ℝ g) [(complexifiedSubalgebra A).IsCartanSubalgebra]
    (b : (rootSystem (complexifiedSubalgebra A)).Base) {n : ℕ} (s : b.support ≃ Fin n)
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.B n ∨ b.cartanMatrix.reindex s s = CartanMatrix.D n) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (g ≃ₗ⁅ℝ⁆ orthogonalAlgebra (EuclideanSpace ℝ ι)) := by
  letI : IsSimple ℂ (ℂ ⊗[ℝ] g) := AbsoluteSimplicity.compact_pair_complexification_simple B h ha hp e
  cases n with
  | zero =>
    letI : Nontrivial (complexifiedSubalgebra A) := RootPairing.IsIrreducible.nontrivial' (rootSystem (complexifiedSubalgebra A))
    obtain ⟨i⟩ := b.toCoweightBasis.index_nonempty
    exact (s i).elim0
  | succ m =>
    rcases hm with hB | hD
    · exact ⟨_, inferInstance, TypeBCompactRecognition.typeB_exists_orthogonal_equiv B A b s hB⟩
    · cases m with
      | zero =>
        rw [CartanMatrix.D_one] at hD
        exact (hr (TypeACompactRecognition.type_A_cubic_radical_eq_bot B h ha hp e A b s hD)).elim
      | succ k => exact ⟨_, inferInstance, TypeDCompactRecognition.typeD_exists_orthogonal_equiv B A b s hD⟩

end CubicAnomaly.Classification.ClassicalOrthogonalRecognition
