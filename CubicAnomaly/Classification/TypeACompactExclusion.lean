import CubicAnomaly.Classification.TypeACompactRecognition
import CubicAnomaly.Classification.ClassicalModelTransport

/-! Type A is impossible for the ambient algebra of an anomalous pair,
for every rank of the isotropy and every compact ambient real form. -/

namespace CubicAnomaly.Classification.TypeACompactRecognition

open LieAlgebra LieAlgebra.IsKilling CompactGeometry Structural HermitianRealization
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
  [IsKilling ℂ (ℂ ⊗[ℝ] g)]

/-- The full mixed cubic radical vanishes if the actual ambient simple
Cartan matrix is of type A. The real Cartan can be chosen independently
of the isotropy. -/
theorem type_A_cubic_radical_eq_bot (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (A : LieSubalgebra ℝ g) [(complexifiedSubalgebra A).IsCartanSubalgebra]
    (b : (rootSystem (complexifiedSubalgebra A)).Base) {n : ℕ} (s : b.support ≃ Fin n)
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊥ := by
  letI : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g) :=
    AbsoluteSimplicity.compact_pair_complexification_simple B h ha hp e
  obtain ⟨f⟩ := exists_special_unitary_equiv B A b s hm
  exact ClassicalModelTransport.special_unitary_model_radical_eq_bot B h ha hp e f

end CubicAnomaly.Classification.TypeACompactRecognition
