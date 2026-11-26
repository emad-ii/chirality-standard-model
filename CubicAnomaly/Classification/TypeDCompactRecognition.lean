import CubicAnomaly.Classification.TypeDMatrixRecognition
import CubicAnomaly.Classification.OrthogonalCompactModelD

/-! The actual compact form of an even orthogonal simple algebra. -/
namespace CubicAnomaly.Classification.TypeDCompactRecognition

open LieAlgebra LieAlgebra.IsKilling LieModule Module CompactGeometry Structural OrthogonalDefining
open OrthogonalCompactModel OrthogonalMatrixGenerators CompactChevalleyConjugation
open scoped TensorProduct Matrix

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  [IsKilling ℂ (ℂ ⊗[ℝ] g)] [IsSimple ℂ (ℂ ⊗[ℝ] g)]

/-- A compact simple algebra of type D and rank at least two is the
real orthogonal algebra on its real defining space of twice the rank. -/
theorem typeD_exists_orthogonal_equiv (B : CompactForm g) (A : LieSubalgebra ℝ g)
    [(complexifiedSubalgebra A).IsCartanSubalgebra]
    (b : (rootSystem (complexifiedSubalgebra A)).Base) {n : ℕ} (s : b.support ≃ Fin (n+2))
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.D (n+2)) :
    Nonempty (g ≃ₗ⁅ℝ⁆ orthogonalAlgebra (EuclideanSpace ℝ (Fin (n+2) ⊕ Fin (n+2)))) := by
  let F := matrixDEquiv (Fin (n+2))
  have hc (i : Fin (n+2)) : scalarConjugation (F.symm (raising i)) = -F.symm (lowering i) := by
    apply F.injective
    apply Subtype.ext
    change (F (scalarConjugation (F.symm (raising i)))).val = (F (-F.symm (lowering i))).val
    have hn : F (-F.symm (lowering i)) = -lowering i :=
      (_root_.map_neg F.toLinearMap (F.symm (lowering i))).trans (congrArg Neg.neg (F.apply_symm_apply _))
    rw [typeD_scalar_conjugation, F.apply_symm_apply, hn, typeD_raising_adjoint]
    rfl
  apply ClassicalMatrixRecognition.exists_compact_equiv B A b F (raising ∘ s) (lowering ∘ s)
    (fun i => hc (s i))
  intro e f ht he hf
  obtain ⟨Φ, _, hΦe, hΦf⟩ := TypeDMatrixRecognition.typeD_exists_matrix_equiv _ b s hm e f ht he hf
  exact ⟨Φ, hΦe, hΦf⟩

end CubicAnomaly.Classification.TypeDCompactRecognition
