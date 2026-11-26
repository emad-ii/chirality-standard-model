import CubicAnomaly.Classification.TypeBMatrixRecognition
import CubicAnomaly.Classification.OrthogonalCompactModel
import CubicAnomaly.Classification.TypeBCompactAdjoint

/-! The actual compact form of an odd orthogonal simple algebra. -/
namespace CubicAnomaly.Classification.TypeBCompactRecognition

open LieAlgebra LieAlgebra.IsKilling LieModule Module CompactGeometry Structural OrthogonalDefining
open OrthogonalCompactModel OddOrthogonalMatrixGenerators CompactChevalleyConjugation
open scoped TensorProduct Matrix

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  [IsKilling ℂ (ℂ ⊗[ℝ] g)] [IsSimple ℂ (ℂ ⊗[ℝ] g)]

/-- A compact simple algebra of type B is the
real orthogonal algebra on its odd-dimensional defining space. -/
theorem typeB_exists_orthogonal_equiv (B : CompactForm g) (A : LieSubalgebra ℝ g)
    [(complexifiedSubalgebra A).IsCartanSubalgebra]
    (b : (rootSystem (complexifiedSubalgebra A)).Base) {n : ℕ} (s : b.support ≃ Fin (n+1))
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.B (n+1)) :
    Nonempty (g ≃ₗ⁅ℝ⁆ orthogonalAlgebra (EuclideanSpace ℝ (Unit ⊕ (Fin (n+1) ⊕ Fin (n+1))))) := by
  let F := matrixBEquiv (Fin (n+1))
  have hc (i : Fin (n+1)) : scalarConjugation (F.symm (raising i)) = -F.symm (lowering i) := by
    apply F.injective
    apply Subtype.ext
    change (F (scalarConjugation (F.symm (raising i)))).val = (F (-F.symm (lowering i))).val
    have hn : F (-F.symm (lowering i)) = -lowering i :=
      (_root_.map_neg F.toLinearMap (F.symm (lowering i))).trans (congrArg Neg.neg (F.apply_symm_apply _))
    rw [typeB_scalar_conjugation, F.apply_symm_apply, hn]
    exact congrArg Neg.neg (TypeBCompactAdjoint.raising_block_adjoint i)
  apply ClassicalMatrixRecognition.exists_compact_equiv B A b F (raising ∘ s) (lowering ∘ s)
    (fun i => hc (s i))
  intro e f ht he hf
  obtain ⟨Φ, _, hΦe, hΦf⟩ := TypeBMatrixRecognition.typeB_exists_matrix_equiv _ b s hm e f ht he hf
  exact ⟨Φ, hΦe, hΦf⟩

end CubicAnomaly.Classification.TypeBCompactRecognition
