import CubicAnomaly.Classification.TypeBCartanCoordinates
import CubicAnomaly.Classification.ClassicalMatrixRecognition
import CubicAnomaly.Classification.OrthogonalMatrixDimension

/-! Match all normalized simple triples of type B to the actual split odd
orthogonal algebra. -/
namespace CubicAnomaly.Classification.TypeBMatrixRecognition

open LieAlgebra LieAlgebra.Orthogonal LieAlgebra.IsKilling LieModule Module
open OddOrthogonalMatrixGenerators TypeBCartanCoordinates

variable {n : ℕ} {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  (s : b.support ≃ Fin (n+1)) (hm : b.cartanMatrix.reindex s s = CartanMatrix.B (n+1))

noncomputable def cartanHom : H →ₗ⁅ℂ⁆ typeB (Fin (n+1)) ℂ where
  toFun h := diagonal (coordinates H b s h)
  map_add' h k := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ + Matrix.diagonal _
    rw [Matrix.diagonal_add]
    apply congrArg Matrix.diagonal
    ext i
    rcases i with _ | (i|i) <;> simp [diagonalEntries, map_add, add_comm]
  map_smul' c h := by
    apply Subtype.ext
    change Matrix.diagonal _ = c • Matrix.diagonal _
    rw [← Matrix.diagonal_smul]
    apply congrArg Matrix.diagonal
    ext i
    rcases i with _ | (i|i) <;> simp [diagonalEntries, map_smul]
  map_lie' {h k} := by
    apply Subtype.ext
    change Matrix.diagonal _ = ⁅Matrix.diagonal _, Matrix.diagonal _⁆
    rw [trivial_lie_zero]
    have hz : diagonalEntries (0 : Fin (n+1) → ℂ) = 0 := by
      ext i; rcases i with _ | (i|i) <;> simp [diagonalEntries]
    simp [Ring.lie_def, Matrix.diagonal_mul_diagonal, mul_comm, hz]

theorem typeB_cartanHom_injective : Function.Injective (cartanHom H b s) := by
  intro x y h
  apply (coordinates H b s).injective
  ext i
  have h' := congrArg (fun A : typeB (Fin (n+1)) ℂ => A.val (pos i) (pos i)) h
  change Matrix.diagonal (diagonalEntries (coordinates H b s x)) (pos i) (pos i) =
    Matrix.diagonal (diagonalEntries (coordinates H b s y)) (pos i) (pos i) at h'
  simpa [diagonalEntries] using h'

set_option maxHeartbeats 1200000 in
include hm in
theorem typeB_exists_matrix_equiv [LieAlgebra.IsSimple ℂ L] (e f : b.support → L)
    (ht : ∀ i, IsSl2Triple (coroot i.val.val : L) (e i) (f i))
    (he : ∀ i, e i ∈ rootSpace H i.val.val)
    (hf : ∀ i, f i ∈ rootSpace H (-(i.val.val : H → ℂ))) :
    ∃ Φ : L ≃ₗ⁅ℂ⁆ typeB (Fin (n+1)) ℂ, (∀ h : H, Φ h.val = cartanHom H b s h) ∧
      (∀ i, Φ (e i) = raising (s i)) ∧ ∀ i, Φ (f i) = lowering (s i) := by
  have hwt (i : b.support) (h : H) : weight (s i) (coordinates H b s h) = i.val.val h := by
    simpa only [s.symm_apply_apply] using typeB_weight_coordinates H b s h (s i)
  refine ClassicalMatrixRecognition.classical_exists_matrix_equiv H b (cartanHom H b s) (typeB_cartanHom_injective H b s)
    (raising ∘ s) (lowering ∘ s) ?_ ?_ ?_ (fun i j hij => typeB_mixed_distinct _ _ (s.injective.ne hij))
    ((OrthogonalMatrixDimension.typeB_finrank_le _).trans (typeB_source_dimension H b s hm)) e f ht he hf
  · intro h i
    exact (typeB_diagonal_raising _ (s i)).trans (congrArg (· • raising (s i)) (hwt i h))
  · intro h i
    exact (typeB_diagonal_lowering _ (s i)).trans (congrArg (fun c : ℂ => -c • lowering (s i)) (hwt i h))
  · intro i
    have hi := typeB_coordinates_coroot H b s hm (s i)
    rw [s.symm_apply_apply] at hi
    change ⁅raising (s i), lowering (s i)⁆ = diagonal (coordinates H b s (coroot i.val.val))
    rw [typeB_mixed_same, hi]

end CubicAnomaly.Classification.TypeBMatrixRecognition
