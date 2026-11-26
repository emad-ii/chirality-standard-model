import CubicAnomaly.Classification.TypeDCartanCoordinates
import CubicAnomaly.Classification.ClassicalMatrixRecognition
import CubicAnomaly.Classification.OrthogonalMatrixDimension

/-! Matrix recognition of the actual even orthogonal simple Lie algebra. -/

namespace CubicAnomaly.Classification.TypeDMatrixRecognition

open LieAlgebra LieAlgebra.Orthogonal LieAlgebra.IsKilling LieModule Module
open OrthogonalMatrixGenerators TypeDCartanCoordinates

variable {n : ℕ} {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  (s : b.support ≃ Fin (n+2)) (hm : b.cartanMatrix.reindex s s = CartanMatrix.D (n+2))

/-- The actual Cartan mapped to the standard diagonal orthogonal matrices. -/
noncomputable def cartanHom : H →ₗ⁅ℂ⁆ typeD (Fin (n+2)) ℂ where
  toLinearMap := generalLinear.toLinearMap.comp
    ((Matrix.diagonalLinearMap (Fin (n+2)) ℂ ℂ).comp (coordinates H b s).toLinearMap)
  map_lie' {x y} := by
    change generalLinear (Matrix.diagonal (coordinates H b s ⁅x,y⁆)) =
      ⁅generalLinear (Matrix.diagonal (coordinates H b s x)), generalLinear (Matrix.diagonal (coordinates H b s y))⁆
    rw [trivial_lie_zero, map_zero, ← LieHom.map_lie]
    congr 1
    simp [Ring.lie_def, Matrix.diagonal_mul_diagonal, mul_comm]

theorem typeD_cartanHom_injective : Function.Injective (cartanHom H b s) := by
  intro x y h
  apply (coordinates H b s).injective
  ext i
  have h' := congrArg (fun A : typeD (Fin (n+2)) ℂ => A.val (.inl i) (.inl i)) h
  change Matrix.diagonal (coordinates H b s x) i i = Matrix.diagonal (coordinates H b s y) i i at h'
  simpa using h'

include hm in
/-- The actual type-D complex Lie algebra has the indicated standard split
matrix realization, matching every chosen normalized simple triple. -/
theorem typeD_exists_matrix_equiv [LieAlgebra.IsSimple ℂ L] (e f : b.support → L)
    (ht : ∀ i, IsSl2Triple (coroot i.val.val : L) (e i) (f i))
    (he : ∀ i, e i ∈ rootSpace H i.val.val)
    (hf : ∀ i, f i ∈ rootSpace H (-(i.val.val : H → ℂ))) :
    ∃ Φ : L ≃ₗ⁅ℂ⁆ typeD (Fin (n+2)) ℂ, (∀ h : H, Φ h.val = cartanHom H b s h) ∧
      (∀ i, Φ (e i) = raising (s i)) ∧ ∀ i, Φ (f i) = lowering (s i) := by
  have hwt (i : b.support) (h : H) : weight (s i) (coordinates H b s h) = i.val.val h := by
    simpa only [s.symm_apply_apply] using typeD_weight_coordinates H b s h (s i)
  refine ClassicalMatrixRecognition.classical_exists_matrix_equiv H b (cartanHom H b s) (typeD_cartanHom_injective H b s)
    (raising ∘ s) (lowering ∘ s) ?_ ?_ ?_ (fun i j hij => typeD_mixed_distinct _ _ (s.injective.ne hij))
    ((OrthogonalMatrixDimension.typeD_finrank_le _).trans (typeD_source_dimension H b s hm)) e f ht he hf
  · intro h i
    exact (typeD_diagonal_raising _ (s i)).trans (congrArg (· • raising (s i)) (hwt i h))
  · intro h i
    exact (typeD_diagonal_lowering _ (s i)).trans (congrArg (fun c : ℂ => -c • lowering (s i)) (hwt i h))
  · intro i
    have hc := typeD_coordinates_coroot H b s hm (s i)
    rw [s.symm_apply_apply] at hc
    change ⁅raising (s i), lowering (s i)⁆ = generalLinear (Matrix.diagonal (coordinates H b s (coroot i.val.val)))
    rw [typeD_mixed_same, typeD_diagonal_eq, hc]

end CubicAnomaly.Classification.TypeDMatrixRecognition
