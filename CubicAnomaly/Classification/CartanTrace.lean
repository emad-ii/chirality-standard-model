import CubicAnomaly.Classification.CartanCubic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The actual matrix trace cubic and Cartan detection

This connects the direct Cartan restriction theorem to an actual complex Lie
representation.  The invariant tensor and its full symmetry are proved from
matrix trace identities; neither is a supplied representation hypothesis.
-/

namespace CubicAnomaly.Classification.CartanTrace

open Matrix
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanCubic

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Cyclicity of trace makes the symmetrized cubic symmetric in its first slots. -/
theorem matrix_trace_cubic_swap_first (A B C : Matrix n n ℂ) :
    matrixTraceCubic A B C = matrixTraceCubic B A C := by
  simp only [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add]
  rw [Matrix.trace_mul_cycle' A C B, Matrix.trace_mul_cycle' B C A]
  ring

omit [DecidableEq n] in
/-- Symmetry of the last two slots follows directly from the anticommutator. -/
theorem matrix_trace_cubic_swap_last (A B C : Matrix n n ℂ) :
    matrixTraceCubic A B C = matrixTraceCubic A C B := by
  simp only [matrixTraceCubic, add_comm]

/-- The symmetrized matrix trace as a complex trilinear form. -/
noncomputable def complexTraceCubicForm {L : Type*} [AddCommGroup L] [Module ℂ L]
    (T : L →ₗ[ℂ] Matrix n n ℂ) : L →ₗ[ℂ] L →ₗ[ℂ] L →ₗ[ℂ] ℂ where
  toFun x := {
    toFun := fun y => {
      toFun := fun z => matrixTraceCubic (T x) (T y) (T z)
      map_add' := by
        intro z w
        simp [matrixTraceCubic, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
        ring
      map_smul' := by
        intro t z
        simp [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
        ring }
    map_add' := by
      intro y z
      ext w
      simp [matrixTraceCubic, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
      ring
    map_smul' := by
      intro t y
      ext z
      simp [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
      ring }
  map_add' := by
    intro x y
    ext z w
    simp [matrixTraceCubic, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    ring
  map_smul' := by
    intro t x
    ext y z
    simp [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
    ring

/-- Every complex-linear matrix action has a fully symmetric trace cubic. -/
theorem complex_trace_cubic_symmetric {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (T : L →ₗ[ℂ] Matrix n n ℂ) : IsSymmetric (complexTraceCubicForm T) :=
  ⟨fun x y z => matrix_trace_cubic_swap_first (T x) (T y) (T z),
    fun x y z => matrix_trace_cubic_swap_last (T x) (T y) (T z)⟩

/-- A complex Lie representation gives an invariant trace cubic. -/
theorem complex_trace_cubic_invariant {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (ρ : L →ₗ⁅ℂ⁆ Matrix n n ℂ) : IsInvariant (complexTraceCubicForm ρ.toLinearMap) := by
  intro a x y z
  change matrixTraceCubic (ρ ⁅a, x⁆) (ρ y) (ρ z) +
    matrixTraceCubic (ρ x) (ρ ⁅a, y⁆) (ρ z) +
    matrixTraceCubic (ρ x) (ρ y) (ρ ⁅a, z⁆) = 0
  simp only [LieHom.map_lie, Ring.lie_def]
  exact matrix_trace_cubic_invariant (ρ a) (ρ x) (ρ y) (ρ z)

/-- The actual full trace-cubic radical of a complex Lie representation. -/
noncomputable def complexTraceRadical {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (ρ : L →ₗ⁅ℂ⁆ Matrix n n ℂ) : LieIdeal ℂ L :=
  radical (complexTraceCubicForm ρ.toLinearMap) (complex_trace_cubic_invariant ρ)

/-- Cartan tests determine which actual Lie ideals lie in the full trace radical. -/
theorem complex_trace_radical_ideal_iff_cartan
    {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (ρ : L →ₗ⁅ℂ⁆ Matrix n n ℂ) (I : LieIdeal ℂ L) :
    I ≤ complexTraceRadical ρ ↔
      ∀ x : H, (x : L) ∈ I → ∀ y z : H,
        matrixTraceCubic (ρ x) (ρ y) (ρ z) = 0 :=
  ideal_le_radical_iff_cartan H (complexTraceCubicForm ρ.toLinearMap)
    (complex_trace_cubic_invariant ρ) (complex_trace_cubic_symmetric ρ.toLinearMap) I

/-- The complete anomaly test reduces to the kernel of a finite Cartan tensor
matrix, with invariance and symmetry proved from the representation. -/
theorem complex_trace_radical_ne_bot_iff_matrix_kernel
    {L ι : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    [Fintype ι] (b : Module.Basis ι ℂ H) (ρ : L →ₗ⁅ℂ⁆ Matrix n n ℂ) :
    complexTraceRadical ρ ≠ ⊥ ↔
      ∃ v : ι → ℂ, v ≠ 0 ∧
        cartanCubicMatrix H b (complexTraceCubicForm ρ.toLinearMap) *ᵥ v = 0 :=
  radical_ne_bot_iff_cartan_matrix_kernel H b (complexTraceCubicForm ρ.toLinearMap)
    (complex_trace_cubic_invariant ρ) (complex_trace_cubic_symmetric ρ.toLinearMap)

end CubicAnomaly.Classification.CartanTrace
