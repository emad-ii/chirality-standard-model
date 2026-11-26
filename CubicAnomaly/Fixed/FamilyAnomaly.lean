import CubicAnomaly.Fixed.TensorAnomaly
import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The actual three-dimensional family representation

The defining representation of the literal complex Lie algebra `sl(3,ℂ)`
has nondegenerate full cubic. This is proved directly by elementary matrices,
without a simplicity classification. Combining it with the constructed
external tensor action identifies its radical and surviving family cubic.
-/

namespace CubicAnomaly.Fixed.FamilyAnomaly

open Matrix
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Fixed.TensorAnomaly

noncomputable section

private theorem cubic_single_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (d : n → ℂ) (i j : n) :
    matrixTraceCubic A (single j i 1) (diagonal d) =
      ((d i + d j) / 2) * A i j := by
  rw [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add]
  rw [Matrix.trace_mul_cycle' A (single j i 1) (diagonal d)]
  simp only [← Matrix.mul_assoc, Matrix.trace_mul_single,
    MulOpposite.op_one, one_smul, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private def familyDiagonal : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal ![1, 1, -2]

private theorem family_diagonal_trace : trace familyDiagonal = 0 := by
  norm_num [familyDiagonal, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

/-- Elementary traceless test matrices detect every entry of a `3 × 3`
matrix through the full cubic. No Lie simplicity theorem is assumed. -/
theorem three_by_three_cubic_detects_matrix
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ B C : Matrix (Fin 3) (Fin 3) ℂ,
      trace B = 0 → trace C = 0 → matrixTraceCubic A B C = 0) : A = 0 := by
  have hoff (i j : Fin 3) (hij : i ≠ j) : A i j = 0 := by
    have h := hA (single j i 1) familyDiagonal
      (Matrix.trace_single_eq_of_ne j i 1 hij.symm) family_diagonal_trace
    change matrixTraceCubic A (single j i 1) (diagonal ![1, 1, -2]) = 0 at h
    rw [cubic_single_diagonal] at h
    have hc : ((![1, 1, -2] i + ![1, 1, -2] j) / 2 : ℂ) ≠ 0 := by
      fin_cases i <;> fin_cases j <;> norm_num at *
    exact (mul_eq_zero.mp h).resolve_left hc
  have hdiag (d : Fin 3 → ℂ) (hd : ∑ i, d i = 0) :
      matrixTraceCubic A (diagonal d) (diagonal d) = 0 :=
    hA _ _ (by simpa using hd) (by simpa using hd)
  have h01 := hdiag ![1, -1, 0] (by norm_num [Fin.sum_univ_succ])
  have h02 := hdiag ![1, 0, -1] (by norm_num [Fin.sum_univ_succ])
  have h12 := hdiag ![0, 1, -1] (by norm_num [Fin.sum_univ_succ])
  norm_num [matrixTraceCubic, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.diagonal, Matrix.of_apply, Fin.sum_univ_succ] at h01 h02 h12
  simp only [hoff 0 2 (by decide), hoff 2 0 (by decide), zero_mul,
    zero_add, add_zero] at h02
  simp only [hoff 1 2 (by decide), hoff 2 1 (by decide), zero_mul,
    zero_add, add_zero] at h12
  have h00 : A 0 0 = 0 := by linear_combination (h01 + h02 - h12) / 4
  have h11 : A 1 1 = 0 := by linear_combination (h01 + h12 - h02) / 4
  have h22 : A 2 2 = 0 := by linear_combination (h02 + h12 - h01) / 4
  ext i j
  by_cases hij : i = j
  · subst j
    fin_cases i <;> assumption
  · exact hoff i j hij

/-- The actual defining complex family Lie algebra. -/
abbrev FamilyLie := LieAlgebra.SpecialLinear.sl (Fin 3) ℂ

/-- Its literal action by its own `3 × 3` matrices. -/
def familyRepresentation : FamilyLie →ₗ⁅ℂ⁆ Matrix (Fin 3) (Fin 3) ℂ :=
  FamilyLie.incl

/-- Every actual family generator is traceless by the definition of `sl₃`. -/
theorem family_representation_trace (x : FamilyLie) :
    trace (familyRepresentation x) = 0 := x.property

/-- The full cubic radical of the actual defining family representation
is zero. The elementary-matrix proof includes every mixed insertion. -/
theorem family_representation_radical_eq_bot :
    complexTraceRadical familyRepresentation = ⊥ := by
  apply (radical_eq_bot_iff _ _).mpr
  intro x hx
  apply Subtype.ext
  apply three_by_three_cubic_detects_matrix x.val
  intro B C hB hC
  exact hx ⟨B, hB⟩ ⟨C, hC⟩

/-- A concrete nonzero family cubic witness with eigenvalues `1,1,-2`. -/
def familyWitness : FamilyLie := ⟨familyDiagonal, family_diagonal_trace⟩

/-- The normalized defining family cubic is explicitly nonzero. -/
theorem family_cubic_witness :
    matrixTraceCubic (familyRepresentation familyWitness)
      (familyRepresentation familyWitness) (familyRepresentation familyWitness) = -6 := by
  change matrixTraceCubic familyDiagonal familyDiagonal familyDiagonal = -6
  norm_num [matrixTraceCubic, familyDiagonal, Matrix.mul_add,
    Matrix.diagonal_mul_diagonal, Matrix.trace_add, Matrix.trace_diagonal,
    Fin.sum_univ_succ]

variable {L m : Type*} [LieRing L] [LieAlgebra ℂ L]
  [Fintype m] [DecidableEq m]

/-- Tensoring any actual matrix representation with the defining family
representation gives a literal action on triples of its defining space. -/
def familyTensorRepresentation (ρ : L →ₗ⁅ℂ⁆ Matrix m m ℂ) :
    ProductLie L FamilyLie →ₗ⁅ℂ⁆ Matrix (m × Fin 3) (m × Fin 3) ℂ :=
  tensorRepresentation ρ familyRepresentation

/-- The concrete family factor contributes no cubic-radical directions.
Only tracelessness and the vanishing cubic of the left representation remain
as hypotheses; the right representation and its nondegeneracy are proved. -/
theorem family_tensor_radical_eq_left_ideal [Nonempty m]
    (ρ : L →ₗ⁅ℂ⁆ Matrix m m ℂ)
    (hρ : ∀ x, trace (ρ x) = 0)
    (hleft : ∀ x y z, matrixTraceCubic (ρ x) (ρ y) (ρ z) = 0) :
    complexTraceRadical (familyTensorRepresentation ρ) =
      (secondProjection : ProductLie L FamilyLie →ₗ⁅ℂ⁆ FamilyLie).ker :=
  tensor_radical_eq_first_ideal ρ familyRepresentation hρ
    family_representation_trace hleft family_representation_radical_eq_bot

/-- Every surviving cubic insertion is exactly the family cubic times
the dimension of the left defining space. -/
theorem family_tensor_full_cubic
    (ρ : L →ₗ⁅ℂ⁆ Matrix m m ℂ)
    (hρ : ∀ x, trace (ρ x) = 0)
    (hleft : ∀ x y z, matrixTraceCubic (ρ x) (ρ y) (ρ z) = 0)
    (x y z : ProductLie L FamilyLie) :
    matrixTraceCubic (familyTensorRepresentation ρ x)
      (familyTensorRepresentation ρ y) (familyTensorRepresentation ρ z) =
      (Fintype.card m : ℂ) *
        matrixTraceCubic (familyRepresentation x.2)
          (familyRepresentation y.2) (familyRepresentation z.2) := by
  rw [familyTensorRepresentation, tensor_representation_cubic ρ familyRepresentation
    hρ family_representation_trace, hleft, mul_zero, zero_add]

/-- Pure family insertions have the same dimension coefficient without
any assumptions on the other representation's anomaly or trace. -/
theorem family_tensor_pure_cubic
    (ρ : L →ₗ⁅ℂ⁆ Matrix m m ℂ) (x y z : FamilyLie) :
    matrixTraceCubic (familyTensorRepresentation ρ (0, x))
      (familyTensorRepresentation ρ (0, y)) (familyTensorRepresentation ρ (0, z)) =
      (Fintype.card m : ℂ) *
        matrixTraceCubic (familyRepresentation x)
          (familyRepresentation y) (familyRepresentation z) := by
  change matrixTraceCubic (tensorAction (ρ 0) (familyRepresentation x))
    (tensorAction (ρ 0) (familyRepresentation y))
    (tensorAction (ρ 0) (familyRepresentation z)) = _
  rw [tensor_action_trace_cubic _ _ _ _ _ _ (by simp) (by simp) (by simp)
    (family_representation_trace x) (family_representation_trace y)
    (family_representation_trace z)]
  simp [matrixTraceCubic]

/-- The 81-dimensional tensor construction has the explicit nonzero
family cubic `27 * (-6) = -162`, independently of its left-factor anomaly. -/
theorem family_tensor_27_cubic_witness
    (ρ : L →ₗ⁅ℂ⁆ Matrix (Fin 27) (Fin 27) ℂ) :
    matrixTraceCubic (familyTensorRepresentation ρ (0, familyWitness))
      (familyTensorRepresentation ρ (0, familyWitness))
      (familyTensorRepresentation ρ (0, familyWitness)) = -162 := by
  rw [family_tensor_pure_cubic, family_cubic_witness]
  norm_num

end

end CubicAnomaly.Fixed.FamilyAnomaly
