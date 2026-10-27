import CubicAnomaly.Fixed.MatterSpectrum

/-!
# The actual Standard Model matrix Lie algebra

The complex Standard Model algebra is constructed as the block-diagonal
subalgebra of traceless five-by-five matrices. Every element is proved to
have the colour, weak and hypercharge form used in the literal matter
branching. Consequently the branching and anomaly formulas apply to all
elements of this actual subalgebra.
-/

namespace CubicAnomaly.Fixed.MatterLieAlgebra

open Matrix
open CubicAnomaly.Fixed.MatterBranching
open CubicAnomaly.Fixed.MatterSpectrum

noncomputable section

/-- Literal block-diagonal inclusion of the two full matrix algebras. -/
def blockDiagonalLieHom :
    (Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ) →ₗ⁅ℂ⁆ MatrixFive where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_add' p q := by ext (i | i) (j | j) <;> simp
  map_smul' c p := by ext (i | i) (j | j) <;> simp
  map_lie' {p q} := by
    change Matrix.fromBlocks (p.1 * q.1 - q.1 * p.1) 0 0
      (p.2 * q.2 - q.2 * p.2) =
      Matrix.fromBlocks p.1 0 0 p.2 * Matrix.fromBlocks q.1 0 0 q.2 -
        Matrix.fromBlocks q.1 0 0 q.2 * Matrix.fromBlocks p.1 0 0 p.2
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
    ext (i | i) (j | j) <;> simp

/-- The actual block-diagonal traceless subalgebra. -/
def standardModelLieSubalgebra : LieSubalgebra ℂ MatrixFive :=
  blockDiagonalLieHom.range ⊓ LieAlgebra.SpecialLinear.sl FiveIndex ℂ

/-- The actual complex Standard Model Lie algebra, with inherited brackets. -/
abbrev StandardModelAlgebra := standardModelLieSubalgebra

/-- Every colour/weak/hypercharge generator is an element of the actual algebra. -/
def standardModelGeneratorElement (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) : StandardModelAlgebra :=
  ⟨standardModelGenerator A B q, ⟨⟨(A + (-2 * q) • 1, B + (3 * q) • 1), rfl⟩,
    standard_model_generator_trace A B q hA hB⟩⟩

/-- The constructed element has exactly the advertised matrix. -/
@[simp] theorem standard_model_generator_element_val
    (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) :
    (standardModelGeneratorElement A B q hA hB).val =
      standardModelGenerator A B q := rfl

/-- Every actual Standard Model element admits traceless colour and weak
parameters and the primitive hypercharge parameter. This is a proved
exhaustiveness statement for the concrete subalgebra, not a record field. -/
theorem standard_model_element_parameters (x : StandardModelAlgebra) :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ),
      Matrix.trace A = 0 ∧ Matrix.trace B = 0 ∧
        standardModelGenerator A B q = x.val := by
  rcases x.property.1 with ⟨⟨C, D⟩, hCD⟩
  have ht : Matrix.trace C + Matrix.trace D = 0 := by
    have hx : Matrix.trace x.val = 0 := x.property.2
    rw [← hCD] at hx
    simpa [blockDiagonalLieHom, Matrix.trace, Fintype.sum_sum_type] using hx
  let q : ℂ := Matrix.trace D / 6
  let A := C + (2 * q) • 1
  let B := D - (3 * q) • 1
  refine ⟨A, B, q, ?_, ?_, ?_⟩
  · change Matrix.trace (C + (2 * q) • 1) = 0
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    dsimp [q]
    linear_combination ht
  · change Matrix.trace (D - (3 * q) • 1) = 0
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    dsimp [q]
    ring
  · change Matrix.fromBlocks (C + (2 * q) • 1 + (-2 * q) • 1) 0 0
      (D - (3 * q) • 1 + (3 * q) • 1) = x.val
    convert hCD using 1
    congr 1
    · module
    · abel

/-- The inherited actual Standard Model action on every part of the
constructed twenty-seven is the literal action of its included matrix. -/
@[simp] theorem standard_model_matter27_action (x : StandardModelAlgebra) (v : Matter27) :
    ⁅x, v⁆ = ⁅x.val, v⁆ := rfl

end

end CubicAnomaly.Fixed.MatterLieAlgebra
