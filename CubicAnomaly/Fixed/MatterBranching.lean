import CubicAnomaly.Fixed.MatterBlocks
import CubicAnomaly.Fixed.MatterSmall

/-!
# An actual Standard Model restriction of the ten

The five-dimensional defining space is split into a three-dimensional
colour space and a two-dimensional weak space. The constructed alternating
tensor representation then restricts, by an explicit linear equivalence,
to the dual colour module, the colour-weak tensor module, and a singlet.
The primitive hypercharge generator has respective integer charges
`-4`, `1`, and `6`; conventional hypercharge divides these by six.

No exceptional branching theorem is assumed here. Identifying this actual
classical module with the restriction of an exceptional module remains
a separate theorem.
-/

namespace CubicAnomaly.Fixed.MatterBranching

open Matrix
open CubicAnomaly.Fixed.MatterAlternating
open CubicAnomaly.Fixed.MatterBlocks
open CubicAnomaly.Fixed.MatterSmall

noncomputable section

/-- Colour and weak indices of the actual five-dimensional defining space. -/
abbrev FiveIndex := Fin 3 ⊕ Fin 2

/-- The actual alternating-tensor ten. -/
abbrev Ten := AlternatingTensor FiveIndex

/-- Actual coordinates for the dual colour, colour-weak and singlet summands. -/
def tenCoordinates : Ten ≃ₗ[ℂ]
    (Fin 3 → ℂ) × (Matrix (Fin 3) (Fin 2) ℂ × ℂ) :=
  (alternatingBlockEquiv (Fin 3) (Fin 2)).trans
    (LinearEquiv.prodCongr alternatingThreeEquiv
      (LinearEquiv.prodCongr (LinearEquiv.refl ℂ _) alternatingTwoEquiv))

/-- The constructed ten has dimension ten. -/
theorem ten_finrank : Module.finrank ℂ Ten = 10 := by
  rw [tenCoordinates.finrank_eq]
  simp [Module.finrank_prod, Module.finrank_matrix]

/-- Exact restriction to arbitrary colour and weak block matrices. -/
theorem ten_block_action (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (X : Ten) :
    tenCoordinates ⁅Matrix.fromBlocks A 0 0 B, X⁆ =
      (Matrix.trace A • (tenCoordinates X).1 - Aᵀ *ᵥ (tenCoordinates X).1,
        A * (tenCoordinates X).2.1 + (tenCoordinates X).2.1 * Bᵀ,
        Matrix.trace B * (tenCoordinates X).2.2) := by
  simp only [tenCoordinates, LinearEquiv.trans_apply, alternating_block_action,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    alternating_three_action, alternating_two_action]

/-- The conventional block embedding, with integer hypercharge normalization. -/
def standardModelGenerator (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) : Matrix FiveIndex FiveIndex ℂ :=
  Matrix.fromBlocks (A + (-2 * q) • 1) 0 0 (B + (3 * q) • 1)

/-- Traceless colour and weak inputs give a traceless five-dimensional generator. -/
theorem standard_model_generator_trace (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) :
    Matrix.trace (standardModelGenerator A B q) = 0 := by
  have hblocks (C : Matrix (Fin 3) (Fin 3) ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ) :
      Matrix.trace (Matrix.fromBlocks C 0 0 D) = Matrix.trace C + Matrix.trace D := by
    simp [Matrix.trace, Fintype.sum_sum_type]
  rw [standardModelGenerator, hblocks]
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, hA, hB,
    Fintype.card_fin, Nat.cast_ofNat, zero_add, smul_eq_mul]
  ring

/-- Actual Standard Model action on the three summands of the ten.
The integer charges are `-4`, `1`, and `6`. -/
theorem ten_standard_model_action (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) (X : Ten) :
    tenCoordinates ⁅standardModelGenerator A B q, X⁆ =
      (-Aᵀ *ᵥ (tenCoordinates X).1 + (-4 * q) • (tenCoordinates X).1,
        A * (tenCoordinates X).2.1 + (tenCoordinates X).2.1 * Bᵀ +
          q • (tenCoordinates X).2.1,
        (6 * q) * (tenCoordinates X).2.2) := by
  rw [standardModelGenerator, ten_block_action]
  apply Prod.ext
  · ext i
    simp [hA, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.neg_mulVec,
      Matrix.transpose_add, Matrix.transpose_smul]
    ring
  · apply Prod.ext
    · ext i j
      simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    · simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, hB,
        Fintype.card_fin, Nat.cast_ofNat, zero_add, smul_eq_mul]
      ring

/-- The primitive hypercharge generator alone acts with its literal charges. -/
theorem ten_hypercharge_action (X : Ten) :
    tenCoordinates ⁅standardModelGenerator 0 0 1, X⁆ =
      ((-4 : ℂ) • (tenCoordinates X).1,
        (tenCoordinates X).2.1, (6 : ℂ) * (tenCoordinates X).2.2) := by
  simpa using ten_standard_model_action 0 0 1 (by simp) (by simp) X

end

end CubicAnomaly.Fixed.MatterBranching
