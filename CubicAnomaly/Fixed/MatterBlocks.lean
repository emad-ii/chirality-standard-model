import CubicAnomaly.Fixed.MatterAlternating

/-!
# Literal block restriction of the alternating matter module

An alternating tensor on a sum of a colour and a weak vector space splits
into colour-colour, colour-weak and weak-weak blocks. We construct this
linear equivalence and prove its intertwining formula for every block
diagonal matrix, including the hypercharge generator.
-/

namespace CubicAnomaly.Fixed.MatterBlocks

open Matrix
open CubicAnomaly.Fixed.MatterAlternating

noncomputable section

variable (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

private def colourPart (X : AlternatingTensor (m ⊕ n)) : AlternatingTensor m :=
  ⟨X.val.toBlocks₁₁, by
    change X.val.toBlocks₁₁ᵀ = -X.val.toBlocks₁₁
    exact congrArg Matrix.toBlocks₁₁ X.property⟩

private def weakPart (X : AlternatingTensor (m ⊕ n)) : AlternatingTensor n :=
  ⟨X.val.toBlocks₂₂, by
    change X.val.toBlocks₂₂ᵀ = -X.val.toBlocks₂₂
    exact congrArg Matrix.toBlocks₂₂ X.property⟩

private def fromParts
    (p : AlternatingTensor m × (Matrix m n ℂ × AlternatingTensor n)) :
    AlternatingTensor (m ⊕ n) :=
  ⟨Matrix.fromBlocks p.1.val p.2.1 (-p.2.1ᵀ) p.2.2.val, by
    change (Matrix.fromBlocks p.1.val p.2.1 (-p.2.1ᵀ) p.2.2.val)ᵀ = _
    rw [Matrix.fromBlocks_transpose, transpose_neg, transpose_transpose,
      p.1.property, p.2.2.property]
    ext (i | i) (j | j) <;> simp⟩

/-- The actual colour-colour, colour-weak and weak-weak decomposition. -/
def alternatingBlockEquiv :
    AlternatingTensor (m ⊕ n) ≃ₗ[ℂ]
      AlternatingTensor m × (Matrix m n ℂ × AlternatingTensor n) where
  toFun X := (colourPart m n X, X.val.toBlocks₁₂, weakPart m n X)
  invFun := fromParts m n
  left_inv X := by
    apply Subtype.ext
    ext (i | i) (j | j)
    · rfl
    · rfl
    · have hx := congrArg (fun A : Matrix (m ⊕ n) (m ⊕ n) ℂ =>
        A (Sum.inl j) (Sum.inr i)) X.property
      change X.val (Sum.inr i) (Sum.inl j) = -X.val (Sum.inl j) (Sum.inr i) at hx
      exact hx.symm
    · rfl
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    rfl
  map_add' X Y := rfl
  map_smul' c X := rfl

/-- Under the actual block equivalence the restricted tensor action is
the colour alternating action, the tensor-product action, and the weak
alternating action. -/
theorem alternating_block_action (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : AlternatingTensor (m ⊕ n)) :
    alternatingBlockEquiv m n ⁅Matrix.fromBlocks A 0 0 B, X⁆ =
      (⁅A, (alternatingBlockEquiv m n X).1⁆,
        A * (alternatingBlockEquiv m n X).2.1 +
          (alternatingBlockEquiv m n X).2.1 * Bᵀ,
        ⁅B, (alternatingBlockEquiv m n X).2.2⁆) := by
  obtain ⟨p, rfl⟩ := (alternatingBlockEquiv m n).symm.surjective X
  rcases p with ⟨a, b, c⟩
  apply Prod.ext
  · apply Subtype.ext
    simp [alternatingBlockEquiv, colourPart, fromParts, alternating_action_val,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, Matrix.toBlocks₁₁]
    rfl
  · apply Prod.ext
    · simp [alternatingBlockEquiv, fromParts, alternating_action_val,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, Matrix.toBlocks₁₂]
      rfl
    · apply Subtype.ext
      simp [alternatingBlockEquiv, weakPart, fromParts, alternating_action_val,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, Matrix.toBlocks₂₂]
      rfl

end

end CubicAnomaly.Fixed.MatterBlocks
