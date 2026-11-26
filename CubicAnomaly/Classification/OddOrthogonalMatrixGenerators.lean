import CubicAnomaly.Classification.OrthogonalMatrixGenerators

/-! The split odd orthogonal matrices in the standard Witt coordinates,
with the middle coordinate of square length two. -/
namespace CubicAnomaly.Classification.OddOrthogonalMatrixGenerators

open LieAlgebra LieAlgebra.Orthogonal Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Index (ι : Type*) := Unit ⊕ (ι ⊕ ι)
abbrev mid : Index ι := .inl ()
abbrev pos (i : ι) : Index ι := .inr (.inl i)
abbrev neg (i : ι) : Index ι := .inr (.inr i)

def flip : Index ι ≃ Index ι := Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)
def scale : Index ι → ℂ := Sum.elim (fun _ => 2) (fun _ => 1)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem flip_flip (i : Index ι) : flip (flip i) = i := by
  rcases i with _ | (i|i) <;> rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem scale_flip (i : Index ι) : scale (flip i) = scale i := by
  rcases i with _ | (i|i) <;> rfl

omit [Fintype ι] in
private theorem jb_apply (i j : Index ι) : JB ι ℂ i j = if flip i = j then scale i else 0 := by
  rcases i with _ | (i|i) <;> rcases j with _ | (j|j) <;>
    simp [JB, JD, Matrix.fromBlocks, Matrix.one_apply, flip, scale]

private theorem skew_condition (X : Matrix (Index ι) (Index ι) ℂ)
    (hX : ∀ i j, X (flip j) i * scale j = scale i * (-X (flip i) j)) : X ∈ typeB ι ℂ := by
  simp only [typeB, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  change Xᵀ * JB ι ℂ = JB ι ℂ * (-X)
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, jb_apply, Matrix.neg_apply, ite_mul, mul_ite,
    zero_mul, mul_zero]
  have he (a : Index ι) : flip a = j ↔ a = flip j := by
    constructor <;> intro h
    · rw [← h, flip_flip]
    · rw [h, flip_flip]
  simpa [he] using hX i j

/-- Paired matrix units skew for the split form. The two coefficients
account for the length of the middle coordinate. -/
def unit (i j : Index ι) : typeB ι ℂ :=
  ⟨single i j (scale j) - single (flip j) (flip i) (scale i), by
    apply skew_condition
    intro a b
    have ic (u v : Index ι) : flip u = flip v ↔ u = v := flip.injective.eq_iff
    have sw (u v : Index ι) : u = flip v ↔ flip u = v := by
      constructor <;> intro h
      · rw [h, flip_flip]
      · rw [← h, flip_flip]
    simp only [Matrix.sub_apply, Matrix.single_apply, sw i a, sw i b, ic]
    split_ifs <;> grind [scale_flip]⟩

variable {n : ℕ}

def raising (i : Fin (n+1)) : typeB (Fin (n+1)) ℂ :=
  Fin.lastCases (unit (pos (Fin.last n)) mid) (fun j => unit (pos j.castSucc) (pos j.succ)) i

def lowering (i : Fin (n+1)) : typeB (Fin (n+1)) ℂ :=
  Fin.lastCases (unit mid (pos (Fin.last n))) (fun j => unit (pos j.succ) (pos j.castSucc)) i

/-- The diagonal Cartan acts by the coordinates on the positive labels
and by their negatives on the negative labels. -/
def diagonalEntries (d : ι → ℂ) : Index ι → ℂ := Sum.elim (fun _ => 0) (Sum.elim d (-d))

def diagonal (d : ι → ℂ) : typeB ι ℂ := ⟨Matrix.diagonal (diagonalEntries d), by
  apply skew_condition
  intro i j
  by_cases h : flip j = i
  · subst i
    simp only [diagonal_apply_eq, flip_flip, scale_flip]
    rcases j with _ | (j|j) <;> simp [diagonalEntries, flip, scale, mul_comm]
  · have h' : flip i ≠ j := by
      intro hh
      rw [← hh, flip_flip] at h
      contradiction
    simp [diagonal_apply_ne _ h, diagonal_apply_ne _ h']⟩

/-- The last simple root is the last coordinate itself in type B. -/
def weight (i : Fin (n+1)) (d : Fin (n+1) → ℂ) : ℂ :=
  Fin.lastCases (d (Fin.last n)) (fun j => d j.castSucc - d j.succ) i

def corootVector (i : Fin (n+1)) : Fin (n+1) → ℂ :=
  Fin.lastCases (Pi.single (Fin.last n) 2) (fun j => Pi.single j.castSucc 1 - Pi.single j.succ 1) i

theorem typeB_weight_coroot (i j : Fin (n+1)) :
    weight i (corootVector j) = (CartanMatrix.B (n+1) i j : ℂ) := by
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [weight, corootVector, Fin.lastCases_last, Fin.lastCases_castSucc, Pi.sub_apply,
      Pi.single_apply, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
      Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel] <;> split_ifs <;> norm_num <;> omega

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem diagonalEntries_flip (d : ι → ℂ) (i : Index ι) :
    diagonalEntries d (flip i) = -diagonalEntries d i := by
  rcases i with _ | (i|i) <;> simp [diagonalEntries, flip]

private theorem bracket_single (d : Index ι → ℂ) (i j : Index ι) (c : ℂ) :
    ⁅Matrix.diagonal d, single i j c⁆ = (d i - d j) • single i j c := by
  rw [show single i j c = c • single i j 1 by simp [Matrix.smul_single], lie_smul,
    SpecialLinearCartan.bracket_diagonal_single, smul_comm]

theorem diagonal_unit (d : ι → ℂ) (i j : Index ι) :
    ⁅diagonal d, unit i j⁆ = (diagonalEntries d i - diagonalEntries d j) • unit i j := by
  apply Subtype.ext
  change ⁅Matrix.diagonal _, single i j _ - single (flip j) (flip i) _⁆ = _ • (_ - _)
  rw [lie_sub, bracket_single, bracket_single, diagonalEntries_flip, diagonalEntries_flip, neg_sub_neg, smul_sub]

theorem typeB_diagonal_raising (d : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    ⁅diagonal d, raising i⁆ = weight i d • raising i := by
  induction i using Fin.lastCases with
  | last => simp [raising, diagonal_unit, diagonalEntries, weight]
  | cast j => simp [raising, diagonal_unit, diagonalEntries, weight]

theorem typeB_diagonal_lowering (d : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    ⁅diagonal d, lowering i⁆ = -weight i d • lowering i := by
  induction i using Fin.lastCases with
  | last => simp [lowering, diagonal_unit, diagonalEntries, weight]
  | cast j => simp [lowering, diagonal_unit, diagonalEntries, weight, neg_sub]

private theorem diagonal_single (i : ι) (c : ℂ) :
    (diagonal (Pi.single i c)).val = single (pos i) (pos i) c - single (neg i) (neg i) c := by
  ext a b
  rcases a with _ | (a|a) <;> rcases b with _ | (b|b) <;>
    simp [diagonal, diagonalEntries, Matrix.diagonal_apply, Matrix.single_apply, Pi.single_apply] <;> grind

theorem diagonal_sub (d e : ι → ℂ) : (diagonal (d-e)).val = (diagonal d).val - (diagonal e).val := by
  change Matrix.diagonal _ = Matrix.diagonal _ - Matrix.diagonal _
  rw [Matrix.diagonal_sub]
  apply congrArg Matrix.diagonal
  ext k
  rcases k with _ | (k|k) <;> simp [diagonalEntries, neg_sub]
  ring

theorem typeB_mixed_same (i : Fin (n+1)) : ⁅raising i, lowering i⁆ = diagonal (corootVector i) := by
  induction i using Fin.lastCases with
  | last =>
    apply Subtype.ext
    simp only [raising, lowering, corootVector, Fin.lastCases_last]
    change ⁅(unit (pos (Fin.last n)) mid).val, (unit mid (pos (Fin.last n))).val⁆ = _
    rw [diagonal_single]
    simp [unit, flip, scale, mid, neg, pos, Ring.lie_def, mul_sub, sub_mul, single_mul_single_of_ne]
    abel
  | cast j =>
    apply Subtype.ext
    simp only [raising, lowering, corootVector, Fin.lastCases_castSucc]
    change ⁅(unit (pos j.castSucc) (pos j.succ)).val, (unit (pos j.succ) (pos j.castSucc)).val⁆ = _
    rw [diagonal_sub, diagonal_single, diagonal_single]
    simp [unit, flip, scale, Ring.lie_def, mul_sub, sub_mul, single_mul_single_of_ne]
    abel

theorem typeB_mixed_distinct (i j : Fin (n+1)) (hij : i ≠ j) : ⁅raising i, lowering j⁆ = 0 := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j =>
      apply Subtype.ext
      simp only [raising, lowering, Fin.lastCases_last, Fin.lastCases_castSucc]
      change ⁅(unit (pos (Fin.last n)) mid).val, (unit (pos j.succ) (pos j.castSucc)).val⁆ = 0
      have h := Fin.castSucc_ne_last j
      simp [unit, flip, scale, Ring.lie_def, mul_sub, sub_mul, h, h.symm, single_mul_single_of_ne]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      apply Subtype.ext
      simp only [raising, lowering, Fin.lastCases_last, Fin.lastCases_castSucc]
      change ⁅(unit (pos i.castSucc) (pos i.succ)).val, (unit mid (pos (Fin.last n))).val⁆ = 0
      have h := Fin.castSucc_ne_last i
      simp [unit, flip, scale, Ring.lie_def, mul_sub, sub_mul, h, h.symm, single_mul_single_of_ne]
    | cast j =>
      apply Subtype.ext
      have h : i ≠ j := fun he => hij (congrArg Fin.castSucc he)
      simp only [raising, lowering, Fin.lastCases_castSucc]
      change ⁅(unit (pos i.castSucc) (pos i.succ)).val, (unit (pos j.succ) (pos j.castSucc)).val⁆ = 0
      simp [unit, flip, scale, Ring.lie_def, mul_sub, sub_mul, h, h.symm, single_mul_single_of_ne]

end CubicAnomaly.Classification.OddOrthogonalMatrixGenerators
