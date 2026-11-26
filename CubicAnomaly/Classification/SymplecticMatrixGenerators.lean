import CubicAnomaly.Classification.SpecialLinearCartan
import Mathlib.Algebra.Lie.Classical

/-! The standard symplectic simple-root generators in block coordinates. -/
namespace CubicAnomaly.Classification.SymplecticMatrixGenerators

open LieAlgebra Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Hamiltonian matrix with arbitrary upper-left block and symmetric off-diagonal blocks. -/
def blocks (A B C : Matrix ι ι ℂ) (hB : Bᵀ = B) (hC : Cᵀ = C) : Symplectic.sp ι ℂ :=
  ⟨fromBlocks A B C (-Aᵀ), by
    simp only [Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
    change (fromBlocks A B C (-Aᵀ))ᵀ * J ι ℂ = J ι ℂ * -(fromBlocks A B C (-Aᵀ))
    simp [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg, hB, hC]⟩

/-- The standard general-linear subalgebra acting on a space and its dual. -/
def generalLinear : Matrix ι ι ℂ →ₗ⁅ℂ⁆ Symplectic.sp ι ℂ where
  toFun A := blocks A 0 0 (transpose_zero) (transpose_zero)
  map_add' A B := by
    apply Subtype.ext
    simp [blocks, fromBlocks_add, add_comm]
  map_smul' c A := by
    apply Subtype.ext
    simp [blocks, fromBlocks_smul, smul_neg]
  map_lie' {A B} := by
    apply Subtype.ext
    change (blocks ⁅A,B⁆ 0 0 _ _).val =
      ⁅(blocks A 0 0 _ _).val, (blocks B 0 0 _ _).val⁆
    simp [blocks, Ring.lie_def, fromBlocks_multiply, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, add_comm]

def upper (k : ι) : Symplectic.sp ι ℂ :=
  blocks 0 (Matrix.single k k 1) 0 (by simp) (by simp)

def lower (k : ι) : Symplectic.sp ι ℂ :=
  blocks 0 0 (Matrix.single k k 1) (by simp) (by simp)

theorem upper_lower (k : ι) : ⁅upper k, lower k⁆ = generalLinear (Matrix.single k k 1) := by
  apply Subtype.ext
  change ⁅(upper k).val, (lower k).val⁆ = _
  change ⁅(upper k).val, (lower k).val⁆ = fromBlocks (single k k 1) 0 0 (-(single k k 1)ᵀ)
  simp [upper, lower, blocks, Ring.lie_def, fromBlocks_multiply, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]

variable {n : ℕ}

def raising (i : Fin (n+1)) : Symplectic.sp (Fin (n+1)) ℂ :=
  Fin.lastCases (upper (Fin.last n)) (fun j => generalLinear (SpecialLinearGenerators.raising j).val) i

def lowering (i : Fin (n+1)) : Symplectic.sp (Fin (n+1)) ℂ :=
  Fin.lastCases (lower (Fin.last n)) (fun j => generalLinear (SpecialLinearGenerators.lowering j).val) i

def diagonal (i : Fin (n+1)) : Symplectic.sp (Fin (n+1)) ℂ :=
  Fin.lastCases (generalLinear (Matrix.single (Fin.last n) (Fin.last n) 1))
    (fun j => generalLinear (SpecialLinearGenerators.diagonal j).val) i

theorem raising_adjoint (i : Fin (n+1)) : (raising i).valᴴ = (lowering i).val := by
  induction i using Fin.lastCases with
  | last => simp [raising, lowering, upper, lower, blocks, fromBlocks_conjTranspose]
  | cast j => simp [raising, lowering, generalLinear, blocks, fromBlocks_conjTranspose,
      SpecialLinearGenerators.raising, SpecialLinearGenerators.lowering, conjTranspose_single]

theorem symplectic_mixed_same (i : Fin (n+1)) : ⁅raising i, lowering i⁆ = diagonal i := by
  induction i using Fin.lastCases with
  | last => simp [raising, lowering, diagonal, upper_lower]
  | cast j =>
    simp only [raising, lowering, diagonal, Fin.lastCases_castSucc]
    rw [← LieHom.map_lie]
    exact congrArg (fun A : LieAlgebra.SpecialLinear.sl (Fin (n+1)) ℂ => generalLinear A.val)
      (SpecialLinearCartan.mixed_same j)

theorem symplectic_mixed_distinct (i j : Fin (n+1)) (hij : i ≠ j) : ⁅raising i, lowering j⁆ = 0 := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j =>
      apply Subtype.ext
      simp only [raising, lowering, Fin.lastCases_last, Fin.lastCases_castSucc]
      change ⁅(upper (Fin.last n)).val, (generalLinear (SpecialLinearGenerators.lowering j).val).val⁆ = 0
      have h : j.castSucc ≠ Fin.last n := Fin.castSucc_ne_last j
      simp [upper, generalLinear, SpecialLinearGenerators.lowering, blocks, Ring.lie_def,
        fromBlocks_multiply, h, h.symm, single_mul_single_of_ne]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      apply Subtype.ext
      simp only [raising, lowering, Fin.lastCases_last, Fin.lastCases_castSucc]
      change ⁅(generalLinear (SpecialLinearGenerators.raising i).val).val, (lower (Fin.last n)).val⁆ = 0
      have h : i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last i
      simp [lower, generalLinear, SpecialLinearGenerators.raising, blocks, Ring.lie_def,
        fromBlocks_multiply, h, h.symm, single_mul_single_of_ne]
    | cast j =>
      have h : i ≠ j := fun he => hij (congrArg Fin.castSucc he)
      simp only [raising, lowering, Fin.lastCases_castSucc]
      rw [← LieHom.map_lie]
      have he := congrArg Subtype.val (SpecialLinearCartan.mixed_distinct i j h)
      change ⁅(SpecialLinearGenerators.raising i).val, (SpecialLinearGenerators.lowering j).val⁆ = 0 at he
      rw [he, map_zero]

/-- The values of the simple roots on a diagonal Cartan vector. -/
def weight (i : Fin (n+1)) (d : Fin (n+1) → ℂ) : ℂ :=
  Fin.lastCases (2 * d (Fin.last n)) (fun j => d j.castSucc - d j.succ) i

/-- The diagonal coefficients of a simple symplectic coroot. -/
def corootVector (i : Fin (n+1)) : Fin (n+1) → ℂ :=
  Fin.lastCases (Pi.single (Fin.last n) 1) (fun j => Pi.single j.castSucc 1 - Pi.single j.succ 1) i

theorem diagonal_eq (i : Fin (n+1)) :
    diagonal i = generalLinear (Matrix.diagonal (corootVector i)) := by
  induction i using Fin.lastCases with
  | last => simp [diagonal, corootVector, diagonal_single]
  | cast j =>
    simp only [diagonal, corootVector, Fin.lastCases_castSucc]
    apply congrArg generalLinear
    change single j.castSucc j.castSucc (1 : ℂ) - single j.succ j.succ 1 = _
    rw [← diagonal_single, ← diagonal_single, diagonal_sub]
    rfl

theorem weight_coroot (i j : Fin (n+1)) :
    weight i (corootVector j) = (CartanMatrix.C (n+1) i j : ℂ) := by
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases with
    | last => simp [weight, corootVector, CartanMatrix.C]
    | cast j =>
      simp only [weight, corootVector, Fin.lastCases_last, Fin.lastCases_castSucc, Pi.sub_apply,
        Pi.single_apply, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
        Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel]
      split_ifs <;> norm_num <;> omega
  | cast i => induction j using Fin.lastCases with
    | last =>
      simp only [weight, corootVector, Fin.lastCases_last, Fin.lastCases_castSucc, Pi.single_apply,
        CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_last, Fin.val_succ,
        Fin.val_castSucc, Nat.add_sub_cancel]
      split_ifs <;> norm_num <;> omega
    | cast j =>
      simp only [weight, corootVector, Fin.lastCases_castSucc, Pi.sub_apply, Pi.single_apply,
        CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_last, Fin.val_succ,
        Fin.val_castSucc, Nat.add_sub_cancel]
      split_ifs <;> norm_num <;> omega


private theorem generalLinear_diag_coe (d : ι → ℂ) :
    (generalLinear (Matrix.diagonal d)).val = Matrix.diagonal (Sum.elim d (-d)) := by
  simp [generalLinear, blocks, Matrix.diagonal_neg]

private theorem upper_coe (i : ι) : (upper i).val = single (Sum.inl i) (Sum.inr i) 1 := by
  ext x y
  cases x <;> cases y <;> simp [upper, blocks, single_apply, fromBlocks]

private theorem lower_coe (i : ι) : (lower i).val = single (Sum.inr i) (Sum.inl i) 1 := by
  ext x y
  cases x <;> cases y <;> simp [lower, blocks, single_apply, fromBlocks]

theorem symplectic_diagonal_raising (d : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    ⁅generalLinear (Matrix.diagonal d), raising i⁆ = weight i d • raising i := by
  induction i using Fin.lastCases with
  | cast i =>
    simp only [raising, weight, Fin.lastCases_castSucc]
    rw [← LieHom.map_lie, ← map_smul]
    exact congrArg generalLinear (SpecialLinearCartan.bracket_diagonal_single d i.castSucc i.succ)
  | last =>
    apply Subtype.ext
    simp only [raising, weight, Fin.lastCases_last]
    change ⁅(generalLinear (Matrix.diagonal d)).val, (upper (Fin.last n)).val⁆ =
      (2 * d (Fin.last n)) • (upper (Fin.last n)).val
    rw [generalLinear_diag_coe, upper_coe, SpecialLinearCartan.bracket_diagonal_single]
    simp [two_mul]

theorem symplectic_diagonal_lowering (d : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    ⁅generalLinear (Matrix.diagonal d), lowering i⁆ = -weight i d • lowering i := by
  induction i using Fin.lastCases with
  | cast i =>
    simp only [lowering, weight, Fin.lastCases_castSucc]
    rw [← LieHom.map_lie, ← map_smul, neg_sub]
    exact congrArg generalLinear (SpecialLinearCartan.bracket_diagonal_single d i.succ i.castSucc)
  | last =>
    apply Subtype.ext
    simp only [lowering, weight, Fin.lastCases_last]
    change ⁅(generalLinear (Matrix.diagonal d)).val, (lower (Fin.last n)).val⁆ =
      -(2 * d (Fin.last n)) • (lower (Fin.last n)).val
    rw [generalLinear_diag_coe, lower_coe, SpecialLinearCartan.bracket_diagonal_single]
    simp [two_mul, sub_eq_add_neg]

end CubicAnomaly.Classification.SymplecticMatrixGenerators
