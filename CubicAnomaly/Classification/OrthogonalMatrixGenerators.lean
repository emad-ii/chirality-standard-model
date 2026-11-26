import CubicAnomaly.Classification.SpecialLinearCartan
import Mathlib.Algebra.Lie.Classical

/-! The standard even orthogonal simple-root generators in block coordinates. -/
namespace CubicAnomaly.Classification.OrthogonalMatrixGenerators

open LieAlgebra LieAlgebra.Orthogonal Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Split orthogonal matrix with arbitrary upper-left block and skew-symmetric off-diagonal blocks. -/
def blocks (A B C : Matrix ι ι ℂ) (hB : Bᵀ = -B) (hC : Cᵀ = -C) : typeD ι ℂ :=
  ⟨fromBlocks A B C (-Aᵀ), by
    simp only [typeD, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
    change (fromBlocks A B C (-Aᵀ))ᵀ * JD ι ℂ = JD ι ℂ * -(fromBlocks A B C (-Aᵀ))
    simp [JD, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg, hB, hC]⟩

/-- The standard general-linear subalgebra acting on a space and its dual. -/
def generalLinear : Matrix ι ι ℂ →ₗ⁅ℂ⁆ typeD ι ℂ where
  toFun A := blocks A 0 0 (by simp) (by simp)
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


/-- The two-coordinate skew matrix at the fork of the D diagram. -/
def skew (a b : ι) : Matrix ι ι ℂ := single a b 1 - single b a 1

omit [Fintype ι] in
@[simp] theorem skew_transpose (a b : ι) : (skew a b)ᵀ = -skew a b := by simp [skew, neg_sub]

def upper (a b : ι) : typeD ι ℂ := blocks 0 (skew a b) 0 (by simp) (by simp)

def lower (a b : ι) : typeD ι ℂ := blocks 0 0 (-skew a b) (by simp) (by simp)

theorem typeD_upper_lower {a b : ι} (hab : a ≠ b) :
    ⁅upper a b, lower a b⁆ = generalLinear (single a a 1 + single b b 1) := by
  apply Subtype.ext
  change ⁅(upper a b).val, (lower a b).val⁆ = fromBlocks _ 0 0 (-(_ : Matrix ι ι ℂ)ᵀ)
  simp [upper, lower, blocks, skew, Ring.lie_def, fromBlocks_multiply, add_mul, mul_add,
    single_mul_single_of_ne, hab, hab.symm, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, add_comm]

variable {n : ℕ}

abbrev penultimate (n : ℕ) := (Fin.last n).castSucc
abbrev terminal (n : ℕ) := Fin.last (n+1)

def raising (i : Fin (n+2)) : typeD (Fin (n+2)) ℂ :=
  Fin.lastCases (upper (penultimate n) (terminal n)) (fun j => generalLinear (SpecialLinearGenerators.raising j).val) i

def lowering (i : Fin (n+2)) : typeD (Fin (n+2)) ℂ :=
  Fin.lastCases (lower (penultimate n) (terminal n)) (fun j => generalLinear (SpecialLinearGenerators.lowering j).val) i

def diagonal (i : Fin (n+2)) : typeD (Fin (n+2)) ℂ :=
  Fin.lastCases (generalLinear (single (penultimate n) (penultimate n) 1 + single (terminal n) (terminal n) 1))
    (fun j => generalLinear (SpecialLinearGenerators.diagonal j).val) i

theorem typeD_raising_adjoint (i : Fin (n+2)) : (raising i).valᴴ = (lowering i).val := by
  induction i using Fin.lastCases with
  | last => simp [raising, lowering, upper, lower, blocks, skew, fromBlocks_conjTranspose, neg_sub]
  | cast j => simp [raising, lowering, generalLinear, blocks, fromBlocks_conjTranspose,
      SpecialLinearGenerators.raising, SpecialLinearGenerators.lowering, conjTranspose_single]

theorem typeD_mixed_same (i : Fin (n+2)) : ⁅raising i, lowering i⁆ = diagonal i := by
  induction i using Fin.lastCases with
  | last => simp [raising, lowering, diagonal, typeD_upper_lower (Fin.castSucc_ne_last (Fin.last n))]
  | cast j =>
    simp only [raising, lowering, diagonal, Fin.lastCases_castSucc]
    rw [← LieHom.map_lie]
    exact congrArg (fun A : LieAlgebra.SpecialLinear.sl (Fin (n+2)) ℂ => generalLinear A.val)
      (SpecialLinearCartan.mixed_same j)

private theorem mixed_last (i : Fin (n+1)) : ⁅raising i.castSucc, lowering (Fin.last (n+1))⁆ = 0 := by
  simp only [raising, lowering, Fin.lastCases_castSucc, Fin.lastCases_last]
  apply Subtype.ext
  change ⁅(generalLinear (SpecialLinearGenerators.raising i).val).val, (lower (penultimate n) (terminal n)).val⁆ = 0
  have hl := Fin.castSucc_ne_last i
  by_cases h : i = Fin.last n
  · subst i
    simp [generalLinear, SpecialLinearGenerators.raising, lower, blocks, skew, Ring.lie_def,
      fromBlocks_multiply, mul_sub, sub_mul, penultimate, terminal, Fin.succ_last, hl, hl.symm,
      single_mul_single_of_ne]
  · have hp : i.castSucc ≠ penultimate n := fun he => h (Fin.castSucc_inj.mp he)
    simp [generalLinear, SpecialLinearGenerators.raising, lower, blocks, skew, Ring.lie_def,
      fromBlocks_multiply, mul_sub, sub_mul, hl, hl.symm, hp, hp.symm, single_mul_single_of_ne]

theorem typeD_mixed_distinct (i j : Fin (n+2)) (hij : i ≠ j) : ⁅raising i, lowering j⁆ = 0 := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j =>
      have he := congrArg (fun x : typeD (Fin (n+2)) ℂ => x.valᴴ) (mixed_last j)
      change (⁅(raising j.castSucc).val, (lowering _).val⁆)ᴴ = 0ᴴ at he
      apply Subtype.ext
      change ⁅(raising _).val, (lowering j.castSucc).val⁆ = 0
      have ht (k : Fin (n+2)) : (lowering k).valᴴ = (raising k).val := by
        rw [← typeD_raising_adjoint, conjTranspose_conjTranspose]
      simpa only [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, ht, typeD_raising_adjoint, conjTranspose_zero] using he
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact mixed_last i
    | cast j =>
      have h : i ≠ j := fun he => hij (congrArg Fin.castSucc he)
      simp only [raising, lowering, Fin.lastCases_castSucc]
      rw [← LieHom.map_lie]
      have he := congrArg Subtype.val (SpecialLinearCartan.mixed_distinct i j h)
      change ⁅(SpecialLinearGenerators.raising i).val, (SpecialLinearGenerators.lowering j).val⁆ = 0 at he
      rw [he, map_zero]

/-- The simple root coordinates at the fork are the sum of the last two coordinates. -/
def weight (i : Fin (n+2)) (d : Fin (n+2) → ℂ) : ℂ :=
  Fin.lastCases (d (penultimate n) + d (terminal n)) (fun j => d j.castSucc - d j.succ) i

def corootVector (i : Fin (n+2)) : Fin (n+2) → ℂ :=
  Fin.lastCases (Pi.single (penultimate n) 1 + Pi.single (terminal n) 1)
    (fun j => Pi.single j.castSucc 1 - Pi.single j.succ 1) i

theorem typeD_diagonal_eq (i : Fin (n+2)) :
    diagonal i = generalLinear (Matrix.diagonal (corootVector i)) := by
  induction i using Fin.lastCases with
  | last =>
    simp only [diagonal, corootVector, Fin.lastCases_last]
    apply congrArg generalLinear
    rw [← diagonal_single, ← diagonal_single, Matrix.diagonal_add]
    rfl
  | cast j =>
    simp only [diagonal, corootVector, Fin.lastCases_castSucc]
    apply congrArg generalLinear
    change single j.castSucc j.castSucc (1 : ℂ) - single j.succ j.succ 1 = _
    rw [← diagonal_single, ← diagonal_single, diagonal_sub]
    rfl


private theorem generalLinear_diag_coe (d : ι → ℂ) :
    (generalLinear (Matrix.diagonal d)).val = Matrix.diagonal (Sum.elim d (-d)) := by
  simp [generalLinear, blocks, Matrix.diagonal_neg]

private theorem upper_coe (a b : ι) : (upper a b).val =
    single (Sum.inl a) (Sum.inr b) 1 - single (Sum.inl b) (Sum.inr a) 1 := by
  ext x y
  cases x <;> cases y <;> simp [upper, blocks, single_apply, fromBlocks, skew]

private theorem lower_coe (a b : ι) : (lower a b).val =
    single (Sum.inr b) (Sum.inl a) 1 - single (Sum.inr a) (Sum.inl b) 1 := by
  ext x y
  cases x <;> cases y <;> simp [lower, blocks, single_apply, fromBlocks, skew, neg_sub]

theorem typeD_diagonal_raising (d : Fin (n+2) → ℂ) (i : Fin (n+2)) :
    ⁅generalLinear (Matrix.diagonal d), raising i⁆ = weight i d • raising i := by
  induction i using Fin.lastCases with
  | cast i =>
    simp only [raising, weight, Fin.lastCases_castSucc]
    rw [← LieHom.map_lie, ← map_smul]
    exact congrArg generalLinear (SpecialLinearCartan.bracket_diagonal_single d i.castSucc i.succ)
  | last =>
    apply Subtype.ext
    simp only [raising, weight, Fin.lastCases_last]
    change ⁅(generalLinear (Matrix.diagonal d)).val, (upper _ _).val⁆ = _ • (upper _ _).val
    simp [generalLinear_diag_coe, upper_coe, lie_sub, SpecialLinearCartan.bracket_diagonal_single, smul_sub, add_comm]

theorem typeD_diagonal_lowering (d : Fin (n+2) → ℂ) (i : Fin (n+2)) :
    ⁅generalLinear (Matrix.diagonal d), lowering i⁆ = -weight i d • lowering i := by
  induction i using Fin.lastCases with
  | cast i =>
    simp only [lowering, weight, Fin.lastCases_castSucc]
    rw [← LieHom.map_lie, ← map_smul, neg_sub]
    exact congrArg generalLinear (SpecialLinearCartan.bracket_diagonal_single d i.succ i.castSucc)
  | last =>
    apply Subtype.ext
    simp only [lowering, weight, Fin.lastCases_last]
    change ⁅(generalLinear (Matrix.diagonal d)).val, (lower _ _).val⁆ = _ • (lower _ _).val
    simp [generalLinear_diag_coe, lower_coe, SpecialLinearCartan.bracket_diagonal_single,
      add_comm, sub_eq_add_neg]
set_option maxHeartbeats 4000000 in
theorem typeD_weight_coroot (i j : Fin (n+2)) : weight i (corootVector j) = (CartanMatrix.D (n+2) i j : ℂ) := by
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [weight, corootVector, Fin.lastCases_last, Fin.lastCases_castSucc, Pi.add_apply, Pi.sub_apply,
      Pi.single_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
      penultimate, terminal, Fin.val_last, Fin.val_castSucc] <;> split_ifs <;> norm_num <;> simp only [or_true, and_true] at * <;> omega

end CubicAnomaly.Classification.OrthogonalMatrixGenerators
