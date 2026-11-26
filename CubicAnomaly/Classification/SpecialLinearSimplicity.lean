import CubicAnomaly.Classification.SpecialLinearGenerators
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! A nonzero ideal of the traceless matrices contains an off-diagonal matrix
unit. Bracketing twice with a matrix unit extracts the opposite coefficient,
and brackets of consecutive matrix units propagate to every pair of indices. -/

namespace CubicAnomaly.Classification.SpecialLinearSimplicity

open LieAlgebra LieAlgebra.SpecialLinear

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev unit (i j : ι) (h : i ≠ j) : sl ι ℂ := single i j h 1

private theorem extract_unit (I : LieIdeal ℂ (sl ι ℂ)) (x : sl ι ℂ) (hx : x ∈ I)
    (i j : ι) (h : i ≠ j) (hne : x.val j i ≠ 0) : unit i j h ∈ I := by
  let E := unit i j h
  have hdouble : ⁅E, ⁅E, x⁆⁆ = (-2 * x.val j i) • E := by
    apply Subtype.ext
    change E.val * (E.val * x.val - x.val * E.val) - (E.val * x.val - x.val * E.val) * E.val = _
    have hee : E.val * E.val = 0 := Matrix.single_mul_single_of_ne _ _ _ _ h.symm _
    rw [mul_sub, sub_mul, ← mul_assoc, hee, zero_mul, mul_assoc x.val, hee, mul_zero,
      ← mul_assoc]
    change 0 - (Matrix.single i j (1 : ℂ) * x.val * Matrix.single i j 1) -
      (Matrix.single i j 1 * x.val * Matrix.single i j 1 - 0) =
        (-2 * x.val j i) • Matrix.single i j 1
    simp only [Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single, smul_eq_mul]
    ext a b
    by_cases ha : i = a <;> by_cases hb : j = b <;> simp [Matrix.single, ha, hb]
    ring
  have hmem := I.lie_mem (x := E) (I.lie_mem (x := E) hx)
  rw [hdouble] at hmem
  exact (I.toSubmodule.smul_mem_iff (mul_ne_zero (by norm_num) hne)).mp hmem

private theorem chain (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅unit i j hij, unit j k hjk⁆ = unit i k hik := by
  apply Subtype.ext
  rw [sl_bracket]
  simp [unit, Matrix.single_mul_single_of_ne _ _ _ _ hik.symm]

private theorem all_units (I : LieIdeal ℂ (sl ι ℂ)) (i j : ι) (hij : i ≠ j)
    (h : unit i j hij ∈ I) : ∀ a b (hab : a ≠ b), unit a b hab ∈ I := by
  have out' (b : ι) (hb : i ≠ b) : unit i b hb ∈ I := by
    by_cases heq : j = b
    · subst b; exact h
    · rw [← chain i j b hij heq hb]
      exact lie_mem_left ℂ _ I _ _ h
  have in' (a : ι) (ha : a ≠ i) : unit a i ha ∈ I :=
    extract_unit I _ (out' a ha.symm) a i ha (by simp [unit])
  intro a b hab
  by_cases ha : a = i
  · subst a; exact out' b hab
  by_cases hb : b = i
  · subst b; exact in' a hab
  rw [← chain a i b ha (Ne.symm hb) hab]
  exact lie_mem_left ℂ _ I _ _ (in' a ha)

variable [Nonempty ι]

private theorem exists_unit (I : LieIdeal ℂ (sl ι ℂ)) (hne : I ≠ ⊥) :
    ∃ (i j : ι) (h : i ≠ j), unit i j h ∈ I := by
  by_contra! hn
  have off (x : sl ι ℂ) (hx : x ∈ I) (a b : ι) (hab : a ≠ b) : x.val a b = 0 :=
    Classical.byContradiction fun hnz => hn b a hab.symm (extract_unit I x hx b a hab.symm hnz)
  apply hne
  apply le_bot_iff.mp
  intro x hx
  change x = 0
  obtain ⟨i⟩ := ‹Nonempty ι›
  have diag (j : ι) : x.val j j = x.val i i := by
    by_cases he : i = j
    · subst j; rfl
    · have h := off ⁅unit i j he, x⁆ (I.lie_mem hx) i j he
      rw [sl_bracket] at h
      simpa [unit, sub_eq_zero] using h
  have ht : ∑ j, x.val j j = 0 := x.property
  simp only [diag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
  have hi := (mul_eq_zero.mp ht).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  apply Subtype.ext
  ext a b
  by_cases hab : a = b
  · subst b; exact (diag a).trans hi
  · exact off x hx a b hab

/-- The complex traceless matrices of order at least two form a simple Lie algebra. -/
theorem isSimple (hcard : 1 < Fintype.card ι) :
    IsSimple ℂ (sl ι ℂ) where
  non_abelian := sl_non_abelian ι ℂ hcard
  eq_bot_or_eq_top I := by
    by_cases hb : I = ⊥
    · exact Or.inl hb
    obtain ⟨i, j, hij, h⟩ := exists_unit I hb
    have ht := SpecialLinearGenerators.eq_top_of_offdiag (I.toLieSubalgebra ℂ _) (all_units I i j hij h)
    exact Or.inr (top_unique fun x _ => show x ∈ I.toLieSubalgebra ℂ _ from ht ▸ LieSubalgebra.mem_top x)

end CubicAnomaly.Classification.SpecialLinearSimplicity
