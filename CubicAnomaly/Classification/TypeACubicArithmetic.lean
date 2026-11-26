import CubicAnomaly.Classification.Classical
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The two cyclic matrix-unit cubic eigenvalues combine into the shifted
type-A cubic in the diagonal highest-weight coordinates. -/

namespace CubicAnomaly.Classification.TypeACubicArithmetic

noncomputable section

open Finset

variable {N : ℕ}

private def t (i : Fin N) : ℂ := N - 1 - 2 * (i.val : ℂ)

private def before (u : Fin N → ℂ) (i : Fin N) : ℂ := ∑ j, if j < i then u j else 0

private def after (u : Fin N → ℂ) (i : Fin N) : ℂ := ∑ j, if i < j then u j else 0

/-- Eigenvalue of the cyclic matrix-unit cubic on a highest-weight vector. -/
def gelfandEigenvalue (u : Fin N → ℂ) : ℂ :=
  ∑ i, (u i + t i) * (u i ^ 2 + ∑ j, if i < j then u i - u j else 0)

private lemma before_sum (f : ℕ → ℂ) (i : Fin N) :
    before (fun j => f j.val) i = ∑ j ∈ range i.val, f j := by
  change (∑ j, if j < i then f (j : ℕ) else 0) = _
  rw [← sum_filter]
  rw [show univ.filter (fun j : Fin N => j < i) = Iio i by ext j; simp]
  change ∑ a ∈ Iio i, f (Fin.valEmbedding a) = _
  rw [← sum_map (Iio i) Fin.valEmbedding f, Fin.map_valEmbedding_Iio]
  rw [Nat.Iio_eq_range]

private lemma before_one (i : Fin N) : before (fun _ => 1) i = i.val := by
  simpa using before_sum (fun _ => 1) i

private lemma before_t (i : Fin N) : before t i = (i.val : ℂ) * (N - i.val) := by
  rw [show before t i = ∑ j ∈ range i.val, ((N : ℂ) - 1 - 2 * j) from before_sum (fun j => (N : ℂ) - 1 - 2 * j) i]
  generalize i.val = k
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

private lemma t_rev (i : Fin N) : t i.rev = -t i := by
  have hle : i.val + 1 ≤ N := i.isLt
  simp [t, Fin.val_rev, Nat.cast_sub hle]
  ring

private lemma after_before_rev (u : Fin N → ℂ) (i : Fin N) :
    after u i = before (fun j => u j.rev) i.rev := by
  have hs := Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N) (fun j => if i < j then u j else 0)
  simpa only [before, after, Fin.revPerm_apply, Fin.lt_rev_iff] using hs.symm

private lemma after_one (i : Fin N) : after (fun _ => 1) i = N - 1 - i.val := by
  rw [after_before_rev, before_one]
  have hle : i.val + 1 ≤ N := i.isLt
  simp [Fin.val_rev, Nat.cast_sub hle]
  ring

private lemma before_neg (u : Fin N → ℂ) (i : Fin N) :
    before (fun k => -u k) i = -before u i := by simp [before, ← sum_neg_distrib, apply_ite]

private lemma after_neg (u : Fin N → ℂ) (i : Fin N) :
    after (fun k => -u k) i = -after u i := by simp [after, ← sum_neg_distrib, apply_ite]

private lemma linear_coeff (i : Fin N) :
    t i ^ 2 + after t i - before t i = (3 * t i ^ 2 - ((N : ℂ)^2 - 1)) / 2 := by
  rw [after_before_rev, show (fun j : Fin N => t j.rev) = (fun j => -t j) from funext t_rev,
    before_neg, before_t, before_t]
  have hle : i.val + 1 ≤ N := i.isLt
  simp [t, Fin.val_rev, Nat.cast_sub hle]
  ring

private lemma interchange (u w : Fin N → ℂ) :
    ∑ i, u i * after w i = ∑ i, w i * before u i := by
  simp only [before, after, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  simp_rw [mul_comm]

private lemma row_diff (u : Fin N → ℂ) (i : Fin N) :
    (∑ j, if i < j then u i - u j else 0) = after (fun _ => 1) i * u i - after u i := by
  simp only [after, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h : i < j <;> simp [h]

/-- Collect the ordered pairs appearing in the action of the cyclic cubic
on a highest-weight vector. -/
theorem pair_sum_eq_gelfandEigenvalue (u : Fin N → ℂ) :
    let s := fun i => u i ^ 2 + ∑ j, if i < j then u i - u j else 0
    (∑ i, (u i * s i + ∑ j, if i < j then s i - s j else 0)) = gelfandEigenvalue u := by
  intro s
  have hs := interchange (fun _ : Fin N => (1 : ℂ)) s
  simp only [one_mul] at hs
  change _ = ∑ i, (u i + t i) * s i
  simp_rw [row_diff s]
  rw [sum_add_distrib, sum_sub_distrib, hs, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [after_one, before_one, t]
  ring

private lemma reversed_eigenvalue (u : Fin N → ℂ) :
    gelfandEigenvalue (fun i => -u i.rev) = ∑ i, (-u i - t i) *
      (u i ^ 2 - before (fun _ => 1) i * u i + before u i) := by
  unfold gelfandEigenvalue
  simp_rw [row_diff (fun i => -u i.rev)]
  rw [← Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N)]
  apply sum_congr rfl
  intro i _
  simp only [Fin.revPerm_apply, Fin.rev_rev, t_rev, after_before_rev, before_neg]
  ring

private lemma cross_sum (u : Fin N → ℂ) :
    (∑ i, (u i + t i) * (before u i - after u i)) =
      ∑ i, u i * (after t i - before t i) := by
  simp_rw [mul_sub, add_mul, sum_sub_distrib, sum_add_distrib]
  rw [interchange u u, ← interchange u t, interchange t u]
  ring

private lemma cubic_offset_sum : (∑ i : Fin N, t i ^ 3) = 0 := by
  have he := Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N) (fun i => t i ^ 3)
  have h3 (i : Fin N) : (t i.rev) ^ 3 = -(t i ^ 3) := by rw [t_rev]; ring
  simp only [Fin.revPerm_apply, h3, sum_neg_distrib] at he
  linear_combination -he / 2

/-- The odd part of the cyclic cubic eigenvalue is twice the sum of the
cubes of the centered, shifted diagonal weights. -/
theorem gelfand_difference_eq_centered (u : Fin N → ℂ) (hu : ∑ i, u i = 0) :
    gelfandEigenvalue u - gelfandEigenvalue (fun i => -u i.rev) =
      2 * ∑ i, (u i + ((N : ℂ) - 1 - 2 * i.val) / 2) ^ 3 := by
  rw [reversed_eigenvalue, gelfandEigenvalue, ← sum_sub_distrib]
  have pt (i : Fin N) : (u i + t i) * (u i ^ 2 + ∑ j, if i < j then u i - u j else 0) -
      (-u i - t i) * (u i ^ 2 - before (fun _ => 1) i * u i + before u i) =
      (2 * u i ^ 3 + 3 * t i * u i ^ 2 + t i ^ 2 * u i) +
        (u i + t i) * (before u i - after u i) := by
    rw [row_diff, after_one, before_one, t]
    ring
  simp_rw [pt]
  rw [sum_add_distrib, cross_sum, ← sum_add_distrib]
  have pc (i : Fin N) :
      2 * u i ^ 3 + 3 * t i * u i ^ 2 + t i ^ 2 * u i + u i * (after t i - before t i) =
      2 * (u i + t i / 2) ^ 3 - (((N : ℂ)^2 - 1)/2) * u i - t i ^ 3 / 4 := by
    linear_combination u i * (linear_coeff i)
  simp_rw [pc]
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hu, mul_zero, sub_zero,
    ← sum_div, cubic_offset_sum, zero_div, sub_zero]
  rfl

private lemma zero_sum_of_reverse (u : Fin N → ℂ) (h : ∀ i, u i.rev = -u i) : ∑ i, u i = 0 := by
  have hs := Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N) u
  simp only [Fin.revPerm_apply, h, sum_neg_distrib] at hs
  linear_combination -hs / 2

/-- Lowering at a positive node strictly to the left of its opposite gives
a nonzero cubic for any dominant self-dual set of diagonal coordinates. -/
theorem shifted_difference_ne_zero (u : Fin N → ℂ) (hsym : ∀ k, u k.rev = -u k)
    (hdom : Antitone (fun k => (u k).re)) (i j : Fin N) (hadj : j.val = i.val + 1)
    (hleft : i < j.rev) (hpos : u i ≠ u j) :
    let v := fun k => u k - (if k = i then 1 else 0) + (if k = j then 1 else 0)
    gelfandEigenvalue v - gelfandEigenvalue (fun k => -v k.rev) ≠ 0 := by
  classical
  intro v
  let x := fun k => u k + t k / 2
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  have hsum : ∑ k, v k = 0 := by simp [v, sum_add_distrib, sum_sub_distrib, zero_sum_of_reverse u hsym]
  have hzero : ∑ k, x k ^ 3 = 0 := by
    apply zero_sum_of_reverse
    intro k
    simp only [x, hsym, t_rev]
    ring
  have hshift := Classical.cubic_sum_two_coordinate_shift x i j hij
  have hadj' : (j.val : ℂ) = i.val + 1 := by exact_mod_cast hadj
  have hx : x i - x j - 1 = u i - u j := by dsimp [x, t]; rw [hadj']; ring
  have hxy : x i + x j ≠ 0 := by
    have hle : (u j.rev).re ≤ (u i).re := hdom hleft.le
    rw [hsym, Complex.neg_re] at hle
    have hij' : i.val < j.rev.val := hleft
    rw [Fin.val_rev] at hij'
    have hjlim := j.isLt
    have hjlt : i.val + j.val + 1 < N := by omega
    have hpos' : (i.val : ℝ) + j.val + 1 < N := by exact_mod_cast hjlt
    intro hz
    have hh := congrArg Complex.re hz
    simp [x, t] at hh
    linarith
  rw [gelfand_difference_eq_centered v hsum]
  apply mul_ne_zero (by norm_num)
  have he (k : Fin N) : v k + ((N : ℂ) - 1 - 2 * k.val) / 2 =
      x k - (if k = i then 1 else 0) + (if k = j then 1 else 0) := by dsimp [v, x, t]; ring
  simp_rw [he]
  rw [hshift, hzero, zero_add]
  have hid : (x i - 1)^3 - (x i)^3 + ((x j + 1)^3 - (x j)^3) =
      -3 * (x i + x j) * (x i - x j - 1) := by ring
  rw [hid, hx]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hxy) (sub_ne_zero.mpr hpos)

end

end CubicAnomaly.Classification.TypeACubicArithmetic
