import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unbounded arithmetic in the classical rank-deficient argument

These theorems establish the cubic calculation and dimension inequalities used
in Proposition `classical-rankdef` of the manuscript for arbitrary rank.  They
are ordinary kernel proofs, without bounded enumeration or `native_decide`.

The functions `oddDRatioOne` and `oddDRatioTwo` are the rational expressions
printed in that proposition.  Identifying them with dimensions of actual
highest-weight modules requires Weyl's dimension formula and is **not** asserted
by defining these functions.  Likewise, the cubic calculation below is an
identity of centred coordinates; identifying its value with the trace-cubic
index is a representation-theoretic step outside this module.
-/

namespace CubicAnomaly.Classification.Classical

/-- The change in a sum of cubes when a simple root shifts two coordinates. -/
theorem cubic_coordinate_shift (u v : ℚ) :
    (u - 1) ^ 3 - u ^ 3 + (v + 1) ^ 3 - v ^ 3 =
      3 * (u + v) * (v - u + 1) := by
  ring

/-- The type-A calculation for the representative with `2 * i < N`.
The orientation hypothesis matters: the dual support node gives the negative
of this value, not the same unsigned expression. -/
theorem typeA_dual_support_cubic (N a i : ℕ) (u v : ℚ)
    (hsub : u - v = 2 * (a : ℚ) + 1)
    (hadd : u + v = 2 * (a : ℚ) + N - 2 * i) :
    (u - 1) ^ 3 - u ^ 3 + (v + 1) ^ 3 - v ^ 3 =
      -6 * (a : ℚ) * (2 * a + N - 2 * i) := by
  rw [cubic_coordinate_shift, hadd]
  have h : v - u + 1 = -2 * (a : ℚ) := by linarith
  rw [h]
  ring

/-- Nonvanishing is uniform in the rank and in the support coefficient. -/
theorem typeA_dual_support_cubic_ne_zero (N a i : ℕ)
    (ha : 0 < a) (hi : 2 * i < N) :
    -6 * (a : ℚ) * (2 * a + N - 2 * i) ≠ 0 := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hi' : 2 * (i : ℚ) < N := by exact_mod_cast hi
  have hlast : (0 : ℚ) < 2 * a + N - 2 * i := by linarith
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt ha')) (ne_of_gt hlast)

/-- The centred shifted coordinates of `2a (ω_i + ω_(N-i))`, indexed from
zero.  The mean has already been subtracted in this explicit expression. -/
def typeACenteredCoordinates (N a i : ℕ) (j : Fin N) : ℚ :=
  (if j.val < i then 2 * (a : ℚ)
    else if j.val < N - i then 0 else -2 * (a : ℚ)) +
      ((N : ℚ) - 1) / 2 - j.val

/-- The sum of cubes after subtracting the simple root at the one-based
support node `i`.  Only coordinates `i-1` and `i` change. -/
def typeASupportCubic (N a i : ℕ) : ℚ :=
  ∑ j : Fin N, (typeACenteredCoordinates N a i j -
    (if j.val = i - 1 then 1 else 0) + (if j.val = i then 1 else 0)) ^ 3

private theorem typeACentered_reverse (N a i : ℕ) (hi : 2 * i < N)
    (j : Fin N) :
    typeACenteredCoordinates N a i j.rev = -typeACenteredCoordinates N a i j := by
  have hj := j.isLt
  have hcast : ((N - (j.val + 1) : ℕ) : ℚ) = N - j.val - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [typeACenteredCoordinates, Fin.val_rev]
  rw [hcast]
  split_ifs
  all_goals first | omega | ring

private theorem typeACentered_cubic_zero (N a i : ℕ) (hi : 2 * i < N) :
    ∑ j : Fin N, typeACenteredCoordinates N a i j ^ 3 = 0 := by
  have h := Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N)
    (fun j => typeACenteredCoordinates N a i j ^ 3)
  have heq : ∀ j : Fin N, typeACenteredCoordinates N a i j.rev ^ 3 =
      -(typeACenteredCoordinates N a i j ^ 3) := by
    intro j
    rw [typeACentered_reverse N a i hi]
    ring
  simp_rw [Fin.revPerm_apply, heq, Finset.sum_neg_distrib] at h
  linarith

private theorem cubic_sum_two_coordinate_shift {N : ℕ} (x : Fin N → ℚ)
    (p q : Fin N) (hpq : p ≠ q) :
    (∑ j : Fin N, (x j - (if j = p then 1 else 0) +
      (if j = q then 1 else 0)) ^ 3) =
      (∑ j : Fin N, x j ^ 3) +
        ((x p - 1) ^ 3 - x p ^ 3) + ((x q + 1) ^ 3 - x q ^ 3) := by
  have hpoint : ∀ j : Fin N,
      (x j - (if j = p then 1 else 0) + (if j = q then 1 else 0)) ^ 3 =
      x j ^ 3 + (if j = p then (x p - 1) ^ 3 - x p ^ 3 else 0) +
        (if j = q then (x q + 1) ^ 3 - x q ^ 3 else 0) := by
    intro j
    by_cases hjp : j = p
    · subst j
      simp [hpq]
    · by_cases hjq : j = q
      · subst j
        simp [hjp]
      · simp [hjp, hjq]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp

/-- The complete finite sum of centred-coordinate cubes, proved for every
rank and every coefficient.  No search bound on `N` or `a` occurs. -/
theorem typeA_support_cubic_formula (N a i : ℕ) (hi : 1 ≤ i)
    (hhalf : 2 * i < N) :
    typeASupportCubic N a i = -6 * (a : ℚ) * (2 * a + N - 2 * i) := by
  let p : Fin N := ⟨i - 1, by omega⟩
  let q : Fin N := ⟨i, by omega⟩
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p, q] at hv
    omega
  have hcast : ((i - 1 : ℕ) : ℚ) = i - 1 := by
    rw [Nat.cast_sub hi]
    norm_num
  have hp : typeACenteredCoordinates N a i p =
      2 * (a : ℚ) + ((N : ℚ) - 1) / 2 - (i - 1) := by
    simp [typeACenteredCoordinates, p, show i - 1 < i by omega, hcast]
  have hq : typeACenteredCoordinates N a i q = ((N : ℚ) - 1) / 2 - i := by
    simp [typeACenteredCoordinates, q, show i < N - i by omega]
  have h := cubic_sum_two_coordinate_shift (typeACenteredCoordinates N a i) p q hpq
  have hsum : typeASupportCubic N a i =
      (typeACenteredCoordinates N a i p - 1) ^ 3 -
        typeACenteredCoordinates N a i p ^ 3 +
      (typeACenteredCoordinates N a i q + 1) ^ 3 -
        typeACenteredCoordinates N a i q ^ 3 := by
    simpa [typeASupportCubic, Fin.ext_iff, p, q,
      typeACentered_cubic_zero N a i hhalf, sub_eq_add_neg, add_assoc] using h
  rw [hsum]
  apply typeA_dual_support_cubic
  · rw [hp, hq]
    ring
  · rw [hp, hq]
    ring

/-- Nonvanishing of the full type-A coordinate cubic, for all admissible
support nodes and positive coefficients. -/
theorem typeA_support_cubic_nonzero (N a i : ℕ) (ha : 0 < a)
    (hi : 1 ≤ i) (hhalf : 2 * i < N) : typeASupportCubic N a i ≠ 0 := by
  rw [typeA_support_cubic_formula N a i hi hhalf]
  exact typeA_dual_support_cubic_ne_zero N a i ha hhalf

/-- Rational formula for `4 M_(r,1) / D_(r,1)^2`. -/
def oddDRatioOne (r : ℚ) : ℚ :=
  36 * (r - 1) * (2 * r + 1) / (r * (r + 2) * (r + 3) * (r + 4))

/-- Rational formula for `4 M_(r,2) / D_(r,2)^2`. -/
def oddDRatioTwo (r : ℚ) : ℚ :=
  5376000 * (r - 1) * (r + 2) * (2 * r + 1) * (2 * r + 3) ^ 2 *
      (2 * r + 5) /
    (r * (r + 1) * (r + 3) ^ 2 * (r + 4) ^ 3 * (r + 5) ^ 3 *
      (r + 6) ^ 2 * (r + 7) * (r + 8))

private theorem ratioOne_denominator_pos (r : ℚ) (hr : 5 ≤ r) :
    0 < r * (r + 2) * (r + 3) * (r + 4) := by
  have : 0 < r := by linarith
  positivity

private theorem ratioTwo_denominator_pos (r : ℚ) (hr : 5 ≤ r) :
    0 < r * (r + 1) * (r + 3) ^ 2 * (r + 4) ^ 3 * (r + 5) ^ 3 *
      (r + 6) ^ 2 * (r + 7) * (r + 8) := by
  have : 0 < r := by linarith
  positivity

/-- A direct polynomial proof of the first ratio bound for every `r ≥ 5`.
It even holds for rational ranks, so no parity assumption is needed here. -/
theorem oddD_ratio_one_lt_two_thirds (r : ℚ) (hr : 5 ≤ r) :
    oddDRatioOne r < 2 / 3 := by
  let n := r - 5
  have hn : 0 ≤ n := by dsimp [n]; linarith
  have hid : 2 * (r * (r + 2) * (r + 3) * (r + 4)) -
      3 * (36 * (r - 1) * (2 * r + 1)) =
      2 * n ^ 4 + 58 * n ^ 3 + 406 * n ^ 2 + 866 * n + 288 := by
    dsimp [n]
    ring
  have hp : 0 < 2 * n ^ 4 + 58 * n ^ 3 + 406 * n ^ 2 + 866 * n + 288 := by
    positivity
  unfold oddDRatioOne
  apply (div_lt_iff₀ (ratioOne_denominator_pos r hr)).2
  linarith

/-- A direct positive-coefficient polynomial proof of the second ratio bound
for every `r ≥ 5`.  The degree-fourteen identity is checked by `ring`. -/
theorem oddD_ratio_two_lt_one_sixth (r : ℚ) (hr : 5 ≤ r) :
    oddDRatioTwo r < 1 / 6 := by
  let n := r - 5
  have hn : 0 ≤ n := by dsimp [n]; linarith
  have hid :
      r * (r + 1) * (r + 3) ^ 2 * (r + 4) ^ 3 * (r + 5) ^ 3 *
          (r + 6) ^ 2 * (r + 7) * (r + 8) -
        6 * (5376000 * (r - 1) * (r + 2) * (2 * r + 1) *
          (2 * r + 3) ^ 2 * (2 * r + 5)) =
      n ^ 14 + 131 * n ^ 13 + 7937 * n ^ 12 + 294763 * n ^ 11 +
        7495467 * n ^ 10 + 138039825 * n ^ 9 + 1898429027 * n ^ 8 +
        19803492097 * n ^ 7 + 156914273392 * n ^ 6 +
        929841620624 * n ^ 5 + 3975965654976 * n ^ 4 +
        11520097288560 * n ^ 3 + 20191160923200 * n ^ 2 +
        16482917376000 * n + 1235520000000 := by
    dsimp [n]
    ring
  have hp : 0 < n ^ 14 + 131 * n ^ 13 + 7937 * n ^ 12 + 294763 * n ^ 11 +
        7495467 * n ^ 10 + 138039825 * n ^ 9 + 1898429027 * n ^ 8 +
        19803492097 * n ^ 7 + 156914273392 * n ^ 6 +
        929841620624 * n ^ 5 + 3975965654976 * n ^ 4 +
        11520097288560 * n ^ 3 + 20191160923200 * n ^ 2 +
        16482917376000 * n + 1235520000000 := by
    positivity
  unfold oddDRatioTwo
  apply (div_lt_iff₀ (ratioTwo_denominator_pos r hr)).2
  linarith

/-- The first exterior-square gap, conditional only on the explicitly stated
dimension lower bound and Weyl-ratio identity. -/
theorem oddD_dimension_gap_one (r D M : ℚ) (hr : 5 ≤ r)
    (hD : r * (2 * r - 1) ≤ D)
    (hratio : 4 * M / D ^ 2 = oddDRatioOne r) :
    r * (2 * r - 1) < D * (D - 1) / 2 - 2 * M := by
  let H := r * (2 * r - 1)
  have hH : 45 ≤ H := by dsimp [H]; nlinarith [sq_nonneg (r - 5)]
  have hDpos : 0 < D := by change H ≤ D at hD; linarith
  have hbound : 4 * M / D ^ 2 < 2 / 3 := by
    rw [hratio]
    exact oddD_ratio_one_lt_two_thirds r hr
  have hm : 4 * M < 2 / 3 * D ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hDpos)).1 hbound
  have hprod : 0 ≤ (D - H) * (D + H - 3) := by
    apply mul_nonneg
    · change H ≤ D at hD
      linarith
    · linarith
  have hgap : 0 < H * (H - 9) := mul_pos (by linarith) (by linarith)
  change H < _
  nlinarith only [hm, hprod, hgap]

/-- The second exterior-square gap, with the same explicit boundary between
the rational calculation and its representation-theoretic interpretation. -/
theorem oddD_dimension_gap_two (r D M : ℚ) (hr : 5 ≤ r)
    (hD : r * (2 * r - 1) ≤ D)
    (hratio : 4 * M / D ^ 2 = oddDRatioTwo r) :
    r * (2 * r - 1) < D * (D - 1) / 2 - 2 * M := by
  let H := r * (2 * r - 1)
  have hH : 45 ≤ H := by dsimp [H]; nlinarith [sq_nonneg (r - 5)]
  have hDpos : 0 < D := by change H ≤ D at hD; linarith
  have hbound : 4 * M / D ^ 2 < 1 / 6 := by
    rw [hratio]
    exact oddD_ratio_two_lt_one_sixth r hr
  have hm : 4 * M < 1 / 6 * D ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hDpos)).1 hbound
  have hprod : 0 ≤ (D - H) * (5 * (D + H) - 6) := by
    apply mul_nonneg
    · change H ≤ D at hD
      linarith
    · linarith
  have hgap : 0 < H * (5 * H - 18) := mul_pos (by linarith) (by linarith)
  change H < _
  nlinarith only [hm, hprod, hgap]

/-- The first D-type candidate has sufficient dimension in every rank:
`choose (2*r) (r-1) ≥ dim so(2*r)`.  This is a binomial inequality, independent
of any highest-weight classification or dimension-formula hypothesis. -/
theorem oddD_binomial_dimension_lower_bound (r : ℕ) (hr : 3 ≤ r) :
    r * (2 * r - 1) ≤ (2 * r).choose (r - 1) := by
  have hmono : ∀ k, 2 ≤ k → k ≤ r →
      (2 * r).choose 2 ≤ (2 * r).choose k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hk ih =>
      intro hkr
      exact (ih (by omega)).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))
  have h := hmono (r - 1) (by omega) (by omega)
  have heq : (2 * r).choose 2 = r * (2 * r - 1) := by
    simp [Nat.choose_two_right, Nat.mul_assoc]
  rwa [heq] at h

/-- Natural-number form of the first dimension gap.  The conclusion uses the
actual binomial dimension of an exterior square, with no rational rounding. -/
theorem oddD_exterior_square_not_exhausted_one (r D M : ℕ) (hr : 5 ≤ r)
    (hD : r * (2 * r - 1) ≤ D)
    (hratio : 4 * (M : ℚ) / (D : ℚ) ^ 2 = oddDRatioOne r) :
    r * (2 * r - 1) + 2 * M < D.choose 2 := by
  have hr' : (5 : ℚ) ≤ r := by exact_mod_cast hr
  have hn : 1 ≤ 2 * r := by omega
  have hD' : (r : ℚ) * (2 * r - 1) ≤ D := by
    have h := (Nat.cast_le (α := ℚ)).2 hD
    simpa only [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_ofNat, Nat.cast_one] using h
  have h := oddD_dimension_gap_one r D M hr' hD' hratio
  have hc := Nat.cast_choose_two ℚ D
  have he : ((r * (2 * r - 1) + 2 * M : ℕ) : ℚ) =
      (r : ℚ) * (2 * r - 1) + 2 * M := by
    push_cast [Nat.cast_sub hn]
    ring
  have : ((r * (2 * r - 1) + 2 * M : ℕ) : ℚ) < D.choose 2 := by
    rw [he, hc]
    linarith
  exact_mod_cast this

/-- Natural-number form of the second dimension gap. -/
theorem oddD_exterior_square_not_exhausted_two (r D M : ℕ) (hr : 5 ≤ r)
    (hD : r * (2 * r - 1) ≤ D)
    (hratio : 4 * (M : ℚ) / (D : ℚ) ^ 2 = oddDRatioTwo r) :
    r * (2 * r - 1) + 2 * M < D.choose 2 := by
  have hr' : (5 : ℚ) ≤ r := by exact_mod_cast hr
  have hn : 1 ≤ 2 * r := by omega
  have hD' : (r : ℚ) * (2 * r - 1) ≤ D := by
    have h := (Nat.cast_le (α := ℚ)).2 hD
    simpa only [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_ofNat, Nat.cast_one] using h
  have h := oddD_dimension_gap_two r D M hr' hD' hratio
  have hc := Nat.cast_choose_two ℚ D
  have he : ((r * (2 * r - 1) + 2 * M : ℕ) : ℚ) =
      (r : ℚ) * (2 * r - 1) + 2 * M := by
    push_cast [Nat.cast_sub hn]
    ring
  have : ((r * (2 * r - 1) + 2 * M : ℕ) : ℚ) < D.choose 2 := by
    rw [he, hc]
    linarith
  exact_mod_cast this

/-- For the first candidate the binomial bound discharges the dimension
inequality automatically.  Only the stated Weyl-ratio identity remains as an
input; all ranks `r ≥ 5` are covered by the proof. -/
theorem oddD_binomial_candidate_not_exhausted (r M : ℕ) (hr : 5 ≤ r)
    (hratio : 4 * (M : ℚ) / (((2 * r).choose (r - 1) : ℕ) : ℚ) ^ 2 =
      oddDRatioOne r) :
    r * (2 * r - 1) + 2 * M < ((2 * r).choose (r - 1)).choose 2 := by
  exact oddD_exterior_square_not_exhausted_one r _ M hr
    (oddD_binomial_dimension_lower_bound r (by omega)) hratio

/-- Arithmetic gaps for the four E6 dual-support candidates.  The values of
`D` and `M` themselves must still be obtained from Weyl's dimension formula. -/
theorem e6_dual_support_arithmetic_gaps :
    (650 : ℕ).choose 2 - 78 - 2 * 78975 = 52897 ∧
    (85293 : ℕ).choose 2 - 78 - 2 * 314269956 = 3008865288 ∧
    (70070 : ℕ).choose 2 - 78 - 2 * 252808452 = 1949250433 ∧
    (221077350 : ℕ).choose 2 - 78 - 2 * 64821173232816 =
      24307954884506865 := by
  norm_num [Nat.choose_two_right]

end CubicAnomaly.Classification.Classical
