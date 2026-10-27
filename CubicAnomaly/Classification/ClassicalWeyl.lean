import CubicAnomaly.Classification.Classical
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Weyl-product identities for the unbounded D-type families

This module evaluates explicit products over the positive roots of type D.
The coordinates are in reverse orthonormal order, so the positive roots are
the pairs `0 ≤ l < k < r`.  The product is the usual Weyl dimension expression.
The identification with dimensions of Lie algebra representations remains a
representation-theoretic theorem; the product identities here are kernel
proofs for every rank, rather than a bounded numerical check.
-/

namespace CubicAnomaly.Classification.Classical

private def risingProduct (x : ℚ) (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, (x + j)

private theorem risingProduct_add (x : ℚ) (m n : ℕ) :
    risingProduct x (m + n) = risingProduct x m * risingProduct (x + m) n := by
  simp [risingProduct, Finset.prod_range_add, Nat.cast_add, add_assoc]

private theorem risingProduct_pos (x : ℚ) (hx : 0 < x) (n : ℕ) :
    0 < risingProduct x n := by
  apply Finset.prod_pos
  intro j _
  positivity

/-- Interchanging the length and integer shift in a rising-product ratio. -/
private theorem shiftedProduct_exchange (x : ℚ) (hx : 0 < x) (n k : ℕ) :
    (∏ j ∈ Finset.range n, (x + k + j) / (x + j)) =
      risingProduct (x + n) k / risingProduct x k := by
  rw [Finset.prod_div_distrib]
  change risingProduct (x + k) n / risingProduct x n = _
  apply (div_eq_div_iff (ne_of_gt (risingProduct_pos x hx n))
    (ne_of_gt (risingProduct_pos x hx k))).2
  calc
    risingProduct (x + k) n * risingProduct x k = risingProduct x (k + n) := by
      rw [risingProduct_add]
      ring
    _ = risingProduct x (n + k) := by rw [Nat.add_comm]
    _ = risingProduct (x + n) k * risingProduct x n := by
      rw [risingProduct_add]
      ring

/-- The two Weyl factors for the roots `e_k-e_l` and `e_k+e_l`. -/
def typeDWeylFactor (coordinates : ℕ → ℚ) (k l : ℕ) : ℚ :=
  (coordinates k - coordinates l + k - l) / ((k : ℚ) - l) *
    (coordinates k + coordinates l + k + l) / ((k : ℚ) + l)

/-- The full positive-root Weyl product, without any rank cutoff. -/
def typeDWeylProduct (r : ℕ) (coordinates : ℕ → ℚ) : ℚ :=
  ∏ k ∈ Finset.range r, ∏ l ∈ Finset.range k, typeDWeylFactor coordinates k l

/-- Coordinates of `a(ω_(r-1)+ω_r)`, in reverse orthonormal order. -/
def typeDDefiningCoordinates (a : ℕ) (k : ℕ) : ℚ :=
  if k = 0 then 0 else a

/-- Coordinates of `2a(ω_(r-1)+ω_r)-α_(r-1)`, in reverse order. -/
def typeDConstituentCoordinates (a : ℕ) (k : ℕ) : ℚ :=
  if k = 0 then 1 else if k = 1 then 2 * (a : ℚ) - 1 else 2 * a

/-- The defining candidate's Weyl dimension product. -/
def typeDDefiningDimension (r a : ℕ) : ℚ :=
  typeDWeylProduct r (typeDDefiningCoordinates a)

/-- The proposed exterior-square constituent's Weyl dimension product. -/
def typeDConstituentDimension (r a : ℕ) : ℚ :=
  typeDWeylProduct r (typeDConstituentCoordinates a)

private theorem typeDWeylProduct_succ (r : ℕ) (c : ℕ → ℚ) :
    typeDWeylProduct (r + 1) c = typeDWeylProduct r c *
      ∏ l ∈ Finset.range r, typeDWeylFactor c r l := by
  simp only [typeDWeylProduct, Finset.prod_range_succ]

private theorem definingFactor_zero (n a : ℕ) :
    typeDWeylFactor (typeDDefiningCoordinates a) (n + 1) 0 =
      (((a : ℚ) + (n + 1)) / (n + 1)) ^ 2 := by
  simp [typeDWeylFactor, typeDDefiningCoordinates]
  ring

private theorem definingFactor_succ (n a l : ℕ) (hl : l < n) :
    typeDWeylFactor (typeDDefiningCoordinates a) (n + 1) (l + 1) =
      ((n : ℚ) + 2 + 2 * a + l) / (n + 2 + l) := by
  have hl' : (l : ℚ) < n := by exact_mod_cast hl
  have hden : (n : ℚ) + 1 - (l + 1) ≠ 0 := by linarith
  simp only [typeDWeylFactor, typeDDefiningCoordinates, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte, Nat.cast_add, Nat.cast_one,
    sub_self, zero_add, div_self hden, one_mul]
  congr 1 <;> ring

private theorem definingRow (n a : ℕ) :
    (∏ l ∈ Finset.range (n + 1),
      typeDWeylFactor (typeDDefiningCoordinates a) (n + 1) l) =
      (((a : ℚ) + (n + 1)) / (n + 1)) ^ 2 *
        (risingProduct (2 * (n + 1)) (2 * a) / risingProduct (n + 2) (2 * a)) := by
  rw [Finset.prod_range_succ']
  rw [definingFactor_zero]
  have hprod :
      (∏ l ∈ Finset.range n,
        typeDWeylFactor (typeDDefiningCoordinates a) (n + 1) (l + 1)) =
      ∏ l ∈ Finset.range n, ((n : ℚ) + 2 + (2 * a : ℕ) + l) / (n + 2 + l) := by
    apply Finset.prod_congr rfl
    intro l hl
    rw [definingFactor_succ n a l (Finset.mem_range.mp hl)]
    push_cast
    rfl
  rw [hprod, shiftedProduct_exchange (n + 2) (by positivity)]
  have hx : (n : ℚ) + 2 + n = 2 * (n + 1) := by ring
  rw [hx]
  ring

private theorem definingDimension_succ (n a : ℕ) :
    typeDDefiningDimension (n + 2) a = typeDDefiningDimension (n + 1) a *
      ((((a : ℚ) + (n + 1)) / (n + 1)) ^ 2 *
        (risingProduct (2 * (n + 1)) (2 * a) / risingProduct (n + 2) (2 * a))) := by
  unfold typeDDefiningDimension
  rw [typeDWeylProduct_succ, definingRow]

private theorem constituentFactor_tail (n a l : ℕ) (hl : l < n) :
    typeDWeylFactor (typeDConstituentCoordinates a) (n + 2) (l + 2) =
      ((n : ℚ) + 4 + 4 * a + l) / (n + 4 + l) := by
  have hl' : (l : ℚ) < n := by exact_mod_cast hl
  have hden : (n : ℚ) + 2 - (l + 2) ≠ 0 := by linarith
  simp only [typeDWeylFactor, typeDConstituentCoordinates,
    show n + 2 ≠ 0 by omega, show n + 2 ≠ 1 by omega,
    show l + 2 ≠ 0 by omega, show l + 2 ≠ 1 by omega,
    ↓reduceIte, Nat.cast_add, Nat.cast_ofNat, sub_self, zero_add,
    div_self hden, one_mul]
  congr 1 <;> ring

private theorem constituentRow (n a : ℕ) :
    (∏ l ∈ Finset.range (n + 2),
      typeDWeylFactor (typeDConstituentCoordinates a) (n + 2) l) =
      (((n : ℚ) + 2 * a + 1) * (n + 2 * a + 3) * (n + 4 * a + 2) /
        ((n + 2) * (n + 1) * (n + 3))) *
      (risingProduct (2 * (n + 2)) (4 * a) / risingProduct (n + 4) (4 * a)) := by
  simp only [Finset.prod_range_succ', Nat.add_assoc, Nat.reduceAdd]
  have hprod :
      (∏ l ∈ Finset.range n,
        typeDWeylFactor (typeDConstituentCoordinates a) (n + 2) (l + 2)) =
      ∏ l ∈ Finset.range n, ((n : ℚ) + 4 + (4 * a : ℕ) + l) / (n + 4 + l) := by
    apply Finset.prod_congr rfl
    intro l hl
    rw [constituentFactor_tail n a l (Finset.mem_range.mp hl)]
    push_cast
    rfl
  rw [hprod, shiftedProduct_exchange (n + 4) (by positivity)]
  have hx : (n : ℚ) + 4 + n = 2 * (n + 2) := by ring
  rw [hx]
  simp only [typeDWeylFactor, typeDConstituentCoordinates,
    show n + 2 ≠ 0 by omega, show n + 2 ≠ 1 by omega,
    Nat.one_ne_zero, ↓reduceIte, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero, sub_zero, add_zero]
  have h1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℚ) + 2 - 1 ≠ 0 := by
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith
  have h4 : (n : ℚ) + 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem constituentDimension_succ (n a : ℕ) :
    typeDConstituentDimension (n + 3) a = typeDConstituentDimension (n + 2) a *
      ((((n : ℚ) + 2 * a + 1) * (n + 2 * a + 3) * (n + 4 * a + 2) /
        ((n + 2) * (n + 1) * (n + 3))) *
      (risingProduct (2 * (n + 2)) (4 * a) / risingProduct (n + 4) (4 * a))) := by
  unfold typeDConstituentDimension
  rw [typeDWeylProduct_succ, constituentRow]

private def definingStepOne (r : ℚ) : ℚ :=
  2 * (r + 1) * (2 * r + 1) / (r * (r + 2))

private def definingStepTwo (r : ℚ) : ℚ :=
  4 * (r + 2) * (2 * r + 1) * (2 * r + 3) / (r * (r + 3) * (r + 4))

private def constituentStepOne (r : ℚ) : ℚ :=
  4 * (r + 1) * (2 * r + 1) * (2 * r + 3) / ((r - 1) * (r + 2) * (r + 5))

private def constituentStepTwo (r : ℚ) : ℚ :=
  16 * (r + 3) * (2 * r + 1) * (2 * r + 3) * (2 * r + 5) * (2 * r + 7) /
    ((r - 1) * (r + 4) * (r + 6) * (r + 7) * (r + 9))

private theorem definingDimension_one_step (r : ℕ) (hr : 1 ≤ r) :
    typeDDefiningDimension (r + 1) 1 =
      typeDDefiningDimension r 1 * definingStepOne r := by
  cases r with
  | zero => omega
  | succ n =>
    rw [show n.succ + 1 = n + 2 by omega, definingDimension_succ]
    congr 1
    norm_num [risingProduct, Finset.prod_range_succ, definingStepOne]
    field_simp
    ring

private theorem definingDimension_two_step (r : ℕ) (hr : 1 ≤ r) :
    typeDDefiningDimension (r + 1) 2 =
      typeDDefiningDimension r 2 * definingStepTwo r := by
  cases r with
  | zero => omega
  | succ n =>
    rw [show n.succ + 1 = n + 2 by omega, definingDimension_succ]
    congr 1
    norm_num [risingProduct, Finset.prod_range_succ, definingStepTwo]
    field_simp
    ring

private theorem constituentDimension_one_step (r : ℕ) (hr : 2 ≤ r) :
    typeDConstituentDimension (r + 1) 1 =
      typeDConstituentDimension r 1 * constituentStepOne r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 2 + n + 1 = n + 3 by omega, constituentDimension_succ]
  have h : 2 + n = n + 2 := by omega
  rw [h]
  congr 1
  norm_num [risingProduct, Finset.prod_range_succ, constituentStepOne]
  have hne : (1 : ℚ) + n ≠ 0 := by positivity
  ring_nf
  field_simp [hne]
  ring

private theorem constituentDimension_two_step (r : ℕ) (hr : 2 ≤ r) :
    typeDConstituentDimension (r + 1) 2 =
      typeDConstituentDimension r 2 * constituentStepTwo r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 2 + n + 1 = n + 3 by omega, constituentDimension_succ]
  have h : 2 + n = n + 2 := by omega
  rw [h]
  congr 1
  norm_num [risingProduct, Finset.prod_range_succ, constituentStepTwo]
  have hne : (1 : ℚ) + n ≠ 0 := by positivity
  ring_nf
  field_simp [hne]
  ring

private theorem definingStepOne_pos (r : ℚ) (hr : 0 < r) :
    0 < definingStepOne r := by
  unfold definingStepOne
  exact div_pos (by positivity) (by positivity)

private theorem definingStepTwo_pos (r : ℚ) (hr : 0 < r) :
    0 < definingStepTwo r := by
  unfold definingStepTwo
  exact div_pos (by positivity) (by positivity)

private theorem definingDimension_one_pos (r : ℕ) (hr : 2 ≤ r) :
    0 < typeDDefiningDimension r 1 := by
  induction r, hr using Nat.le_induction with
  | base =>
    norm_num [typeDDefiningDimension, typeDWeylProduct, typeDWeylFactor,
      typeDDefiningCoordinates, Finset.prod_range_succ]
  | succ r hr ih =>
    rw [definingDimension_one_step r (by omega)]
    exact mul_pos ih (definingStepOne_pos r (by exact_mod_cast (by omega : 0 < r)))

private theorem definingDimension_two_pos (r : ℕ) (hr : 2 ≤ r) :
    0 < typeDDefiningDimension r 2 := by
  induction r, hr using Nat.le_induction with
  | base =>
    norm_num [typeDDefiningDimension, typeDWeylProduct, typeDWeylFactor,
      typeDDefiningCoordinates, Finset.prod_range_succ]
  | succ r hr ih =>
    rw [definingDimension_two_step r (by omega)]
    exact mul_pos ih (definingStepTwo_pos r (by exact_mod_cast (by omega : 0 < r)))

private theorem ratioOne_step_identity (r : ℚ) (hr : 2 ≤ r) :
    oddDRatioOne (r + 1) * definingStepOne r ^ 2 =
      oddDRatioOne r * constituentStepOne r := by
  have hrpos : 0 < r := by linarith
  have hm : r - 1 ≠ 0 := by linarith
  unfold oddDRatioOne definingStepOne constituentStepOne
  field_simp
  ring

private theorem ratioTwo_step_identity (r : ℚ) (hr : 2 ≤ r) :
    oddDRatioTwo (r + 1) * definingStepTwo r ^ 2 =
      oddDRatioTwo r * constituentStepTwo r := by
  have hrpos : 0 < r := by linarith
  have hm : r - 1 ≠ 0 := by linarith
  unfold oddDRatioTwo definingStepTwo constituentStepTwo
  field_simp
  ring

private theorem ratioOne_cross_product (r : ℕ) (hr : 2 ≤ r) :
    4 * typeDConstituentDimension r 1 =
      oddDRatioOne r * typeDDefiningDimension r 1 ^ 2 := by
  induction r, hr using Nat.le_induction with
  | base =>
    norm_num [typeDDefiningDimension, typeDConstituentDimension, typeDWeylProduct,
      typeDWeylFactor, typeDDefiningCoordinates, typeDConstituentCoordinates,
      Finset.prod_range_succ, oddDRatioOne]
  | succ r hr ih =>
    rw [constituentDimension_one_step r hr, definingDimension_one_step r (by omega)]
    push_cast
    calc
      4 * (typeDConstituentDimension r 1 * constituentStepOne r) =
          (4 * typeDConstituentDimension r 1) * constituentStepOne r := by ring
      _ = (oddDRatioOne r * typeDDefiningDimension r 1 ^ 2) *
          constituentStepOne r := by rw [ih]
      _ = typeDDefiningDimension r 1 ^ 2 * (oddDRatioOne r * constituentStepOne r) := by ring
      _ = typeDDefiningDimension r 1 ^ 2 *
          (oddDRatioOne (r + 1) * definingStepOne r ^ 2) := by
        rw [ratioOne_step_identity r (by exact_mod_cast hr)]
      _ = _ := by ring

private theorem ratioTwo_cross_product (r : ℕ) (hr : 2 ≤ r) :
    4 * typeDConstituentDimension r 2 =
      oddDRatioTwo r * typeDDefiningDimension r 2 ^ 2 := by
  induction r, hr using Nat.le_induction with
  | base =>
    norm_num [typeDDefiningDimension, typeDConstituentDimension, typeDWeylProduct,
      typeDWeylFactor, typeDDefiningCoordinates, typeDConstituentCoordinates,
      Finset.prod_range_succ, oddDRatioTwo]
  | succ r hr ih =>
    rw [constituentDimension_two_step r hr, definingDimension_two_step r (by omega)]
    push_cast
    calc
      4 * (typeDConstituentDimension r 2 * constituentStepTwo r) =
          (4 * typeDConstituentDimension r 2) * constituentStepTwo r := by ring
      _ = (oddDRatioTwo r * typeDDefiningDimension r 2 ^ 2) *
          constituentStepTwo r := by rw [ih]
      _ = typeDDefiningDimension r 2 ^ 2 * (oddDRatioTwo r * constituentStepTwo r) := by ring
      _ = typeDDefiningDimension r 2 ^ 2 *
          (oddDRatioTwo (r + 1) * definingStepTwo r ^ 2) := by
        rw [ratioTwo_step_identity r (by exact_mod_cast hr)]
      _ = _ := by ring

/-- The first displayed Weyl ratio follows from the full positive-root product
in every rank `r ≥ 2`.  No dimension-ratio identity is assumed. -/
theorem typeD_weyl_ratio_one (r : ℕ) (hr : 2 ≤ r) :
    4 * typeDConstituentDimension r 1 / typeDDefiningDimension r 1 ^ 2 =
      oddDRatioOne r := by
  apply (div_eq_iff (pow_ne_zero 2 (ne_of_gt (definingDimension_one_pos r hr)))).2
  exact ratioOne_cross_product r hr

/-- The second displayed Weyl ratio, also derived for every rank `r ≥ 2`. -/
theorem typeD_weyl_ratio_two (r : ℕ) (hr : 2 ≤ r) :
    4 * typeDConstituentDimension r 2 / typeDDefiningDimension r 2 ^ 2 =
      oddDRatioTwo r := by
  apply (div_eq_iff (pow_ne_zero 2 (ne_of_gt (definingDimension_two_pos r hr)))).2
  exact ratioTwo_cross_product r hr

private theorem definingStepOne_growth (r : ℚ) (hr : 3 ≤ r) :
    (r + 1) * (2 * (r + 1) - 1) ≤ r * (2 * r - 1) * definingStepOne r := by
  have hrpos : 0 < r := by linarith
  have hlast : 0 < 3 * r - 4 := by linarith
  unfold definingStepOne
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < r * (r + 2))).2
  have hp : 0 ≤ r * (r + 1) * (2 * r + 1) * (3 * r - 4) := by positivity
  nlinarith only [hp]

private theorem definingStep_one_le_two (r : ℚ) (hr : 0 < r) :
    definingStepOne r ≤ definingStepTwo r := by
  unfold definingStepOne definingStepTwo
  apply (div_le_div_iff₀ (by positivity : 0 < r * (r + 2))
    (by positivity : 0 < r * (r + 3) * (r + 4))).2
  have hp : 0 ≤ 2 * r * (2 * r + 1) * (3 * r ^ 3 + 14 * r ^ 2 + 21 * r + 12) := by
    positivity
  nlinarith only [hp]

/-- A dimension lower bound obtained directly from the Weyl product. -/
theorem typeD_weyl_dimension_one_lower_bound (r : ℕ) (hr : 3 ≤ r) :
    (r : ℚ) * (2 * r - 1) ≤ typeDDefiningDimension r 1 := by
  induction r, hr using Nat.le_induction with
  | base =>
    norm_num [typeDDefiningDimension, typeDWeylProduct, typeDWeylFactor,
      typeDDefiningCoordinates, Finset.prod_range_succ]
  | succ r hr ih =>
    rw [definingDimension_one_step r (by omega)]
    push_cast
    exact (definingStepOne_growth r (by exact_mod_cast hr)).trans
      (mul_le_mul_of_nonneg_right ih
        (le_of_lt (definingStepOne_pos r (by exact_mod_cast (by omega : 0 < r)))))

private theorem definingDimension_one_le_two (r : ℕ) (hr : 2 ≤ r) :
    typeDDefiningDimension r 1 ≤ typeDDefiningDimension r 2 := by
  induction r, hr using Nat.le_induction with
  | base =>
    norm_num [typeDDefiningDimension, typeDWeylProduct, typeDWeylFactor,
      typeDDefiningCoordinates, Finset.prod_range_succ]
  | succ r hr ih =>
    rw [definingDimension_one_step r (by omega), definingDimension_two_step r (by omega)]
    have hrpos : (0 : ℚ) < r := by exact_mod_cast (by omega : 0 < r)
    exact (mul_le_mul_of_nonneg_right ih (le_of_lt (definingStepOne_pos r hrpos))).trans
      (mul_le_mul_of_nonneg_left (definingStep_one_le_two r hrpos)
        (le_of_lt (definingDimension_two_pos r hr)))

/-- The same lower bound for the second candidate, also proved from its product. -/
theorem typeD_weyl_dimension_two_lower_bound (r : ℕ) (hr : 3 ≤ r) :
    (r : ℚ) * (2 * r - 1) ≤ typeDDefiningDimension r 2 :=
  (typeD_weyl_dimension_one_lower_bound r hr).trans
    (definingDimension_one_le_two r (by omega))

/-- The first candidate's exterior-square dimension exceeds the adjoint and
proposed dual pair in every rank `r ≥ 5`, directly from the Weyl products. -/
theorem typeD_weyl_exterior_gap_one (r : ℕ) (hr : 5 ≤ r) :
    (r : ℚ) * (2 * r - 1) + 2 * typeDConstituentDimension r 1 <
      typeDDefiningDimension r 1 * (typeDDefiningDimension r 1 - 1) / 2 := by
  have h := oddD_dimension_gap_one r (typeDDefiningDimension r 1)
    (typeDConstituentDimension r 1) (by exact_mod_cast hr)
    (typeD_weyl_dimension_one_lower_bound r (by omega))
    (typeD_weyl_ratio_one r (by omega))
  linarith

/-- The second candidate's unconditional all-rank Weyl-product gap. -/
theorem typeD_weyl_exterior_gap_two (r : ℕ) (hr : 5 ≤ r) :
    (r : ℚ) * (2 * r - 1) + 2 * typeDConstituentDimension r 2 <
      typeDDefiningDimension r 2 * (typeDDefiningDimension r 2 - 1) / 2 := by
  have h := oddD_dimension_gap_two r (typeDDefiningDimension r 2)
    (typeDConstituentDimension r 2) (by exact_mod_cast hr)
    (typeD_weyl_dimension_two_lower_bound r (by omega))
    (typeD_weyl_ratio_two r (by omega))
  linarith

end CubicAnomaly.Classification.Classical
