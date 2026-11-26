import CubicAnomaly.Classification.RootClassificationExceptional

/-!
# Complete bounded dominant-label catalog for the exceptional sieve

A factor of strictly smaller rank than an exceptional ambient has rank at
most seven. For every such simple Cartan type, compute the Weyl product on
the positive coroots and enumerate its sublevel set at 121. Completeness for
unbounded labels follows by decreasing one coordinate: the product is
monotone, and closure under every admissible single-label increment is checked
on the entire finite catalog. Independent multiplication verifies each
fundamental-weight Gram matrix against its Cartan matrix and root lengths.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveCatalog

open CubicAnomaly.Classification.Exceptional

inductive Factor where
  | a (node : Fin 7) | b (node : Fin 6) | c (node : Fin 6) | d (node : Fin 4)
  | g2 | f4 | e6 | e7
  deriving DecidableEq, Fintype

namespace Factor

def rank : Factor → ℕ
  | .a i => i + 1 | .b i | .c i => i + 2 | .d i => i + 4
  | .g2 => 2 | .f4 => 4 | .e6 => 6 | .e7 => 7

def algebraDim (t : Factor) : ℕ :=
  let r := t.rank
  match t with
  | .a _ => r * (r + 2) | .b _ | .c _ => r * (2 * r + 1)
  | .d _ => r * (2 * r - 1)
  | .g2 => 14 | .f4 => 52 | .e6 => 78 | .e7 => 133

def dualCoxeter (t : Factor) : ℕ :=
  let r := t.rank
  match t with
  | .a _ | .c _ => r + 1 | .b _ => 2 * r - 1 | .d _ => 2 * r - 2
  | .g2 => 4 | .f4 => 9 | .e6 => 12 | .e7 => 18

private def klass (r : ℕ) (c : ℕ → ℕ → ℤ) (len : ℕ → ℤ) : RootDatum :=
  { cartan := Array.ofFn fun i : Fin r => Array.ofFn fun j : Fin r => c i j
    symmetrizer := Array.ofFn fun i : Fin r => len i }

private def path (i j : ℕ) : ℤ :=
  if i = j then 2 else if i + 1 = j ∨ j + 1 = i then -1 else 0

def datum (t : Factor) : RootDatum :=
  let r := t.rank
  match t with
  | .a _ => klass r path (fun _ => 1)
  | .b _ => klass r (fun i j => if i + 2 = r ∧ j + 1 = r then -2 else path i j)
      (fun i => if i + 1 = r then 1 else 2)
  | .c _ => klass r (fun i j => if i + 1 = r ∧ j + 2 = r then -2 else path i j)
      (fun i => if i + 1 = r then 2 else 1)
  | .d _ => klass r (fun i j => if i = j then 2 else
      if i + 1 = r then (if j + 3 = r then -1 else 0)
      else if j + 1 = r then (if i + 3 = r then -1 else 0) else path i j) (fun _ => 1)
  | .g2 => g2Datum | .f4 => f4Datum | .e6 => e6Datum | .e7 => e7Datum

abbrev Node (t : Factor) := Fin t.rank
abbrev Label (t : Factor) := t.Node → ℕ

private def longLengthFactor : Factor → ℤ
  | .b _ | .c _ | .f4 => 2 | .g2 => 3 | _ => 1

/-- The transposed simple Cartan matrix with reciprocal root lengths. -/
def transposeDatum (t : Factor) : RootDatum :=
  klass t.rank (fun i j => ((datum t).cartan[j]!)[i]!)
    (fun i => t.longLengthFactor / ((datum t).symmetrizer[i]!))

def positiveCoroots (t : Factor) : List (t.Node → ℕ) :=
  ((roots (transposeDatum t)).toList.filter (fun v => v.all (0 ≤ ·))).map
    (fun v i => (v[i.val]!).toNat)

def numerator {t : Factor} (coroots : List (t.Node → ℕ)) (a : t.Label) : ℕ :=
  (coroots.map fun v => ∑ i, v i * (a i + 1)).prod

private theorem numerator_mono {t : Factor} (rows : List (t.Node → ℕ)) :
    Monotone (numerator rows) := by
  intro a b hab
  induction rows with
  | nil => simp [numerator]
  | cons v vs ih =>
    change (∑ i, v i * (a i + 1)) * numerator vs a ≤ (∑ i, v i * (b i + 1)) * numerator vs b
    exact Nat.mul_le_mul (Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.succ_le_succ (hab i))) ih

/-- All original and dual rank-at-most-seven Cartan root lists pass the
reflection and descent certificate. Root counts recover the algebra dimensions;
the adjoint squared trace on each long simple coroot is exactly 4 h∨. -/
theorem cartan_geometry : ∀ (t : Factor),
    RootClassificationExceptional.Certified t.datum ∧
    RootClassificationExceptional.Certified t.transposeDatum ∧
    t.rank + (roots t.datum).size = t.algebraDim ∧
    ∀ i : t.Node, t.datum.symmetrizer[i.val]! = t.longLengthFactor →
      (((roots t.datum).toList.map (fun v => (∑ j : t.Node,
        v[j.val]! * (t.datum.cartan[j.val]!)[i.val]!) ^ 2)).sum : ℤ) = 4 * t.dualCoxeter := by
  native_decide

/-- A division-free sublevel test for the Weyl product. -/
def Fits (t : Factor) (a : t.Label) : Prop :=
  numerator (positiveCoroots t) a ≤ 121 * numerator (positiveCoroots t) 0

instance (t : Factor) (a : t.Label) : Decidable (Fits t a) := by unfold Fits; infer_instance

private def search {t : Factor} (rows : List (t.Node → ℕ)) (bound : ℕ) :
    List t.Node → t.Label → List t.Label
  | [], lab => [lab]
  | i :: nodes, lab =>
    let vals := (List.range 121).takeWhile fun k => decide (numerator rows (Function.update lab i k) ≤ bound)
    vals.flatMap fun k => search rows bound nodes (Function.update lab i k)

/-- The finite catalog includes the zero label for the inductive completeness proof. -/
def labels (t : Factor) : List t.Label :=
  let rows := positiveCoroots t
  search rows (121 * numerator rows 0) (List.finRange _) 0

private def Closed (t : Factor) : Prop :=
  (0 : t.Label) ∈ labels t ∧
    ∀ a ∈ labels t, ∀ i : t.Node, Fits t (a + Pi.single i 1) → a + Pi.single i 1 ∈ labels t

private instance (t : Factor) : Decidable (Closed t) := by unfold Closed; infer_instance

private theorem closed_all : ∀ t : Factor, Closed t := by native_decide

/-- Every dominant label within the bound occurs, however large its input
coordinates. The finite successor certificate suffices because decreasing
an individual nonzero label can only decrease the numerator. -/
theorem label_mem_of_fits (t : Factor) (a : t.Label) (ha : Fits t a) : a ∈ labels t := by
  have hc := closed_all t
  induction n : ∑ i, a i using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hz : a = 0
    · simpa [hz] using hc.1
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by simpa [funext_iff] using hz
    let b := Function.update a i (a i - 1)
    have he : b + Pi.single i 1 = a := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [b, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]
      · simp [b, hj]
    have hb : Fits t b := by
      apply (numerator_mono (positiveCoroots t) (a := b) (b := a) ?_).trans ha
      intro j
      by_cases hj : j = i <;> simp [b, hj]
    have hlen := congrArg (fun x : t.Label => ∑ j, x j) he
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true] at hlen
    rw [n] at hlen
    have hm := ih (∑ j, b j) (by omega) b hb rfl
    exact he ▸ hc.2 b hm i (he ▸ ha)

/-- For each catalog label the Weyl product is an exact positive integer
at most 121. Integer division in the product search is therefore exact. -/
theorem bounded_label_catalog_sound : ∀ (t : Factor) (a : t.Label), a ∈ labels t →
    let rows := positiveCoroots t
    let N := numerator rows a / numerator rows 0
    0 < N ∧ N ≤ 121 ∧ numerator rows a = N * numerator rows 0 := by
  native_decide

private def g2Gram : Array (Array ℕ) := #[#[2,3], #[3,6]]
private def f4Gram : Array (Array ℕ) :=
  #[#[4,6,4,2], #[6,12,8,4], #[4,8,6,3], #[2,4,3,2]]
private def e6Gram : Array (Array ℕ) :=
  #[#[4,3,5,6,4,2], #[3,6,6,9,6,3], #[5,6,10,12,8,4], #[6,9,12,18,12,6],
    #[4,6,8,12,10,5], #[2,3,4,6,5,4]]
private def e7Gram : Array (Array ℕ) :=
  #[#[4,4,6,8,6,4,2], #[4,7,8,12,9,6,3], #[6,8,12,16,12,8,4],
    #[8,12,16,24,18,12,6], #[6,9,12,18,15,10,5], #[4,6,8,12,10,8,4],
    #[2,3,4,6,5,4,3]]

/-- Fundamental-weight Gram entries with the long roots of squared length two. -/
def gram (t : Factor) (i j : t.Node) : ℚ :=
  let r := t.rank
  let x := i.val + 1
  let y := j.val + 1
  let small : ℚ := min x y
  match t with
  | .a _ => small * ((r + 1 - max x y : ℕ) : ℚ) / (r + 1 : ℕ)
  | .b _ => small / (if x = r then 2 else 1) / (if y = r then 2 else 1)
  | .c _ => small / 2
  | .d _ => if x + 2 ≤ r ∧ y + 2 ≤ r then small else
      if x + 2 ≤ r ∨ y + 2 ≤ r then small / 2 else if x = y then (r : ℚ) / 4
      else ((r - 2 : ℕ) : ℚ) / 4
  | .g2 => ((g2Gram[i.val]!)[j.val]! : ℚ) / 3
  | .f4 => ((f4Gram[i.val]!)[j.val]! : ℚ) / 2
  | .e6 => ((e6Gram[i.val]!)[j.val]! : ℚ) / 3
  | .e7 => ((e7Gram[i.val]!)[j.val]! : ℚ) / 2

/-- Multiplication by the simple Cartan matrix gives the normalized
root-length diagonal: this checks every entry, including non-simply-laced
and spin-node conventions. -/
theorem fundamental_gram_normalization : ∀ (t : Factor) (i j : t.Node),
    gram t i j = gram t j i ∧
    (∑ k, ((((datum t).cartan[i.val]!)[k.val]! : ℤ) : ℚ) * gram t k j) =
      if i = j then (((datum t).symmetrizer[i.val]! : ℤ) : ℚ) / longLengthFactor t else 0 := by
  native_decide

/-- The doubled Casimir eigenvalue expression in dominant Dynkin labels. -/
def casimir (t : Factor) (a : t.Label) : ℚ :=
  ∑ i, ∑ j, a i * gram t i j * (a j + 2)

end Factor

end CubicAnomaly.Classification.ExceptionalSieveCatalog
