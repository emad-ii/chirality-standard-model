import CubicAnomaly.Classification.RootClassificationReflection
import CubicAnomaly.Classification.Selection

/-!
# Column-kernel tests for exceptional toral assignments

An explicit integral vector annihilating all grade-zero roots excludes
full zero-root rank. Integer row elimination on the grade-one cubic proves
triviality of its rational kernel whenever it produces a row supported at
each single column. Only the checked witnesses enter these implications.
-/

namespace CubicAnomaly.Classification.RootClassificationExceptional

open Matrix
open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.Selection
variable {n : ℕ}

private def dotZ (x y : Vector ℤ n) : ℤ := ∑ i, x.get i * y.get i

private def combine (a : ℤ) (v : Vector ℤ n) (b : ℤ) (w : Vector ℤ n) :=
  Vector.ofFn fun i => a * v.get i - b * w.get i

/- Start with the standard basis. Each root imposes one equation on the
current list of candidate null vectors. The output is independently tested
against every original root before it is used. -/
private def cutCandidates (vs : List (Vector ℤ n)) (r : Vector ℤ n) : List (Vector ℤ n) :=
  match vs.find? (fun v => dotZ r v != 0) with
  | none => vs
  | some p =>
    let t := dotZ r p
    vs.filterMap fun v =>
      if v == p then none else
        let u := dotZ r v
        some (if u = 0 then v else combine t v u p)

private def nullCandidate (rows : List (Vector ℤ n)) : Vector ℤ n :=
  let init := (List.finRange n).map (fun i => Vector.ofFn (Pi.single i (1 : ℤ)))
  (rows.foldl cutCandidates init).headD (Vector.replicate n 0)

private def rawRoots (d : RootDatum) : List (Vector ℤ d.cartan.size) :=
  (roots d).toList.map fun r => Vector.ofFn fun i : Index d => r[i.val]!

private def residue (a : Fin n → ZMod 3) (r : Vector ℤ n) : ZMod 3 :=
  ∑ i, (r.get i : ZMod 3) * a i

private def ZeroWitness (zs : List (Vector ℤ n)) (z : Finset (Vector ℤ n)) : Prop :=
  let w := nullCandidate zs
  (∃ i : Fin n, w.get i ≠ 0) ∧ ∀ v ∈ z, dotZ v w = 0

private instance (zs : List (Vector ℤ n)) (z : Finset (Vector ℤ n)) : Decidable (ZeroWitness zs z) := by
  unfold ZeroWitness
  infer_instance

/- Fraction-free elimination retaining the pivot row. The kernel soundness
argument works for any chosen pivot. -/
private def eliminate (rows : List (Vector ℤ n)) (i : Fin n) : List (Vector ℤ n) :=
  match rows.find? (fun r => r.get i != 0 && (List.finRange n).all
      (fun j => decide (i ≤ j) || r.get j == 0)) with
  | none => rows
  | some p => rows.map fun r =>
      if r = p ∨ r.get i = 0 then r else combine (p.get i) r (r.get i) p

private def diagRows (rows : List (Vector ℤ n)) := (List.finRange n).foldl eliminate rows

private def Separates (rows : List (Vector ℤ n)) : Prop :=
  let reduced := diagRows rows
  ∀ i : Fin n, ∃ r ∈ reduced, r.get i ≠ 0 ∧ ∀ j : Fin n, j ≠ i → r.get j = 0

private instance (rows : List (Vector ℤ n)) : Decidable (Separates rows) := by
  unfold Separates
  infer_instance

private def evalQ (r : Vector ℤ n) (x : Fin n → ℚ) : ℚ := ∑ i, (r.get i : ℚ) * x i

private theorem evalQ_combine (a : ℤ) (v : Vector ℤ n) (b : ℤ) (w : Vector ℤ n) (x : Fin n → ℚ) :
    evalQ (combine a v b w) x = a * evalQ v x - b * evalQ w x := by
  simp [evalQ, combine, Vector.get, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

private theorem eliminate_preserves_null (rows : List (Vector ℤ n)) (i : Fin n) (x : Fin n → ℚ)
    (hx : ∀ r ∈ rows, evalQ r x = 0) : ∀ r ∈ eliminate rows i, evalQ r x = 0 := by
  unfold eliminate
  split
  · exact hx
  · rename_i p hp
    have hp' := hx p (List.mem_of_find?_eq_some hp)
    intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    split
    · exact hx r hr
    · simp [evalQ_combine, hx r hr, hp']

private theorem separates_kernel (rows : List (Vector ℤ n)) (hf : Separates rows)
    (x : Fin n → ℚ) (hx : ∀ r ∈ rows, evalQ r x = 0) : x = 0 := by
  have hfold (is : List (Fin n)) (rs : List (Vector ℤ n))
      (hrs : ∀ r ∈ rs, evalQ r x = 0) : ∀ r ∈ is.foldl eliminate rs, evalQ r x = 0 := by
    induction is generalizing rs with
    | nil => exact hrs
    | cons i is ih => exact ih _ (eliminate_preserves_null rs i x hrs)
  funext i
  obtain ⟨r, hr, hi, hj⟩ := hf i
  have h := hfold (List.finRange n) rows hx r hr
  rw [evalQ, Finset.sum_eq_single i (fun j _ hji => by simp [hj j hji]) (by simp)] at h
  exact (mul_eq_zero.mp h).resolve_left (Int.cast_ne_zero.mpr hi)

private def cubicRows (roots₁ : Finset (Vector ℤ n)) : List (Vector ℤ n) :=
  (List.finRange n).flatMap fun j => (List.finRange n).map fun k =>
    Vector.ofFn fun i => ∑ v : ↥roots₁, v.val.get i * v.val.get j * v.val.get k

private theorem cubic_rows_kernel {d : RootDatum} {a : Index d → ZMod 3}
    {x : Index d → ℚ} (hx : ((censusCubicMatrix d a 1).map (Int.cast : ℤ → ℚ)) *ᵥ x = 0) :
    ∀ r ∈ cubicRows (gradeTable d a 1), evalQ r x = 0 := by
  intro r hr
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hr
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj
  simpa [evalQ, Vector.get, censusCubicMatrix, mulVec, dotProduct] using congrFun hx (j,k)

private def Checked (rs : List (Vector ℤ n)) (t : Finset (Vector ℤ n)) (a : Fin n → ZMod 3) : Prop :=
  let z := t.filter fun v => residue a v = 0
  let o := t.filter fun v => residue a v = 1
  a = 0 ∨ (n = 8 ∧ z.card = 78 ∧ o.card = 81) ∨
    ZeroWitness (rs.filter fun r => residue a r = 0) z ∨ Separates (cubicRows o)

private instance (rs : List (Vector ℤ n)) (t : Finset (Vector ℤ n)) (a : Fin n → ZMod 3) :
    Decidable (Checked rs t a) := by
  unfold Checked
  infer_instance

private def encode (a : Fin n → ZMod 3) : ℕ :=
  (List.finRange n).foldl (fun acc i => 3 * acc + (a i).val) 0

private def depth (levels : Array ℕ) (a : Fin n → ZMod 3) : ℕ :=
  levels[encode a]?.getD (3 ^ n)

/- This search proposes a decreasing score under simple reflection. Every
descent is independently checked below. The proof uses no completeness
assumption about breadth-first search or about the proposed seeds. -/
private def levels (d : RootDatum) : Array ℕ := Id.run do
  let n := d.cartan.size
  let size := 3 ^ n
  let mut result := Array.replicate size size
  for seed in [:size] do
    if result[seed]! == size then
      let initial := Vector.ofFn fun i : Fin n => (((seed / 3 ^ (n - 1 - i.val)) % 3 : ℕ) : ZMod 3)
      let mut queue := #[initial]
      let mut cursor := 0
      result := result.set! seed 0
      for _ in [:size] do
        if hc : cursor < queue.size then
          let x := queue[cursor]
          cursor := cursor + 1
          let score := depth result x.get
          for i in List.finRange n do
            let y := Vector.ofFn (reflectDual d i x.get)
            let k := encode y.get
            if result[k]! == size then
              result := result.set! k (score + 1)
              queue := queue.push y
        else
          break
  return result

/-- Each assignment has a verified descending simple reflection or an
independently checked obstruction or surviving pair of grade counts. -/
@[noinline] private def allChecked (d : RootDatum) (ls : Array ℕ)
    (rs : List (Vector ℤ d.cartan.size)) (t : Finset (Vector ℤ d.cartan.size)) : Bool :=
  decide (∀ a, (∃ i, depth ls (reflectDual d i a) < depth ls a) ∨ Checked rs t a)

private def certifiedChecks (d : RootDatum) : Bool := allChecked d (levels d) (rawRoots d) (table d)

private theorem checked_g2 : certifiedChecks g2Datum = true := by native_decide
private theorem checked_f4 : certifiedChecks f4Datum = true := by native_decide
private theorem checked_e6 : certifiedChecks e6Datum = true := by native_decide
private theorem checked_e7 : certifiedChecks e7Datum = true := by native_decide
private theorem checked_e8 : certifiedChecks e8Datum = true := by native_decide

/-- Direct exhaustive selection over every assignment, with no orbit,
graph-connectivity, or membership-in-a-census-row assumption. -/
theorem exceptional_assignment_selection {d : RootDatum} (hd : IsExceptionalCensusDatum d)
    (a : Index d → ZMod 3) (ha : a ≠ 0)
    (hsep : ∀ w : Vector ℤ d.cartan.size, (∀ v ∈ gradeTable d a 0,
      ∑ i, v.get i * w.get i = 0) → ∀ i, w.get i = 0)
    (hker : ∃ x : Index d → ℚ, x ≠ 0 ∧
      ((censusCubicMatrix d a 1).map (Int.cast : ℤ → ℚ)) *ᵥ x = 0) :
    d = e8Datum ∧ (gradeTable d a 0).card = 78 ∧ (gradeTable d a 1).card = 81 := by
  have htables : certifiedChecks d = true := by
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact checked_g2
    · exact checked_f4
    · exact checked_e6
    · exact checked_e7
    · exact checked_e8
  have descend := (of_decide_eq_true htables : ∀ a,
    (∃ i, depth (levels d) (reflectDual d i a) < depth (levels d) a) ∨ Checked (rawRoots d) (table d) a)
  induction hn : depth (levels d) a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rcases descend a with ⟨i, hi⟩ | hc
    · obtain ⟨ha', hs', hk'⟩ := reflect_admissible hd i (show Admissible d a from ⟨ha, hsep, hker⟩)
      obtain ⟨he, h0, h1⟩ := ih _ (hi.trans_eq hn) _ ha' hs' hk' rfl
      exact ⟨he, (reflect_grade_card hd i a 0).trans h0, (reflect_grade_card hd i a 1).trans h1⟩
    rcases hc with hzero | ⟨hrank, hcounts⟩ | hw | hrows
    · exact (ha hzero).elim
    · refine ⟨?_, hcounts⟩
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> first | rfl | contradiction
    · obtain ⟨⟨i, hi⟩, hv⟩ := hw
      exact (hi (hsep _ hv i)).elim
    · obtain ⟨x, hx, hAx⟩ := hker
      exact (hx (separates_kernel _ hrows x (cubic_rows_kernel hAx))).elim

end CubicAnomaly.Classification.RootClassificationExceptional
