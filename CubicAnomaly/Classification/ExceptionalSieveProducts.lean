import CubicAnomaly.Classification.ExceptionalSieveCatalog

/-!
# Dimension and index tests on arbitrary exceptional representation products

Apply the dimension equation and the ambient Killing-trace divisor to every
product of bounded dominant labels of smaller total rank. The test uses the
long-root Gram normalization of the label catalog. It allows third-integer
indices in E6 and quarter-integer indices in E7. All factor orderings are
included. The resulting five ordered products represent four unordered rows.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveProducts

open CubicAnomaly.Classification.ExceptionalSieveCatalog

inductive Ambient | g2 | f4 | e6 | e7 | e8 deriving DecidableEq, Fintype

namespace Ambient

def rank : Ambient → ℕ | .g2 => 2 | .f4 => 4 | .e6 => 6 | .e7 => 7 | .e8 => 8
def dimension : Ambient → ℕ | .g2 => 14 | .f4 => 52 | .e6 => 78 | .e7 => 133 | .e8 => 248
def divisor : Ambient → ℕ | .g2 => 16 | .f4 => 36 | .e6 => 16 | .e7 => 18 | .e8 => 120
end Ambient

structure Row where
  factor : Factor
  labels : List ℕ
  dimension : ℕ
  casimir : ℚ
  deriving DecidableEq

def row (t : Factor) (a : t.Label) : Row :=
  let roots := t.positiveCoroots
  ⟨t, List.ofFn a, Factor.numerator roots a / Factor.numerator roots 0, t.casimir a⟩

private def types : List Factor :=
  (List.finRange 7).map .a ++ (List.finRange 6).map .b ++ (List.finRange 6).map .c ++
    (List.finRange 4).map .d ++ [.g2, .f4, .e6, .e7]

private theorem mem_types (t : Factor) : t ∈ types := by cases t <;> simp [types]

/-- Nontrivial simple-factor rows at the common dimension cutoff. -/
def catalog : List Row :=
  types.flatMap fun t => (t.labels.filter (fun a => decide (a ≠ 0))).map (row t)

/-- Each nonzero dominant label satisfying the cutoff supplies its exact
Weyl-product dimension and normalized quadratic datum to the product search. -/
theorem row_mem_catalog (t : Factor) (a : t.Label) (ha : a ≠ 0) (hf : t.Fits a) :
    row t a ∈ catalog := by
  apply List.mem_flatMap.mpr
  exact ⟨t, mem_types t, List.mem_map.mpr ⟨a, List.mem_filter.mpr
    ⟨Factor.label_mem_of_fits t a hf, decide_eq_true ha⟩, rfl⟩⟩

/-- On a long coroot, the ambient adjoint trace predicted by the dimension
and Casimir formulas is 4 h∨ + 4 dim(V) (λ,λ+2ρ)/dim(hᵢ). -/
def indexQuotient (g : Ambient) (n : ℕ) (r : Row) : ℚ :=
  (4 * r.factor.dualCoxeter + 4 * n * r.casimir / r.factor.algebraDim) / g.divisor

def Compatible (g : Ambient) (n : ℕ) (r : Row) : Prop :=
  (indexQuotient g n r).den = 1

instance (g : Ambient) (n : ℕ) (r : Row) : Decidable (Compatible g n r) := by
  unfold Compatible
  infer_instance

private def options (g : Ambient) (n : ℕ) : List Row :=
  catalog.filter (fun r => decide (0 < r.dimension ∧ r.dimension ∣ n ∧ Compatible g n r))

private def stop (n h : ℕ) : List (List Row) :=
  if n = 1 ∧ h = 0 then [[]] else []

private def products (xs : List Row) : ℕ → ℕ → ℕ → ℕ → List (List Row)
  | 0, n, h, _ => stop n h
  | fuel + 1, n, h, rank =>
    stop n h ++ xs.flatMap fun r =>
      if r.factor.rank ≤ rank ∧ r.factor.algebraDim ≤ h ∧ r.dimension ∣ n then
        (products xs fuel (n / r.dimension) (h - r.factor.algebraDim) (rank - r.factor.rank)).map (r :: ·)
      else []

abbrev Key := Factor × List ℕ
def keys (rs : List Row) : List Key := rs.map (fun r => (r.factor, r.labels))

/-- The four unordered products surviving the relaxed numerical index restriction. -/
def survivors (g : Ambient) (n : ℕ) : Finset (List Key) :=
  if g = .e6 ∧ n = 35 then
    {[(.a 1,[1,4])], [(.a 1,[4,1])]}
  else if g = .e6 ∧ n = 36 then
    {[(.a 0,[1]), (.a 0,[17])], [(.a 0,[17]), (.a 0,[1])], [(.a 0,[5]), (.a 0,[5])]}
  else ∅

/-- Candidate sequences respecting the rank, dimension and trace tests. -/
def results (g : Ambient) (n : ℕ) :=
  products (options g n) (g.rank - 1) n (g.dimension - 2*n) (g.rank - 1)

/-- Exact positive and negative controls on the entire output, including
both orderings of the unequal factors. -/
theorem exact_product_sieve : ∀ (g : Ambient) (n : Fin 122),
    (if 2*n.val ≤ g.dimension then ((results g n).map keys).toFinset else ∅) =
      survivors g n := by native_decide

private theorem products_complete (xs : List Row) (rs : List Row) (fuel rank : ℕ)
    (hmem : ∀ r ∈ rs, r ∈ xs ∧ 0 < r.dimension) (hlen : rs.length ≤ fuel)
    (hrank : (rs.map fun r => r.factor.rank).sum ≤ rank) :
    rs ∈ products xs fuel (rs.map Row.dimension).prod
      (rs.map (fun r => r.factor.algebraDim)).sum rank := by
  induction rs generalizing fuel rank with
  | nil => cases fuel <;> simp [products, stop]
  | cons r rs ih =>
    cases fuel with
    | zero => simp at hlen
    | succ fuel =>
      obtain ⟨hr, hp⟩ := hmem r (List.mem_cons_self ..)
      simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons] at *
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨r, hr, ?_⟩
      rw [if_pos ⟨by omega, Nat.le_add_right .., dvd_mul_right ..⟩,
        Nat.mul_div_cancel_left _ hp, Nat.add_sub_cancel_left]
      exact List.mem_map.mpr ⟨rs, ih _ _ (fun u hu => hmem u (List.mem_cons_of_mem _ hu))
        (by omega) (by omega), rfl⟩

private theorem length_le_rank_sum (rs : List Row) :
    rs.length ≤ (rs.map fun r => r.factor.rank).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have hrpos (t : Factor) : 0 < t.rank := by cases t <;> simp [Factor.rank]
    have := hrpos r.factor
    omega

/-- Completeness for arbitrary products, with no ordering or enumeration
witness required of the input. Together with `row_mem_catalog` this test
covers every nonzero dominant label under the Weyl bound. -/
theorem every_compatible_product_survives (g : Ambient) (rs : List Row)
    (hm : ∀ r ∈ rs, r ∈ catalog ∧ 0 < r.dimension)
    (hr : (rs.map fun r => r.factor.rank).sum < g.rank)
    (hd : g.dimension = (rs.map fun r => r.factor.algebraDim).sum + 2 * (rs.map Row.dimension).prod)
    (hb : (rs.map Row.dimension).prod ≤ 121)
    (hi : ∀ r ∈ rs, Compatible g (rs.map Row.dimension).prod r) :
    keys rs ∈ survivors g (rs.map Row.dimension).prod := by
  let n := (rs.map Row.dimension).prod
  have hlen := length_le_rank_sum rs
  have hopt (r : Row) (h : r ∈ rs) : r ∈ options g n ∧ 0 < r.dimension := by
    obtain ⟨hc, hp⟩ := hm r h
    refine ⟨List.mem_filter.mpr ⟨hc, decide_eq_true ⟨hp, ?_, hi r h⟩⟩, hp⟩
    exact List.dvd_prod (List.mem_map_of_mem h)
  have hm' := products_complete (options g n) rs (g.rank - 1) (g.rank - 1) hopt
    (by omega) (by omega)
  have hresult : rs ∈ results g n := by
    unfold results
    rwa [show g.dimension - 2*n = (rs.map fun r => r.factor.algebraDim).sum by dsimp [n]; omega]
  have he := exact_product_sieve g ⟨n, by dsimp [n]; omega⟩
  rw [if_pos (show 2*n ≤ g.dimension by dsimp [n]; omega)] at he
  exact he ▸ (List.mem_toFinset.mpr (List.mem_map_of_mem hresult))

/-- Dynkin labels of the contragredient in the Cartan numbering of the catalog. -/
def dualLabels (key : Key) : List ℕ :=
  let xs := key.2
  match key.1 with
  | .a _ => xs.reverse
  | .d _ => if Odd key.1.rank then
      xs.take (key.1.rank - 2) ++ [xs[key.1.rank - 1]!, xs[key.1.rank - 2]!]
    else xs
  | .e6 => [xs[5]!, xs[1]!, xs[4]!, xs[3]!, xs[2]!, xs[0]!]
  | _ => xs

/-- For type A this is the centered shifted-row cubic, multiplied by
(rank+1)³ to clear all denominators. -/
def cubicZero (key : Key) : Bool :=
  match key.1 with
  | .a _ =>
    let n := key.1.rank + 1
    let shifted := (List.range n).map fun i => (key.2.drop i).sum + (n-1-i)
    let total := shifted.sum
    decide ((shifted.map fun x => ((n : ℤ) * x - total) ^ 3).sum = 0)
  | _ => true

/-- The four remaining unordered products fail either the dual-label test
or the cubic-zero test. The A1 pairs are self-dual; the two A2 cubics are
both nonzero. -/
theorem survivors_fail_label_filters : ∀ (g : Ambient) (n : Fin 122),
    ∀ ks ∈ survivors g n,
      ¬((∃ k ∈ ks, dualLabels k ≠ k.2) ∧ (∃ k ∈ ks, cubicZero k = true)) := by
  native_decide

abbrev LabelledFactor := (t : Factor) × t.Label

/-- The exceptional numerical sieve is empty for arbitrary lists of
dominant highest-weight labels satisfying the paper's dimension, rank,
index, dual-label and cubic conditions. Coverage refers to unbounded input
labels; each bounded Weyl product is located by the completeness proof. -/
theorem no_exceptional_label_product (g : Ambient) (factors : List LabelledFactor)
    (hf : ∀ f ∈ factors, f.2 ≠ 0 ∧ f.1.Fits f.2) :
    let rs := factors.map (fun f => row f.1 f.2)
    let n := (rs.map Row.dimension).prod
    (rs.map (fun r => r.factor.rank)).sum < g.rank →
    g.dimension = (rs.map (fun r => r.factor.algebraDim)).sum + 2*n →
    n ≤ 121 → (∀ r ∈ rs, Compatible g n r) →
    (∃ k ∈ keys rs, dualLabels k ≠ k.2) → (∃ k ∈ keys rs, cubicZero k = true) → False := by
  intro rs n hr hd hb hi hdual hcubic
  have hm (r : Row) (h : r ∈ rs) : r ∈ catalog ∧ 0 < r.dimension := by
    obtain ⟨f, hmem, rfl⟩ := List.mem_map.mp h
    obtain ⟨hpos, hfit⟩ := hf f hmem
    exact ⟨row_mem_catalog _ _ hpos hfit,
      (Factor.bounded_label_catalog_sound _ _ (Factor.label_mem_of_fits _ _ hfit)).1⟩
  have hs := every_compatible_product_survives g rs hm hr hd hb hi
  exact survivors_fail_label_filters g ⟨n, by omega⟩ (keys rs) hs ⟨hdual, hcubic⟩

end CubicAnomaly.Classification.ExceptionalSieveProducts
