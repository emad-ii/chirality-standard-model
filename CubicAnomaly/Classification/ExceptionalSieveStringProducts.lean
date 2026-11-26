import CubicAnomaly.Classification.ExceptionalSieveStringCatalog

/-!
# Exceptional candidates under simple-string dimension bounds

The dimension of the ambient algebra fixes the total module dimension. Each
simple constituent contributes its own long-coroot trace test and its computed
string lower bound. Their product may fall short of the dimension. All factor
orders and all dominant labels under the bounds are included.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveStringProducts

open ExceptionalSieveCatalog ExceptionalSieveProducts
open ExceptionalSieveStringCatalog

/-- The dimension entry records the lower bound obtained by lowering in
distinct simple directions. -/
def stringRow (t : Factor) (a : t.Label) : Row :=
  ⟨t, List.ofFn a, lower t a, t.casimir a⟩

private def types : List Factor :=
  (List.finRange 7).map .a ++ (List.finRange 6).map .b ++ (List.finRange 6).map .c ++
    (List.finRange 4).map .d ++ [.g2, .f4, .e6, .e7]

private def stringCatalog : List Row :=
  types.flatMap fun t => ((labels t).filter (fun a => decide (a ≠ 0))).map (stringRow t)

private theorem stringRow_mem (t : Factor) (a : t.Label) (hne : a ≠ 0)
    (hl : lower t a ≤ 121) (ha : ∀ i, a i ≤ 121) : stringRow t a ∈ stringCatalog := by
  have ht : t ∈ types := by cases t <;> simp [types]
  exact List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨a, List.mem_filter.mpr
    ⟨label_mem_of_lower _ _ hl ha, decide_eq_true hne⟩, rfl⟩⟩

private def options (g : Ambient) (n : ℕ) : List Row :=
  stringCatalog.filter (fun r => decide (0 < r.dimension ∧ r.dimension ≤ n ∧ Compatible g n r))

private def stop (h : ℕ) : List (List Row) := if h = 0 then [[]] else []

private def products (xs : List Row) : ℕ → ℕ → ℕ → ℕ → List (List Row)
  | 0, _, h, _ => stop h
  | fuel + 1, n, h, rank =>
    stop h ++ xs.flatMap fun r =>
      if r.factor.rank ≤ rank ∧ r.factor.algebraDim ≤ h ∧ r.dimension ≤ n then
        (products xs fuel (n / r.dimension) (h - r.factor.algebraDim) (rank - r.factor.rank)).map (r :: ·)
      else []

private def results (g : Ambient) (n : ℕ) :=
  products (options g n) (g.rank - 1) n (g.dimension - 2*n) (g.rank - 1)

/-- All non-self-opposite products surviving the string bounds and index
test. Both half orientations and all factor orderings are retained. -/
def remaining (g : Ambient) (n : ℕ) : Finset (List Key) :=
  if g = .f4 ∧ n = 22 then {[(.a 1, [0,3])], [(.a 1, [3,0])]}
  else if g = .e6 ∧ n = 35 then {[(.a 1, [1,4])], [(.a 1, [4,1])]}
  else if g = .e7 ∧ n = 52 then
    {[(.a 1,[0,3]), (.b 1,[0,0,1])], [(.a 1,[3,0]), (.b 1,[0,0,1])],
     [(.b 1,[0,0,1]), (.a 1,[0,3])], [(.b 1,[0,0,1]), (.a 1,[3,0])]}
  else ∅

private theorem exact_results : ∀ (g : Ambient) (n : Fin 122),
    (if 2*n.val ≤ g.dimension then
      (((results g n).map keys).filter fun ks => ks.any (fun k => dualLabels k != k.2)).toFinset
      else ∅) = remaining g n := by native_decide

private theorem products_complete (xs : List Row) (rs : List Row) (fuel rank n : ℕ)
    (hmem : ∀ r ∈ rs, r ∈ xs ∧ 0 < r.dimension) (hlen : rs.length ≤ fuel)
    (hrank : (rs.map fun r => r.factor.rank).sum ≤ rank)
    (hbound : (rs.map Row.dimension).prod ≤ n) :
    rs ∈ products xs fuel n (rs.map (fun r => r.factor.algebraDim)).sum rank := by
  induction rs generalizing fuel rank n with
  | nil => cases fuel <;> simp [products, stop]
  | cons r rs ih =>
    cases fuel with
    | zero => simp at hlen
    | succ fuel =>
      obtain ⟨hr, hp⟩ := hmem r (List.mem_cons_self ..)
      have htail : 0 < (rs.map Row.dimension).prod := by
        apply List.prod_pos
        intro x hx
        obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
        exact (hmem u (List.mem_cons_of_mem _ hu)).2
      simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons] at *
      have hdn : r.dimension ≤ n := (Nat.le_mul_of_pos_right _ htail).trans hbound
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨r, hr, ?_⟩
      rw [if_pos ⟨by omega, Nat.le_add_right .., hdn⟩, Nat.add_sub_cancel_left]
      exact List.mem_map.mpr ⟨rs, ih _ _ _ (fun u hu => hmem u (List.mem_cons_of_mem _ hu))
        (by omega) (by omega) ((Nat.le_div_iff_mul_le hp).mpr ((Nat.mul_comm ..) ▸ hbound)), rfl⟩

/-- Completeness of the relaxed search for any list of actual factor labels.
The trace compatibility here is exactly the existing actual-index interface. -/
theorem compatible_string_products (g : Ambient) (n : ℕ) (fs : List LabelledFactor)
    (hf : ∀ f ∈ fs, f.2 ≠ 0 ∧ 0 < lower f.1 f.2 ∧ lower f.1 f.2 ≤ n ∧ ∀ i, f.2 i ≤ 121)
    (hn : n ≤ 121)
    (hr : (fs.map fun f => f.1.rank).sum < g.rank)
    (hd : g.dimension = (fs.map fun f => f.1.algebraDim).sum + 2*n)
    (hp : (fs.map fun f => lower f.1 f.2).prod ≤ n)
    (hi : ∀ f ∈ fs, Compatible g n (row f.1 f.2))
    (hdual : ∃ k ∈ keys (fs.map fun f => stringRow f.1 f.2), dualLabels k ≠ k.2) :
    keys (fs.map fun f => stringRow f.1 f.2) ∈ remaining g n := by
  let rs := fs.map (fun f => stringRow f.1 f.2)
  have hopt (r : Row) (h : r ∈ rs) : r ∈ options g n ∧ 0 < r.dimension := by
    obtain ⟨f,hm,rfl⟩ := List.mem_map.mp h
    obtain ⟨hne,hl₀,hl,ha⟩ := hf f hm
    exact ⟨List.mem_filter.mpr ⟨stringRow_mem _ _ hne (hl.trans hn) ha,
      decide_eq_true ⟨hl₀, hl, hi f hm⟩⟩, hl₀⟩
  have length_bound (xs : List LabelledFactor) : xs.length ≤ (xs.map fun f => f.1.rank).sum := by
    induction xs with
    | nil => simp
    | cons f xs ih =>
      have hpos (t : Factor) : 0 < t.rank := by cases t <;> simp [Factor.rank]
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have := hpos f.1
      omega
  have hlen : rs.length ≤ (fs.map fun f => f.1.rank).sum := by simpa [rs] using length_bound fs
  have hsum : (rs.map (fun r => r.factor.rank)).sum < g.rank := by simpa [rs, List.map_map, Function.comp_def, stringRow] using hr
  have halg : g.dimension - 2*n = (rs.map (fun r => r.factor.algebraDim)).sum := by
    simp only [rs,List.map_map, Function.comp_def, stringRow]
    omega
  have hprod : (rs.map Row.dimension).prod ≤ n := by simpa [rs, List.map_map, Function.comp_def, stringRow] using hp
  have hres : rs ∈ results g n := by
    unfold results
    rw [halg]
    exact products_complete _ _ _ _ _ hopt (by omega) (by omega) hprod
  have he := exact_results g ⟨n, by omega⟩
  rw [if_pos (show 2*n ≤ g.dimension by omega)] at he
  apply he ▸ List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_map_of_mem hres, ?_⟩)
  obtain ⟨k,hk,hh⟩ := hdual
  exact List.any_eq_true.mpr ⟨k,hk, by simpa using hh⟩

end CubicAnomaly.Classification.ExceptionalSieveStringProducts
