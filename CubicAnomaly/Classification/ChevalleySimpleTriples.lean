import CubicAnomaly.Classification.ChevalleyRootGeneration

/-!
# Simultaneous simple-root triples

For a base of the roots of a split Killing algebra, normalize raising and
lowering vectors by the actual simple coroots. Different positive and
negative simple-root vectors commute because their difference is neither
a root nor zero.
-/

namespace CubicAnomaly.Classification.ChevalleySimpleTriples

open LieAlgebra LieModule Module LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

/-- Distinct signed simple root spaces commute across the two signs. -/
theorem lie_simple_opposite_of_ne {i j : b.support} (hij : i ≠ j)
    {x y : L} (hx : x ∈ rootSpace H i.val.val) (hy : y ∈ rootSpace H (-(j.val.val : H → K))) :
    ⁅x, y⁆ = 0 := by
  let a := (i.val.val : H → K) - (j.val.val : H → K)
  have ha : a ≠ 0 := by
    intro h
    exact hij (Subtype.ext (Subtype.ext (Weight.ext (congrFun (sub_eq_zero.mp h)))))
  have hbot : rootSpace H a = ⊥ := by
    by_contra hn
    let α : H.root := ⟨Weight.mk a hn, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    exact b.sub_notMem_range_root i.property j.property ⟨α, by ext h; rfl⟩
  have hmem : ⁅x, y⁆ ∈ rootSpace H a := by
    simpa only [a, sub_eq_add_neg] using LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy
  simpa only [hbot, LieSubmodule.mem_bot] using hmem

/-- Simultaneous simple-root triples, their signed weights, the mixed
commutators, and generation by the two sets of root vectors. -/
theorem exists_simple_root_triples :
    ∃ e f : b.support → L,
      (∀ i, IsSl2Triple (coroot i.val.val : L) (e i) (f i)) ∧
      (∀ i, e i ∈ rootSpace H i.val.val) ∧
      (∀ i, f i ∈ rootSpace H (-(i.val.val : H → K))) ∧
      (∀ i j, i ≠ j → ⁅e i, f j⁆ = 0) ∧
      LieSubalgebra.lieSpan K L (Set.range e ∪ Set.range f) = ⊤ := by
  have hs (i : b.support) : ∃ e f : L,
      IsSl2Triple (coroot i.val.val : L) e f ∧ e ∈ rootSpace H i.val.val ∧
        f ∈ rootSpace H (-(i.val.val : H → K)) := by
    have hα : i.val.val.IsNonZero := (Finset.mem_filter.mp i.val.property).2
    obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
    exact ⟨e, f, ht.h_eq_coroot hα he hf ▸ ht, he, hf⟩
  choose e f ht he hf using hs
  exact ⟨e, f, ht, he, hf, fun i j hij => lie_simple_opposite_of_ne H b hij (he i) (hf j),
    ChevalleyRootGeneration.lieSpan_simple_root_vectors_eq_top H b e f he
      (fun i => (ht i).e_ne_zero) hf (fun i => (ht i).f_ne_zero)⟩

end CubicAnomaly.Classification.ChevalleySimpleTriples
