import CubicAnomaly.Classification.RootSupportDimension
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Classification-free dimension and parity bounds

An actual root-system base divides the roots into positive and negative
pairs, and its simple roots form a basis of the Cartan dual. Consequently
the positive-root count is at least the Cartan dimension. The actual
root-space decomposition gives dimension at least three times the Cartan
dimension and the same parity as that dimension. In particular, a nonzero
even-dimensional Killing Lie algebra has dimension at least six.
-/

namespace CubicAnomaly.Classification.KillingDimension

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.RootSupportDimension

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

private def actualRootsEquiv : H.root ≃ containedRoots H (⊤ : Submodule K L) where
  toFun α := ⟨α.val, (Finset.mem_filter.mp α.property).2,
    α.val.genWeightSpace_ne_bot, le_top⟩
  invFun α := ⟨Weight.mk α.val α.property.2.1,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, α.property.1⟩⟩
  left_inv α := by apply Subtype.ext; apply Weight.ext; intro x; rfl
  right_inv α := by apply Subtype.ext; rfl

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
/-- Counting the actual function-valued roots agrees with counting the
actual root-system index type. -/
theorem actual_root_count_eq_card :
    (containedRoots H (⊤ : Submodule K L)).ncard = Fintype.card H.root := by
  have h := Nat.card_congr (actualRootsEquiv H)
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h
  exact h.symm

/-- The actual number of roots is twice the positive-root count, and that
count is at least the actual Cartan dimension. -/
theorem root_count_eq_twice_positive :
    ∃ n : ℕ, finrank K H ≤ n ∧
      (containedRoots H (⊤ : Submodule K L)).ncard = 2 * n := by
  classical
  obtain ⟨b⟩ := RootPairing.nonempty_base (rootSystem H)
  letI := (rootSystem H).indexNeg
  let E : {α : H.root // b.IsPos α} ≃ {α : H.root // ¬b.IsPos α} := {
    toFun := fun α => ⟨-α.val, fun hneg => ((RootPairing.Base.IsPos.neg_iff_not b α.val).mp hneg) α.property⟩
    invFun := fun α => ⟨-α.val, (RootPairing.Base.IsPos.neg_iff_not b α.val).mpr α.property⟩
    left_inv := fun α => Subtype.ext (neg_neg α.val)
    right_inv := fun α => Subtype.ext (neg_neg α.val) }
  have hcard := Fintype.card_congr E
  have htotal := Fintype.card_subtype_compl b.IsPos
  have hbound : Fintype.card b.support ≤ Fintype.card {α : H.root // b.IsPos α} := by
    apply Fintype.card_le_of_injective
      (fun α : b.support => (⟨α.val, b.isPos_of_mem_support α.property⟩ : {α // b.IsPos α}))
    intro α β h
    exact Subtype.ext (congrArg (fun z : {α : H.root // b.IsPos α} => z.val) h)
  have hbase : finrank K H = Fintype.card b.support := by
    rw [← Subspace.dual_finrank_eq]
    exact finrank_eq_card_basis b.toWeightBasis
  refine ⟨Fintype.card {α : H.root // b.IsPos α}, ?_, ?_⟩
  · rwa [hbase]
  · rw [actual_root_count_eq_card H]
    omega

/-- The dimension of the actual algebra is the Cartan dimension plus the
number of its actual roots. -/
theorem killing_finrank_eq_cartan_add_roots :
    finrank K L = finrank K H + (containedRoots H (⊤ : Submodule K L)).ncard := by
  have h := subalgebra_finrank_eq_cartan_add_root_count H ⊤ le_top
  change finrank K (⊤ : Submodule K L) = finrank K H +
    (containedRoots H (⊤ : Submodule K L)).ncard at h
  simpa only [finrank_top] using h

/-- The root-space count gives an exact dimension formula with at least
one positive root for each Cartan dimension. -/
theorem killing_dimension_eq_rank_add_twice :
    ∃ n : ℕ, finrank K H ≤ n ∧ finrank K L = finrank K H + 2 * n := by
  obtain ⟨n, hn, hcount⟩ := root_count_eq_twice_positive H
  exact ⟨n, hn, by rw [killing_finrank_eq_cartan_add_roots H, hcount]⟩

/-- Every actual splitting Cartan has at most one third of the dimension
of its finite-dimensional Killing algebra. -/
theorem three_cartan_finrank_le : 3 * finrank K H ≤ finrank K L := by
  obtain ⟨n, hn, hdim⟩ := killing_dimension_eq_rank_add_twice H
  omega

/-- Algebra and Cartan dimensions have the same parity because roots occur
in nonzero opposite pairs. -/
theorem killing_dimension_parity : finrank K L % 2 = finrank K H % 2 := by
  obtain ⟨n, _, hdim⟩ := killing_dimension_eq_rank_add_twice H
  omega

include H in
/-- A nonzero actual Killing Lie algebra has dimension at least three. -/
theorem nonzero_killing_dimension_ge_three [Nontrivial L] : 3 ≤ finrank K L := by
  have hpos : 0 < finrank K H := finrank_pos
  have hb := three_cartan_finrank_le H
  omega

include H in
/-- A nonzero actual Killing Lie algebra of even dimension has dimension
at least six. Dimensions two and four are excluded without a type list. -/
theorem nonzero_even_killing_dimension_ge_six [Nontrivial L]
    (heven : Even (finrank K L)) : 6 ≤ finrank K L := by
  have hpos : 0 < finrank K H := finrank_pos
  have hb := three_cartan_finrank_le H
  have hp := killing_dimension_parity H
  obtain ⟨k, hk⟩ := heven
  omega

end CubicAnomaly.Classification.KillingDimension
