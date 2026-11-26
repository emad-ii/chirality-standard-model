import CubicAnomaly.Classification.CommonCartan
import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Generation by simple root vectors

For a splitting Cartan in a Killing Lie algebra, one nonzero vector in
each signed simple root space generates the full algebra. Opposite simple
root spaces contain the raising and lowering elements of an actual
`sl₂` triple, so the generated subalgebra contains every simple coroot.
Induction by addition of simple roots generates all remaining root spaces.
-/

namespace CubicAnomaly.Classification.ChevalleyRootGeneration

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open CubicAnomaly.Classification.CommonCartan

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

omit [CharZero K] in
private theorem neg_root_nonzero (α : H.root) : rootSpace H (-(α.val : H → K)) ≠ ⊥ := by
  exact (-α.val).genWeightSpace_ne_bot

/-- A subalgebra containing one nonzero vector in each signed simple root
space of an actual splitting Cartan is the full Lie algebra. -/
theorem eq_top_of_simple_root_vectors (S : LieSubalgebra K L)
    (e f : b.support → L)
    (he : ∀ i, e i ∈ rootSpace H i.val.val) (hne : ∀ i, e i ≠ 0)
    (hf : ∀ i, f i ∈ rootSpace H (-(i.val.val : H → K))) (hnf : ∀ i, f i ≠ 0)
    (heS : ∀ i, e i ∈ S) (hfS : ∀ i, f i ∈ S) : S = ⊤ := by
  let roots := containedRoots H S.toSubmodule
  have hs (i : b.support) : (i.val.val : H → K) ∈ roots ∧ -(i.val.val : H → K) ∈ roots := by
    have hroot : (i.val.val : H → K) ≠ 0 := (Finset.mem_filter.mp i.val.property).2
    exact ⟨⟨hroot, i.val.val.genWeightSpace_ne_bot,
        root_space_le_of_nonzero_mem H S.toSubmodule hroot (he i) (heS i) (hne i)⟩,
      ⟨neg_ne_zero.mpr hroot, neg_root_nonzero H i.val,
        root_space_le_of_nonzero_mem H S.toSubmodule (neg_ne_zero.mpr hroot) (hf i) (hfS i) (hnf i)⟩⟩
  have hH : H ≤ S := by
    intro t ht
    let z : H := ⟨t, ht⟩
    have hcart (i : b.support) : ((b.toCoweightBasis i : H) : L) ∈ S := by
      obtain ⟨s, u, v, tri, hu, hv⟩ := exists_isSl2Triple_of_weight_isNonZero (hs i).1.1
      rw [b.toCoweightBasis_apply]
      change (coroot i.val.val : L) ∈ S
      rw [← tri.h_eq_coroot (hs i).1.1 hu hv, ← tri.lie_e_f]
      exact S.lie_mem ((hs i).1.2.2 hu) ((hs i).2.2.2 hv)
    change (z : L) ∈ S
    rw [← b.toCoweightBasis.sum_repr z]
    simpa using S.toSubmodule.sum_mem fun i (_ : i ∈ Finset.univ) =>
      S.smul_mem ((b.toCoweightBasis.repr z) i) (hcart i)
  have hall (α : H.root) : (α.val : H → K) ∈ roots ∧ -(α.val : H → K) ∈ roots := by
    apply b.induction_add α
    · intro i hi
      have hneg : (((rootSystem H).reflectionPerm i i).val : H → K) = -(i.val : H → K) :=
        congrArg DFunLike.coe ((rootSystem H).root_reflectionPerm i i |>.trans
          ((rootSystem H).reflection_apply_self i))
      simpa only [hneg, neg_neg] using And.intro hi.2 hi.1
    · exact fun i hi => hs ⟨i, hi⟩
    · intro i j k hij hi hj
      have hk : (k.val : H → K) = (i.val : H → K) + (j.val : H → K) :=
        congrArg DFunLike.coe hij
      have hn : -(k.val : H → K) = -(i.val : H → K) + -(j.val : H → K) := by rw [hk, neg_add]
      have hk0 : (k.val : H → K) ≠ 0 := (Finset.mem_filter.mp k.property).2
      constructor
      · rw [hk]
        exact contained_roots_add H S hi.1 (hs ⟨j,hj⟩).1 (hk ▸ ⟨hk0, k.val.genWeightSpace_ne_bot⟩)
      · rw [hn]
        exact contained_roots_add H S hi.2 (hs ⟨j,hj⟩).2
          (hn ▸ ⟨neg_ne_zero.mpr hk0, neg_root_nonzero H k⟩)
  apply top_unique
  change (⊤ : LieSubalgebra K L).toSubmodule ≤ S.toSubmodule
  rw [subalgebra_eq_root_decomposition H ⊤ le_top]
  refine sup_le hH (iSup_le fun a => iSup_le fun ha => ?_)
  let α : H.root := ⟨Weight.mk a ha.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.1⟩⟩
  exact (hall α).1.2.2

/-- The positive and negative simple-root vectors alone generate the
actual Lie algebra. In particular no additional Cartan generators are required. -/
theorem lieSpan_simple_root_vectors_eq_top (e f : b.support → L)
    (he : ∀ i, e i ∈ rootSpace H i.val.val) (hne : ∀ i, e i ≠ 0)
    (hf : ∀ i, f i ∈ rootSpace H (-(i.val.val : H → K))) (hnf : ∀ i, f i ≠ 0) :
    LieSubalgebra.lieSpan K L (Set.range e ∪ Set.range f) = ⊤ :=
  eq_top_of_simple_root_vectors H b _ e f he hne hf hnf
    (fun i => LieSubalgebra.subset_lieSpan (Or.inl ⟨i, rfl⟩)) (fun i => LieSubalgebra.subset_lieSpan (Or.inr ⟨i, rfl⟩))

end CubicAnomaly.Classification.ChevalleyRootGeneration
