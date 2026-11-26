import CubicAnomaly.Classification.RootSupportDimension
import CubicAnomaly.Classification.WeightCubic

/-!
# The actual root-sum formula for a Cartan trace cubic

For a Cartan-stable ambient subspace disjoint from the Cartan, its actual
weights are exactly the ambient roots whose root spaces it contains. Each
weight has multiplicity one. The representation trace cubic is therefore
the unweighted sum of the three root evaluations used by a toral census.
No table of representation weights or multiplicities is supplied.
-/

namespace CubicAnomaly.Classification.RootSupportTrace

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.RootSupportDimension

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- Every actual weight of a Cartan-stable subspace with no zero weight is
an actual ambient root whose whole one-dimensional root space lies there. -/
theorem weight_mem_containedRoots (N : LieSubmodule K H L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule) (χ : Weight K H N) :
    (χ : H → K) ∈ containedRoots H N.toSubmodule := by
  obtain ⟨x, hx, hx0⟩ := χ.exists_ne_zero
  have hxL : (x : L) ≠ 0 := fun hz => hx0 (Subtype.ext hz)
  have hxroot : (x : L) ∈ rootSpace H χ :=
    map_genWeightSpace_le N.incl ((LieSubmodule.mem_map _).mpr ⟨x, hx, rfl⟩)
  have hχ : (χ : H → K) ≠ 0 := by
    intro hzero
    have hxH : (x : L) ∈ H := by
      simpa only [hzero, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hxroot
    have hm : (x : L) ∈ H.toSubmodule ⊓ N.toSubmodule := ⟨hxH, x.property⟩
    exact hxL (by simpa only [hdis.eq_bot, Submodule.mem_bot] using hm)
  exact ⟨hχ,
    by intro hb; exact hxL (by simpa only [hb, LieSubmodule.mem_bot] using hxroot),
    root_space_le_of_nonzero_mem H N.toSubmodule hχ hxroot x.property hxL⟩

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [IsTriangularizable K H L] in
private theorem supported_root_is_weight (N : LieSubmodule K H L)
    {α : H → K} (hα : α ∈ containedRoots H N.toSubmodule) :
    genWeightSpace N α ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Weight.mk α hα.2.1).exists_ne_zero
  have hxN : x ∈ N := hα.2.2 hx
  have hxweight : (⟨x, hxN⟩ : N) ∈ genWeightSpace N α := by
    rw [← comap_genWeightSpace_eq_of_injective (f := N.incl) Subtype.val_injective]
    exact hx
  intro hb
  rw [hb, LieSubmodule.mem_bot] at hxweight
  exact hx0 (congrArg Subtype.val hxweight)

/-- The actual weights are canonically identified with the actual supported
ambient roots. Both directions preserve the function on the Cartan. -/
def weightSupportEquiv (N : LieSubmodule K H L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule) :
    Weight K H N ≃ containedRoots H N.toSubmodule where
  toFun χ := ⟨χ, weight_mem_containedRoots H N hdis χ⟩
  invFun α := Weight.mk α.val (supported_root_is_weight H N α.property)
  left_inv χ := by apply Weight.ext; intro x; rfl
  right_inv α := by apply Subtype.ext; rfl

/-- Every actual generalized weight space of the root-space module has
multiplicity one; the module does not need to be irreducible. -/
theorem supported_weight_finrank_eq_one (N : LieSubmodule K H L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule) (χ : Weight K H N) :
    finrank K (genWeightSpace N χ) = 1 := by
  have hχ := weight_mem_containedRoots H N hdis χ
  have hmap : (genWeightSpace N χ).map N.incl = rootSpace H χ := by
    rw [map_genWeightSpace_eq_of_injective Subtype.val_injective, LieSubmodule.range_incl]
    exact inf_eq_left.mpr hχ.2.2
  have hdim := (LieSubmodule.equivMapOfInjective (genWeightSpace N χ)
    (f := N.incl) Subtype.val_injective).toLinearEquiv.finrank_eq
  rw [hmap] at hdim
  exact hdim.trans (finrank_rootSpace_eq_one (Weight.mk χ hχ.2.1) hχ.1)

/-- The cubic sum over actual contained roots, each counted once. -/
noncomputable def actualRootCubic (N : Submodule K L) (x y z : H) : K :=
  letI := (containedRoots_finite H N).fintype
  ∑ α : containedRoots H N, α.val x * α.val y * α.val z

/-- The actual trace of three Cartan action operators is the unweighted
cubic sum over the actual ambient roots in the module support. -/
theorem trace_cubic_eq_actual_root_sum (N : LieSubmodule K H L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule) (x y z : H) :
    LinearMap.trace K N (toEnd K H N x * toEnd K H N y * toEnd K H N z) =
      actualRootCubic H N.toSubmodule x y z := by
  classical
  letI := (containedRoots_finite H N.toSubmodule).fintype
  rw [WeightCubic.trace_cubic_eq_sum_weights]
  simp_rw [supported_weight_finrank_eq_one H N hdis, one_smul]
  exact (weightSupportEquiv H N hdis).sum_comp
    (fun α : containedRoots H N.toSubmodule => α.val x * α.val y * α.val z)

/-- The symmetrized trace cubic, with its factor one half, has the same
actual root-sum formula on the Cartan. -/
theorem symmetrized_trace_cubic_eq_actual_root_sum (N : LieSubmodule K H L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule) (x y z : H) :
    (1 / 2 : K) * LinearMap.trace K N
      (toEnd K H N x * (toEnd K H N y * toEnd K H N z +
        toEnd K H N z * toEnd K H N y)) =
      actualRootCubic H N.toSubmodule x y z := by
  classical
  letI := (containedRoots_finite H N.toSubmodule).fintype
  rw [WeightCubic.symmetrized_trace_cubic_eq_sum_weights]
  simp_rw [supported_weight_finrank_eq_one H N hdis, one_smul]
  exact (weightSupportEquiv H N hdis).sum_comp
    (fun α : containedRoots H N.toSubmodule => α.val x * α.val y * α.val z)

end CubicAnomaly.Classification.RootSupportTrace
