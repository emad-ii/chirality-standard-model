import CubicAnomaly.Classification.RootGrading
import CubicAnomaly.Classification.AmbientComplexification
import CubicAnomaly.Classification.RootBracket

/-!
# Subalgebras containing an actual ambient Cartan

The roots attached to a Cartan-stable subspace are defined by containment of
the actual one-dimensional root spaces.  A subalgebra containing the Cartan
is reconstructed from these roots.  Nondegeneracy of the restricted invariant
form supplies closure under negation, rather than making that a root-data
assumption.
-/

namespace CubicAnomaly.Classification.CommonCartan

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The actual ambient roots whose whole root spaces lie in a given subspace. -/
def containedRoots (N : Submodule K L) : Set (H → K) :=
  {α | α ≠ 0 ∧ rootSpace H α ≠ ⊥ ∧ (rootSpace H α).toSubmodule ≤ N}

/-- One nonzero root vector in a subspace puts the entire root space there. -/
theorem root_space_le_of_nonzero_mem (N : Submodule K L) {α : H → K}
    (hα : α ≠ 0) {x : L} (hx : x ∈ rootSpace H α) (hxN : x ∈ N)
    (hx0 : x ≠ 0) : (rootSpace H α).toSubmodule ≤ N := by
  have hαne : rootSpace H α ≠ ⊥ := by
    intro hb
    exact hx0 (by simpa only [hb, LieSubmodule.mem_bot] using hx)
  let a : Weight K H L := ⟨α, hαne⟩
  intro y hy
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hx⟩ : rootSpace H α)
    (by simpa using hx0)).mp (finrank_rootSpace_eq_one a hα) ⟨y, hy⟩
  have hcy : c • x = y := congrArg Subtype.val hc
  rw [← hcy]
  exact N.smul_mem c hxN

/-- An ambient Cartan acts on each subalgebra that contains it. -/
def cartanStableSubalgebra (S : LieSubalgebra K L) (hHS : H ≤ S) :
    LieSubmodule K H L where
  __ := S.toSubmodule
  lie_mem := fun {x} {_y} hy => S.lie_mem (hHS x.property) hy

/-- A Cartan-stable subspace containing the Cartan is the sum of the Cartan
and exactly the root spaces it contains. -/
theorem cartan_submodule_eq_root_decomposition (N : LieSubmodule K H L)
    (hHN : H.toSubmodule ≤ N.toSubmodule) :
    N.toSubmodule = H.toSubmodule ⊔
      ⨆ α ∈ containedRoots H N.toSubmodule, (rootSpace H α).toSubmodule := by
  apply le_antisymm
  · intro x hx
    suffices hall : ∀ y : N, (y : L) ∈ H.toSubmodule ⊔
        ⨆ α ∈ containedRoots H N.toSubmodule, (rootSpace H α).toSubmodule from hall ⟨x, hx⟩
    intro y
    have hy : y ∈ ⨆ α : H → K, genWeightSpace N α := by
      rw [iSup_genWeightSpace_eq_top]
      trivial
    induction hy using LieSubmodule.iSup_induction' with
    | mem α y hy =>
      have hr : (y : L) ∈ rootSpace H α :=
        map_genWeightSpace_le N.incl ((LieSubmodule.mem_map _).mpr ⟨y, hy, rfl⟩)
      by_cases hα : α = 0
      · have hyH : (y : L) ∈ H := by
          simpa only [hα, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hr
        exact Submodule.mem_sup_left hyH
      · by_cases hy0 : (y : L) = 0
        · simpa only [hy0] using (H.toSubmodule ⊔
            ⨆ α ∈ containedRoots H N.toSubmodule, (rootSpace H α).toSubmodule).zero_mem
        · have hαN : α ∈ containedRoots H N.toSubmodule := ⟨hα,
            by intro hb; exact hy0 (by simpa only [hb, LieSubmodule.mem_bot] using hr),
            root_space_le_of_nonzero_mem H N.toSubmodule hα hr y.property hy0⟩
          have hle : (rootSpace H α).toSubmodule ≤
              ⨆ β ∈ containedRoots H N.toSubmodule, (rootSpace H β).toSubmodule :=
            le_iSup_of_le α (le_iSup_of_le hαN le_rfl)
          exact Submodule.mem_sup_right (hle hr)
    | zero => simp
    | add x y _ _ hx hy =>
      exact (H.toSubmodule ⊔
        ⨆ α ∈ containedRoots H N.toSubmodule, (rootSpace H α).toSubmodule).add_mem hx hy
  · exact sup_le hHN (iSup_le fun α => iSup_le fun hα => hα.2.2)

/-- A subalgebra containing an ambient Cartan is reconstructed from its actual
contained root spaces. -/
theorem subalgebra_eq_root_decomposition (S : LieSubalgebra K L) (hHS : H ≤ S) :
    S.toSubmodule = H.toSubmodule ⊔
      ⨆ α ∈ containedRoots H S.toSubmodule, (rootSpace H α).toSubmodule :=
  cartan_submodule_eq_root_decomposition H (cartanStableSubalgebra H S hHS) hHS

/-- Invariance pairs root spaces only when their weights sum to zero. -/
theorem invariant_form_root_pair_zero (Φ : LinearMap.BilinForm K L)
    (hΦ : Φ.lieInvariant H) {α β : H → K} {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (hab : α + β ≠ 0) :
    Φ x y = 0 := by
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hab
  have ht' : α t + β t ≠ 0 := ht
  have h := hΦ t x y
  rw [lie_eq_smul_of_mem_rootSpace hx, lie_eq_smul_of_mem_rootSpace hy] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have hmul : (α t + β t) * Φ x y = 0 := by
    rw [add_mul, h, neg_add_cancel]
  exact (mul_eq_zero.mp hmul).resolve_left ht'

/-- Nondegeneracy on a Cartan-stable subspace forces its actual roots to occur
in opposite pairs. -/
theorem contained_roots_neg (N : LieSubmodule K H L)
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant H)
    (hnd : (Φ.restrict N.toSubmodule).Nondegenerate)
    {α : H → K} (hα : α ∈ containedRoots H N.toSubmodule) :
    -α ∈ containedRoots H N.toSubmodule := by
  by_contra hneg
  let a : Weight K H L := ⟨α, hα.2.1⟩
  obtain ⟨x, hx, hx0⟩ := a.exists_ne_zero
  have hxN : x ∈ N := hα.2.2 hx
  have hxorth : ∀ y : N, Φ x (y : L) = 0 := by
    intro y
    have hy : y ∈ ⨆ β : H → K, genWeightSpace N β := by
      rw [iSup_genWeightSpace_eq_top]
      trivial
    induction hy using LieSubmodule.iSup_induction' with
    | mem β y hy =>
      have hr : (y : L) ∈ rootSpace H β :=
        map_genWeightSpace_le N.incl ((LieSubmodule.mem_map _).mpr ⟨y, hy, rfl⟩)
      by_cases hy0 : (y : L) = 0
      · simp only [hy0, map_zero]
      · have hab : α + β ≠ 0 := by
          intro hab
          have hb : β = -α := eq_neg_of_add_eq_zero_right hab
          subst β
          apply hneg
          exact ⟨neg_ne_zero.mpr hα.1,
            by intro hb; exact hy0 (by simpa only [hb, LieSubmodule.mem_bot] using hr),
            root_space_le_of_nonzero_mem H N.toSubmodule (neg_ne_zero.mpr hα.1)
              hr y.property hy0⟩
        exact invariant_form_root_pair_zero H Φ hΦ hx hr hab
    | zero => simp
    | add x y _ _ hx hy => simp only [LieSubmodule.coe_add, map_add, hx, hy, add_zero]
  have hxzero : (⟨x, hxN⟩ : N) = 0 := hnd.1 ⟨x, hxN⟩ hxorth
  exact hx0 (congrArg Subtype.val hxzero)

/-- Lie closure implies additive closure of the actual contained roots. -/
theorem contained_roots_add (S : LieSubalgebra K L)
    {α β : H → K} (hα : α ∈ containedRoots H S.toSubmodule)
    (hβ : β ∈ containedRoots H S.toSubmodule)
    (hsum : α + β ≠ 0 ∧ rootSpace H (α + β) ≠ ⊥) :
    α + β ∈ containedRoots H S.toSubmodule := by
  obtain ⟨x, hx, y, hy, hxy⟩ := RootBracket.exists_nonzero_root_bracket_of_functions
    hα.1 hα.2.1 hβ.2.1 hsum.2
  exact ⟨hsum.1, hsum.2, root_space_le_of_nonzero_mem H S.toSubmodule hsum.1
    (LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy)
    (S.lie_mem (hα.2.2 hx) (hβ.2.2 hy)) hxy⟩

/-- The quotient by the integer span of the actual roots of a Cartan-containing
subalgebra has exactly that subalgebra as its zero component. -/
theorem subalgebra_eq_quotient_zero_grade (S : LieSubalgebra K L) (hHS : H ≤ S)
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant H)
    (hnd : (Φ.restrict S.toSubmodule).Nondegenerate) :
    RootGrading.weightGrade H L
      (QuotientAddGroup.mk' (AddSubgroup.closure (containedRoots H S.toSubmodule))) 0 =
        S.toSubmodule := by
  rw [RootGrading.quotient_root_grade_zero_eq H (containedRoots H S.toSubmodule)
    (fun _ hα => ⟨hα.1, hα.2.1⟩)
    (fun _ hα => contained_roots_neg H (cartanStableSubalgebra H S hHS) Φ hΦ hnd hα)
    (fun _ hα _ hβ hsum => contained_roots_add H S hα hβ hsum)]
  exact (subalgebra_eq_root_decomposition H S hHS).symm

end CubicAnomaly.Classification.CommonCartan
