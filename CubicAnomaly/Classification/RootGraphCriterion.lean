import CubicAnomaly.Classification.RootSupportDimension

/-!
# The actual root-support graph criterion for irreducibility

When the acting roots are closed under negation, root-space containment in
an invariant subspace propagates along every support-graph edge. Nonzero
root brackets therefore give the converse to the component-span argument:
connected actual root support is equivalent to irreducibility. The invariant
nondegenerate form on a compactified isotropy algebra supplies negation
closure automatically.
-/

namespace CubicAnomaly.Classification.RootGraphCriterion

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.EqualRank
open CubicAnomaly.Classification.RootSupportGraph
open CubicAnomaly.Classification.RootSupportDimension

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [IsTriangularizable K H L] in
/-- Any two actual roots in a connected support are mutually reachable. -/
theorem connected_support_reachable (S : LieSubalgebra K L) (N : Submodule K L)
    (hconn : SupportConnected H S N) {α β : H → K}
    (hα : α ∈ containedRoots H N) (hβ : β ∈ containedRoots H N) :
    SupportReachable H S N α β := by
  obtain ⟨γ, _, hγ⟩ := hconn
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hγ α hα)) (hγ β hβ)

private theorem root_space_le_of_adjacent (S : LieSubalgebra K L)
    (N : Submodule K L) (T : LieSubmodule K S L) {α β : H → K}
    (hab : SupportAdjacent H S N α β)
    (haT : (rootSpace H α).toSubmodule ≤ T.toSubmodule) :
    (rootSpace H β).toSubmodule ≤ T.toSubmodule := by
  have hγ := hab.2.2
  obtain ⟨x, hx, y, hy, hxy⟩ := RootBracket.exists_nonzero_root_bracket_of_functions
    hγ.1 hγ.2.1 hab.1.2.1 (by simpa only [sub_add_cancel] using hab.2.1.2.1)
  have hxyβ : ⁅x, y⁆ ∈ rootSpace H β := by
    simpa only [sub_add_cancel] using LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy
  have hxyT : ⁅x, y⁆ ∈ T := T.lie_mem (x := ⟨x, hγ.2.2 hx⟩) (haT hy)
  exact root_space_le_of_nonzero_mem H T.toSubmodule hab.2.1.1 hxyβ hxyT hxy

/-- Actual root-space containment in an invariant subspace is constant on
support-graph components. Nonzero root brackets supply the propagation. -/
theorem reachable_preserves_root_space_containment (S : LieSubalgebra K L)
    (N : Submodule K L) (T : LieSubmodule K S L)
    (hneg : ∀ γ ∈ containedRoots H S.toSubmodule, -γ ∈ containedRoots H S.toSubmodule)
    {α β : H → K} (hab : SupportReachable H S N α β) :
    (rootSpace H α).toSubmodule ≤ T.toSubmodule ↔
      (rootSpace H β).toSubmodule ≤ T.toSubmodule := by
  induction hab with
  | rel α β hab =>
    constructor
    · exact root_space_le_of_adjacent H S N T hab
    · apply root_space_le_of_adjacent H S N T
      refine ⟨hab.2.1, hab.1, ?_⟩
      have hh := hneg (β - α) hab.2.2
      simpa only [neg_sub] using hh
  | refl => rfl
  | symm α β _ ih => exact ih.symm
  | trans α β γ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem irreducible_of_connected_support
    (S : LieSubalgebra K L) (hHS : H ≤ S) (N : LieSubmodule K S L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule)
    (hneg : ∀ γ ∈ containedRoots H S.toSubmodule, -γ ∈ containedRoots H S.toSubmodule)
    (hconn : SupportConnected H S N.toSubmodule) : LieModule.IsIrreducible K S N := by
  have hconn' := hconn
  obtain ⟨α, hα, _⟩ := hconn'
  obtain ⟨x, hx, hx0⟩ := (Weight.mk α hα.2.1).exists_ne_zero
  letI : Nontrivial N := ⟨⟨⟨x, hα.2.2 hx⟩, 0,
    fun hz => hx0 (congrArg Subtype.val hz)⟩⟩
  apply LieModule.IsIrreducible.mk
  intro U hU
  let T := U.map N.incl
  have hinj : Function.Injective (LieSubmodule.map N.incl) :=
    LieSubmodule.map_injective_of_injective Subtype.val_injective
  have hT : T ≠ ⊥ := by
    intro hb
    apply hU
    apply hinj
    simpa only [LieSubmodule.map_bot] using hb
  have hTN : T ≤ N := LieSubmodule.map_incl_le
  let T' := restrictCartanSubmodule H S hHS T
  have hT' : T' ≠ ⊥ := by
    intro hb
    apply hT
    exact LieSubmodule.toSubmodule_injective
      (congrArg (fun P : LieSubmodule K H L => P.toSubmodule) hb)
  obtain ⟨β, y, hyT, hyβ, hy0⟩ := exists_nonzero_root_vector H T' hT'
  have hyN : y ∈ N := hTN hyT
  have hβ0 : β ≠ 0 := by
    intro hb
    have hyH : y ∈ H := by
      simpa only [hb, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hyβ
    have hm : y ∈ H.toSubmodule ⊓ N.toSubmodule := ⟨hyH, hyN⟩
    exact hy0 (by simpa only [hdis.eq_bot, Submodule.mem_bot] using hm)
  have hβ : β ∈ containedRoots H N.toSubmodule := ⟨hβ0,
    by intro hb; exact hy0 (by simpa only [hb, LieSubmodule.mem_bot] using hyβ),
    root_space_le_of_nonzero_mem H N.toSubmodule hβ0 hyβ hyN hy0⟩
  have hβT : (rootSpace H β).toSubmodule ≤ T.toSubmodule :=
    root_space_le_of_nonzero_mem H T.toSubmodule hβ0 hyβ hyT hy0
  have hNT : N ≤ T := by
    change (restrictCartanSubmodule H S hHS N).toSubmodule ≤ T.toSubmodule
    rw [cartan_submodule_eq_supported_root_sum H (restrictCartanSubmodule H S hHS N) hdis]
    refine iSup_le fun γ => ?_
    exact (reachable_preserves_root_space_containment H S N.toSubmodule T hneg
      (connected_support_reachable H S N.toSubmodule hconn hβ γ.property)).mp hβT
  apply hinj
  rw [LieSubmodule.map_incl_top]
  exact le_antisymm hTN hNT

/-- For an actual root-space module with no zero weight and a symmetric
acting root set, nonempty graph connectedness is exactly irreducibility. -/
theorem root_support_connected_iff_irreducible
    (S : LieSubalgebra K L) (hHS : H ≤ S) (N : LieSubmodule K S L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule)
    (hneg : ∀ γ ∈ containedRoots H S.toSubmodule, -γ ∈ containedRoots H S.toSubmodule) :
    SupportConnected H S N.toSubmodule ↔ LieModule.IsIrreducible K S N := by
  constructor
  · exact irreducible_of_connected_support H S hHS N hdis hneg
  · intro hirred
    letI := hirred
    exact irreducible_root_support_connected H S hHS N hdis

/-- An invariant nondegenerate form on the acting subalgebra supplies the
root-negation hypothesis in the actual graph criterion. -/
theorem nondegenerate_root_support_connected_iff_irreducible
    (S : LieSubalgebra K L) (hHS : H ≤ S) (N : LieSubmodule K S L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule)
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant H)
    (hnd : (Φ.restrict S.toSubmodule).Nondegenerate) :
    SupportConnected H S N.toSubmodule ↔ LieModule.IsIrreducible K S N :=
  root_support_connected_iff_irreducible H S hHS N hdis
    (fun _ hγ => contained_roots_neg H (cartanStableSubalgebra H S hHS) Φ hΦ hnd hγ)

end CubicAnomaly.Classification.RootGraphCriterion
