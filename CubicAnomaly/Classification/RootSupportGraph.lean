import CubicAnomaly.Classification.EqualRank
import CubicAnomaly.Classification.CompactCartan

/-!
# Connected support graphs of actual irreducible root-space modules

An edge joins two actual roots in a module's support when their difference
is an actual root of the acting Cartan-containing subalgebra.  Every graph
component spans an invariant submodule.  Irreducibility therefore forces
the actual support graph to be connected, rather than merely forcing its
weights into one lattice coset.
-/

namespace CubicAnomaly.Classification.RootSupportGraph

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.EqualRank

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- An edge has actual supported roots at both endpoints and an acting root
as its displacement. Intermediate vertices cannot leave the actual support. -/
def SupportAdjacent (S : LieSubalgebra K L) (N : Submodule K L)
    (α β : H → K) : Prop :=
  α ∈ containedRoots H N ∧ β ∈ containedRoots H N ∧
    β - α ∈ containedRoots H S.toSubmodule

/-- Undirected graph reachability inside the actual root support. -/
def SupportReachable (S : LieSubalgebra K L) (N : Submodule K L)
    (α β : H → K) : Prop :=
  Relation.EqvGen (SupportAdjacent H S N) α β

/-- Nonempty connectedness of the actual supported-root graph. -/
def SupportConnected (S : LieSubalgebra K L) (N : Submodule K L) : Prop :=
  ∃ α ∈ containedRoots H N, ∀ β ∈ containedRoots H N, SupportReachable H S N α β

/-- The actual ambient span of one supported-root graph component. -/
noncomputable def rootComponent (S : LieSubalgebra K L) (N : Submodule K L)
    (α : H → K) : Submodule K L :=
  ⨆ β : {β : H → K // β ∈ containedRoots H N ∧ SupportReachable H S N α β},
    (rootSpace H β.val).toSubmodule

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [IsTriangularizable K H L] in
/-- A supported root space lies in its own graph component. -/
theorem rootSpace_le_rootComponent (S : LieSubalgebra K L) (N : Submodule K L)
    {α : H → K} (hα : α ∈ containedRoots H N) :
    (rootSpace H α).toSubmodule ≤ rootComponent H S N α :=
  le_iSup_of_le ⟨α, hα, Relation.EqvGen.refl α⟩ le_rfl

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [IsTriangularizable K H L] in
/-- Component spans stay in the actual module whose roots they use. -/
theorem rootComponent_le (S : LieSubalgebra K L) (N : Submodule K L) (α : H → K) :
    rootComponent H S N α ≤ N :=
  iSup_le fun β => β.property.1.2.2

private theorem rootComponent_cartan_stable (S : LieSubalgebra K L)
    (N : Submodule K L) (α : H → K) (t : H) {y : L}
    (hy : y ∈ rootComponent H S N α) : ⁅(t : L), y⁆ ∈ rootComponent H S N α := by
  change y ∈ ⨆ β : {β : H → K // β ∈ containedRoots H N ∧
    SupportReachable H S N α β}, (rootSpace H β.val).toSubmodule at hy
  refine Submodule.iSup_induction (motive := fun y : L =>
    ⁅(t : L), y⁆ ∈ rootComponent H S N α) _ hy (fun β y hy => ?_) ?_ ?_
  · have hlie := lie_eq_smul_of_mem_rootSpace hy t
    change ⁅(t : L), y⁆ = β.val t • y at hlie
    change ⁅(t : L), y⁆ ∈ rootComponent H S N α
    rw [hlie]
    have hle : (rootSpace H β.val).toSubmodule ≤ rootComponent H S N α :=
      le_iSup_of_le β le_rfl
    exact (rootComponent H S N α).smul_mem _ (hle hy)
  · simpa only [lie_zero] using (rootComponent H S N α).zero_mem
  · intro y z hy hz
    simpa only [lie_add] using (rootComponent H S N α).add_mem hy hz

private theorem rootComponent_root_stable (S : LieSubalgebra K L)
    (N : LieSubmodule K S L) (hdis : Disjoint H.toSubmodule N.toSubmodule)
    (α : H → K) {γ : H → K} (hγ : γ ∈ containedRoots H S.toSubmodule)
    {x y : L} (hx : x ∈ rootSpace H γ) (hy : y ∈ rootComponent H S N.toSubmodule α) :
    ⁅x, y⁆ ∈ rootComponent H S N.toSubmodule α := by
  change y ∈ ⨆ β : {β : H → K // β ∈ containedRoots H N.toSubmodule ∧
    SupportReachable H S N.toSubmodule α β}, (rootSpace H β.val).toSubmodule at hy
  refine Submodule.iSup_induction (motive := fun y : L =>
    ⁅x, y⁆ ∈ rootComponent H S N.toSubmodule α) _ hy (fun β y hy => ?_) ?_ ?_
  · have hxy := LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy
    have hxyN : ⁅x, y⁆ ∈ N := N.lie_mem (x := ⟨x, hγ.2.2 hx⟩) (β.property.1.2.2 hy)
    by_cases hz : ⁅x, y⁆ = 0
    · simpa only [hz] using (rootComponent H S N.toSubmodule α).zero_mem
    have hsum : γ + β.val ≠ 0 := by
      intro hb
      have hxH : ⁅x, y⁆ ∈ H := by
        simpa only [hb, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hxy
      have hmem : ⁅x, y⁆ ∈ H.toSubmodule ⊓ N.toSubmodule := ⟨hxH, hxyN⟩
      exact hz (by simpa only [hdis.eq_bot, Submodule.mem_bot] using hmem)
    have hsupp : γ + β.val ∈ containedRoots H N.toSubmodule := ⟨hsum,
      by intro hb; exact hz (by simpa only [hb, LieSubmodule.mem_bot] using hxy),
      root_space_le_of_nonzero_mem H N.toSubmodule hsum hxy hxyN hz⟩
    have hedge : SupportAdjacent H S N.toSubmodule β.val (γ + β.val) :=
      ⟨β.property.1, hsupp, by simpa only [add_sub_cancel_right] using hγ⟩
    have hreach : SupportReachable H S N.toSubmodule α (γ + β.val) :=
      Relation.EqvGen.trans _ _ _ β.property.2 (Relation.EqvGen.rel _ _ hedge)
    have hle : (rootSpace H (γ + β.val)).toSubmodule ≤
        rootComponent H S N.toSubmodule α :=
      le_iSup_of_le ⟨γ + β.val, hsupp, hreach⟩ le_rfl
    exact hle hxy
  · simpa only [lie_zero] using (rootComponent H S N.toSubmodule α).zero_mem
  · intro y z hy hz
    simpa only [lie_add] using (rootComponent H S N.toSubmodule α).add_mem hy hz

/-- Every support-graph component spans an invariant submodule of the actual
Cartan-containing isotropy algebra. -/
noncomputable def rootComponentSubmodule (S : LieSubalgebra K L) (hHS : H ≤ S)
    (N : LieSubmodule K S L) (hdis : Disjoint H.toSubmodule N.toSubmodule)
    (α : H → K) : LieSubmodule K S L where
  toSubmodule := rootComponent H S N.toSubmodule α
  lie_mem := by
    intro x y hy
    have hx : (x : L) ∈ H.toSubmodule ⊔
        ⨆ γ ∈ containedRoots H S.toSubmodule, (rootSpace H γ).toSubmodule := by
      rw [← subalgebra_eq_root_decomposition H S hHS]
      exact x.property
    obtain ⟨t, ht, z, hz, htz⟩ := Submodule.mem_sup.mp hx
    change ⁅(x : L), y⁆ ∈ rootComponent H S N.toSubmodule α
    rw [← htz, add_lie]
    apply (rootComponent H S N.toSubmodule α).add_mem
    · exact rootComponent_cartan_stable H S N.toSubmodule α ⟨t, ht⟩ hy
    · refine Submodule.iSup_induction (motive := fun z : L =>
        ⁅z, y⁆ ∈ rootComponent H S N.toSubmodule α) _ hz (fun γ z hz => ?_) ?_ ?_
      · refine Submodule.iSup_induction (motive := fun z : L =>
          ⁅z, y⁆ ∈ rootComponent H S N.toSubmodule α) _ hz (fun hγ z hz => ?_) ?_ ?_
        · exact rootComponent_root_stable H S N hdis α hγ hz hy
        · simpa only [zero_lie] using (rootComponent H S N.toSubmodule α).zero_mem
        · intro z w hz hw
          simpa only [add_lie] using (rootComponent H S N.toSubmodule α).add_mem hz hw
      · simpa only [zero_lie] using (rootComponent H S N.toSubmodule α).zero_mem
      · intro z w hz hw
        simpa only [add_lie] using (rootComponent H S N.toSubmodule α).add_mem hz hw

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [IsTriangularizable K H L] in
/-- A nonzero root vector in a component can only have a root in that same
component; this uses independence of actual root spaces. -/
theorem reachable_of_nonzero_root_mem_component (S : LieSubalgebra K L)
    (N : Submodule K L) {α β : H → K} {x : L}
    (hx : x ∈ rootSpace H β) (hxc : x ∈ rootComponent H S N α) (hx0 : x ≠ 0) :
    SupportReachable H S N α β := by
  by_contra hnot
  have hind : iSupIndep (fun γ : H → K => (rootSpace H γ).toSubmodule) :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace K H L)
  have hle : rootComponent H S N α ≤
      ⨆ (γ : H → K) (_ : γ ≠ β), (rootSpace H γ).toSubmodule := by
    refine iSup_le fun γ => ?_
    have hne : γ.val ≠ β := by
      intro heq
      exact hnot (heq ▸ γ.property.2)
    exact le_iSup_of_le γ.val (le_iSup_of_le hne le_rfl)
  have hmem : x ∈ (rootSpace H β).toSubmodule ⊓ rootComponent H S N α := ⟨hx, hxc⟩
  have hd := (hind β).mono_right hle
  exact hx0 (by simpa only [hd.eq_bot, Submodule.mem_bot] using hmem)

/-- Irreducibility forces actual supported roots to be connected by actual
isotropy-root steps, with every intermediate vertex still in the support. -/
theorem irreducible_root_support_connected
    (S : LieSubalgebra K L) (hHS : H ≤ S) (N : LieSubmodule K S L)
    [LieModule.IsIrreducible K S N] (hdis : Disjoint H.toSubmodule N.toSubmodule) :
    SupportConnected H S N.toSubmodule := by
  letI : Nontrivial N := LieModule.nontrivial_of_isIrreducible K S N
  have hN : N ≠ ⊥ := (LieSubmodule.nontrivial_iff_ne_bot K S L).mp inferInstance
  let N' := restrictCartanSubmodule H S hHS N
  have hN' : N' ≠ ⊥ := by
    intro hb
    apply hN
    exact LieSubmodule.toSubmodule_injective
      (congrArg (fun T : LieSubmodule K H L => T.toSubmodule) hb)
  obtain ⟨α, x, hxN, hxα, hx0⟩ := exists_nonzero_root_vector H N' hN'
  have hα0 : α ≠ 0 := by
    intro ha
    have hxH : x ∈ H := by
      simpa only [ha, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hxα
    have hmem : x ∈ H.toSubmodule ⊓ N.toSubmodule := ⟨hxH, hxN⟩
    exact hx0 (by simpa only [hdis.eq_bot, Submodule.mem_bot] using hmem)
  have hα : α ∈ containedRoots H N.toSubmodule := ⟨hα0,
    by intro hb; exact hx0 (by simpa only [hb, LieSubmodule.mem_bot] using hxα),
    root_space_le_of_nonzero_mem H N.toSubmodule hα0 hxα hxN hx0⟩
  let C := rootComponentSubmodule H S hHS N hdis α
  let C' := C.comap N.incl
  have hC' : C' ≠ ⊥ := by
    intro hb
    have hxC : (⟨x, hxN⟩ : N) ∈ C' := (rootSpace_le_rootComponent H S N.toSubmodule hα) hxα
    rw [hb, LieSubmodule.mem_bot] at hxC
    exact hx0 (congrArg Subtype.val hxC)
  have htop : C' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top C').resolve_left hC'
  refine ⟨α, hα, ?_⟩
  intro β hβ
  obtain ⟨y, hyβ, hy0⟩ := (Weight.mk β hβ.2.1).exists_ne_zero
  have hyN : y ∈ N := hβ.2.2 hyβ
  have hyC : y ∈ rootComponent H S N.toSubmodule α := by
    have : (⟨y, hyN⟩ : N) ∈ C' := by rw [htop]; trivial
    exact this
  exact reachable_of_nonzero_root_mem_component H S N.toSubmodule hyβ hyC hy0

section CompactPair

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.CompactCartan
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- For an actual common Cartan, both actual complex halves have nonempty
connected root support. The anomaly hypothesis is not needed for this
representation-theoretic conclusion. -/
theorem compact_common_cartan_half_support_connected
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) :
    let q := orthogonalComplement B h
    let J := commutantComplexStructure e
    SupportConnected H (complexifiedSubalgebra h)
      (ambientComplexifiedHalf q J Complex.I).toSubmodule ∧
    SupportConnected H (complexifiedSubalgebra h)
      (ambientComplexifiedHalf q J (-Complex.I)).toSubmodule := by
  let q := orthogonalComplement B h
  let J := commutantComplexStructure e
  let P₀ := ambientComplexifiedHalf q J Complex.I
  let Q₀ := ambientComplexifiedHalf q J (-Complex.I)
  let S := complexifiedSubalgebra h
  let P := imageActionSubmodule h P₀
  let Q := imageActionSubmodule h Q₀
  have hgcenter := (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) :=
    compact_complexification_isKilling B hgcenter
  have hc := compact_orthogonal_complement_isCompl B h
  have hqne : q ≠ ⊥ := by
    intro hz
    have ht := hc.sup_eq_top
    have hz' : q.toSubmodule = ⊥ := congrArg LieSubmodule.toSubmodule hz
    rw [hz', sup_bot_eq] at ht
    exact hproper ((LieSubalgebra.toSubmodule_eq_top h).mp ht)
  letI : Nontrivial q := (LieSubmodule.nontrivial_iff_ne_bot ℝ h g).mpr hqne
  letI : LieModule.IsIrreducible ℝ h q := compact_complex_commutant_irreducible B h q e
  have hirred := ambient_complex_halves_irreducible q J (commutant_complex_structure_square e)
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) P₀ := hirred.1
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) Q₀ := hirred.2
  letI : LieModule.IsIrreducible ℂ S P := imageActionSubmodule_irreducible h P₀
  letI : LieModule.IsIrreducible ℂ S Q := imageActionSubmodule_irreducible h Q₀
  have hPQ : P.toSubmodule ⊔ Q.toSubmodule = q.toSubmodule.baseChange ℂ :=
    congrArg LieSubmodule.toSubmodule
      (ambient_complex_halves_sup q J (commutant_complex_structure_square e))
  have hdis : Disjoint S.toSubmodule (P.toSubmodule ⊔ Q.toSubmodule) := by
    rw [hPQ]
    exact (compact_pair_complexification_isCompl B h).disjoint
  have hHS : H.toSubmodule ≤ S.toSubmodule := hH
  exact ⟨irreducible_root_support_connected H S hH P
      ((hdis.mono_left hHS).mono_right le_sup_left),
    irreducible_root_support_connected H S hH Q
      ((hdis.mono_left hHS).mono_right le_sup_right)⟩

/-- Equal geometric abelian ranks construct the ambient Cartan and the
connected support graphs of both actual complex halves. -/
theorem equal_abelianRank_exists_connected_half_support
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hrank : abelianRank ℝ h = abelianRank ℝ g) :
    ∃ (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H.IsCartanSubalgebra),
      letI := hH
      H ≤ complexifiedSubalgebra h ∧ Module.finrank ℂ H = abelianRank ℝ g ∧
      (let q := orthogonalComplement B h
       let J := commutantComplexStructure e
       SupportConnected H (complexifiedSubalgebra h)
         (ambientComplexifiedHalf q J Complex.I).toSubmodule ∧
       SupportConnected H (complexifiedSubalgebra h)
         (ambientComplexifiedHalf q J (-Complex.I)).toSubmodule) := by
  obtain ⟨H, hH, hHS, hdim⟩ := compact_equal_abelianRank_exists_complex_cartan B h hrank
  letI := hH
  exact ⟨H, hH, hHS, hdim, compact_common_cartan_half_support_connected B h heff hproper e H hHS⟩

end CompactPair

end CubicAnomaly.Classification.RootSupportGraph
