import CubicAnomaly.Classification.ClassicalConstituentWeights

/-!
# Uniqueness of a highest line in an irreducible module

Iterated actions of negative root vectors on a highest vector span a Lie
submodule. Its only line at the original height is the starting line.
This yields uniqueness of the highest line of an irreducible module
directly from its action and root-space decomposition.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentHighest

open LieAlgebra LieModule Module LieAlgebra.IsKilling

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]

/-- A common Cartan eigenvector killed by all positive root spaces. -/
def IsHighestVector (b : (rootSystem H).Base) (μ : H → ℂ) (v : M) : Prop :=
  v ≠ 0 ∧ (∀ x : H, ⁅x, v⁆ = μ x • v) ∧
    ∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, v⁆ = 0

private structure Lowering (b : (rootSystem H).Base) where
  root : H.root
  neg : ¬ b.IsPos root
  op : L
  mem : op ∈ rootSpace H root.val

private def word (b : (rootSystem H).Base) (v : M) : List (Lowering H b) → M
  | [] => v
  | f :: w => ⁅f.op, word b v w⁆

private def wordSpan (b : (rootSystem H).Base) (v : M) :=
  Submodule.span ℂ (Set.range (word H b v))

omit [LieModule ℂ L M] in
private theorem word_mem (b : (rootSystem H).Base) (v : M) (w : List (Lowering H b)) :
    word H b v w ∈ wordSpan H b v := Submodule.subset_span ⟨w, rfl⟩

private theorem lower_mem (b : (rootSystem H).Base) (v : M) (f : Lowering H b) {w : M}
    (hw : w ∈ wordSpan H b v) : ⁅f.op, w⁆ ∈ wordSpan H b v := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, rfl⟩ := hw
    exact word_mem H b v (f :: s)
  | zero => rw [lie_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [lie_smul]; exact Submodule.smul_mem _ c hx

private theorem base_action_mem (b : (rootSystem H).Base) {μ : H → ℂ} {v : M}
    (hv : IsHighestVector H b μ v) (x : L) : ⁅x, v⁆ ∈ wordSpan H b v := by
  let N := (wordSpan H b v).comap ((toEnd ℂ L M).toLinearMap.flip v)
  suffices h : (⊤ : Submodule ℂ L) ≤ N from h Submodule.mem_top
  rw [← LieSubmodule.top_toSubmodule (L := H), ← cartan_sup_iSup_rootSpace_eq_top H,
    LieSubmodule.sup_toSubmodule, LieSubmodule.iSup_toSubmodule, sup_le_iff]
  constructor
  · intro y hy
    change ⁅y, v⁆ ∈ wordSpan H b v
    rw [show ⁅y, v⁆ = μ ⟨y, hy⟩ • v from hv.2.1 ⟨y, hy⟩]
    exact Submodule.smul_mem _ _ (word_mem H b v [])
  · apply iSup_le
    intro α
    rw [LieSubmodule.iSup_toSubmodule]
    apply iSup_le
    intro hα y hy
    let i : H.root := ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩⟩
    change ⁅y, v⁆ ∈ wordSpan H b v
    by_cases hp : b.IsPos i
    · rw [hv.2.2 i hp y hy]
      exact Submodule.zero_mem _
    · exact word_mem H b v [⟨i, hp, y, hy⟩]

private theorem action_word_mem (b : (rootSystem H).Base) {μ : H → ℂ} {v : M}
    (hv : IsHighestVector H b μ v) (w : List (Lowering H b)) (x : L) :
    ⁅x, word H b v w⁆ ∈ wordSpan H b v := by
  induction w generalizing x with
  | nil => exact base_action_mem H b hv x
  | cons f w ih =>
    rw [word, leibniz_lie]
    exact Submodule.add_mem _ (ih ⁅x, f.op⁆) (lower_mem H b v f (ih x))

private def wordSpanSubmodule (b : (rootSystem H).Base)
    {μ : H → ℂ} {v : M} (hv : IsHighestVector H b μ v) : LieSubmodule ℂ L M := {
    wordSpan H b v with
    lie_mem := by
      intro x w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨s, rfl⟩ := hw
        exact action_word_mem H b hv s x
      | zero => rw [lie_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [lie_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [lie_smul]; exact Submodule.smul_mem _ c ha }

private theorem wordSpan_eq_top [IsIrreducible ℂ L M] (b : (rootSystem H).Base)
    {μ : H → ℂ} {v : M} (hv : IsHighestVector H b μ v) :
    wordSpan H b v = ⊤ := by
  let N := wordSpanSubmodule H b hv
  have hN : N ≠ ⊥ := by
    intro h
    have hw : v ∈ N := word_mem H b v []
    exact hv.1 (by simpa [h] using hw)
  exact (LieSubmodule.toSubmodule_eq_top N).mpr ((IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN)

private theorem word_lower_eigenvalue (b : (rootSystem H).Base) {μ : H → ℂ} {v : M}
    (hv : IsHighestVector H b μ v) (h : H) (hh : ∀ α : H.root, α.val h = (b.height α : ℂ))
    (w : List (Lowering H b)) :
    ∃ ν : ℂ, ⁅h, word H b v w⁆ = ν • word H b v w ∧
      ν.re ≤ (μ h).re ∧ (w ≠ [] → ν.re < (μ h).re) := by
  induction w with
  | nil => exact ⟨_, hv.2.1 h, le_rfl, fun hn => (hn rfl).elim⟩
  | cons f w ih =>
    obtain ⟨ν, he, hle, _⟩ := ih
    have hs : ⁅(h : L), f.op⁆ = f.root.val h • f.op := lie_eq_smul_of_mem_rootSpace f.mem h
    have hneg : (b.height f.root : ℝ) < 0 := by
      have hn := b.height_ne_zero f.root
      have hp := f.neg
      rw [RootPairing.Base.isPos_iff] at hp
      exact_mod_cast (show b.height f.root < 0 by omega)
    have hlt : (f.root.val h + ν).re < (μ h).re := by
      rw [hh]
      simp only [Complex.add_re, Complex.intCast_re]
      linarith
    refine ⟨_, ?_, le_of_lt hlt, fun _ => hlt⟩
    change ⁅(h : L), ⁅f.op, word H b v w⁆⁆ = _
    rw [leibniz_lie, hs, smul_lie, show ⁅(h : L), word H b v w⁆ = _ from he,
      lie_smul, ← add_smul]
    rfl

private theorem wordSpan_le_height_split (b : (rootSystem H).Base) {μ : H → ℂ} {v : M}
    (hv : IsHighestVector H b μ v) (h : H) (hh : ∀ α : H.root, α.val h = (b.height α : ℂ)) :
    wordSpan H b v ≤ ℂ ∙ v ⊔ ⨆ ν ∈ {ν : ℂ | ν.re < (μ h).re}, (toEnd ℂ L M h).eigenspace ν := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  rcases eq_or_ne w [] with rfl | hn
  · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  · obtain ⟨ν, he, _, hlt⟩ := word_lower_eigenvalue H b hv h hh w
    have hl : (toEnd ℂ L M h).eigenspace ν ≤
        ⨆ t ∈ {r : ℂ | r.re < (μ h).re}, (toEnd ℂ L M h).eigenspace t :=
      le_iSup₂_of_le ν (hlt hn) le_rfl
    exact Submodule.mem_sup_right (hl (Module.End.mem_eigenspace_iff.mpr he))

private theorem mem_highest_line (b : (rootSystem H).Base)
    {μ ν : H → ℂ} {v w : M} (hv : IsHighestVector H b μ v) (hw : IsHighestVector H b ν w)
    (h : H) (hh : ∀ α : H.root, α.val h = (b.height α : ℂ)) (hle : (μ h).re ≤ (ν h).re)
    (hmem : w ∈ wordSpan H b v) :
    w ∈ ℂ ∙ v := by
  let T := toEnd ℂ L M h
  let S := {t : ℂ | t.re < (μ h).re}
  let E := fun t : ℂ => T.eigenspace t
  have hw' : w ∈ E (ν h) := Module.End.mem_eigenspace_iff.mpr (hw.2.1 h)
  have hspan : ℂ ∙ v ≤ E (μ h) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (Module.End.mem_eigenspace_iff.mpr (hv.2.1 h))
  have hle' := wordSpan_le_height_split H b hv h hh
  have heq : ν h = μ h := by
    by_contra hne
    let S' := insert (μ h) S
    have hl : ℂ ∙ v ⊔ ⨆ t ∈ S, E t ≤ ⨆ t ∈ S', E t :=
      sup_le (hspan.trans (le_iSup₂_of_le (μ h) (Set.mem_insert _ _) le_rfl))
        (iSup_le fun t => iSup_le fun ht => le_iSup₂_of_le t (Set.mem_insert_of_mem _ ht) le_rfl)
    have hd := T.eigenspaces_iSupIndep.disjoint_biSup
      (show ν h ∉ S' from fun ht => (Set.mem_insert_iff.mp ht).elim hne (not_lt.mpr hle))
    exact hw.1 (hd.le_bot (show w ∈ E (ν h) ⊓ ⨆ t ∈ S', E t from
      ⟨hw', hl (hle' hmem)⟩))
  rw [heq] at hw'
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp (hle' hmem)
  have hc' : c ∈ E (μ h) := by
    rw [show c = w - a by rw [← hac]; abel]
    exact (E _).sub_mem hw' (hspan ha)
  have hd := T.eigenspaces_iSupIndep.disjoint_biSup (show μ h ∉ S from lt_irrefl (μ h).re)
  have hc₀ : c = 0 := hd.le_bot (show c ∈ E (μ h) ⊓ ⨆ t ∈ S, E t from ⟨hc', hc⟩)
  simpa [← hac, hc₀] using ha

/-- Even in a reducible module the cyclic submodule generated by a highest
vector has a single highest line at the generating weight. -/
theorem cyclic_highest_line (b : (rootSystem H).Base) {μ : H → ℂ} {v w : M}
    (hv : IsHighestVector H b μ v) (hw : IsHighestVector H b μ w)
    (hmem : w ∈ LieSubmodule.lieSpan ℂ L {v}) : w ∈ ℂ ∙ v := by
  obtain ⟨h, hh⟩ := ExceptionalSieveWeights.exists_height_element H b
  apply mem_highest_line H b hv hw h hh le_rfl
  have hle : LieSubmodule.lieSpan ℂ L {v} ≤ wordSpanSubmodule H b hv :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr (word_mem H b v []))
  exact hle hmem

/-- A nonzero functional killed by all negative root spaces has nonzero
evaluation on the highest line. -/
theorem negative_annihilator_pairs_highest [IsIrreducible ℂ L M] (b : (rootSystem H).Base)
    {μ : H → ℂ} {v : M} (hv : IsHighestVector H b μ v) (f : Dual ℂ M) (hf : f ≠ 0)
    (hneg : ∀ i : H.root, ¬ b.IsPos i → ∀ x ∈ rootSpace H i.val, ∀ m : M, f ⁅x,m⁆ = 0) :
    f v ≠ 0 := by
  intro hz
  have hle : wordSpan H b v ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    cases w with
    | nil => exact hz
    | cons x w => exact hneg x.root x.neg x.op x.mem _
  rw [wordSpan_eq_top H b hv] at hle
  exact hf (LinearMap.ext fun m => hle (show m ∈ (⊤ : Submodule ℂ M) from trivial))

/-- In an irreducible module any two highest vectors for an actual root-system
base span the same line and have identical Cartan weights. -/
theorem irreducible_highest_weight_unique [IsIrreducible ℂ L M] (b : (rootSystem H).Base)
    {μ ν : H → ℂ} {v w : M} (hv : IsHighestVector H b μ v) (hw : IsHighestVector H b ν w) :
    ℂ ∙ v = ℂ ∙ w ∧ μ = ν := by
  obtain ⟨h, hh⟩ := ExceptionalSieveWeights.exists_height_element H b
  have hline : ℂ ∙ v = ℂ ∙ w := by
    rcases le_total (μ h).re (ν h).re with hle | hle
    · obtain ⟨c, hcw⟩ := Submodule.mem_span_singleton.mp (mem_highest_line H b hv hw h hh hle
        (by rw [wordSpan_eq_top H b hv]; trivial))
      have hc : c ≠ 0 := fun hz => hw.1 (by simpa [hz] using hcw.symm)
      rw [← hcw, Submodule.span_singleton_smul_eq hc.isUnit]
    · obtain ⟨c, hcv⟩ := Submodule.mem_span_singleton.mp (mem_highest_line H b hw hv h hh hle
        (by rw [wordSpan_eq_top H b hw]; trivial))
      have hc : c ≠ 0 := fun hz => hv.1 (by simpa [hz] using hcv.symm)
      rw [← hcv, Submodule.span_singleton_smul_eq hc.isUnit]
  refine ⟨hline, ?_⟩
  obtain ⟨c, hcw⟩ := Submodule.mem_span_singleton.mp
    (show w ∈ ℂ ∙ v by rw [hline]; exact Submodule.mem_span_singleton_self _)
  funext x
  have hz : μ x • w = ν x • w := by
    rw [← hw.2.1 x, ← hcw, lie_smul, hv.2.1, smul_comm]
  exact (smul_left_injective ℂ hw.1) hz

end CubicAnomaly.Classification.ClassicalConstituentHighest
