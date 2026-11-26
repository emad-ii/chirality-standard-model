import CubicAnomaly.Classification.ExceptionalSieveWeightOrbit

/-! A minuscule highest vector generates only its Weyl orbit of weight lines.
Any finite reflection-stable list of weights containing the highest weight
therefore bounds the dimension of the original irreducible module. -/

namespace CubicAnomaly.Classification.MinusculeDimension

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentHighest ClassicalConstituentWeyl

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
    [IsIrreducible ℂ L M] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    {χ : Weight ℂ H M} {v : M} (hv : IsHighestVector H b χ v)

include hv in
omit [FiniteDimensional ℂ M] in
private lemma above_zero {α : H.root} (hp : b.IsPos α) {y : M}
    (hy : ∀ z : H, ⁅(z : L), y⁆ = (χ z + α.val z) • y) : y = 0 := by
  by_contra hn
  obtain ⟨z, hz⟩ := ExceptionalSieveWeights.exists_height_element H b
  have h := eigenvalue_le_highest_at_height H b hv z hz hn (hy z)
  rw [Complex.add_re, hz, Complex.intCast_re] at h
  have hpos : 0 < b.height α := b.isPos_iff.mp hp
  exact (not_le_of_gt (Int.cast_pos.mpr hpos : (0 : ℝ) < b.height α)) (by linarith)

omit [FiniteDimensional ℂ M] [IsIrreducible ℂ L M] in
private lemma root_action_weight (α : H.root) {x : L} (hx : x ∈ rootSpace H α.val)
    {μ : H → ℂ} {y : M} (hy : ∀ z : H, ⁅(z : L), y⁆ = μ z • y) (z : H) :
    ⁅(z : L), ⁅x, y⁆⁆ = (μ z + α.val z) • ⁅x, y⁆ := by
  have hh : ⁅(z : L), x⁆ = α.val z • x := lie_eq_smul_of_mem_rootSpace hx z
  rw [leibniz_lie, hh, smul_lie, hy, lie_smul, add_smul, add_comm]

include hv in
private lemma highest_line {y : M} (hy : ∀ z : H, ⁅(z : L), y⁆ = χ z • y) : y ∈ ℂ ∙ v := by
  by_cases hy0 : y = 0
  · rw [hy0]; exact Submodule.zero_mem _
  have hy' : IsHighestVector H b χ y := ⟨hy0, hy,
    fun α hp x hx => above_zero H b hv hp (root_action_weight H α hx hy)⟩
  rw [(irreducible_highest_weight_unique H b hv hy').1]
  exact Submodule.mem_span_singleton_self _

omit [IsIrreducible ℂ L M] in
private lemma transport_eigen (w : List H.root) {μ : H → ℂ} {y : M}
    (hy : ∀ z : H, ⁅(z : L), y⁆ = μ (cartanWord H w z) • y) :
    ∃ E : M ≃ₗ[ℂ] M, ∀ z : H, ⁅(z : L), E y⁆ = μ z • E y := by
  obtain ⟨σ, E, hσ, hE⟩ := exists_module_weyl_word (M := M) H w
  refine ⟨E, fun z => ?_⟩
  obtain ⟨z, rfl⟩ := (cartanWord H w).surjective z
  rw [← hσ, ← hE, hy, map_smul]

omit [IsIrreducible ℂ L M] in
private lemma reflected (α : H.root) (z : H) :
    χ ((rootSystem H).coreflection α z) = χ z - α.val z * χ (coroot α.val) := by
  change (χ : H →ₗ[ℂ] ℂ) (z - α.val z • coroot α.val) = _
  rw [map_sub, map_smul, smul_eq_mul]
  rfl

private lemma word_append_one (w : List H.root) (α : H.root) (z : H) :
    cartanWord H (w ++ [α]) z = (rootSystem H).coreflection α (cartanWord H w z) := by
  induction w generalizing z with
  | nil => rfl
  | cons j w ih => exact ih ((rootSystem H).coreflection j z)

include hv in
private lemma advance (w : List H.root) {y : M}
    (hy : ∀ z : H, ⁅(z : L), y⁆ = χ (cartanWord H w z) • y)
    (j : H.root) {x : L} (hx : x ∈ rootSpace H j.val)
    (hmin : ∀ i : H.root, b.IsPos i → χ (coroot i.val) = 0 ∨ χ (coroot i.val) = 1) :
    ⁅x, y⁆ = 0 ∨ ∃ w' : List H.root, ∀ z : H, ⁅(z : L), ⁅x, y⁆⁆ = χ (cartanWord H w' z) • ⁅x, y⁆ := by
  let β := rootWord H w j
  let R := fun z : H => χ z + β.val z
  have hxy (z : H) : ⁅(z : L), ⁅x, y⁆⁆ = R (cartanWord H w z) • ⁅x,y⁆ := by
    dsimp only [R]
    rw [root_action_weight H j hx hy, show β.val (cartanWord H w z) = j.val z from word_root_eval H w j z]
  by_cases hp : b.IsPos β
  · obtain ⟨E, hE⟩ := transport_eigen H w hxy
    exact Or.inl (E.map_eq_zero_iff.mp (above_zero H b hv hp hE))
  letI := (rootSystem H).indexNeg
  let γ := -β
  have hp' : b.IsPos γ := (RootPairing.Base.IsPos.neg_iff_not b β).mpr hp
  have hneg : (γ.val : H → ℂ) = -(β.val : H → ℂ) :=
    congrArg DFunLike.coe (((rootSystem H).root_reflectionPerm β β).trans ((rootSystem H).reflection_apply_self β))
  have hR (z : H) : R z = χ z - γ.val z := by
    change χ z + β.val z = χ z - γ.val z
    rw [show γ.val z = -β.val z from congrFun hneg z]; ring
  rcases hmin γ hp' with h0 | h1
  · obtain ⟨E, hE⟩ := transport_eigen H w hxy
    let r := (rootSystem H).coreflection γ
    have hγ (z : H) : γ.val (r z) = -γ.val z := by
      change (γ.val : H →ₗ[ℂ] ℂ) (z - γ.val z • coroot γ.val) = _
      rw [map_sub, map_smul, smul_eq_mul]
      change γ.val z - γ.val z * γ.val (coroot γ.val) = _
      rw [root_apply_coroot (Finset.mem_filter.mp γ.property).2]; ring
    have hE' (z : H) : ⁅(z : L), E ⁅x,y⁆⁆ =
        (χ (cartanWord H [γ] z) + γ.val (cartanWord H [γ] z)) • E ⁅x,y⁆ := by
      change _ = (χ (r z) + γ.val (r z)) • _
      rw [hE, hR, hγ, reflected H γ, h0, mul_zero, sub_zero, sub_eq_add_neg]
    obtain ⟨F, hF⟩ := transport_eigen H [γ] (μ := fun z => χ z + γ.val z) hE'
    exact Or.inl (E.map_eq_zero_iff.mp (F.map_eq_zero_iff.mp (above_zero H b hv hp' hF)))
  · refine Or.inr ⟨w ++ [γ], fun z => ?_⟩
    rw [hxy, hR, word_append_one, reflected H γ, h1, mul_one]

include hv in
private lemma orbit_line (w : List H.root) :
    ∃ u : M, ∀ y : M, (∀ z : H, ⁅(z : L), y⁆ = χ (cartanWord H w z) • y) → y ∈ ℂ ∙ u := by
  obtain ⟨σ, E, hs, hE⟩ := exists_module_weyl_word (M := M) H w
  refine ⟨E.symm v, fun y hy => ?_⟩
  have hm := highest_line H b hv (y := E y) (fun z => by
    obtain ⟨z, rfl⟩ := (cartanWord H w).surjective z
    rw [← hs, ← hE, hy, map_smul])
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  exact Submodule.mem_span_singleton.mpr ⟨a, E.injective (by rw [map_smul, E.apply_symm_apply, ha])⟩

include hv in
/-- A finite set containing the minuscule highest weight and closed under
the actual root reflections bounds the dimension of the actual module. -/
theorem finrank_le_card_of_minuscule_orbit (S : Finset (H → ℂ)) (hbase : (χ : H → ℂ) ∈ S)
    (hstable : ∀ μ ∈ S, ∀ i : H.root, (fun x => μ ((rootSystem H).coreflection i x)) ∈ S)
    (hmin : ∀ i : H.root, b.IsPos i → χ (coroot i.val) = 0 ∨ χ (coroot i.val) = 1) :
    finrank ℂ M ≤ S.card := by
  classical
  have hS (w : List H.root) : (fun z => χ (cartanWord H w z)) ∈ S := by
    induction w with
    | nil => exact hbase
    | cons i w ih => exact hstable _ ih i
  let idx (w : List H.root) : S := ⟨_, hS w⟩
  have exists_line (s : S) : ∃ u : M, ∀ (w : List H.root), idx w = s →
      ∀ y : M, (∀ z : H, ⁅(z : L), y⁆ = s.val z • y) → y ∈ ℂ ∙ u := by
    by_cases he : ∃ w, idx w = s
    · obtain ⟨w, rfl⟩ := he
      obtain ⟨u, hu⟩ := orbit_line H b hv w
      exact ⟨u, fun _ _ y hy => hu y hy⟩
    · exact ⟨0, fun w hw => (he ⟨w, hw⟩).elim⟩
  choose u hu using exists_line
  have covers (l : List (Lowering H b)) : word H b v l = 0 ∨
      ∃ w : List H.root, ∀ z : H, ⁅(z : L), word H b v l⁆ = χ (cartanWord H w z) • word H b v l := by
    induction l with
    | nil => exact Or.inr ⟨[], hv.2.1⟩
    | cons f l ih =>
      rcases ih with hz | ⟨w, hw⟩
      · exact Or.inl (by rw [word, hz, lie_zero])
      · exact advance H b hv w hw f.root f.mem hmin
  suffices h : Submodule.span ℂ (Set.range u) = ⊤ by
    simpa using finrank_le_of_span_eq_top h
  apply top_unique
  rw [← wordSpan_eq_top H b hv]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  rcases covers l with hz | ⟨w, hw⟩
  · rw [hz]; exact Submodule.zero_mem _
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self (idx w)))
      (hu (idx w) w rfl _ hw)

end CubicAnomaly.Classification.MinusculeDimension
