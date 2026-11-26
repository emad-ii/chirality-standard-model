import CubicAnomaly.Classification.ClassicalConstituentWeyl

/-! # Weyl invariance of actual weight multiplicities

A module isomorphism realizing a Weyl word maps the entire generalized
weight space onto the corresponding transformed weight space.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveWeightOrbit

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentWeyl ClassicalConstituentHighest

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

omit [FiniteDimensional ℂ L] [IsKilling ℂ L] [FiniteDimensional ℂ M] in
private lemma weight_mem_iff (T : H ≃ₗ[ℂ] H) (E : M ≃ₗ[ℂ] M)
    (h : ∀ (z : H) (v : M), E ⁅z,v⁆ = ⁅T z,E v⁆)
    (μ ν : H → ℂ) (ht : ∀ z, ν (T z) = μ z) (v : M) :
    E v ∈ genWeightSpace M ν ↔ v ∈ genWeightSpace M μ := by
  simp only [mem_genWeightSpace]
  have powers (z : H) (n : ℕ) :
      ((toEnd ℂ H M (T z) - ν (T z) • 1)^n).comp E.toLinearMap =
        E.toLinearMap.comp ((toEnd ℂ H M z - μ z • 1)^n) := by
    apply Module.End.commute_pow_left_of_commute _ n
    ext x
    change ⁅T z, E x⁆ - ν (T z) • E x = E (⁅z,x⁆ - μ z • x)
    rw [map_sub, map_smul, h, ht]
  constructor
  · intro hv z
    obtain ⟨n, hn⟩ := hv (T z)
    refine ⟨n, E.injective ?_⟩
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hn, map_zero] using
      (LinearMap.congr_fun (powers z n) v).symm
  · intro hv u
    obtain ⟨z, rfl⟩ := T.surjective u
    obtain ⟨n, hn⟩ := hv z
    refine ⟨n, ?_⟩
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hn, map_zero] using
      LinearMap.congr_fun (powers z n) v

/-- A Weyl word preserves all generalized weight multiplicities in the
actual module, including the zero multiplicities outside its support. -/
theorem multiplicity_of_weyl_word (w : List H.root) (μ ν : H → ℂ)
    (ht : ∀ z, ν (cartanWord H w z) = μ z) :
    finrank ℂ (genWeightSpace M μ) = finrank ℂ (genWeightSpace M ν) := by
  obtain ⟨σ, τ, hσ, hτ⟩ := exists_module_weyl_word (M := M) H w
  have h (z : H) (v : M) : τ ⁅z,v⁆ = ⁅cartanWord H w z, τ v⁆ := by
    simpa only [hσ] using hτ z.val v
  have hmap : (genWeightSpace M μ).toSubmodule.map τ.toLinearMap = (genWeightSpace M ν).toSubmodule := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (weight_mem_iff H _ τ h μ ν ht a).mpr ha
    · intro hx
      exact ⟨τ.symm x, (weight_mem_iff H _ τ h μ ν ht _).mp (by simpa using hx), τ.apply_symm_apply x⟩
  exact (τ.ofSubmodules _ _ hmap).finrank_eq


/-- A nonnegative integral combination of the actual simple root functions. -/
noncomputable def positiveRootSum (b : (rootSystem H).Base) (c : b.support → ℕ) : H → ℂ :=
  ∑ i, c i • (i.val.val : H → ℂ)

private lemma positive_sum_add (b : (rootSystem H).Base) (a c : b.support → ℕ) :
    positiveRootSum H b (a + c) = positiveRootSum H b a + positiveRootSum H b c := by
  simp only [positiveRootSum, Pi.add_apply, add_nsmul, Finset.sum_add_distrib]

private lemma positive_sum_single (b : (rootSystem H).Base) (i : b.support) [DecidableEq b.support] :
    positiveRootSum H b (Pi.single i 1) = (i.val.val : H → ℂ) := by
  classical
  simp only [positiveRootSum, Pi.single_apply, ite_smul, zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma positive_root_coefficients (b : (rootSystem H).Base) (α : H.root) (hp : b.IsPos α) :
    ∃ c : b.support → ℕ, (α.val : H → ℂ) = positiveRootSum H b c := by
  classical
  apply hp.induction_on_add (p := fun α => ∃ c, (α.val : H → ℂ) = positiveRootSum H b c)
  · intro i hi
    exact ⟨Pi.single ⟨i, hi⟩ 1, (positive_sum_single H b ⟨i, hi⟩).symm⟩
  · rintro i j k hk ⟨c, hc⟩ hj
    refine ⟨c + Pi.single ⟨j, hj⟩ 1, ?_⟩
    rw [positive_sum_add, positive_sum_single H b ⟨j, hj⟩, ← hc]
    exact congrArg DFunLike.coe hk

omit [FiniteDimensional ℂ M] in
private lemma word_weight (b : (rootSystem H).Base) {ν : H → ℂ} {v : M}
    (hv : IsHighestVector H b ν v) (w : List (Lowering H b)) :
    ∃ c, word H b v w ∈ genWeightSpace M (ν - positiveRootSum H b c) := by
  classical
  induction w with
  | nil =>
    refine ⟨0, ?_⟩
    simpa only [positiveRootSum, Pi.zero_apply, zero_nsmul, Finset.sum_const_zero, sub_zero, word]
      using (weightSpace_le_genWeightSpace M ν ((mem_weightSpace _ _).mpr hv.2.1))
  | cons a w ih =>
    obtain ⟨c, hc⟩ := ih
    letI := (rootSystem H).indexNeg
    obtain ⟨u, hu⟩ := positive_root_coefficients H b (-a.root)
      ((RootPairing.Base.IsPos.neg_iff_not b a.root).mpr a.neg)
    have hneg : ((-a.root).val : H → ℂ) = -(a.root.val : H → ℂ) := by
      apply congrArg DFunLike.coe
        ((rootSystem H).root_reflectionPerm a.root a.root |>.trans ((rootSystem H).reflection_apply_self a.root))
    have hν : (a.root.val : H → ℂ) + (ν - positiveRootSum H b c) = ν - positiveRootSum H b (c + u) := by
      rw [positive_sum_add, ← hu, hneg]
      abel
    exact ⟨c + u, hν ▸ lie_mem_genWeightSpace_of_mem_genWeightSpace a.mem hc⟩

omit [FiniteDimensional ℂ M] in
/-- Every actual weight is the highest weight minus a nonnegative integral
combination of the chosen simple roots. This upper support bound applies to
all generalized weights simultaneously. -/
theorem weight_le_highest_in_root_cone [IsIrreducible ℂ L M] (b : (rootSystem H).Base)
    {ν : H → ℂ} {v : M} (hv : IsHighestVector H b ν v) (μ : Weight ℂ H M) :
    ∃ c : b.support → ℕ, (μ : H → ℂ) = ν - positiveRootSum H b c := by
  classical
  by_contra h
  have hne (c : b.support → ℕ) : ν - positiveRootSum H b c ≠ (μ : H → ℂ) :=
    fun hh => h ⟨c, hh.symm⟩
  let U := ⨆ θ ∈ {θ : H → ℂ | θ ≠ (μ : H → ℂ)}, (genWeightSpace M θ).toSubmodule
  have hspan : wordSpan H b v ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    obtain ⟨c, hc⟩ := word_weight H b hv w
    exact (le_iSup₂_of_le (ν - positiveRootSum H b c) (hne c) le_rfl :
      (genWeightSpace M _).toSubmodule ≤ U) hc
  rw [wordSpan_eq_top H b hv] at hspan
  have hind : iSupIndep (fun θ : H → ℂ => (genWeightSpace M θ).toSubmodule) :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace ℂ H M)
  obtain ⟨x, hx, hx0⟩ := μ.exists_ne_zero
  exact hx0 ((hind (μ : H → ℂ)).le_bot (show x ∈ (genWeightSpace M (μ : H → ℂ)).toSubmodule ⊓ U from
    ⟨hx, hspan Submodule.mem_top⟩))

end CubicAnomaly.Classification.ExceptionalSieveWeightOrbit
