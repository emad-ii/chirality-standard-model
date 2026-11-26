import CubicAnomaly.Classification.ExceptionalSieveCasimir
import CubicAnomaly.Classification.WeightStringTrace

/-! # Freudenthal's weight-multiplicity recurrence for the actual representation

Taking the trace of the inverse-Killing Casimir on an individual weight
space expresses its multiplicity through the higher weights on positive
root strings. All scalar products use the actual inverse Killing form.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveFreudenthal

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ExceptionalSieveCasimir WeightStringTrace
open scoped TensorProduct

noncomputable section

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

private def rootEnd (μ : H → ℂ) (α : H.root) : Module.End ℂ (genWeightSpace M μ) :=
  (pairScale H α)⁻¹ • loweringRaisingEnd M H (rootPair H α).he (rootPair H α).hf μ

private theorem casimir_trace_on_weight {c : ℂ} (hc : casimirOperator L M = c • LinearMap.id)
    (μ : Dual ℂ H) :
    c * (finrank ℂ (genWeightSpace M (μ : H → ℂ)) : ℂ) =
      μ ((cartanEquivDual H).symm μ) * finrank ℂ (genWeightSpace M (μ : H → ℂ)) +
      ∑ α : H.root, LinearMap.trace ℂ _ (rootEnd (M := M) H μ α) := by
  let V := genWeightSpace M (μ : H → ℂ)
  let b := Module.finBasis ℂ H
  let C (i : Fin (finrank ℂ H)) := toEnd ℂ H V (cartanDual H b i) * toEnd ℂ H V (b i)
  have hOp : (c • LinearMap.id : Module.End ℂ V) =
      (∑ i, C i) + ∑ α : H.root, rootEnd (M := M) H μ α := by
    ext1 v
    apply Subtype.ext
    have hv := LinearMap.congr_fun hc v.val
    rw [casimirOperator, casimir_tensor_by_roots H b, map_add, map_sum, LinearMap.add_apply,
      LinearMap.sum_apply, cartanTensor, map_sum, LinearMap.sum_apply] at hv
    change c • v.val = ((∑ i, C i) v + (∑ α, rootEnd (M := M) H μ α) v).val
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    change c • v.val = V.toSubmodule.subtype (∑ i, C i v) +
      V.toSubmodule.subtype (∑ α, rootEnd (M := M) H μ α v)
    rw [map_sum, map_sum]
    apply hv.symm.trans
    congr 1
    apply Finset.sum_congr rfl
    intro α _
    rw [rootTensor, map_smul]
    rfl
  have hTr (i : Fin (finrank ℂ H)) : LinearMap.trace ℂ V (C i) =
      (μ (b i) * μ (cartanDual H b i)) * finrank ℂ V := by
    have ht := traceForm_genWeightSpace_eq ℂ H M (μ : H → ℂ) (cartanDual H b i) (b i)
    change LinearMap.trace ℂ V (C i) = _ at ht
    rw [ht]
    simp only [nsmul_eq_mul]
    ring
  have hSum : (∑ i, μ (b i) * μ (cartanDual H b i)) = μ ((cartanEquivDual H).symm μ) := by
    have h := congrArg (fun u : Dual ℂ H => μ ((cartanEquivDual H).symm u)) (b.dualBasis.sum_repr μ)
    simpa only [map_sum, map_smul, Basis.dualBasis_repr, smul_eq_mul] using h
  have h := congrArg (LinearMap.trace ℂ V) hOp
  simpa only [map_smul, LinearMap.trace_id, smul_eq_mul, map_add, map_sum, hTr, ← Finset.sum_mul,
    hSum] using h

/-- The sum of the higher multiplicities on one root string, contracted
against the same root with the inverse Killing form. -/
def stringContribution (μ α : Dual ℂ H) (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M] : ℂ :=
  ∑ j ∈ Finset.range n,
    (finrank ℂ (genWeightSpace M ((j + 1) • (α : H → ℂ) + (μ : H → ℂ))) : ℂ) *
    (((j + 1) • α + μ) ((cartanEquivDual H).symm α))

private theorem normalized_string {α : Dual ℂ H} {e f : L} (h : H) (scale : ℂ)
    (hs : scale ≠ 0) (hc : h = scale • (cartanEquivDual H).symm α)
    (hef : ⁅e, f⁆ = h.val) (he : e ∈ rootSpace H (α : H → ℂ))
    (hf : f ∈ rootSpace H (-(α : H → ℂ)))
    (μ : Dual ℂ H) (n : ℕ) (hn : genWeightSpace M (n • (α : H → ℂ) + (μ : H → ℂ)) = ⊥) :
    scale⁻¹ * loweringRaisingTrace M H he hf μ = stringContribution H μ α n M := by
  rw [finite_weight_string_trace_of_cutoff M H h hef he hf μ n hn, stringContribution,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hv : ((i + 1) • (α : H → ℂ) + (μ : H → ℂ)) h =
      scale * (((i + 1) • α + μ) ((cartanEquivDual H).symm α)) := by
    change (((i + 1) • α + μ) h) = _
    rw [hc, map_smul, smul_eq_mul]
  rw [hv]
  field_simp

private theorem root_trace (μ : Dual ℂ H) (α : H.root) (n : ℕ)
    (hn : genWeightSpace M (n • (α.val : H → ℂ) + (μ : H → ℂ)) = ⊥) :
    LinearMap.trace ℂ _ (rootEnd (M := M) H μ α) =
      stringContribution H μ (α.val : Dual ℂ H) n M := by
  rw [rootEnd, map_smul, smul_eq_mul]
  exact normalized_string H _ _ (pairScale_ne_zero H α) (coroot_eq_pairScale_smul_dual H α)
    (rootPair H α).triple.lie_e_f (rootPair H α).he (rootPair H α).hf μ n hn

private theorem negative_root_trace (μ : Dual ℂ H) (α : H.root) (n : ℕ)
    (hn : genWeightSpace M (n • (α.val : H → ℂ) + (μ : H → ℂ)) = ⊥) :
    letI := (rootSystem H).indexNeg
    LinearMap.trace ℂ _ (rootEnd (M := M) H μ (-α)) =
      stringContribution H μ (α.val : Dual ℂ H) n M +
      μ ((cartanEquivDual H).symm α.val) * finrank ℂ (genWeightSpace M (μ : H → ℂ)) := by
  letI := (rootSystem H).indexNeg
  let P := rootPair H (-α)
  let s := pairScale H (-α)
  let h := -coroot (-α).val
  have dual_neg : ((-α).val : Dual ℂ H) = -(α.val : Dual ℂ H) := by
    change (rootSystem H).root (-α) = -(rootSystem H).root α
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have fn_neg : ((-α).val : H → ℂ) = -(α.val : H → ℂ) := congrArg DFunLike.coe dual_neg
  have he : P.f ∈ rootSpace H (α.val : H → ℂ) := by
    simpa only [fn_neg, neg_neg] using P.hf
  have hf : P.e ∈ rootSpace H (-(α.val : H → ℂ)) := by
    simpa only [fn_neg] using P.he
  have hb : ⁅P.f, P.e⁆ = h.val := by
    rw [← lie_skew P.f P.e, P.triple.lie_e_f]
    rfl
  have hs : s ≠ 0 := pairScale_ne_zero H _
  have hc : h = s • (cartanEquivDual H).symm (α.val : Dual ℂ H) := by
    dsimp only [h, s]
    rw [coroot_eq_pairScale_smul_dual, dual_neg, map_neg, smul_neg, neg_neg]
  have hop : loweringRaisingEnd M H P.he P.hf μ =
      loweringRaisingEnd M H he hf μ + toEnd ℂ H (genWeightSpace M (μ : H → ℂ)) h := by
    ext1 v
    apply Subtype.ext
    change ⁅P.f, ⁅P.e, (v : M)⁆⁆ = ⁅P.e, ⁅P.f, (v : M)⁆⁆ + ⁅h.val, (v : M)⁆
    rw [leibniz_lie, hb, add_comm]
  have ht := normalized_string H h s hs hc hb he hf μ n hn
  change s⁻¹ * LinearMap.trace ℂ _ (loweringRaisingEnd M H he hf μ) = _ at ht
  rw [rootEnd, map_smul, smul_eq_mul]
  change s⁻¹ * LinearMap.trace ℂ _ (loweringRaisingEnd M H P.he P.hf μ) = _
  rw [hop, map_add, LieModule.trace_toEnd_genWeightSpace, mul_add, ht, hc, map_smul,
    smul_eq_mul, nsmul_eq_mul]
  congr 1
  field_simp


private theorem sum_over_opposites (b : (rootSystem H).Base) (F : H.root → ℂ) :
    letI := (rootSystem H).indexNeg
    letI := Classical.propDecidable
    ∑ α, F α = ∑ α, if b.IsPos α then F α + F (-α) else 0 := by
  classical
  letI := (rootSystem H).indexNeg
  let g (α : H.root) := if b.IsPos α then 0 else F α
  calc
    _ = (∑ α, if b.IsPos α then F α else 0) + ∑ α, g α := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro α _
      by_cases hp : b.IsPos α <;> simp [g, hp]
    _ = _ := by
      rw [← Equiv.sum_comp (Equiv.neg H.root) g, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro α _
      by_cases hp : b.IsPos α
      · have hn := (RootPairing.Base.IsPos.neg_iff_not b α).not.mpr (not_not.mpr hp)
        simp only [Equiv.neg_apply, g, hp, hn, if_true, if_false]
      · have hn := (RootPairing.Base.IsPos.neg_iff_not b α).mpr hp
        simp only [Equiv.neg_apply, g, hp, hn, if_true, if_false, add_zero]

/-- Freudenthal's recurrence for an actual irreducible representation. The
finite cutoffs on every root string include all nonzero higher weights.
The left coefficient is the difference of the inverse-Killing Casimir
quadratics at the highest weight and the weight under consideration. -/
theorem freudenthal_weight_multiplicity [IsIrreducible ℂ L M]
    (b : (rootSystem H).Base) (ν μ : Dual ℂ H)
    {v : M} (hv : v ≠ 0) (hev : ∀ h : H, ⁅h, v⁆ = ν h • v)
    (hkill : ∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, v⁆ = 0) :
    letI := Classical.propDecidable
    ∃ n : H.root → ℕ,
      (∀ (α : H.root) (j : ℕ), n α ≤ j →
        genWeightSpace M (j • (α.val : H → ℂ) + (μ : H → ℂ)) = ⊥) ∧
      (highestCasimirValue H b ν - highestCasimirValue H b μ) *
          finrank ℂ (genWeightSpace M (μ : H → ℂ)) =
        2 * ∑ α : H.root, if b.IsPos α then stringContribution H μ α.val (n α) M else 0 := by
  classical
  letI := (rootSystem H).indexNeg
  have bounds (α : H.root) := Filter.eventually_atTop.mp
    (LieModule.eventually_genWeightSpace_smul_add_eq_bot M (α.val : H → ℂ) (μ : H → ℂ)
      (Finset.mem_filter.mp α.property).2)
  choose n hn using bounds
  refine ⟨n, hn, ?_⟩
  obtain ⟨c, hc⟩ := irreducible_casimir_scalar (L := L) (M := M)
  have ht := highest_weight_casimir_formula H b ν hev hkill
  rw [hc] at ht
  have hc' : c = highestCasimirValue H b ν := smul_left_injective ℂ hv ht
  let m : ℂ := finrank ℂ (genWeightSpace M (μ : H → ℂ))
  let F (α : H.root) := LinearMap.trace ℂ _ (rootEnd (M := M) H μ α)
  let p (α : H.root) := if b.IsPos α then stringContribution H μ α.val (n α) M else 0
  let r (α : H.root) := if b.IsPos α then μ ((cartanEquivDual H).symm α.val) else 0
  have hs : ∑ α, F α = 2 * ∑ α, p α + (∑ α, r α) * m := by
    rw [sum_over_opposites H b F, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α _
    by_cases hp : b.IsPos α
    · simp only [F, p, r, hp, if_true, root_trace H μ α (n α) (hn α _ le_rfl),
        negative_root_trace H μ α (n α) (hn α _ le_rfl)]
      dsimp only [m]
      ring
    · simp only [p, r, hp, if_false, mul_zero, zero_mul, add_zero]
  have h := casimir_trace_on_weight H hc μ
  change c * m = μ ((cartanEquivDual H).symm μ) * m + ∑ α, F α at h
  rw [hc', hs] at h
  change (highestCasimirValue H b ν - (μ ((cartanEquivDual H).symm μ) + ∑ α, r α)) * m =
    2 * ∑ α, p α
  linear_combination h


end

end CubicAnomaly.Classification.ExceptionalSieveFreudenthal
