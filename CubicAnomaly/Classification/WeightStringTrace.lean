import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.Trace

/-! The contribution of a raising/lowering pair to the quadratic Casimir
can be evaluated from the multiplicities along a root string. Cyclicity of
the rectangular trace moves one raising operator across the trace. -/

namespace CubicAnomaly.Classification.WeightStringTrace

open LieAlgebra LieModule Module

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M] (H : LieSubalgebra K L) [LieRing.IsNilpotent H]

/-- The operator of a root vector between two individual generalized weights. -/
private def shift {α μ ν : H → K} {x : L} (hx : x ∈ rootSpace H α) (h : α + μ = ν) :
    genWeightSpace M μ →ₗ[K] genWeightSpace M ν where
  toFun v := ⟨⁅x, v.val⁆, h ▸ lie_mem_genWeightSpace_of_mem_genWeightSpace hx v.property⟩
  map_smul' _ _ := Subtype.ext (lie_smul _ _ _)
  map_add' _ _ := Subtype.ext (lie_add _ _ _)

variable (M) {α : H → K} {e f : L}

/-- Lowering after raising as an endomorphism of the indicated weight subspace. -/
noncomputable def loweringRaisingEnd (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (μ : H → K) : Module.End K (genWeightSpace M μ) :=
  (shift H hf (neg_add_cancel_left α μ)).comp (shift H he rfl)

/-- Trace of lowering after raising, on the indicated weight subspace. -/
noncomputable def loweringRaisingTrace (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (μ : H → K) : K := LinearMap.trace K (genWeightSpace M μ)
      (loweringRaisingEnd M H he hf μ)

/-- The successive difference of the actual root-operator traces is the
weight multiplicity times the eigenvalue on the coroot. -/
theorem adjacent_weight_trace (h : H) (hef : ⁅e, f⁆ = h.val)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α)) (μ : H → K) :
    loweringRaisingTrace M H he hf μ = loweringRaisingTrace M H he hf (α + μ) +
      (finrank K (genWeightSpace M (α + μ)) : K) * (α + μ) h := by
  let ν := α + μ
  let U := genWeightSpace M μ
  let V := genWeightSpace M ν
  let E : U →ₗ[K] V := shift H he rfl
  let F : V →ₗ[K] U := shift H hf (neg_add_cancel_left α μ)
  let E' : V →ₗ[K] genWeightSpace M (α + ν) := shift H he rfl
  let F' : genWeightSpace M (α + ν) →ₗ[K] V := shift H hf (neg_add_cancel_left α ν)
  have comm : E.comp F = F'.comp E' + toEnd K H V h := by
    ext x
    change ⁅e, ⁅f, (x : M)⁆⁆ = ⁅f, ⁅e, (x : M)⁆⁆ + ⁅(h : L), (x : M)⁆
    rw [leibniz_lie, hef, add_comm]
  change LinearMap.trace K U (F.comp E) = LinearMap.trace K V (F'.comp E') + _
  rw [LinearMap.trace_comp_comm' E F, comm, map_add, LieModule.trace_toEnd_genWeightSpace]
  simp [ν, nsmul_eq_mul, mul_add]

/-- An empty weight space gives an explicit cutoff for the root-string trace. -/
theorem finite_weight_string_trace_of_cutoff (h : H) (hef : ⁅e, f⁆ = h.val)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α)) (μ : H → K)
    (n : ℕ) (hn : genWeightSpace M (n • α + μ) = ⊥) :
    loweringRaisingTrace M H he hf μ = ∑ i ∈ Finset.range n,
      (finrank K (genWeightSpace M ((i + 1) • α + μ)) : K) * ((i + 1) • α + μ) h := by
  classical
  let T (i : ℕ) := loweringRaisingTrace M H he hf (i • α + μ)
  let m (i : ℕ) := (finrank K (genWeightSpace M (i • α + μ)) : K) * (i • α + μ) h
  have hs (i : ℕ) : T i = T (i + 1) + m (i + 1) := by
    have ha : α + (i • α + μ) = (i + 1) • α + μ := by rw [succ_nsmul']; abel
    have hr := adjacent_weight_trace M H h hef he hf (i • α + μ)
    rw [ha] at hr
    exact hr
  have ht (j : ℕ) : T 0 = T j + ∑ i ∈ Finset.range j, m (i + 1) := by
    induction j with
    | zero => simp
    | succ i ih => rw [ih, hs i, Finset.sum_range_succ]; abel
  have hT : T n = 0 := by
    letI : Subsingleton (genWeightSpace M (n • α + μ)) := by rw [hn]; infer_instance
    unfold T loweringRaisingTrace loweringRaisingEnd
    rw [Subsingleton.elim (LinearMap.comp _ _) 0, map_zero]
  have hfin := ht n
  rw [hT, zero_add] at hfin
  simpa only [T, m, zero_nsmul, zero_add] using hfin

/-- Iterating the adjacent trace identity recovers the operator trace from
the multiplicities up to the first empty weight space. -/
theorem finite_weight_string_trace [CharZero K] {α : H → K} (hα : α ≠ 0)
    {e f : L} (h : H) (hef : ⁅e, f⁆ = h.val)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α)) (μ : H → K) :
    ∃ n : ℕ, genWeightSpace M (n • α + μ) = ⊥ ∧
      loweringRaisingTrace M H he hf μ = ∑ i ∈ Finset.range n,
        (finrank K (genWeightSpace M ((i + 1) • α + μ)) : K) * ((i + 1) • α + μ) h := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ, genWeightSpace M (n • α + μ) = ⊥ := by
    by_contra! hbad
    let f (i : ℕ) : Weight K H M := ⟨i • α + μ, hbad i⟩
    apply not_injective_infinite_finite f
    intro i j hij
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hα
    have hxy := congrArg (fun w : Weight K H M => w x) hij
    change i • α x + μ x = j • α x + μ x at hxy
    exact Nat.cast_injective (mul_right_cancel₀ hx (by simpa only [nsmul_eq_mul, add_left_inj] using hxy))
  exact ⟨n, hn, finite_weight_string_trace_of_cutoff M H h hef he hf μ n hn⟩

end CubicAnomaly.Classification.WeightStringTrace
