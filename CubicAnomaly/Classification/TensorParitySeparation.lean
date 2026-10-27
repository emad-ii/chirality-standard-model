import CubicAnomaly.Classification.TensorParityBlocks

/-!
# Separating actual tensor parity blocks from the diagonal action

Partial traces kill the two trace-zero parity blocks. On the diagonal
Lie action they recover the two factor actions. A partial adjoint then
separates the two opposite parity blocks. Together these constructions
show that their sum has zero intersection with the actual action image.
No nondegeneracy theorem for the trace form of a representation is used.
-/

namespace CubicAnomaly.Classification.TensorParitySeparation

open Module LieModule
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.TensorEndomorphisms
open CubicAnomaly.Classification.TensorParityBlocks
open scoped TensorProduct

noncomputable section

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [FiniteDimensional K M] [FiniteDimensional K N]

/-- Partial trace in the second defining factor, transported through the
actual tensor endomorphism equivalence. -/
def leftPartialTrace : Module.End K (M ⊗[K] N) →ₗ[K] Module.End K M :=
  (TensorProduct.rid K (Module.End K M)).toLinearMap.comp
    (((LinearMap.trace K N).lTensor (Module.End K M)).comp
      (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).symm.toLinearMap)

/-- Partial trace in the first defining factor. -/
def rightPartialTrace : Module.End K (M ⊗[K] N) →ₗ[K] Module.End K N :=
  (TensorProduct.lid K (Module.End K N)).toLinearMap.comp
    (((LinearMap.trace K M).rTensor (Module.End K N)).comp
      (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).symm.toLinearMap)

/-- The first partial trace has its literal pure-operator formula. -/
@[simp] theorem left_partial_trace_map (A : Module.End K M) (B : Module.End K N) :
    leftPartialTrace (L := L) (TensorProduct.map A B) = LinearMap.trace K N B • A := by
  rw [← tensor_endomorphism_equiv_tmul (L := L)]
  simp [leftPartialTrace]

/-- The second partial trace has its literal pure-operator formula. -/
@[simp] theorem right_partial_trace_map (A : Module.End K M) (B : Module.End K N) :
    rightPartialTrace (L := L) (TensorProduct.map A B) = LinearMap.trace K M A • B := by
  rw [← tensor_endomorphism_equiv_tmul (L := L)]
  simp [rightPartialTrace]

omit [FiniteDimensional K M] [FiniteDimensional K N] in
/-- The actual diagonal Lie action is the sum of the two literal tensor
factor operators. -/
theorem tensor_action_eq_sum (x : L) :
    toEnd K L (M ⊗[K] N) x =
      TensorProduct.map (toEnd K L M x) (1 : Module.End K N) +
        TensorProduct.map (1 : Module.End K M) (toEnd K L N x) := by
  apply TensorProduct.ext'
  intro m n
  rfl

/-- Partial adjoint in the first defining factor. -/
def leftPartialAdjoint (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate) :
    Module.End K (M ⊗[K] N) →ₗ[K] Module.End K (M ⊗[K] N) :=
  (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).toLinearMap.comp
    (((formAdjoint β hβ).rTensor (Module.End K N)).comp
      (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).symm.toLinearMap)

/-- Partial adjoint applies the actual form adjoint in the first factor. -/
@[simp] theorem left_partial_adjoint_map
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate)
    (A : Module.End K M) (B : Module.End K N) :
    leftPartialAdjoint (L := L) β hβ (TensorProduct.map A B) =
      TensorProduct.map (formAdjoint β hβ A) B := by
  rw [← tensor_endomorphism_equiv_tmul (L := L)]
  change tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)
    (((formAdjoint β hβ).rTensor (Module.End K N))
      ((tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).symm
        (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N) (A ⊗ₜ[K] B)))) = _
  rw [LieModuleEquiv.symm_apply_apply, LinearMap.rTensor_tmul]
  exact tensor_endomorphism_equiv_tmul _ _

/-- A skew-adjoint operator has negative actual form adjoint. -/
theorem form_adjoint_eq_neg_of_skew
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate)
    (A : Module.End K M) (hA : ∀ u v, β (A u) v = -β u (A v)) :
    formAdjoint β hβ A = -A := by
  symm
  apply (β.isAdjointPair_iff_eq_of_nondegenerate hβ (-A) A).mp
  intro u v
  simp only [LinearMap.neg_apply, map_neg, hA, neg_neg]

variable [CharZero K]

/-- Every operator preserving a nondegenerate bilinear form is traceless.
Reflexivity of the form is not needed. -/
theorem trace_eq_zero_of_skew
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate)
    (A : Module.End K M) (hA : ∀ u v, β (A u) v = -β u (A v)) :
    LinearMap.trace K M A = 0 := by
  have ht := trace_form_adjoint β hβ A
  rw [form_adjoint_eq_neg_of_skew β hβ A hA, map_neg] at ht
  have htwo : (2 : K) * LinearMap.trace K M A = 0 := by linear_combination -ht
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Invariance of a nondegenerate factor form forces each actual action
operator to have zero trace. -/
theorem invariant_action_trace_zero
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate) (hi : β.lieInvariant L)
    (x : L) : LinearMap.trace K M (toEnd K L M x) = 0 :=
  trace_eq_zero_of_skew β hβ _ (hi x)

/-- Both partial traces of an actual left parity block vanish. -/
theorem left_parity_block_partial_traces_zero
    (I : LieIdeal K L) (β : LinearMap.BilinForm K M)
    (hβ : β.Nondegenerate) (hiβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hiγ : γ.lieInvariant L)
    (t : I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hiγ) :
    leftPartialTrace (L := L) (leftParityBlock (M := M) I γ hiγ t) = 0 ∧
      rightPartialTrace (L := L) (leftParityBlock (M := M) I γ hiγ t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x p =>
    rw [left_parity_block_tmul, left_partial_trace_map, right_partial_trace_map]
    exact ⟨by rw [show LinearMap.trace K N (p : Module.End K N) = 0 from p.property.2,
      zero_smul], by rw [invariant_action_trace_zero β hβ hiβ, zero_smul]⟩
  | add t u ht hu =>
    simp only [map_add, ht.1, ht.2, hu.1, hu.2, add_zero, and_self]

/-- Both partial traces of an actual right parity block vanish. -/
theorem right_parity_block_partial_traces_zero
    (J : LieIdeal K L) (β : LinearMap.BilinForm K M) (hiβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.Nondegenerate) (hiγ : γ.lieInvariant L)
    (t : traceZeroSelfAdjointLieSubmodule β hiβ ⊗[K] J) :
    leftPartialTrace (L := L) (rightParityBlock (N := N) J β hiβ t) = 0 ∧
      rightPartialTrace (L := L) (rightParityBlock (N := N) J β hiβ t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p x =>
    rw [right_parity_block_tmul, left_partial_trace_map, right_partial_trace_map]
    exact ⟨by rw [invariant_action_trace_zero γ hγ hiγ, zero_smul],
      by rw [show LinearMap.trace K M (p : Module.End K M) = 0 from p.property.2,
        zero_smul]⟩
  | add t u ht hu =>
    simp only [map_add, ht.1, ht.2, hu.1, hu.2, add_zero, and_self]

omit [CharZero K] in
/-- The left block is negative under partial adjoint in the left factor. -/
theorem left_parity_block_partial_adjoint
    (I : LieIdeal K L) (β : LinearMap.BilinForm K M)
    (hβ : β.Nondegenerate) (hiβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hiγ : γ.lieInvariant L)
    (t : I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hiγ) :
    leftPartialAdjoint (L := L) β hβ (leftParityBlock (M := M) I γ hiγ t) =
      -leftParityBlock (M := M) I γ hiγ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x p =>
    rw [left_parity_block_tmul, left_partial_adjoint_map,
      form_adjoint_eq_neg_of_skew β hβ _ (hiβ (x : L))]
    apply TensorProduct.ext'
    intro m n
    simp only [TensorProduct.map_tmul, LinearMap.neg_apply, TensorProduct.neg_tmul]
  | add t u ht hu => simp only [map_add, ht, hu, neg_add]

omit [CharZero K] in
/-- The right block is fixed under partial adjoint in the left factor. -/
theorem right_parity_block_partial_adjoint
    (J : LieIdeal K L) (β : LinearMap.BilinForm K M)
    (hβ : β.Nondegenerate) (hiβ : β.lieInvariant L)
    (t : traceZeroSelfAdjointLieSubmodule β hiβ ⊗[K] J) :
    leftPartialAdjoint (L := L) β hβ (rightParityBlock (N := N) J β hiβ t) =
      rightParityBlock (N := N) J β hiβ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p x =>
    rw [right_parity_block_tmul, left_partial_adjoint_map,
      (mem_selfAdjoint_iff_form_adjoint β hβ (p : Module.End K M)).mp p.property.1]
  | add t u ht hu => simp only [map_add, ht, hu]

variable [Nontrivial M] [Nontrivial N]

/-- Opposite partial-adjoint parities with vanishing partial traces are
jointly disjoint from every tensor sum of traceless factor operators.
This is an operator identity and needs no chosen isotropy subalgebra. -/
theorem opposite_parity_sum_eq_tensor_sum
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate)
    (f g : Module.End K (M ⊗[K] N))
    (hf : leftPartialAdjoint (L := L) β hβ f = -f)
    (hg : leftPartialAdjoint (L := L) β hβ g = g)
    (hfL : leftPartialTrace (L := L) f = 0)
    (hgL : leftPartialTrace (L := L) g = 0)
    (hfR : rightPartialTrace (L := L) f = 0)
    (hgR : rightPartialTrace (L := L) g = 0)
    (A : Module.End K M) (B : Module.End K N)
    (hA : LinearMap.trace K M A = 0) (hB : LinearMap.trace K N B = 0)
    (he : f + g = TensorProduct.map A (1 : Module.End K N) +
      TensorProduct.map (1 : Module.End K M) B) :
    f = 0 ∧ g = 0 ∧ A = 0 ∧ B = 0 := by
  have hdimM : (finrank K M : K) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  have hdimN : (finrank K N : K) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  have hAz : A = 0 := by
    have h := congrArg (leftPartialTrace (L := L)) he
    simp only [map_add, hfL, hgL, left_partial_trace_map,
      LinearMap.trace_one, hB, zero_smul, add_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_left hdimN
  have hBz : B = 0 := by
    have h := congrArg (rightPartialTrace (L := L)) he
    simp only [map_add, hfR, hgR, zero_add, right_partial_trace_map,
      LinearMap.trace_one, hA, zero_smul, add_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_left hdimM
  have hfg : f + g = 0 := by simpa only [hAz, hBz, TensorProduct.map_zero_left,
    TensorProduct.map_zero_right, add_zero] using he
  have hfg' : -f + g = 0 := by
    have h := congrArg (leftPartialAdjoint (L := L) β hβ) hfg
    simpa only [map_add, hf, hg, map_zero] using h
  have hfz : f = 0 := by
    have htwo : (2 : K) • f = 0 := by
      rw [two_smul]
      calc f + f = (f + g) - (-f + g) := by abel
           _ = 0 := by rw [hfg, hfg']; abel
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact ⟨hfz, by simpa only [hfz, zero_add] using hfg, hAz, hBz⟩

/-- The actual left and right parity blocks jointly avoid the full
tensor sum of the two factor form-preserving algebras. Thus this
separation holds before any comparison with the isotropy image. -/
theorem parity_blocks_tensor_sum_separation
    (I J : LieIdeal K L)
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate) (hiβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.Nondegenerate) (hiγ : γ.lieInvariant L)
    (t : I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hiγ)
    (u : traceZeroSelfAdjointLieSubmodule β hiβ ⊗[K] J)
    (A : Module.End K M) (B : Module.End K N)
    (hA : ∀ m m', β (A m) m' = -β m (A m'))
    (hB : ∀ n n', γ (B n) n' = -γ n (B n'))
    (he : leftParityBlock (M := M) I γ hiγ t + rightParityBlock (N := N) J β hiβ u =
      TensorProduct.map A (1 : Module.End K N) + TensorProduct.map (1 : Module.End K M) B) :
    leftParityBlock (M := M) I γ hiγ t = 0 ∧
      rightParityBlock (N := N) J β hiβ u = 0 ∧ A = 0 ∧ B = 0 := by
  have ht := left_parity_block_partial_traces_zero I β hβ hiβ γ hiγ t
  have hu := right_parity_block_partial_traces_zero J β hiβ γ hγ hiγ u
  exact opposite_parity_sum_eq_tensor_sum β hβ _ _
    (left_parity_block_partial_adjoint I β hβ hiβ γ hiγ t)
    (right_parity_block_partial_adjoint J β hβ hiβ u)
    ht.1 hu.1 ht.2 hu.2 A B
    (trace_eq_zero_of_skew β hβ A hA) (trace_eq_zero_of_skew γ hγ B hB) he

/-- With faithful factor ideal actions, equality of a sum of the two
actual parity blocks to any factor-skew tensor sum forces both source
tensors and both factor operators to vanish. -/
theorem parity_blocks_eq_tensor_sum
    (I J : LieIdeal K L)
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate) (hiβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.Nondegenerate) (hiγ : γ.lieInvariant L)
    (hI : Function.Injective (fun x : I => toEnd K L M (x : L)))
    (hJ : Function.Injective (fun x : J => toEnd K L N (x : L)))
    (t : I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hiγ)
    (u : traceZeroSelfAdjointLieSubmodule β hiβ ⊗[K] J)
    (A : Module.End K M) (B : Module.End K N)
    (hA : ∀ m m', β (A m) m' = -β m (A m'))
    (hB : ∀ n n', γ (B n) n' = -γ n (B n'))
    (he : leftParityBlock (M := M) I γ hiγ t + rightParityBlock (N := N) J β hiβ u =
      TensorProduct.map A (1 : Module.End K N) + TensorProduct.map (1 : Module.End K M) B) :
    t = 0 ∧ u = 0 ∧ A = 0 ∧ B = 0 := by
  obtain ⟨ht, hu, hAz, hBz⟩ := parity_blocks_tensor_sum_separation I J
    β hβ hiβ γ hγ hiγ t u A B hA hB he
  exact ⟨(left_parity_block_injective I γ hiγ hI) (by simpa using ht),
    (right_parity_block_injective J β hiβ hJ) (by simpa using hu), hAz, hBz⟩

/-- The sum of the two actual blocks has zero intersection with the
actual diagonal action image. This gives simultaneous quotient
injectivity and disjointness, without a representation trace-form
nondegeneracy hypothesis. -/
theorem parity_blocks_eq_diagonal_action
    (I J : LieIdeal K L)
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate) (hiβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.Nondegenerate) (hiγ : γ.lieInvariant L)
    (hI : Function.Injective (fun x : I => toEnd K L M (x : L)))
    (hJ : Function.Injective (fun x : J => toEnd K L N (x : L)))
    (t : I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hiγ)
    (u : traceZeroSelfAdjointLieSubmodule β hiβ ⊗[K] J) (x : L)
    (he : leftParityBlock (M := M) I γ hiγ t + rightParityBlock (N := N) J β hiβ u =
      toEnd K L (M ⊗[K] N) x) :
    t = 0 ∧ u = 0 := by
  rw [tensor_action_eq_sum] at he
  have h := parity_blocks_eq_tensor_sum I J β hβ hiβ γ hγ hiγ hI hJ
    t u _ _ (hiβ x) (hiγ x) he
  exact ⟨h.1, h.2.1⟩

end

end CubicAnomaly.Classification.TensorParitySeparation
