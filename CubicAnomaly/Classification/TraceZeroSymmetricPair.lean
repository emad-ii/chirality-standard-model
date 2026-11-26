import CubicAnomaly.Classification.SkewTraceComplement
import CubicAnomaly.Classification.TraceZeroEndKilling
import CubicAnomaly.Classification.SymmetricPairDerivations
import CubicAnomaly.Classification.TensorFormFactorization
import Mathlib.Tactic.Module

/-!
# The actual trace-zero symmetric pair of a bilinear form

For a nondegenerate reflexive bilinear form, trace-zero endomorphisms split
as skew-adjoint operators and trace-zero self-adjoint operators. The two
pieces form an actual symmetric pair. Its centralizer is zero whenever
an irreducible defining action preserves the form. Consequently a full
skew-adjoint action admits no nonzero equivariant trace-skew endomorphism
on its trace-zero self-adjoint operators.
-/

namespace CubicAnomaly.Classification.TraceZeroSymmetricPair

open Module LieModule
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.SkewTraceComplement
open CubicAnomaly.Classification.TraceZeroEndKilling
open CubicAnomaly.Classification.SymmetricPairDerivations
open CubicAnomaly.Classification.TensorFormFactorization

noncomputable section

variable {K W : Type*} [Field K] [CharZero K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/-- Every skew-adjoint operator for a nondegenerate bilinear form has
ordinary trace zero. -/
theorem skew_adjoint_trace_zero (β : LinearMap.BilinForm K W)
    (hβ : β.Nondegenerate) (A : Module.End K W) (hA : A ∈ β.skewAdjointSubmodule) :
    LinearMap.trace K W A = 0 := by
  have ht := trace_form_adjoint β hβ A
  rw [(mem_skew_adjoint_iff_form_adjoint β hβ A).mp hA, map_neg] at ht
  have htwo : (2 : K) * LinearMap.trace K W A = 0 := by linear_combination -ht
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The actual skew algebra inside the actual trace-zero endomorphism ideal. -/
def skewTraceZeroSubalgebra (β : LinearMap.BilinForm K W) :
    LieSubalgebra K (traceZeroEndIdeal (K := K) (W := W)) :=
  (skewAdjointLieSubalgebra β).comap (traceZeroEndIdeal (K := K) (W := W)).incl

omit [CharZero K] [FiniteDimensional K W] in
private theorem skew_trace_zero_form_invariant (β : LinearMap.BilinForm K W) :
    β.lieInvariant (skewTraceZeroSubalgebra β) := by
  intro A u v
  have h := (LinearMap.mem_skewAdjointSubmodule A.val.val).mp A.property
  change β (A.val.val u) v = -β u (A.val.val v)
  simpa only [Pi.neg_apply, map_neg] using h u v

/-- The actual self-adjoint complement inside trace-zero endomorphisms. -/
def selfAdjointTraceZeroComplement (β : LinearMap.BilinForm K W) :
    LieSubmodule K (skewTraceZeroSubalgebra β) (traceZeroEndIdeal (K := K) (W := W)) where
  carrier := {A | (A : Module.End K W) ∈ β.selfAdjointSubmodule}
  zero_mem' := β.selfAdjointSubmodule.zero_mem
  add_mem' := fun hA hB => β.selfAdjointSubmodule.add_mem hA hB
  smul_mem' := fun c _ hA => β.selfAdjointSubmodule.smul_mem c hA
  lie_mem := by
    intro A B hB
    exact (selfAdjointLieSubmodule β (skew_trace_zero_form_invariant β)).lie_mem
      (x := A) hB

/-- The actual trace pairing on trace-zero endomorphisms. -/
def traceZeroForm : LinearMap.BilinForm K (traceZeroEndIdeal (K := K) (W := W)) :=
  (endTraceForm (K := K) (W := W)).restrict (traceZeroEndIdeal (K := K) (W := W)).toSubmodule

omit [CharZero K] [FiniteDimensional K W] in
/-- The original operator trace is invariant on the trace-zero Lie algebra. -/
theorem trace_zero_form_invariant :
    (traceZeroForm (K := K) (W := W)).lieInvariant
      (traceZeroEndIdeal (K := K) (W := W)) := by
  intro A B C
  exact end_trace_form_invariant (L := Module.End K W)
    (A : Module.End K W) (B : Module.End K W) (C : Module.End K W)

/-- Skew and trace-zero self-adjoint operators give a literal direct-sum
decomposition of the actual trace-zero endomorphisms. -/
theorem skew_self_adjoint_trace_zero_isCompl
    (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate) (hr : LinearMap.IsRefl β) :
    IsCompl (skewTraceZeroSubalgebra β).toSubmodule
      (selfAdjointTraceZeroComplement β).toSubmodule := by
  apply IsCompl.of_eq
  · apply le_antisymm _ bot_le
    intro A hA
    change A = 0
    apply Subtype.ext
    change A.val = 0
    have hsk := (mem_skew_adjoint_iff_form_adjoint β hβ A.val).mp hA.1
    have hself := (mem_selfAdjoint_iff_form_adjoint β hβ A.val).mp hA.2
    rw [hself] at hsk
    have he : (2 : K) • A.val = 0 := by
      simpa only [two_smul, neg_add_cancel] using congrArg (fun T : Module.End K W => T + A.val) hsk
    exact (smul_eq_zero.mp he).resolve_left (by norm_num)
  · apply top_unique
    intro A _
    let B := (2 : K)⁻¹ • (A.val - formAdjoint β hβ A.val)
    let C := (2 : K)⁻¹ • (A.val + formAdjoint β hβ A.val)
    have ht : LinearMap.trace K W A.val = 0 := A.property
    have hBt : B ∈ traceZeroEndIdeal (K := K) (W := W) := by
      change LinearMap.trace K W B = 0
      simp only [B, map_smul, map_sub, trace_form_adjoint, sub_self, smul_zero]
    have hCt : C ∈ traceZeroEndIdeal (K := K) (W := W) := by
      change LinearMap.trace K W C = 0
      simp only [C, map_smul, map_add, trace_form_adjoint, ht, add_zero, smul_zero]
    have hB : (⟨B, hBt⟩ : traceZeroEndIdeal (K := K) (W := W)) ∈ skewTraceZeroSubalgebra β := by
      apply (mem_skew_adjoint_iff_form_adjoint β hβ B).mpr
      simp only [B, map_smul, map_sub, form_adjoint_involutive β hβ hr]
      module
    have hC : (⟨C, hCt⟩ : traceZeroEndIdeal (K := K) (W := W)) ∈ selfAdjointTraceZeroComplement β := by
      apply (mem_selfAdjoint_iff_form_adjoint β hβ C).mpr
      simp only [C, map_smul, map_add, form_adjoint_involutive β hβ hr]
      module
    refine Submodule.mem_sup.mpr ⟨⟨B, hBt⟩, hB, ⟨C, hCt⟩, hC, ?_⟩
    apply Subtype.ext
    change B + C = A.val
    dsimp [B, C]
    module

omit [CharZero K] in
/-- Two actual self-adjoint operators have skew-adjoint commutator, so
the actual trace-zero decomposition is symmetric. -/
theorem self_adjoint_trace_zero_bracket_mem_skew
    (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate)
    (A B : selfAdjointTraceZeroComplement β) :
    ⁅A.val, B.val⁆ ∈ skewTraceZeroSubalgebra β := by
  apply (mem_skew_adjoint_iff_form_adjoint β hβ _).mpr
  change formAdjoint β hβ (A.val.val * B.val.val - B.val.val * A.val.val) =
    -(A.val.val * B.val.val - B.val.val * A.val.val)
  rw [map_sub, form_adjoint_mul, form_adjoint_mul,
    (mem_selfAdjoint_iff_form_adjoint β hβ A.val.val).mp A.property,
    (mem_selfAdjoint_iff_form_adjoint β hβ B.val.val).mp B.property, neg_sub]

/-- Nondegeneracy of the actual skew trace pairing remains true inside
the actual trace-zero ambient Lie algebra. -/
theorem trace_zero_form_restrict_skew_nondegenerate
    (β : LinearMap.BilinForm K W) (hβ : β.Nondegenerate) (hr : LinearMap.IsRefl β) :
    ((traceZeroForm (K := K) (W := W)).restrict
      (skewTraceZeroSubalgebra β).toSubmodule).Nondegenerate := by
  have hs : LinearMap.IsSymm ((traceZeroForm (K := K) (W := W)).restrict
      (skewTraceZeroSubalgebra β).toSubmodule) :=
    ⟨fun A B => LinearMap.trace_mul_comm K A.val.val B.val.val⟩
  apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro A hA
  have hz : (⟨A.val.val, A.property⟩ : β.skewAdjointSubmodule) = 0 := by
    apply (skew_adjoint_trace_form_nondegenerate β hβ hr).1
    intro B
    exact hA ⟨⟨B.val, skew_adjoint_trace_zero β hβ B.val B.property⟩, B.property⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun T : β.skewAdjointSubmodule => T.val) hz

section IrreducibleAction

variable {L : Type*} [LieRing L] [LieAlgebra K L]
  [LieRingModule L W] [LieModule K L W] [IsAlgClosed K]
  [LieModule.IsIrreducible K L W]

/-- A trace-zero operator commuting with all skew operators is zero
whenever an irreducible defining action preserves the original form.
Schur's lemma makes the operator scalar and trace zero removes the scalar. -/
theorem skew_trace_zero_centralizer_eq_zero
    (β : LinearMap.BilinForm K W) (hi : β.lieInvariant L) (hβ : β.Nondegenerate)
    (Z : traceZeroEndIdeal (K := K) (W := W))
    (hZ : ∀ A : skewTraceZeroSubalgebra β, ⁅A.val, Z⁆ = 0) : Z = 0 := by
  have hcomm (x : L) : toEnd K L W x * Z.val - Z.val * toEnd K L W x = 0 := by
    let A : skewTraceZeroSubalgebra β :=
      ⟨⟨toEnd K L W x, skew_adjoint_trace_zero β hβ _ (action_mem_skew_adjoint β hi x)⟩,
        action_mem_skew_adjoint β hi x⟩
    exact congrArg Subtype.val (hZ A)
  let f : W →ₗ⁅K,L⁆ W := {
    toLinearMap := Z.val
    map_lie' := by
      intro x w
      have h := congrArg (fun A : Module.End K W => A w) (hcomm x)
      change toEnd K L W x (Z.val w) - Z.val (toEnd K L W x w) = 0 at h
      exact (sub_eq_zero.mp h).symm }
  obtain ⟨c, hc⟩ := equivariant_end_eq_smul_id f
  have he : Z.val = c • (1 : Module.End K W) := congrArg LieModuleHom.toLinearMap hc
  letI : Nontrivial W := LieModule.nontrivial_of_isIrreducible K L W
  have hn : (finrank K W : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have ht : LinearMap.trace K W Z.val = 0 := Z.property
  rw [he, map_smul, LinearMap.trace_one] at ht
  have hc0 : c = 0 := (mul_eq_zero.mp ht).resolve_right hn
  apply Subtype.ext
  rw [he, hc0, zero_smul]
  rfl

/-- The two actual presentations of trace-zero self-adjoint operators
are related by the literal identity on the underlying endomorphism. -/
def selfAdjointComplementEquiv
    (β : LinearMap.BilinForm K W) (hi : β.lieInvariant L) :
    selfAdjointTraceZeroComplement β ≃ₗ[K] traceZeroSelfAdjointLieSubmodule β hi where
  toFun A := ⟨A.val.val, ⟨A.property, A.val.property⟩⟩
  invFun A := ⟨⟨A.val, A.property.2⟩, A.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CharZero K] [FiniteDimensional K W] [IsAlgClosed K] [LieModule.IsIrreducible K L W] in
private theorem selfAdjointComplementEquiv_lie
    (β : LinearMap.BilinForm K W) (hi : β.lieInvariant L)
    (A : skewTraceZeroSubalgebra β) (x : L) (hx : toEnd K L W x = A.val.val)
    (B : selfAdjointTraceZeroComplement β) :
    selfAdjointComplementEquiv β hi ⁅A, B⁆ = ⁅x, selfAdjointComplementEquiv β hi B⁆ := by
  apply Subtype.ext
  change A.val.val * B.val.val - B.val.val * A.val.val =
    toEnd K L W x * B.val.val - B.val.val * toEnd K L W x
  rw [hx]

private def fullSkewEndOnComplement
    (β : LinearMap.BilinForm K W) (hi : β.lieInvariant L)
    (hfull : (toEnd K L W).range = skewAdjointLieSubalgebra β)
    (D : traceZeroSelfAdjointLieSubmodule β hi →ₗ⁅K,L⁆ traceZeroSelfAdjointLieSubmodule β hi) :
    selfAdjointTraceZeroComplement β →ₗ⁅K,skewTraceZeroSubalgebra β⁆
      selfAdjointTraceZeroComplement β where
  toLinearMap := (selfAdjointComplementEquiv β hi).symm.toLinearMap.comp
    (D.toLinearMap.comp (selfAdjointComplementEquiv β hi).toLinearMap)
  map_lie' := by
    intro A B
    have hm : A.val.val ∈ (toEnd K L W).range := by rw [hfull]; exact A.property
    obtain ⟨x, hx⟩ := hm
    apply (selfAdjointComplementEquiv β hi).injective
    change selfAdjointComplementEquiv β hi
        ((selfAdjointComplementEquiv β hi).symm (D (selfAdjointComplementEquiv β hi ⁅A, B⁆))) =
      selfAdjointComplementEquiv β hi ⁅A,
        (selfAdjointComplementEquiv β hi).symm (D (selfAdjointComplementEquiv β hi B))⁆
    rw [LinearEquiv.apply_symm_apply, selfAdjointComplementEquiv_lie β hi A x hx,
      D.map_lie, selfAdjointComplementEquiv_lie β hi A x hx, LinearEquiv.apply_symm_apply]

/-- A full skew-adjoint action has no nonzero equivariant endomorphism
of the actual trace-zero self-adjoint module that is skew for the actual
ordinary trace pairing. The proof uses its trace-zero symmetric pair,
the explicit Killing form, and the inner-derivation theorem. -/
theorem full_skew_trace_zero_self_adjoint_skew_end_eq_zero
    (β : LinearMap.BilinForm K W) (hi : β.lieInvariant L)
    (hβ : β.Nondegenerate) (hr : LinearMap.IsRefl β)
    (hfull : (toEnd K L W).range = skewAdjointLieSubalgebra β)
    (D : traceZeroSelfAdjointLieSubmodule β hi →ₗ⁅K,L⁆ traceZeroSelfAdjointLieSubmodule β hi)
    (hD : ∀ A B, traceZeroSelfAdjointModuleTraceForm β hi (D A) B =
      -traceZeroSelfAdjointModuleTraceForm β hi A (D B)) : D = 0 := by
  letI : LieAlgebra.IsKilling K (traceZeroEndIdeal (K := K) (W := W)) :=
    trace_zero_end_isKilling
  let E := selfAdjointComplementEquiv β hi
  let Dq := fullSkewEndOnComplement β hi hfull D
  have hq : Dq = 0 := by
    apply symmetric_complement_skew_end_eq_zero
      (skewTraceZeroSubalgebra β) (selfAdjointTraceZeroComplement β)
      (skew_self_adjoint_trace_zero_isCompl β hβ hr)
      (traceZeroForm (K := K) (W := W)) trace_zero_form_invariant
      (trace_zero_form_restrict_skew_nondegenerate β hβ hr)
      (skew_trace_zero_centralizer_eq_zero β hi hβ) Dq
    · intro A B
      exact hD (E A) (E B)
    · exact self_adjoint_trace_zero_bracket_mem_skew β hβ
  apply LieModuleHom.ext
  intro A
  have h := congrArg (fun F : selfAdjointTraceZeroComplement β →ₗ⁅K,skewTraceZeroSubalgebra β⁆
      selfAdjointTraceZeroComplement β => E (F (E.symm A))) hq
  change E (E.symm (D (E (E.symm A)))) = E 0 at h
  simpa only [LinearEquiv.apply_symm_apply, map_zero] using h

/-- The actual trace-zero self-adjoint module of a full skew action
cannot be an inequivalent irreducible dual pair. This conclusion uses
the actual operator trace and no highest-weight classification. -/
theorem full_skew_trace_zero_self_adjoint_not_inequivalent_dual_pair
    (β : LinearMap.BilinForm K W) (hi : β.lieInvariant L)
    (hβ : β.Nondegenerate) (hr : LinearMap.IsRefl β)
    (hfull : (toEnd K L W).range = skewAdjointLieSubalgebra β)
    (P Q : LieSubmodule K L (traceZeroSelfAdjointLieSubmodule β hi))
    (hpq : IsCompl P Q)
    [LieModule.IsIrreducible K L P] [LieModule.IsIrreducible K L Q]
    (d : Q ≃ₗ⁅K,L⁆ Module.Dual K P) (hne : ¬Nonempty (P ≃ₗ⁅K,L⁆ Q)) : False := by
  obtain ⟨D, hD, hsk⟩ := DualPairSkew.inequivalent_dual_pair_exists_skew_end P Q hpq d hne
  apply hD
  apply full_skew_trace_zero_self_adjoint_skew_end_eq_zero β hi hβ hr hfull D
  exact hsk (traceZeroSelfAdjointModuleTraceForm β hi)
    (trace_zero_self_adjoint_module_trace_form_invariant β hi)

end IrreducibleAction

end

end CubicAnomaly.Classification.TraceZeroSymmetricPair
