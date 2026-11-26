import CubicAnomaly.Classification.UnitaryModuleBridge
import CubicAnomaly.Classification.ScalarTraceZeroDensity
import CubicAnomaly.Classification.SelfDualQuotientObstruction
import CubicAnomaly.Classification.CompactQuotientSkew
import CubicAnomaly.Classification.TraceZeroSymmetricPair
import CubicAnomaly.Classification.TensorFormFactorization
import CubicAnomaly.Classification.SelfDualInvariantForm
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Excluding self-duality of the actual special-unitary defining module

An invariant nondegenerate form on the actual defining module gives the
actual trace-zero self-adjoint operator block. Its intersection with the
isotropy action is zero, so a nonzero block fills the complexified compact
quotient. This forces the action to contain every skew-adjoint operator.
The quotient's nonzero skew sign operator then contradicts the symmetric
pair derivation theorem. If the block is zero, scalar-plus-action density
and the actual trace instead force the isotropy to be the whole ambient
special-unitary algebra.

The resulting exclusion uses the literal defining action, original compact
quotient, and actual operator trace. It requires no highest-weight label
or classification of low-dimensional form-preserving algebras.
-/

namespace CubicAnomaly.Classification.UnitarySelfDualExclusion

open Module LieModule
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.UnitaryDefining
open CubicAnomaly.Classification.UnitaryComplexification
open CubicAnomaly.Classification.UnitaryModuleBridge
open CubicAnomaly.Classification.SelfDualQuotientObstruction
open CubicAnomaly.Classification.CompactQuotientSkew
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.SkewTraceComplement
open CubicAnomaly.Classification.TraceZeroSymmetricPair
open CubicAnomaly.Classification.TensorFormFactorization
open CubicAnomaly.Classification.ScalarTraceZeroDensity
open CubicAnomaly.Classification.SelfDualInvariantForm
open scoped TensorProduct

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

variable (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))

local instance : LieRingModule (ℂ ⊗[ℝ] h) W :=
  complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)

local instance : LieModule ℂ (ℂ ⊗[ℝ] h) W :=
  complexified_defining_lieModule (specialUnitaryDefiningRepresentation h)

/-- Membership in the actual complexified isotropy is detected by the
literal special-unitary ambient defining operator. -/
theorem special_unitary_mem_isotropy_iff_action_range
    (z : ℂ ⊗[ℝ] specialUnitaryAlgebra W) :
    z ∈ h.toSubmodule.baseChange ℂ ↔
      specialUnitaryAmbientOperatorMap h z ∈ (toEnd ℂ (ℂ ⊗[ℝ] h) W).range := by
  change z ∈ complexifiedSubalgebra h ↔ _
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (special_unitary_ambient_operator_map_inclusion h x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, special_unitary_ambient_operator_map_injective h ?_⟩
    exact (special_unitary_ambient_operator_map_inclusion h x).trans hx

private theorem special_unitary_action_trace_zero (x : ℂ ⊗[ℝ] h) :
    LinearMap.trace ℂ W (toEnd ℂ (ℂ ⊗[ℝ] h) W x) = 0 := by
  rw [← special_unitary_ambient_operator_map_inclusion h x]
  exact (specialUnitaryComplexificationEquiv (complexifiedLieHom h.incl x)).property

private theorem self_adjoint_skew_adjoint_eq_zero
    (β : LinearMap.BilinForm ℂ W) (hβ : β.Nondegenerate)
    (A : Module.End ℂ W) (hs : A ∈ β.selfAdjointSubmodule)
    (hk : A ∈ β.skewAdjointSubmodule) : A = 0 := by
  have hself := (mem_selfAdjoint_iff_form_adjoint β hβ A).mp hs
  have hsk := (mem_skew_adjoint_iff_form_adjoint β hβ A).mp hk
  rw [hself] at hsk
  have he : (2 : ℂ) • A = 0 := by
    simpa only [two_smul, neg_add_cancel] using
      congrArg (fun T : Module.End ℂ W => T + A) hsk
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

set_option maxHeartbeats 800000 in
/-- A proper special-unitary compact pair with complex-type complement
and irreducible actual defining action preserves no nondegenerate complex
bilinear form. The form's reflexivity and both zero/nonzero self-adjoint
block cases are derived, rather than supplied. -/
theorem special_unitary_no_invariant_nondegenerate_form_of_irreducible
    (B : CompactForm (specialUnitaryAlgebra W)) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) W]
    (β : LinearMap.BilinForm ℂ W) (hi : β.lieInvariant (ℂ ⊗[ℝ] h))
    (hβ : β.Nondegenerate) : False := by
  let P := traceZeroSelfAdjointLieSubmodule β hi
  have hr : LinearMap.IsRefl β := invariant_form_isRefl β hi
  by_cases hzero : P = ⊥
  · have hfull := action_range_eq_trace_zero_of_trace_zero_lie_submodule_eq_bot
      β hi hzero (special_unitary_action_trace_zero h)
    apply hproper
    apply top_unique
    intro A _
    apply (complexification_real_mem_baseChange_iff (specialUnitaryAlgebra W)
      h.toSubmodule A).mp
    apply (special_unitary_mem_isotropy_iff_action_range h _).mpr
    change specialUnitaryAmbientOperatorMap h (1 ⊗ₜ[ℝ] A) ∈
      (toEnd ℂ (ℂ ⊗[ℝ] h) W).toLinearMap.range
    rw [hfull]
    exact (specialUnitaryComplexificationEquiv (1 ⊗ₜ[ℝ] A)).property
  · letI : Nontrivial P := (LieSubmodule.nontrivial_iff_ne_bot ℂ _ _).mpr hzero
    let f := liftTraceZeroEquivariant h P.incl (fun A => A.property.2)
    have hf (A : P) : specialUnitaryAmbientOperatorMap h (f A) =
        (A : Module.End ℂ W) :=
      lift_trace_zero_equivariant_operator h P.incl (fun A => A.property.2) A
    have hsep : ∀ A : P, f A ∈ h.toSubmodule.baseChange ℂ → A = 0 := by
      intro A hA
      obtain ⟨x, hx⟩ := (special_unitary_mem_isotropy_iff_action_range h (f A)).mp hA
      rw [hf] at hx
      apply Subtype.ext
      apply self_adjoint_skew_adjoint_eq_zero β hβ A.val A.property.1
      rw [← hx]
      exact action_mem_skew_adjoint β hi x
    let F := (complexifiedComplementProjection B h).comp f
    have hsurj : Function.Surjective F :=
      compact_self_dual_block_projection_surjective B h hproper e f
        (trace_zero_self_adjoint_self_dual β hβ hr hi) hsep
    have hinj : Function.Injective F := by
      apply (injective_iff_map_eq_zero F).mpr
      intro A hA
      exact hsep A ((complexified_complement_projection_eq_zero_iff B h (f A)).mp hA)
    let E : P ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] orthogonalComplement B h) :=
      { F, LinearEquiv.ofBijective F.toLinearMap ⟨hinj, hsurj⟩ with }
    have hfull : (toEnd ℂ (ℂ ⊗[ℝ] h) W).range = skewAdjointLieSubalgebra β := by
      apply le_antisymm
      · rintro A ⟨x, rfl⟩
        exact action_mem_skew_adjoint β hi x
      · intro A hA
        have ht : LinearMap.trace ℂ W A = 0 := skew_adjoint_trace_zero β hβ A hA
        let z := specialUnitaryComplexificationEquiv.symm ⟨A, ht⟩
        have hz : specialUnitaryAmbientOperatorMap h z = A :=
          congrArg Subtype.val
            (specialUnitaryComplexificationEquiv.apply_symm_apply ⟨A, ht⟩)
        obtain ⟨p, hp⟩ := hsurj (complexifiedComplementProjection B h z)
        have hm : z - f p ∈ h.toSubmodule.baseChange ℂ := by
          apply (complexified_complement_projection_eq_zero_iff B h _).mp
          change complexifiedComplementProjection B h (z - f p) = 0
          rw [map_sub]
          change complexifiedComplementProjection B h z - F p = 0
          rw [hp, sub_self]
        obtain ⟨x, hx⟩ := (special_unitary_mem_isotropy_iff_action_range h _).mp hm
        rw [map_sub, hz, hf] at hx
        change toEnd ℂ (ℂ ⊗[ℝ] h) W x = A - (p : Module.End ℂ W) at hx
        have hsk : (p : Module.End ℂ W) ∈ β.skewAdjointSubmodule := by
          have hh := β.skewAdjointSubmodule.sub_mem hA (action_mem_skew_adjoint β hi x)
          rw [hx, sub_sub_cancel] at hh
          exact hh
        have hpzero : (p : Module.End ℂ W) = 0 :=
          self_adjoint_skew_adjoint_eq_zero β hβ p.val p.property.1 hsk
        exact ⟨x, by simpa only [hpzero, sub_zero] using hx⟩
    obtain ⟨D, hD, hsk⟩ := compact_equivalent_source_exists_skew_end B h hproper e E
    exact hD (full_skew_trace_zero_self_adjoint_skew_end_eq_zero β hi hβ hr hfull D
      (hsk (traceZeroSelfAdjointModuleTraceForm β hi)
        (trace_zero_self_adjoint_module_trace_form_invariant β hi)))

/-- The original all-rank hypotheses exclude an actual invariant
nondegenerate bilinear form on the special-unitary defining module.
Its actual irreducibility is a consequence, rather than an assumption. -/
theorem all_rank_special_unitary_no_invariant_nondegenerate_form
    (B : CompactForm (specialUnitaryAlgebra W))
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    letI := complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)
    letI := complexified_defining_lieModule (specialUnitaryDefiningRepresentation h)
    ¬ ∃ β : LinearMap.BilinForm ℂ W, β.lieInvariant (ℂ ⊗[ℝ] h) ∧ β.Nondegenerate := by
  letI := complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)
  letI := complexified_defining_lieModule (specialUnitaryDefiningRepresentation h)
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) W :=
    all_rank_special_unitary_complexified_defining_irreducible B h heff hproper e hradical
  rintro ⟨β, hi, hβ⟩
  exact special_unitary_no_invariant_nondegenerate_form_of_irreducible h B hproper e β hi hβ

/-- Under the original all-rank hypotheses, the actual complexified
special-unitary defining representation is not self-dual. Its actual
irreducibility is derived from effectiveness, the complex commutant,
properness, and the nonzero full cubic radical. -/
theorem all_rank_special_unitary_defining_not_self_dual
    (B : CompactForm (specialUnitaryAlgebra W))
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    letI := complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)
    letI := complexified_defining_lieModule (specialUnitaryDefiningRepresentation h)
    ¬ Nonempty (W ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ W) := by
  letI := complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)
  letI := complexified_defining_lieModule (specialUnitaryDefiningRepresentation h)
  intro hs
  exact all_rank_special_unitary_no_invariant_nondegenerate_form B h heff hproper e hradical
    (exists_invariant_nondegenerate_form_of_self_dual hs)

end

end CubicAnomaly.Classification.UnitarySelfDualExclusion
