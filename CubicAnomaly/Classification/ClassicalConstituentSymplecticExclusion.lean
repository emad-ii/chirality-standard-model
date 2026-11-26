import CubicAnomaly.Classification.ClassicalConstituentSymplectic
import CubicAnomaly.Classification.ClassicalConstituentGeneration
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Exclusion of the compact symplectic branch in every rank

The actual complexified isotropy contains the pure square of a highest
vector. Its quaternionic conjugate is the pure square of the quaternionic
image, and their symplectic pairing is nonzero. These two squares generate
all defining symplectic operators, contradicting properness of the
original real isotropy.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentSymplecticExclusion

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open Structural CompactOperatorModel SymplecticGeometry SymplecticDefining SymplecticForm
open HermitianRealization ComplexDefining Complexification ClassicalSimplicity AllRankComplex
open ClassicalConstituentHighest ClassicalConstituentSymplectic ClassicalConstituents
open ClassicalConstituentGeneration
open scoped TensorProduct ComplexConjugate

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (Q : QuaternionicStructure W) (h : LieSubalgebra ℝ (symplecticAlgebra Q))

omit [FiniteDimensional ℂ W] in
private theorem quaternionic_action_closed (x : ℂ ⊗[ℝ] h) :
    letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
    ∃ x' : ℂ ⊗[ℝ] h, ∀ w : W, ⁅x', Q w⁆ = Q ⁅x, w⁆ := by
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun w => by simp⟩
  | tmul a x =>
    refine ⟨(conj a) ⊗ₜ[ℝ] x, fun w => ?_⟩
    rw [complexified_defining_action_tmul, complexified_defining_action_tmul, Q.apply_smul]
    exact congrArg (fun y : W => conj a • y) (x.val.property.2 w)
  | add x y hx hy =>
    obtain ⟨x', hx⟩ := hx
    obtain ⟨y', hy⟩ := hy
    exact ⟨x' + y', fun w => by rw [add_lie, add_lie, Q.apply_add, hx, hy]⟩

private theorem paired_square (v : W) :
    letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
    letI := complexified_defining_lieModule (symplecticDefiningRepresentation Q h)
    let E := formTensorEndEquiv (quaternionicForm Q) (quaternionic_form_nondegenerate Q)
      (quaternionic_form_complexified_invariant Q h)
    E (v ⊗ₜ[ℂ] v) ∈ (toEnd ℂ (ℂ ⊗[ℝ] h) W).range →
      E (Q v ⊗ₜ[ℂ] Q v) ∈ (toEnd ℂ (ℂ ⊗[ℝ] h) W).range := by
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
  letI := complexified_defining_lieModule (symplecticDefiningRepresentation Q h)
  intro E
  rintro ⟨x, hx⟩
  obtain ⟨x', hx'⟩ := quaternionic_action_closed Q h x
  refine ⟨x', ?_⟩
  ext w
  obtain ⟨w, rfl⟩ := Q.surjective w
  calc (toEnd ℂ (ℂ ⊗[ℝ] h) W x') (Q w) = Q ((toEnd ℂ (ℂ ⊗[ℝ] h) W x) w) := hx' w
    _ = Q ((quaternionicForm Q v w) • v) := congrArg (fun A : End ℂ W => Q (A w)) hx
    _ = E (Q v ⊗ₜ[ℂ] Q v) (Q w) := by
      rw [Q.apply_smul]
      exact congrArg (fun c : ℂ => c • Q v) (Q.inner_map (Q v) w).symm

/-- For every effective proper compact symplectic pair with complex
quotient commutant, the full cubic radical is zero. -/
theorem all_rank_symplectic_cubic_radical_eq_bot (B : CompactForm (symplecticAlgebra Q))
    (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊥ := by
  by_contra hr
  letI : IsKilling ℂ (ℂ ⊗[ℝ] h) := (all_rank_complex_structural_reduction B h heff hp e hr).2.2.2.1
  letI : IsSimple ℂ (ℂ ⊗[ℝ] h) := all_rank_symplectic_complexified_isotropy_simple Q B h heff hp e hr
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
  letI := complexified_defining_lieModule (symplecticDefiningRepresentation Q h)
  letI := all_rank_symplectic_complexified_defining_irreducible Q B h heff hp e hr
  letI := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) W
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℂ (ℂ ⊗[ℝ] h)
  let H := LieSubalgebra.engel ℂ x
  letI : H.IsCartanSubalgebra := hx
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  obtain ⟨χ, v, _, hv, hc, hk, _⟩ :=
    ExceptionalSieveWeights.exists_bounded_dominant_highest_weight (M := W) H b
  let β := quaternionicForm Q
  have hβ := quaternionic_form_nondegenerate Q
  have hi := quaternionic_form_complexified_invariant Q h
  have ha := quaternionic_form_alternating Q
  let A := symplecticModel Q h
  have hvv := symplectic_model_square_mem_action B h hp e H b A hβ hi ha
    (show IsHighestVector H b χ v from ⟨hv, hc, hk⟩)
  have huu := paired_square Q h v hvv
  have hpair : β (Q v) v ≠ 0 := by
    change inner ℂ (Q (Q v)) v ≠ 0
    simpa only [Q.square, inner_neg_left, neg_ne_zero, inner_self_ne_zero] using hv
  apply hp
  apply top_unique
  intro w _
  apply (complexification_real_mem_baseChange_iff (symplecticAlgebra Q) h.toSubmodule w).mp
  apply (A.mem_isotropy_iff _).mpr
  exact skew_operators_mem_of_paired_squares β hβ hi ha (Q v) v hpair huu hvv _
    ((A.range_iff _).mp ⟨_, rfl⟩)

end

end CubicAnomaly.Classification.ClassicalConstituentSymplecticExclusion
