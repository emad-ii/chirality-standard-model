import CubicAnomaly.Classification.CyclicBracket
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Actual compact unitary Lie algebras

The unitary and special-unitary algebras are actual real Lie subalgebras of
the complex endomorphisms of a finite-dimensional complex inner-product
space.  The special-unitary condition includes complex trace zero.
-/

namespace CubicAnomaly.Classification.UnitaryGeometry

open scoped TensorProduct

noncomputable section

variable (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- The real Lie algebra of actual skew-Hermitian complex endomorphisms. -/
def unitaryAlgebra : LieSubalgebra ℝ (Module.End ℂ W) where
  carrier := {A | A.adjoint = -A}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change (A + B).adjoint = -(A + B)
    rw [map_add, hA, hB, neg_add]
  smul_mem' := by
    intro r A hA
    change (r • A).adjoint = -(r • A)
    rw [← Complex.coe_smul, map_smulₛₗ, hA]
    simp
  lie_mem' := by
    intro A B hA hB
    change (A ∘ₗ B - B ∘ₗ A).adjoint = -(A ∘ₗ B - B ∘ₗ A)
    rw [map_sub, LinearMap.adjoint_comp, LinearMap.adjoint_comp, hA, hB]
    simp only [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]
    abel

/-- The actual traceless skew-Hermitian real Lie algebra. -/
def specialUnitaryAlgebra : LieSubalgebra ℝ (Module.End ℂ W) where
  carrier := {A | A.adjoint = -A ∧ LinearMap.trace ℂ W A = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    exact ⟨(unitaryAlgebra W).add_mem hA.1 hB.1, by simp [hA.2, hB.2]⟩
  smul_mem' := by
    intro r A hA
    refine ⟨(unitaryAlgebra W).smul_mem r hA.1, ?_⟩
    rw [← Complex.coe_smul, map_smul, hA.2, smul_zero]
  lie_mem' := by
    intro A B hA hB
    refine ⟨(unitaryAlgebra W).lie_mem hA.1 hB.1, ?_⟩
    change LinearMap.trace ℂ W (A ∘ₗ B - B ∘ₗ A) = 0
    rw [map_sub, LinearMap.trace_comp_comm', sub_self]

instance : Module.Finite ℝ (unitaryAlgebra W) := by
  letI : Module.Finite ℝ (Module.End ℂ W) := Module.Finite.trans ℂ (Module.End ℂ W)
  infer_instance

instance : Module.Finite ℝ (specialUnitaryAlgebra W) := by
  letI : Module.Finite ℝ (Module.End ℂ W) := Module.Finite.trans ℂ (Module.End ℂ W)
  infer_instance

variable {W}

/-- Membership is exactly skewness for the actual complex inner product. -/
theorem unitary_mem_iff (A : Module.End ℂ W) :
    A ∈ unitaryAlgebra W ↔ ∀ u v, inner ℂ (A u) v = -inner ℂ u (A v) := by
  constructor
  · intro hA u v
    have h := A.adjoint_inner_right u v
    rw [hA, LinearMap.neg_apply, inner_neg_right] at h
    exact h.symm
  · intro hA
    change A.adjoint = -A
    apply LinearMap.ext
    intro v
    apply ext_inner_left ℂ
    intro u
    rw [LinearMap.adjoint_inner_right, LinearMap.neg_apply, inner_neg_right]
    exact hA u v

/-- Skew-Hermitian membership gives the exact defining-action identity. -/
theorem unitary_skew_action (A : unitaryAlgebra W) (u v : W) :
    inner ℂ (A.val u) v = -inner ℂ u (A.val v) := by
  have h := A.val.adjoint_inner_right u v
  rw [A.property, LinearMap.neg_apply, inner_neg_right] at h
  exact h.symm

/-- The special-unitary defining action is skew-Hermitian. -/
theorem special_unitary_skew_action (A : specialUnitaryAlgebra W) (u v : W) :
    inner ℂ (A.val u) v = -inner ℂ u (A.val v) :=
  unitary_skew_action ⟨A.val, A.property.1⟩ u v

private def realEndConjugation (r : W ≃ₗ[ℂ] W) :
    Module.End ℂ W ≃ₗ⁅ℝ⁆ Module.End ℂ W where
  __ := r.lieConj.toLinearEquiv.restrictScalars ℝ
  map_lie' := fun {x y} => r.lieConj.map_lie x y

private theorem isometry_conjugation_mem (r : W ≃ₗᵢ[ℂ] W)
    (A : Module.End ℂ W) (hA : A ∈ unitaryAlgebra W) :
    realEndConjugation r.toLinearEquiv A ∈ unitaryAlgebra W := by
  apply (unitary_mem_iff _).mpr
  intro u v
  obtain ⟨u, rfl⟩ := r.surjective u
  obtain ⟨v, rfl⟩ := r.surjective v
  change inner ℂ (r (A (r.symm (r u)))) (r v) =
    -inner ℂ (r u) (r (A (r.symm (r v))))
  rw [r.symm_apply_apply, r.symm_apply_apply, r.inner_map_map, r.inner_map_map]
  exact (unitary_mem_iff A).mp hA u v

/-- A complex linear isometry acts by conjugation on the actual real
unitary Lie algebra. -/
def unitaryConjugation (r : W ≃ₗᵢ[ℂ] W) :
    unitaryAlgebra W ≃ₗ⁅ℝ⁆ unitaryAlgebra W :=
  (realEndConjugation r.toLinearEquiv).ofSubalgebras _ _ (by
    ext A
    constructor
    · rintro ⟨C, hC, rfl⟩
      exact isometry_conjugation_mem r C hC
    · intro hA
      refine ⟨realEndConjugation r.symm.toLinearEquiv A,
        isometry_conjugation_mem r.symm A hA, ?_⟩
      exact (realEndConjugation r.toLinearEquiv).apply_symm_apply A)

/-- Conjugation has its usual action on the defining space. -/
theorem unitaryConjugation_apply (r : W ≃ₗᵢ[ℂ] W) (A : unitaryAlgebra W) (w : W) :
    (unitaryConjugation r A).val w = r (A.val (r.symm w)) := rfl

omit [FiniteDimensional ℂ W] in
/-- An invariant complex subspace has invariant orthogonal complement for
any family of actual skew-Hermitian endomorphisms. -/
theorem skew_invariant_orthogonal_mem {L : Type*} [LieRing L]
    [LieRingModule L W] (action : L → Module.End ℂ W)
    (hact : ∀ x w, action x w = ⁅x, w⁆)
    (hsk : ∀ x u v, inner ℂ (action x u) v = -inner ℂ u (action x v))
    (U : LieSubmodule ℂ L W) (x : L) {v : W}
    (hv : v ∈ U.toSubmoduleᗮ) : ⁅x, v⁆ ∈ U.toSubmoduleᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  have hz := hv ⁅x, u⁆ (U.lie_mem hu)
  have hs := hsk x u v
  simp only [hact] at hs
  rw [hz] at hs
  exact neg_eq_zero.mp hs.symm

/-- The orthogonal projection onto an invariant complex subspace commutes
with every skew-Hermitian action operator. -/
theorem invariant_starProjection_commutes {L : Type*} [LieRing L]
    [LieRingModule L W] (action : L → Module.End ℂ W)
    (hact : ∀ x w, action x w = ⁅x, w⁆)
    (hsk : ∀ x u v, inner ℂ (action x u) v = -inner ℂ u (action x v))
    (U : LieSubmodule ℂ L W) (x : L) (w : W) :
    U.toSubmodule.starProjection (action x w) = action x (U.toSubmodule.starProjection w) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := U.toSubmodule.exists_add_mem_mem_orthogonal w
  have hpu := U.toSubmodule.starProjection_eq_self_iff.mpr hu
  have hpv : U.toSubmodule.starProjection v = 0 := by
    rw [Submodule.starProjection_apply]
    exact congrArg Subtype.val
      (U.toSubmodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hv)
  have hxU : action x u ∈ U := by rw [hact]; exact U.lie_mem hu
  have hxV : action x v ∈ U.toSubmoduleᗮ := by
    rw [hact]
    exact skew_invariant_orthogonal_mem action hact hsk U x hv
  have hpxu := U.toSubmodule.starProjection_eq_self_iff.mpr hxU
  have hpxv : U.toSubmodule.starProjection (action x v) = 0 := by
    rw [Submodule.starProjection_apply]
    exact congrArg Subtype.val
      (U.toSubmodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hxV)
  rw [map_add, map_add, hpxu, hpxv, map_add, hpu, hpv, map_add, map_zero, add_zero]

end

end CubicAnomaly.Classification.UnitaryGeometry
