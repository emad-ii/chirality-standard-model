import CubicAnomaly.Classification.SymplecticDefining
import CubicAnomaly.Classification.SelfDualAbsorption

/-!
# The actual alternating form of a quaternionic defining module

The antiunitary quaternionic structure gives a nondegenerate alternating
complex bilinear form.  The actual compact symplectic algebra and its
complexified defining action preserve this form, so the defining module
is equivariantly self-dual.  No invariant-form or duality witness is an
input to the compact-pair endpoint.
-/

namespace CubicAnomaly.Classification.SymplecticForm

open CubicAnomaly.Classification.SymplecticGeometry
open CubicAnomaly.Classification.SymplecticDefining
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.SelfDualAbsorption
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open scoped ComplexConjugate TensorProduct

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The actual complex bilinear form determined by the quaternionic
structure and inner product. -/
def quaternionicForm (J : QuaternionicStructure W) : LinearMap.BilinForm ℂ W where
  toFun u := {
    toFun v := inner ℂ (J u) v
    map_add' := fun _ _ => inner_add_right _ _ _
    map_smul' := by intro c v; simp only [inner_smul_right]; rfl }
  map_add' := by
    intro u v
    ext w
    exact (J.apply_add u v ▸ inner_add_left (J u) (J v) w)
  map_smul' := by
    intro c u
    ext v
    change inner ℂ (J (c • u)) v = c * inner ℂ (J u) v
    rw [J.apply_smul, inner_smul_left]
    simp

/-- Evaluation is the original inner product with a quaternionic first input. -/
theorem quaternionic_form_apply (J : QuaternionicStructure W) (u v : W) :
    quaternionicForm J u v = inner ℂ (J u) v := rfl

/-- The constructed form is alternating. -/
theorem quaternionic_form_alternating (J : QuaternionicStructure W) :
    (quaternionicForm J).IsAlt := by
  intro u
  have h := congrArg conj (J.inner_self_image u)
  simpa only [inner_conj_symm, map_zero] using h

/-- The constructed form has no left or right radical. -/
theorem quaternionic_form_nondegenerate (J : QuaternionicStructure W) :
    (quaternionicForm J).Nondegenerate := by
  constructor
  · intro u hu
    have hz : J u = 0 := inner_self_eq_zero.mp (hu (J u))
    exact J.injective (by simpa only [J.apply_zero] using hz)
  · intro v hv
    have hz := hv (-J v)
    change inner ℂ (J (-J v)) v = 0 at hz
    rw [J.apply_neg, J.square, neg_neg] at hz
    exact inner_self_eq_zero.mp hz

/-- The actual compact symplectic defining action preserves the constructed form. -/
theorem quaternionic_form_invariant (J : QuaternionicStructure W) :
    (quaternionicForm J).lieInvariant (symplecticAlgebra J) := by
  intro A u v
  change inner ℂ (J (A.val u)) v = -inner ℂ (J u) (A.val v)
  rw [← symplectic_commutes J A u]
  exact symplectic_skew_action J A (J u) v

/-- The constructed form is also invariant under the actual complexified
isotropy action on the same complex defining vector space. -/
theorem quaternionic_form_complexified_invariant (J : QuaternionicStructure W)
    (h : LieSubalgebra ℝ (symplecticAlgebra J)) :
    letI := complexifiedDefiningAction (symplecticDefiningRepresentation J h)
    (quaternionicForm J).lieInvariant (ℂ ⊗[ℝ] h) := by
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation J h)
  intro x u v
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change quaternionicForm J (a • x.val.val u) v =
      -quaternionicForm J u (a • x.val.val v)
    rw [map_smul, LinearMap.smul_apply, map_smul]
    have hx := quaternionic_form_invariant J x.val u v
    change quaternionicForm J (x.val.val u) v = -quaternionicForm J u (x.val.val v) at hx
    rw [hx, smul_neg]
  | add x y hx hy =>
    simp only [add_lie, map_add, LinearMap.add_apply, hx, hy, neg_add]

/-- The actual complexified isotropy representation is equivariantly
self-dual via its constructed alternating form. -/
theorem symplectic_complexified_defining_self_dual [FiniteDimensional ℂ W]
    (J : QuaternionicStructure W) (h : LieSubalgebra ℝ (symplecticAlgebra J)) :
    letI := complexifiedDefiningAction (symplecticDefiningRepresentation J h)
    letI := complexified_defining_lieModule (symplecticDefiningRepresentation J h)
    Nonempty (W ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ W) := by
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation J h)
  letI := complexified_defining_lieModule (symplecticDefiningRepresentation J h)
  exact invariant_nondegenerate_form_self_dual (quaternionicForm J)
    (quaternionic_form_complexified_invariant J h) (quaternionic_form_nondegenerate J)

/-- The symplectic branch reaches the actual irreducible self-dual defining
module directly from the original compact-pair hypotheses. -/
theorem all_rank_symplectic_defining_irreducible_self_dual [FiniteDimensional ℂ W]
    (J : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra J))
    (h : LieSubalgebra ℝ (symplecticAlgebra J))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    letI := complexifiedDefiningAction (symplecticDefiningRepresentation J h)
    letI := complexified_defining_lieModule (symplecticDefiningRepresentation J h)
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) W ∧
      Nonempty (W ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ W) :=
  ⟨all_rank_symplectic_complexified_defining_irreducible J B h heff hproper e hradical,
    symplectic_complexified_defining_self_dual J h⟩

end

end CubicAnomaly.Classification.SymplecticForm
