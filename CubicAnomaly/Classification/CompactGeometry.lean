import CubicAnomaly.Classification.AmbientComplexification
import CubicAnomaly.Classification.ComplexDuality

/-!
# Actual complexified subalgebras and their invariant forms

The complexification of a real Lie subalgebra is realized as an actual Lie
subalgebra of the ambient tensor-product algebra.  The inherited bilinear
form is nondegenerate when the original real restriction is nondegenerate;
in particular positivity supplies this for every subspace of a compact
algebra.  These constructions provide the geometric inputs needed to
identify the degree-zero algebra with its actual closed root subsystem.
-/

namespace CubicAnomaly.Classification.CompactGeometry

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.ComplexDuality
open scoped TensorProduct

noncomputable section

section Forms

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- Restricting the extended form to the actual image of a subspace agrees
with extending the restricted form, under the canonical tensor equivalence. -/
theorem complexified_bilinForm_restrict_equiv (Φ : LinearMap.BilinForm ℝ M)
    (p : Submodule ℝ M) (x y : ℂ ⊗[ℝ] p) :
    (Φ.baseChange ℂ) (submoduleComplexificationEquiv p x)
      (submoduleComplexificationEquiv p y) = ((Φ.restrict p).baseChange ℂ) x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b y => rfl
    | add y z hy hz => simp only [map_add, Submodule.coe_add, hy, hz]
  | add x z hx hz => simp only [map_add, Submodule.coe_add, LinearMap.add_apply, hx, hz]

/-- Nondegeneracy on a real subspace survives in its actual complexified
ambient image. -/
theorem complexified_bilinForm_subspace_nondegenerate (Φ : LinearMap.BilinForm ℝ M)
    (p : Submodule ℝ M) (hnd : (Φ.restrict p).Nondegenerate) :
    ((Φ.baseChange ℂ).restrict (p.baseChange ℂ)).Nondegenerate := by
  have hn := complexified_bilinForm_nondegenerate (Φ.restrict p) hnd
  let E := submoduleComplexificationEquiv p
  constructor
  · intro z hz
    obtain ⟨x, rfl⟩ := E.surjective z
    have hx : x = 0 := hn.1 x fun y => by
      rw [← complexified_bilinForm_restrict_equiv Φ p x y]
      exact hz (E y)
    rw [hx, map_zero]
  · intro z hz
    obtain ⟨x, rfl⟩ := E.surjective z
    have hx : x = 0 := hn.2 x fun y => by
      rw [← complexified_bilinForm_restrict_equiv Φ p y x]
      exact hz (E y)
    rw [hx, map_zero]

end Forms

section LieSubalgebra

variable {g k : Type*} [LieRing g] [LieAlgebra ℝ g]
  [LieRing k] [LieAlgebra ℝ k]

/-- The complex-linear Lie homomorphism obtained from a real Lie homomorphism. -/
def complexifiedLieHom (f : g →ₗ⁅ℝ⁆ k) : (ℂ ⊗[ℝ] g) →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] k) := {
  f.toLinearMap.baseChange ℂ with
  map_lie' := by
    intro x y
    exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) f).map_lie x y }

/-- The actual complexified image of a real Lie subalgebra. -/
def complexifiedSubalgebra (h : LieSubalgebra ℝ g) :
    LieSubalgebra ℂ (ℂ ⊗[ℝ] g) :=
  (complexifiedLieHom h.incl).range

/-- The actual Lie-subalgebra carrier is precisely the scalar extension of
the original real subspace. -/
theorem complexifiedSubalgebra_toSubmodule (h : LieSubalgebra ℝ g) :
    (complexifiedSubalgebra h).toSubmodule = h.toSubmodule.baseChange ℂ := rfl

/-- The tensor-product isotropy algebra and its actual ambient image are
isomorphic as complex Lie algebras. -/
def subalgebraComplexificationEquiv (h : LieSubalgebra ℝ g) :
    (ℂ ⊗[ℝ] h) ≃ₗ⁅ℂ⁆ complexifiedSubalgebra h :=
  LieEquiv.ofInjective (complexifiedLieHom h.incl)
    (complexification_linearMap_injective h.incl.toLinearMap Subtype.val_injective)

/-- Pure tensors in the isotropy algebra embed as the corresponding pure
tensors in the ambient algebra. -/
theorem subalgebraComplexificationEquiv_tmul (h : LieSubalgebra ℝ g)
    (a : ℂ) (x : h) :
    (subalgebraComplexificationEquiv h (a ⊗ₜ[ℝ] x) : ℂ ⊗[ℝ] g) =
      a ⊗ₜ[ℝ] (x : g) := rfl

/-- The tensor-product isotropy action agrees with the ambient adjoint
action of the included complexified isotropy element. -/
theorem complexifiedLieHom_inclusion_action (h : LieSubalgebra ℝ g)
    (x : ℂ ⊗[ℝ] h) (y : ℂ ⊗[ℝ] g) :
    ⁅complexifiedLieHom h.incl x, y⁆ = ⁅x, y⁆ := by
  change (LieModule.toEnd ℂ (ℂ ⊗[ℝ] g) (ℂ ⊗[ℝ] g)
    (complexifiedLieHom h.incl x)) y =
      (LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] g) x) y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b y => rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- An invariant ambient subspace can be regarded as a representation of
the actual complexified image, with exactly the same carrier. -/
def imageActionSubmodule (h : LieSubalgebra ℝ g)
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] g)) :
    LieSubmodule ℂ (complexifiedSubalgebra h) (ℂ ⊗[ℝ] g) where
  __ := N.toSubmodule
  lie_mem := by
    intro x m hm
    obtain ⟨x, rfl⟩ := (subalgebraComplexificationEquiv h).surjective x
    change ⁅complexifiedLieHom h.incl x, m⁆ ∈ N
    rw [complexifiedLieHom_inclusion_action]
    exact N.lie_mem hm

/-- Transport to the actual acting image preserves the underlying subspace. -/
theorem imageActionSubmodule_toSubmodule (h : LieSubalgebra ℝ g)
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] g)) :
    (imageActionSubmodule h N).toSubmodule = N.toSubmodule := rfl

/-- Element-level action compatibility for the transported ambient submodule. -/
theorem imageActionSubmodule_lie (h : LieSubalgebra ℝ g)
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] g))
    (x : ℂ ⊗[ℝ] h) (m : imageActionSubmodule h N) :
    ⁅subalgebraComplexificationEquiv h x, m⁆ = (⁅x, (m : N)⁆ : N) := by
  apply Subtype.ext
  exact complexifiedLieHom_inclusion_action h x m.val

/-- Irreducibility is preserved when the tensor-product isotropy action is
replaced with its actual image inside the ambient complexified algebra. -/
theorem imageActionSubmodule_irreducible (h : LieSubalgebra ℝ g)
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] g))
    [LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) N] :
    LieModule.IsIrreducible ℂ (complexifiedSubalgebra h) (imageActionSubmodule h N) := by
  letI : Nontrivial N := LieModule.nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) N
  letI : Nontrivial (imageActionSubmodule h N) := inferInstanceAs (Nontrivial N)
  apply LieModule.IsIrreducible.mk
  intro U hU
  let U' : LieSubmodule ℂ (ℂ ⊗[ℝ] h) N := {
    U.toSubmodule with
    lie_mem := by
      intro x m hm
      have hz := U.lie_mem (x := subalgebraComplexificationEquiv h x) hm
      rw [imageActionSubmodule_lie] at hz
      exact hz }
  have hU' : U' ≠ ⊥ := by
    intro hb
    apply hU
    have heq := congrArg (fun V : LieSubmodule ℂ (ℂ ⊗[ℝ] h) N => V.toSubmodule) hb
    exact LieSubmodule.toSubmodule_injective heq
  have htop : U' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'
  have heq := congrArg (fun V : LieSubmodule ℂ (ℂ ⊗[ℝ] h) N => V.toSubmodule) htop
  exact LieSubmodule.toSubmodule_injective heq

/-- Equivariant equivalences of actual ambient subspaces descend to the
actual complexified acting image. -/
def imageActionEquiv (h : LieSubalgebra ℝ g)
    (P Q : LieSubmodule ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] g))
    (e : P ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Q) :
    imageActionSubmodule h P ≃ₗ⁅ℂ,complexifiedSubalgebra h⁆ imageActionSubmodule h Q := {
  e.toLinearEquiv with
  map_lie' := by
    intro x m
    obtain ⟨x, rfl⟩ := (subalgebraComplexificationEquiv h).surjective x
    change e (⁅subalgebraComplexificationEquiv h x, m⁆ : imageActionSubmodule h P) =
      (⁅subalgebraComplexificationEquiv h x, e m⁆ : imageActionSubmodule h Q)
    rw [imageActionSubmodule_lie, imageActionSubmodule_lie]
    exact e.map_lie x m }

/-- Contragredient duality of actual ambient subspaces descends to the
actual complexified acting image, preserving the dual action. -/
def imageActionDualEquiv (h : LieSubalgebra ℝ g)
    (P Q : LieSubmodule ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] g))
    (e : Q ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ P) :
    imageActionSubmodule h Q ≃ₗ⁅ℂ,complexifiedSubalgebra h⁆
      Module.Dual ℂ (imageActionSubmodule h P) := {
  e.toLinearEquiv with
  map_lie' := by
    intro x m
    obtain ⟨x, rfl⟩ := (subalgebraComplexificationEquiv h).surjective x
    ext n
    change e (⁅subalgebraComplexificationEquiv h x, m⁆ : imageActionSubmodule h Q) n =
      -(e m (⁅subalgebraComplexificationEquiv h x, n⁆ : imageActionSubmodule h P))
    rw [imageActionSubmodule_lie, imageActionSubmodule_lie]
    exact congrArg (fun f : Module.Dual ℂ P => f n) (e.map_lie x m) }

/-- Positivity of the original compact form makes its restriction to every
actual complexified subspace nondegenerate. -/
theorem compact_complexified_subspace_form_nondegenerate (B : CompactForm g)
    (p : Submodule ℝ g) :
    ((B.form.baseChange ℂ).restrict (p.baseChange ℂ)).Nondegenerate := by
  apply complexified_bilinForm_subspace_nondegenerate
  constructor <;> intro x hx <;> apply Subtype.ext
  all_goals
    by_contra hne
    have hpos := B.positive x.val hne
    have hzero : B.form x.val x.val = 0 := hx x
    exact (ne_of_gt hpos) hzero

/-- The inherited invariant form is nondegenerate on the actual ambient
complexification of any compact Lie subalgebra. -/
theorem compact_complexified_subalgebra_form_nondegenerate (B : CompactForm g)
    (h : LieSubalgebra ℝ g) :
    ((B.form.baseChange ℂ).restrict (complexifiedSubalgebra h).toSubmodule).Nondegenerate :=
  compact_complexified_subspace_form_nondegenerate B h.toSubmodule

end LieSubalgebra

end

end CubicAnomaly.Classification.CompactGeometry
