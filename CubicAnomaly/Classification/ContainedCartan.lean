import CubicAnomaly.Classification.CompactGeometry
import Mathlib.Algebra.Lie.CartanSubalgebra

/-!
# The same Cartan inside the actual isotropy algebra

If an ambient Cartan lies in the range of an injective Lie homomorphism,
its literal inverse image is a Cartan of the source.  The canonical Lie
equivalence preserves the ambient inclusion.

Applied to the complexified inclusion of a real isotropy subalgebra, this
constructs a Cartan of the tensor-product isotropy algebra from the common
ambient Cartan.  Thus root and trace calculations can use the same Cartan,
without choosing a second Cartan or assuming a conjugacy theorem.
-/

namespace CubicAnomaly.Classification.ContainedCartan

open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open scoped TensorProduct

noncomputable section

section General

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

/-- Restriction of a Lie homomorphism to the inverse image of a subalgebra. -/
def comapRestriction (f : L →ₗ⁅R⁆ M) (H : LieSubalgebra R M) :
    H.comap f →ₗ⁅R⁆ H where
  toFun x := ⟨f x, x.property⟩
  map_add' x y := Subtype.ext (map_add f (x : L) (y : L))
  map_smul' t x := Subtype.ext (map_smul f t (x : L))
  map_lie' {x y} := Subtype.ext (f.map_lie x y)

/-- A subalgebra contained in an injective image is canonically isomorphic
to its literal inverse image. -/
def cartanComapEquiv (f : L →ₗ⁅R⁆ M) (hf : Function.Injective f)
    (H : LieSubalgebra R M) (hH : H ≤ f.range) : H ≃ₗ⁅R⁆ H.comap f :=
  (LieEquiv.ofBijective (comapRestriction f H) ⟨by
    intro x y hxy
    apply Subtype.ext
    exact hf (congrArg Subtype.val hxy), by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (LieHom.mem_range f y).mp (hH hy)
    exact ⟨⟨x, hy⟩, rfl⟩⟩).symm

/-- The Cartan equivalence preserves the actual ambient inclusion. -/
theorem cartanComapEquiv_inclusion (f : L →ₗ⁅R⁆ M) (hf : Function.Injective f)
    (H : LieSubalgebra R M) (hH : H ≤ f.range) (x : H) :
    f (cartanComapEquiv f hf H hH x : L) = (x : M) := by
  exact congrArg Subtype.val ((cartanComapEquiv f hf H hH).symm_apply_apply x)

/-- An ambient Cartan contained in an injective image is a Cartan in the
source under literal inverse image. -/
theorem isCartanSubalgebra_comap_of_le_range (f : L →ₗ⁅R⁆ M)
    (hf : Function.Injective f) (H : LieSubalgebra R M)
    [H.IsCartanSubalgebra] (hH : H ≤ f.range) : (H.comap f).IsCartanSubalgebra := by
  refine ⟨(cartanComapEquiv f hf H hH).nilpotent_iff_equiv_nilpotent.mp inferInstance,
    le_antisymm ?_ (H.comap f).le_normalizer⟩
  intro x hx
  change f x ∈ H
  have hn : f x ∈ H.normalizer := by
    apply (H.mem_normalizer_iff (f x)).mpr
    intro y hy
    obtain ⟨z, rfl⟩ := (LieHom.mem_range f y).mp (hH hy)
    have hbr := ((H.comap f).mem_normalizer_iff x).mp hx z hy
    change f ⁅x, z⁆ ∈ H at hbr
    simpa only [f.map_lie] using hbr
  simpa only [LieSubalgebra.IsCartanSubalgebra.self_normalizing] using hn

end General

section Isotropy

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- The literal inverse image of the common ambient Cartan in the actual
tensor-product isotropy algebra. -/
def commonCartanInIsotropy (h : LieSubalgebra ℝ g)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) : LieSubalgebra ℂ (ℂ ⊗[ℝ] h) :=
  H.comap (complexifiedLieHom h.incl)

/-- The common ambient Cartan and its isotropy inverse image are the same
Lie algebra under the actual complexified inclusion. -/
def commonCartanIsotropyEquiv (h : LieSubalgebra ℝ g)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H ≤ complexifiedSubalgebra h) :
    H ≃ₗ⁅ℂ⁆ commonCartanInIsotropy h H :=
  cartanComapEquiv (complexifiedLieHom h.incl)
    (complexification_linearMap_injective h.incl.toLinearMap Subtype.val_injective) H hH

/-- Containment of an ambient Cartan constructs a Cartan of the actual
isotropy complexification. -/
theorem commonCartanInIsotropy_isCartan (h : LieSubalgebra ℝ g)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) :
    (commonCartanInIsotropy h H).IsCartanSubalgebra :=
  isCartanSubalgebra_comap_of_le_range (complexifiedLieHom h.incl)
    (complexification_linearMap_injective h.incl.toLinearMap Subtype.val_injective) H hH

/-- Lift an element of the common ambient Cartan to the actual isotropy
complexification, retaining the Lie algebra structure. -/
def commonCartanLift (h : LieSubalgebra ℝ g)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H ≤ complexifiedSubalgebra h) :
    H →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] h) :=
  (commonCartanInIsotropy h H).incl.comp (commonCartanIsotropyEquiv h H hH).toLieHom

/-- Including a lifted Cartan element gives the original ambient element. -/
theorem commonCartanLift_inclusion (h : LieSubalgebra ℝ g)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H ≤ complexifiedSubalgebra h) (x : H) :
    complexifiedLieHom h.incl (commonCartanLift h H hH x) = (x : ℂ ⊗[ℝ] g) :=
  cartanComapEquiv_inclusion (complexifiedLieHom h.incl)
    (complexification_linearMap_injective h.incl.toLinearMap Subtype.val_injective) H hH x

/-- The lifted Cartan inclusion composes to the original literal inclusion. -/
theorem complexified_inclusion_comp_commonCartanLift (h : LieSubalgebra ℝ g)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H ≤ complexifiedSubalgebra h) :
    (complexifiedLieHom h.incl).comp (commonCartanLift h H hH) = H.incl := by
  ext x
  exact commonCartanLift_inclusion h H hH x

/-- The lifted isotropy action is the ambient adjoint action of the same
Cartan element. -/
theorem commonCartanLift_action (h : LieSubalgebra ℝ g)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H ≤ complexifiedSubalgebra h)
    (x : H) (y : ℂ ⊗[ℝ] g) :
    ⁅commonCartanLift h H hH x, y⁆ = ⁅(x : ℂ ⊗[ℝ] g), y⁆ := by
  rw [← complexifiedLieHom_inclusion_action, commonCartanLift_inclusion]

/-- The actual isotropy Cartan has the dimension of the chosen common
ambient Cartan. -/
theorem commonCartanInIsotropy_finrank (h : LieSubalgebra ℝ g)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H ≤ complexifiedSubalgebra h) :
    Module.finrank ℂ (commonCartanInIsotropy h H) = Module.finrank ℂ H :=
  (commonCartanIsotropyEquiv h H hH).toLinearEquiv.finrank_eq.symm

end Isotropy

end

end CubicAnomaly.Classification.ContainedCartan
