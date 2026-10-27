import CubicAnomaly.Classification.CompactKilling
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Module

/-!
# Complexification of compact Lie algebras and complex structures

The scalar extension here is the actual tensor product `ℂ ⊗[ℝ] M` with
Mathlib's extended Lie bracket and action.  Real and imaginary projections
give an explicit decomposition of every tensor.  The Killing form is proved
to extend by scalars, and its nondegeneracy is transported from the real
algebra.  Thus a compact centreless real algebra supplies the complex
`IsKilling` interface directly.
-/

namespace CubicAnomaly.Classification.Complexification

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.CompactKilling
open scoped TensorProduct

section RealVectorSpace

variable (M : Type*) [AddCommGroup M] [Module ℝ M]

/-- The real coordinate of an actual complexified vector. -/
noncomputable def tensorRealPart : (ℂ ⊗[ℝ] M) →ₗ[ℝ] M :=
  (TensorProduct.lid ℝ M).toLinearMap.comp
    (TensorProduct.map Complex.reLm (LinearMap.id : M →ₗ[ℝ] M))

/-- The imaginary coordinate of an actual complexified vector. -/
noncomputable def tensorImagPart : (ℂ ⊗[ℝ] M) →ₗ[ℝ] M :=
  (TensorProduct.lid ℝ M).toLinearMap.comp
    (TensorProduct.map Complex.imLm (LinearMap.id : M →ₗ[ℝ] M))

private theorem tensorRealPart_tmul (z : ℂ) (m : M) :
    tensorRealPart M (z ⊗ₜ[ℝ] m) = z.re • m := by
  simp [tensorRealPart]

private theorem tensorImagPart_tmul (z : ℂ) (m : M) :
    tensorImagPart M (z ⊗ₜ[ℝ] m) = z.im • m := by
  simp [tensorImagPart]

/-- Every complexified vector has unique real and imaginary coordinates;
this theorem gives their reconstruction formula. -/
theorem complexification_real_imag_decomposition (z : ℂ ⊗[ℝ] M) :
    z = 1 ⊗ₜ[ℝ] tensorRealPart M z + Complex.I ⊗ₜ[ℝ] tensorImagPart M z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [tensorRealPart_tmul, tensorImagPart_tmul,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
    congr 1
    simp [Complex.real_smul]
  | add x y hx hy =>
    simpa only [map_add, TensorProduct.tmul_add, add_add_add_comm] using congrArg₂ (· + ·) hx hy

/-- The two real coordinate projections jointly detect zero. -/
theorem complexification_zero_iff_parts (z : ℂ ⊗[ℝ] M) :
    z = 0 ↔ tensorRealPart M z = 0 ∧ tensorImagPart M z = 0 := by
  constructor
  · intro h
    simp [h]
  · rintro ⟨hr, hi⟩
    rw [complexification_real_imag_decomposition M z, hr, hi]
    simp

private theorem tensorRealPart_baseChange
    {N : Type*} [AddCommGroup N] [Module ℝ N]
    (f : M →ₗ[ℝ] N) (z : ℂ ⊗[ℝ] M) :
    tensorRealPart N (f.baseChange ℂ z) = f (tensorRealPart M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [tensorRealPart_tmul]
  | add x y hx hy => simp [hx, hy]

private theorem tensorImagPart_baseChange
    {N : Type*} [AddCommGroup N] [Module ℝ N]
    (f : M →ₗ[ℝ] N) (z : ℂ ⊗[ℝ] M) :
    tensorImagPart N (f.baseChange ℂ z) = f (tensorImagPart M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [tensorImagPart_tmul]
  | add x y hx hy => simp [hx, hy]

/-- Complex scalar extension of a real subspace consists precisely of
the vectors whose real and imaginary coordinates lie in that subspace. -/
theorem complexification_mem_baseChange_iff_parts (N : Submodule ℝ M)
    (z : ℂ ⊗[ℝ] M) :
    z ∈ N.baseChange ℂ ↔ tensorRealPart M z ∈ N ∧ tensorImagPart M z ∈ N := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [tensorRealPart_baseChange, tensorImagPart_baseChange]
    exact ⟨(tensorRealPart N t).property, (tensorImagPart N t).property⟩
  · rintro ⟨hr, hi⟩
    rw [complexification_real_imag_decomposition M z]
    exact (N.baseChange ℂ).add_mem
      (N.tmul_mem_baseChange_of_mem 1 hr) (N.tmul_mem_baseChange_of_mem Complex.I hi)

/-- Scalar extension reflects membership of vectors in the original real
subspace. -/
theorem complexification_real_mem_baseChange_iff (N : Submodule ℝ M) (m : M) :
    1 ⊗ₜ[ℝ] m ∈ N.baseChange ℂ ↔ m ∈ N := by
  rw [complexification_mem_baseChange_iff_parts]
  simp [tensorRealPart_tmul, tensorImagPart_tmul]

end RealVectorSpace

section Killing

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

private theorem complexification_killing_real_tmul (x y : g) :
    killingForm ℂ (ℂ ⊗[ℝ] g) (1 ⊗ₜ[ℝ] x) (1 ⊗ₜ[ℝ] y) =
      (killingForm ℝ g x y : ℂ) := by
  change LinearMap.trace ℂ (ℂ ⊗[ℝ] g)
      ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] g) (ℂ ⊗[ℝ] g) (1 ⊗ₜ[ℝ] x)).comp
        (LieModule.toEnd ℂ (ℂ ⊗[ℝ] g) (ℂ ⊗[ℝ] g) (1 ⊗ₜ[ℝ] y))) = _
  rw [LieModule.toEnd_baseChange, LieModule.toEnd_baseChange,
    ← LinearMap.baseChange_comp, LinearMap.trace_baseChange]
  rfl

/-- On pure tensors the complex Killing form is the scalar extension of
the real Killing form, with no normalization factor. -/
theorem complexification_killing_tmul (a b : ℂ) (x y : g) :
    killingForm ℂ (ℂ ⊗[ℝ] g) (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) =
      a * b * (killingForm ℝ g x y : ℂ) := by
  have ha : a ⊗ₜ[ℝ] x = a • (1 ⊗ₜ[ℝ] x) := by
    rw [TensorProduct.smul_tmul']; simp
  have hb : b ⊗ₜ[ℝ] y = b • (1 ⊗ₜ[ℝ] y) := by
    rw [TensorProduct.smul_tmul']; simp
  rw [ha, hb]
  simp only [map_smul, LinearMap.smul_apply, complexification_killing_real_tmul, smul_eq_mul]
  ring

/-- Equality of bilinear forms, rather than just equality on chosen
coordinates: the Killing form commutes with this scalar extension. -/
theorem complexification_killing_eq_baseChange :
    killingForm ℂ (ℂ ⊗[ℝ] g) = (killingForm ℝ g).baseChange ℂ := by
  ext x y
  change killingForm ℂ (ℂ ⊗[ℝ] g) (1 ⊗ₜ[ℝ] x) (1 ⊗ₜ[ℝ] y) =
    (killingForm ℝ g).baseChange ℂ (1 ⊗ₜ[ℝ] x) (1 ⊗ₜ[ℝ] y)
  rw [complexification_killing_real_tmul, LinearMap.BilinForm.baseChange_tmul]
  simp [Complex.real_smul]

/-- Nondegeneracy of the real Killing form implies nondegeneracy of the
complexified Killing form. -/
theorem complexification_isKilling [LieAlgebra.IsKilling ℝ g] :
    LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) := by
  constructor
  apply le_antisymm
  · intro z hz
    have hz' := (LieIdeal.mem_killingCompl ℂ (ℂ ⊗[ℝ] g) ⊤).mp hz
    have hparts (y : g) :
        (killingForm ℝ g y (tensorRealPart g z) : ℂ) +
          Complex.I * (killingForm ℝ g y (tensorImagPart g z) : ℂ) = 0 := by
      have h := hz' (1 ⊗ₜ[ℝ] y) (by trivial)
      rw [complexification_real_imag_decomposition g z, map_add,
        complexification_killing_tmul, complexification_killing_tmul] at h
      simpa using h
    have hr : tensorRealPart g z ∈ LieIdeal.killingCompl ℝ g ⊤ := by
      apply (LieIdeal.mem_killingCompl ℝ g ⊤).mpr
      intro y _
      simpa using congrArg Complex.re (hparts y)
    have hi : tensorImagPart g z ∈ LieIdeal.killingCompl ℝ g ⊤ := by
      apply (LieIdeal.mem_killingCompl ℝ g ⊤).mpr
      intro y _
      simpa using congrArg Complex.im (hparts y)
    rw [LieAlgebra.IsKilling.killingCompl_top_eq_bot] at hr hi
    exact (complexification_zero_iff_parts g z).2 ⟨hr, hi⟩
  · exact bot_le

/-- The complexification of a compact centreless real Lie algebra has
nondegenerate Killing form.  This needs no classification of real or complex
simple Lie algebras. -/
theorem compact_complexification_isKilling (B : CompactForm g)
    (hc : LieAlgebra.center ℝ g = ⊥) :
    LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) := by
  letI := compact_centerless_isKilling B hc
  exact complexification_isKilling

end Killing

section BracketReflection

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- A bracket inclusion proved after complexification reflects back to
the original real subspaces.  In particular, a symmetric complex complement
forces the real complement to be symmetric. -/
theorem complexification_bracket_inclusion_reflects (p q r : Submodule ℝ g)
    (h : ∀ x ∈ p.baseChange ℂ, ∀ y ∈ q.baseChange ℂ, ⁅x, y⁆ ∈ r.baseChange ℂ) :
    ∀ x ∈ p, ∀ y ∈ q, ⁅x, y⁆ ∈ r := by
  intro x hx y hy
  apply (complexification_real_mem_baseChange_iff g r ⁅x, y⁆).mp
  have ht := h (1 ⊗ₜ[ℝ] x) (p.tmul_mem_baseChange_of_mem 1 hx)
    (1 ⊗ₜ[ℝ] y) (q.tmul_mem_baseChange_of_mem 1 hy)
  simpa using ht

end BracketReflection


end CubicAnomaly.Classification.Complexification
