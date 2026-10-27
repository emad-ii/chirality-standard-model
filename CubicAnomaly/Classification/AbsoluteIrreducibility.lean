import CubicAnomaly.Classification.Complexification
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Absolute irreducibility without a real-division-algebra classification

For an irreducible real Lie module, a proper nonzero submodule of the actual
complexification has zero pure-real intersection.  Its real projection is
therefore injective and, by irreducibility, surjective.  Transporting
multiplication by `I` gives an equivariant complex structure on the original
real module.  Excluding that structure proves absolute irreducibility.
-/

namespace CubicAnomaly.Classification.AbsoluteIrreducibility

open CubicAnomaly.Classification.Complexification
open scoped TensorProduct

noncomputable section

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]

private def pureRealSubmodule (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M)) :
    LieSubmodule ℝ L M where
  __ := (N.toSubmodule.restrictScalars ℝ).comap (TensorProduct.mk ℝ ℂ M 1)
  lie_mem := by
    intro x m hm
    have h := N.lie_mem (x := (1 : ℂ) ⊗ₜ[ℝ] x) hm
    change (1 : ℂ) ⊗ₜ[ℝ] ⁅x, m⁆ ∈ N
    change ⁅(1 : ℂ) ⊗ₜ[ℝ] x, (1 : ℂ) ⊗ₜ[ℝ] m⁆ ∈ N at h
    simpa only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] using h

private theorem pureRealSubmodule_top_implies_top
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M))
    (hN : pureRealSubmodule N = ⊤) : N = ⊤ := by
  apply top_unique
  intro z _
  have hpure : ∀ m : M, 1 ⊗ₜ[ℝ] m ∈ N := by
    intro m
    change m ∈ pureRealSubmodule N
    rw [hN]
    trivial
  rw [complexification_real_imag_decomposition M z]
  apply N.add_mem (hpure _)
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    N.smul_mem Complex.I (hpure (tensorImagPart M z))

private theorem realPart_real_action (x : L) (z : ℂ ⊗[ℝ] M) :
    tensorRealPart M ⁅(1 : ℂ) ⊗ₜ[ℝ] x, z⁆ = ⁅x, tensorRealPart M z⁆ := by
  change tensorRealPart M ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M)
    (1 ⊗ₜ[ℝ] x)) z) = ⁅x, tensorRealPart M z⁆
  induction z using TensorProduct.induction_on with
  | zero => simp only [lie_zero, map_zero]
  | tmul a m => simp [tensorRealPart]
  | add y z hy hz => simp only [map_add, hy, hz, lie_add]

private def submoduleRealPart (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M)) :
    N →ₗ[ℝ] M :=
  (tensorRealPart M).comp (N.toSubmodule.subtype.restrictScalars ℝ)

private theorem submoduleRealPart_injective
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M))
    (hN : pureRealSubmodule N = ⊥) : Function.Injective (submoduleRealPart N) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have hdec := complexification_real_imag_decomposition M (z : ℂ ⊗[ℝ] M)
  change tensorRealPart M z.val = 0 at hz
  rw [hz, TensorProduct.tmul_zero, zero_add] at hdec
  have him : 1 ⊗ₜ[ℝ] tensorImagPart M z.val ∈ N := by
    have ht := N.smul_mem (-Complex.I) z.property
    rw [hdec, TensorProduct.smul_tmul', smul_eq_mul, neg_mul,
      Complex.I_mul_I, neg_neg] at ht
    exact ht
  have himzero : tensorImagPart M z.val = 0 := by
    have hmem : tensorImagPart M z.val ∈ pureRealSubmodule N := him
    rw [hN, LieSubmodule.mem_bot] at hmem
    exact hmem
  apply Subtype.ext
  exact (complexification_zero_iff_parts M z.val).mpr ⟨hz, himzero⟩

private def realProjectedSubmodule
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M)) : LieSubmodule ℝ L M where
  __ := LinearMap.range (submoduleRealPart N)
  lie_mem := by
    rintro x y ⟨z, rfl⟩
    refine ⟨⟨⁅1 ⊗ₜ[ℝ] x, z.val⁆, N.lie_mem z.property⟩, ?_⟩
    exact realPart_real_action x z.val

private theorem realProjectedSubmodule_ne_bot
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M))
    (hne : N ≠ ⊥) (hinj : Function.Injective (submoduleRealPart N)) :
    realProjectedSubmodule N ≠ ⊥ := by
  intro hzero
  apply hne
  apply le_antisymm _ bot_le
  intro z hz
  have hr : submoduleRealPart N (⟨z, hz⟩ : N) ∈ realProjectedSubmodule N :=
    ⟨⟨z, hz⟩, rfl⟩
  rw [hzero, LieSubmodule.mem_bot] at hr
  have hmap : submoduleRealPart N (⟨z, hz⟩ : N) = submoduleRealPart N 0 := by simpa using hr
  exact congrArg Subtype.val (hinj hmap)

private def submoduleTimesI (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M)) : N →ₗ[ℝ] N where
  toFun z := Complex.I • z
  map_add' x y := smul_add Complex.I x y
  map_smul' a z := smul_comm Complex.I a z

private def submoduleRealAction
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M)) (x : L) (z : N) : N :=
  ⟨⁅1 ⊗ₜ[ℝ] x, z.val⁆, N.lie_mem z.property⟩

private theorem submoduleRealPart_action
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M)) (x : L) (z : N) :
    submoduleRealPart N (submoduleRealAction N x z) = ⁅x, submoduleRealPart N z⁆ :=
  realPart_real_action x z.val

private theorem submoduleTimesI_action
    (N : LieSubmodule ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M)) (x : L) (z : N) :
    submoduleTimesI N (submoduleRealAction N x z) =
      submoduleRealAction N x (submoduleTimesI N z) := by
  apply Subtype.ext
  change Complex.I • ⁅1 ⊗ₜ[ℝ] x, z.val⁆ = ⁅1 ⊗ₜ[ℝ] x, Complex.I • z.val⁆
  exact (lie_smul _ _ _).symm

/-- A real irreducible Lie module with no equivariant square root of `-1`
remains irreducible under actual extension of scalars to `ℂ`. -/
theorem complexification_irreducible_of_no_complex_structure
    [LieModule.IsIrreducible ℝ L M]
    (hno : ∀ J : M →ₗ⁅ℝ,L⁆ M, ¬(∀ m, J (J m) = -m)) :
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) := by
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible ℝ L M
  letI : Nontrivial (ℂ ⊗[ℝ] M) := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    refine ⟨⟨1 ⊗ₜ[ℝ] m, 0, ?_⟩⟩
    intro hz
    apply hm
    have hr := congrArg (tensorRealPart M) hz
    simpa [tensorRealPart] using hr
  apply LieModule.IsIrreducible.mk
  intro N hNbot
  by_contra hNtop
  have hreal : pureRealSubmodule N = ⊥ :=
    (IsSimpleOrder.eq_bot_or_eq_top (pureRealSubmodule N)).resolve_right
      (fun htop => hNtop (pureRealSubmodule_top_implies_top N htop))
  have hinj := submoduleRealPart_injective N hreal
  have hrange : realProjectedSubmodule N = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (realProjectedSubmodule N)).resolve_left
      (realProjectedSubmodule_ne_bot N hNbot hinj)
  have hsurj : Function.Surjective (submoduleRealPart N) := by
    intro m
    have hm : m ∈ realProjectedSubmodule N := by rw [hrange]; trivial
    exact hm
  let E : N ≃ₗ[ℝ] M := LinearEquiv.ofBijective (submoduleRealPart N) ⟨hinj, hsurj⟩
  let J : M →ₗ[ℝ] M := E.toLinearMap.comp ((submoduleTimesI N).comp E.symm.toLinearMap)
  have hJ : ∀ m, J (J m) = -m := by
    intro m
    change E (submoduleTimesI N (E.symm (E (submoduleTimesI N (E.symm m))))) = -m
    rw [E.symm_apply_apply]
    have hi : submoduleTimesI N (submoduleTimesI N (E.symm m)) = -E.symm m := by
      change Complex.I • (Complex.I • E.symm m) = -E.symm m
      rw [← mul_smul, Complex.I_mul_I, neg_one_smul]
    rw [hi, map_neg, E.apply_symm_apply]
  have hEsymm : ∀ (x : L) (m : M),
      E.symm ⁅x, m⁆ = submoduleRealAction N x (E.symm m) := by
    intro x m
    apply E.injective
    rw [E.apply_symm_apply]
    change ⁅x, m⁆ = submoduleRealPart N (submoduleRealAction N x (E.symm m))
    rw [submoduleRealPart_action]
    change ⁅x, m⁆ = ⁅x, E (E.symm m)⁆
    rw [E.apply_symm_apply]
  have hcomm : ∀ (x : L) (m : M), J ⁅x, m⁆ = ⁅x, J m⁆ := by
    intro x m
    change E (submoduleTimesI N (E.symm ⁅x, m⁆)) =
      ⁅x, E (submoduleTimesI N (E.symm m))⁆
    rw [hEsymm, submoduleTimesI_action]
    exact submoduleRealPart_action N x (submoduleTimesI N (E.symm m))
  exact hno { J with map_lie' := by intro x m; exact hcomm x m } hJ

end

end CubicAnomaly.Classification.AbsoluteIrreducibility
