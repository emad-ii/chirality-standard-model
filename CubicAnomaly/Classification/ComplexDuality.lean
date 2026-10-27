import CubicAnomaly.Classification.AbsoluteSimplicity
import CubicAnomaly.Classification.ComplexHalf
import CubicAnomaly.Classification.CyclicBracket

/-!
# Duality and inequivalence of the actual complex halves

The eigenspaces here are submodules of the actual scalar extension
`ℂ ⊗[ℝ] M`.  The real commutant obstructs every equivariant complex map
from one half to the other.  An invariant positive form, extended bilinearly,
identifies the negative half with the contragredient of the positive half.
-/

namespace CubicAnomaly.Classification.ComplexDuality

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.AbsoluteSimplicity
open CubicAnomaly.Classification.CyclicBracket
open scoped TensorProduct

noncomputable section

section Inequivalence

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]

/-- A complex-linear equivariant map from the actual positive half to the
negative half vanishes when the real commutant is `ℂ`. -/
theorem opposite_complex_half_intertwiner_eq_zero
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ)
    (f : (invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I)
      →ₗ⁅ℂ,ℂ ⊗[ℝ] L⁆
      (invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I))) :
    f = 0 := by
  let J := commutantComplexStructure e
  have hJ := commutant_complex_structure_square e
  let P := positiveHalfRealEquiv J hJ
  let N := negativeHalfRealEquiv J hJ
  let r : M →ₗ[ℝ] M := N.symm.toLinearMap.comp
    ((f.toLinearMap.restrictScalars ℝ).comp P.toLinearMap)
  have hr : ∀ m, N (r m) = f (P m) := fun m => N.apply_symm_apply _
  let F : M →ₗ⁅ℝ,L⁆ M := {
    r with
    map_lie' := by
      intro x m
      apply N.injective
      change N (r ⁅x, m⁆) = N ⁅x, r m⁆
      rw [hr]
      change f (positiveHalfRealEquiv J hJ ⁅x, m⁆) =
        negativeHalfRealEquiv J hJ ⁅x, r m⁆
      rw [positiveHalfRealEquiv_map_lie, negativeHalfRealEquiv_map_lie, f.map_lie]
      rw [hr] }
  have hanti : ∀ m, F (J m) = -J (F m) := by
    intro m
    apply N.injective
    change N (r (J m)) = N (-J (r m))
    rw [hr, map_neg]
    change f (positiveHalfRealEquiv J hJ (J m)) =
      -negativeHalfRealEquiv J hJ (J (r m))
    rw [positiveHalfRealEquiv_map_complexStructure,
      negativeHalfRealEquiv_map_complexStructure, map_smul, neg_smul, neg_neg]
    rw [hr]
  have hF : F = 0 := anticomplex_intertwiner_eq_zero e F hanti
  apply DFunLike.ext
  intro z
  obtain ⟨m, rfl⟩ := P.surjective z
  have hz : r m = 0 := congrArg (fun t : M →ₗ⁅ℝ,L⁆ M => t m) hF
  change f (P m) = 0
  exact (hr m).symm.trans (by rw [hz, map_zero])

/-- The two actual eigenspace representations are inequivalent, not merely
distinct subspaces of the complexification. -/
theorem complex_halves_not_equivalent [Nontrivial M]
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) :
    ¬Nonempty ((invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I)
      ≃ₗ⁅ℂ,ℂ ⊗[ℝ] L⁆
      (invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I))) := by
  rintro ⟨F⟩
  have hF := opposite_complex_half_intertwiner_eq_zero e F.toLieModuleHom
  let P := positiveHalfRealEquiv (commutantComplexStructure e)
    (commutant_complex_structure_square e)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  apply hm
  apply P.injective
  apply F.injective
  have hz := congrArg (fun f => f (P m)) hF
  simpa using hz

end Inequivalence

section InvariantPairing

variable {K V : Type*} [LieRing K] [LieAlgebra ℂ K]
  [AddCommGroup V] [Module ℂ V] [LieRingModule K V] [LieModule ℂ K V]

private def restrictedInvariantPairing
    (Φ : LinearMap.BilinForm ℂ V) (hΦ : Φ.lieInvariant K)
    (P N : LieSubmodule ℂ K V) : N →ₗ⁅ℂ,K⁆ Module.Dual ℂ P where
  __ := LinearMap.comp P.incl.toLinearMap.dualMap (LinearMap.comp Φ N.incl.toLinearMap)
  map_lie' := by
    intro x y
    ext z
    change Φ ⁅x, y.val⁆ z.val = -Φ y.val ⁅x, z.val⁆
    exact hΦ x y.val z.val

private theorem complementary_isotropic_pairing_injective
    (Φ : LinearMap.BilinForm ℂ V) (hΦ : Φ.lieInvariant K) (hnd : Φ.Nondegenerate)
    (P N : LieSubmodule ℂ K V) (hc : IsCompl P N)
    (hiso : ∀ x y : N, Φ x.val y.val = 0) :
    Function.Injective (restrictedInvariantPairing Φ hΦ P N) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  apply Subtype.ext
  apply hnd.1
  intro z
  have hz : z ∈ P ⊔ N := by rw [hc.sup_eq_top]; trivial
  obtain ⟨p, hp, n, hn, rfl⟩ := (LieSubmodule.mem_sup P N z).mp hz
  have hyp : Φ y.val p = 0 := by
    simpa only [LinearMap.zero_apply] using LinearMap.congr_fun hy (⟨p, hp⟩ : P)
  rw [map_add, hyp, hiso y ⟨n, hn⟩, add_zero]

private theorem nonzero_eigenspace_isotropic
    (J : V →ₗ⁅ℂ,K⁆ V) (Φ : LinearMap.BilinForm ℂ V)
    (hskew : ∀ x y, Φ (J x) y = -Φ x (J y))
    (a : ℂ) (ha : a ≠ 0)
    (x y : invariantEigenspace J a) : Φ x.val y.val = 0 := by
  have hx : J x.val = a • x.val := sub_eq_zero.mp x.property
  have hy : J y.val = a • y.val := sub_eq_zero.mp y.property
  have h := hskew x.val y.val
  simp only [hx, hy, map_smul, smul_eq_mul] at h
  have hsum : a * Φ x.val y.val + a * Φ x.val y.val = 0 :=
    eq_neg_iff_add_eq_zero.mp h
  have htwo : (2 * a) * Φ x.val y.val = 0 := by
    calc
      (2 * a) * Φ x.val y.val = a * Φ x.val y.val + a * Φ x.val y.val := by ring
      _ = 0 := hsum
  exact (mul_eq_zero.mp htwo).resolve_left (mul_ne_zero (by norm_num) ha)

/-- Complementary complex eigenspaces of an invariant complex structure
are contragredient when an invariant nondegenerate bilinear form makes the
structure skew-adjoint. -/
theorem invariant_complex_eigenspaces_dual [Module.Finite ℂ V]
    (J : V →ₗ⁅ℂ,K⁆ V) (hJ : ∀ v, J (J v) = -v)
    (Φ : LinearMap.BilinForm ℂ V) (hΦ : Φ.lieInvariant K) (hnd : Φ.Nondegenerate)
    (hskew : ∀ x y, Φ (J x) y = -Φ x (J y)) :
    Nonempty ((invariantEigenspace J (-Complex.I)) ≃ₗ⁅ℂ,K⁆
      Module.Dual ℂ (invariantEigenspace J Complex.I)) := by
  let P := invariantEigenspace J Complex.I
  let N := invariantEigenspace J (-Complex.I)
  have hc : IsCompl P N := complex_structure_eigenspaces_isCompl J hJ
  let f := restrictedInvariantPairing Φ hΦ P N
  let f' := restrictedInvariantPairing Φ hΦ N P
  have hinj : Function.Injective f := complementary_isotropic_pairing_injective
    Φ hΦ hnd P N hc
      (nonzero_eigenspace_isotropic J Φ hskew (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero))
  have hinj' : Function.Injective f' := complementary_isotropic_pairing_injective
    Φ hΦ hnd N P hc.symm
      (nonzero_eigenspace_isotropic J Φ hskew Complex.I Complex.I_ne_zero)
  have hdim : Module.finrank ℂ N = Module.finrank ℂ (Module.Dual ℂ P) := by
    have hNP := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hinj
    have hPN := LinearMap.finrank_le_finrank_of_injective (f := f'.toLinearMap) hinj'
    rw [Subspace.dual_finrank_eq] at hNP hPN ⊢
    exact Nat.le_antisymm hNP hPN
  exact ⟨{
    f.toLinearMap.linearEquivOfInjective hinj hdim with
    toFun := f
    map_lie' := by intro x y; exact f.map_lie x y }⟩

end InvariantPairing

section RealInvariantForm

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]

private theorem baseChange_form_nondegenerate (Φ : LinearMap.BilinForm ℝ M)
    (hnd : Φ.Nondegenerate) : (Φ.baseChange ℂ).Nondegenerate := by
  have hright (z : ℂ ⊗[ℝ] M) (y : M) :
      Φ.baseChange ℂ z (1 ⊗ₜ[ℝ] y) =
        (Φ (tensorRealPart M z) y : ℂ) + Complex.I * (Φ (tensorImagPart M z) y : ℂ) := by
    conv_lhs => rw [complexification_real_imag_decomposition M z]
    simp [Complex.real_smul, mul_comm]
  have hleft (x : M) (z : ℂ ⊗[ℝ] M) :
      Φ.baseChange ℂ (1 ⊗ₜ[ℝ] x) z =
        (Φ x (tensorRealPart M z) : ℂ) + Complex.I * (Φ x (tensorImagPart M z) : ℂ) := by
    conv_lhs => rw [complexification_real_imag_decomposition M z]
    simp [Complex.real_smul, mul_comm]
  constructor
  · intro z hz
    apply (complexification_zero_iff_parts M z).mpr
    constructor
    · apply hnd.1
      intro y
      have h := hz (1 ⊗ₜ[ℝ] y)
      rw [hright] at h
      simpa using congrArg Complex.re h
    · apply hnd.1
      intro y
      have h := hz (1 ⊗ₜ[ℝ] y)
      rw [hright] at h
      simpa using congrArg Complex.im h
  · intro z hz
    apply (complexification_zero_iff_parts M z).mpr
    constructor
    · apply hnd.2
      intro x
      have h := hz (1 ⊗ₜ[ℝ] x)
      rw [hleft] at h
      simpa using congrArg Complex.re h
    · apply hnd.2
      intro x
      have h := hz (1 ⊗ₜ[ℝ] x)
      rw [hleft] at h
      simpa using congrArg Complex.im h

private theorem baseChange_form_invariant (Φ : LinearMap.BilinForm ℝ M)
    (hΦ : Φ.lieInvariant L) : (Φ.baseChange ℂ).lieInvariant (ℂ ⊗[ℝ] L) := by
  intro x y z
  change (Φ.baseChange ℂ)
      ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) x) y) z =
    -(Φ.baseChange ℂ) y ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) x) z)
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
    | tmul b y =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero, neg_zero]
      | tmul c z =>
        simp only [LieModule.toEnd_apply_apply, LieAlgebra.ExtendScalars.bracket_tmul,
          LinearMap.BilinForm.baseChange_tmul, Complex.real_smul]
        rw [hΦ x y z, Complex.ofReal_neg]
        ring
      | add z w hz hw =>
        simp only [map_add, hz, hw]
        abel
    | add y w hy hw =>
      simp only [map_add, LinearMap.add_apply, hy, hw]
      abel
  | add x w hx hw =>
    simp only [map_add, LinearMap.add_apply, hx, hw]
    abel

private theorem baseChange_form_skew (Φ : LinearMap.BilinForm ℝ M)
    (J : M →ₗ⁅ℝ,L⁆ M) (hskew : ∀ x y, Φ (J x) y = -Φ x (J y)) :
    ∀ x y : ℂ ⊗[ℝ] M,
      (Φ.baseChange ℂ) (complexifiedEnd J x) y =
        -(Φ.baseChange ℂ) x (complexifiedEnd J y) := by
  intro x y
  change (Φ.baseChange ℂ) ((J.toLinearMap.baseChange ℂ) x) y =
    -(Φ.baseChange ℂ) x ((J.toLinearMap.baseChange ℂ) y)
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, neg_zero]
    | tmul b y => simp [hskew, Complex.real_smul]
    | add y z hy hz =>
      simp only [map_add, hy, hz]
      abel
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz]
    abel

/-- A positive invariant real form and the actual complex commutant identify
the negative half with the dual of the positive half, without supplying any
duality or complex-bilinear nondegeneracy as an input. -/
theorem positive_invariant_complex_halves_dual [Module.Finite ℝ M] [Nontrivial M]
    (Φ : LinearMap.BilinForm ℝ M)
    (hpositive : ∀ x : M, x ≠ 0 → 0 < Φ x x)
    (hΦ : Φ.lieInvariant L)
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) :
    Nonempty ((invariantEigenspace (complexifiedEnd (commutantComplexStructure e))
      (-Complex.I)) ≃ₗ⁅ℂ,ℂ ⊗[ℝ] L⁆ Module.Dual ℂ
      (invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I)) := by
  have hdef : ∀ x : M, Φ x x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have := hpositive x hx0
    linarith
  have hnd : Φ.Nondegenerate := by
    constructor <;> intro x hx <;> exact hdef x (hx x)
  exact invariant_complex_eigenspaces_dual
    (complexifiedEnd (commutantComplexStructure e))
    (complexifiedEnd_square (commutantComplexStructure e)
      (commutant_complex_structure_square e))
    (Φ.baseChange ℂ) (baseChange_form_invariant Φ hΦ)
    (baseChange_form_nondegenerate Φ hnd)
    (baseChange_form_skew Φ (commutantComplexStructure e)
      (complex_commutant_structure_skew Φ hpositive hΦ e))

end RealInvariantForm

section CompactPair

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The actual complexification of a proper compact complex-type complement
is a direct sum of two irreducible, inequivalent contragredient modules.
Every conclusion is derived from the positive invariant form and the real
commutant, with no representation-theoretic classification input. -/
theorem compact_complement_complex_type_decomposition
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    let J := complexifiedEnd (commutantComplexStructure e)
    let V := invariantEigenspace J Complex.I
    let Vbar := invariantEigenspace J (-Complex.I)
    IsCompl V Vbar ∧
      LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) V ∧
      LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) Vbar ∧
      Nonempty (Vbar ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ V) ∧
      ¬Nonempty (V ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Vbar) := by
  let q := orthogonalComplement B h
  have hc := compact_orthogonal_complement_isCompl B h
  have hqne : q ≠ ⊥ := by
    intro hq
    have hq' : q.toSubmodule = ⊥ := congrArg LieSubmodule.toSubmodule hq
    have htop := hc.sup_eq_top
    rw [hq', sup_bot_eq] at htop
    exact hproper ((LieSubalgebra.toSubmodule_eq_top h).mp htop)
  letI : Nontrivial q := (LieSubmodule.nontrivial_iff_ne_bot ℝ h g).mpr hqne
  letI : LieModule.IsIrreducible ℝ h q := compact_complex_commutant_irreducible B h q e
  let Φ : LinearMap.BilinForm ℝ q := B.form.restrict q.toSubmodule
  exact ⟨complexified_complex_structure_isCompl (commutantComplexStructure e)
      (commutant_complex_structure_square e),
    complexification_positive_half_irreducible (commutantComplexStructure e)
      (commutant_complex_structure_square e),
    complexification_negative_half_irreducible (commutantComplexStructure e)
      (commutant_complex_structure_square e),
    positive_invariant_complex_halves_dual Φ
      (fun x hx => B.positive x (fun hz => hx (Subtype.ext hz)))
      (fun x y z => B.invariant x.val y.val z.val) e,
    complex_halves_not_equivalent e⟩

end CompactPair

end

end CubicAnomaly.Classification.ComplexDuality
