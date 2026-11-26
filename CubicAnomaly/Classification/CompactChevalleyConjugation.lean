import CubicAnomaly.Classification.CompactCartan
import CubicAnomaly.Classification.ComplexDuality
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Compact conjugation and normalized root triples

Complex conjugation on the scalar extension of a compact Lie algebra is a
real Lie involution. The positive invariant form pairs each nonzero vector
positively with its conjugate. This determines the sign in compact root triples.
-/

namespace CubicAnomaly.Classification.CompactChevalleyConjugation

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open Structural Complexification CompactGeometry ComplexDuality
open scoped TensorProduct ComplexConjugate

noncomputable section

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- The real-linear conjugation of coefficients on the scalar extension. -/
def scalarConjugation : (ℂ ⊗[ℝ] g) →ₗ[ℝ] (ℂ ⊗[ℝ] g) :=
  TensorProduct.map Complex.conjAe.toLinearMap LinearMap.id

@[simp] theorem scalarConjugation_tmul (a : ℂ) (x : g) :
    scalarConjugation (a ⊗ₜ[ℝ] x) = (conj a) ⊗ₜ[ℝ] x := rfl

@[simp] theorem scalarConjugation_twice (x : ℂ ⊗[ℝ] g) :
    scalarConjugation (scalarConjugation x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add x y hx hy => simp [hx, hy]

theorem scalarConjugation_complex_smul (a : ℂ) (x : ℂ ⊗[ℝ] g) :
    scalarConjugation (a • x) = conj a • scalarConjugation x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [smul_add, hx, hy]

theorem scalarConjugation_lie (x y : ℂ ⊗[ℝ] g) :
    scalarConjugation ⁅x, y⁆ = ⁅scalarConjugation x, scalarConjugation y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => simp [add_lie, hx, hz]
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero =>
      change scalarConjugation ((ad ℂ _ (a ⊗ₜ[ℝ] x)) 0) = (ad ℂ _ (scalarConjugation (a ⊗ₜ[ℝ] x))) (scalarConjugation (0 : ℂ ⊗[ℝ] g))
      simp only [map_zero]
    | add y z hy hz =>
      change scalarConjugation ((ad ℂ _ (a ⊗ₜ[ℝ] x)) (y + z)) = (ad ℂ _ (scalarConjugation (a ⊗ₜ[ℝ] x))) (scalarConjugation (y + z))
      simp only [map_add]
      exact congrArg₂ (· + ·) hy hz
    | tmul b y => simp [LieAlgebra.ExtendScalars.bracket_tmul]

private theorem scalarConjugation_mem (A : LieSubalgebra ℝ g) {z : ℂ ⊗[ℝ] g}
    (hz : z ∈ complexifiedSubalgebra A) : scalarConjugation z ∈ complexifiedSubalgebra A := by
  have hp := (complexification_mem_baseChange_iff_parts g A.toSubmodule z).mp hz
  rw [complexification_real_imag_decomposition g z, map_add, scalarConjugation_tmul,
    scalarConjugation_tmul]
  exact (A.toSubmodule.baseChange ℂ).add_mem
    (A.toSubmodule.tmul_mem_baseChange_of_mem _ hp.1)
    (A.toSubmodule.tmul_mem_baseChange_of_mem _ hp.2)

private theorem positive_pairing (B : CompactForm g) (x : ℂ ⊗[ℝ] g) (hx : x ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ (B.form.baseChange ℂ) x (scalarConjugation x) = a := by
  let r := tensorRealPart g x
  let s := tensorImagPart g x
  have nonneg (y : g) : 0 ≤ B.form y y := by
    by_cases hy : y = 0
    · simp [hy]
    · exact (B.positive y hy).le
  refine ⟨B.form r r + B.form s s, ?_, ?_⟩
  · by_cases hr : r = 0
    · have hs : s ≠ 0 := fun hs => hx ((complexification_zero_iff_parts g x).mpr ⟨hr, hs⟩)
      exact add_pos_of_nonneg_of_pos (nonneg _) (B.positive s hs)
    · exact add_pos_of_pos_of_nonneg (B.positive r hr) (nonneg _)
  · have h : x = 1 ⊗ₜ[ℝ] r + Complex.I ⊗ₜ[ℝ] s := complexification_real_imag_decomposition g x
    rw [h]
    simp only [map_add, scalarConjugation_tmul, map_one, Complex.conj_I, LinearMap.add_apply,
      LinearMap.BilinForm.baseChange_tmul, Complex.real_smul, Complex.ofReal_add]
    rw [B.symmetric s r]
    ring_nf
    simp

variable [Module.Finite ℝ g] [IsKilling ℂ (ℂ ⊗[ℝ] g)]
variable (A : LieSubalgebra ℝ g) [ (complexifiedSubalgebra A).IsCartanSubalgebra ]

/-- Compact conjugation exchanges opposite root spaces of a Cartan obtained
by complexification. -/
theorem compact_conjugation_mem_opposite_rootSpace (B : CompactForm g)
    {α : (complexifiedSubalgebra A) → ℂ} {x : ℂ ⊗[ℝ] g}
    (hx : x ∈ rootSpace (complexifiedSubalgebra A) α) :
    scalarConjugation x ∈ rootSpace (complexifiedSubalgebra A) (-α) := by
  by_cases hzero : x = 0
  · simp [hzero]
  apply weightSpace_le_genWeightSpace
  apply (mem_weightSpace _ _).mpr
  intro z
  let z' : complexifiedSubalgebra A := ⟨scalarConjugation z.val, scalarConjugation_mem A z.property⟩
  have he := congrArg scalarConjugation (lie_eq_smul_of_mem_rootSpace hx z')
  change scalarConjugation ⁅scalarConjugation z.val, x⁆ = scalarConjugation (α z' • x) at he
  rw [scalarConjugation_lie, scalarConjugation_twice, scalarConjugation_complex_smul] at he
  have hr := complexified_invariantForm_invariant B.form B.invariant z.val x (scalarConjugation x)
  change (B.form.baseChange ℂ) ⁅z.val, x⁆ (scalarConjugation x) =
    -(B.form.baseChange ℂ) x ⁅z.val, scalarConjugation x⁆ at hr
  rw [show ⁅z.val, x⁆ = α z • x from lie_eq_smul_of_mem_rootSpace hx z, he] at hr
  obtain ⟨a, ha, hpair⟩ := positive_pairing B x hzero
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hpair] at hr
  have h : conj (α z') = -α z := by
    apply mul_right_cancel₀ (show (a : ℂ) ≠ 0 by exact_mod_cast ha.ne')
    linear_combination hr
  exact he.trans (congrArg (· • scalarConjugation x) h)

private theorem scaled_bracket_left {G : Type*} [LieRing G] [LieAlgebra ℂ G]
    (a : ℂ) (x y : G) : ⁅a • x, y⁆ = a • ⁅x, y⁆ := smul_lie _ _ _

private theorem scaled_bracket_right {G : Type*} [LieRing G] [LieAlgebra ℂ G]
    (a : ℂ) (x y : G) : ⁅x, a • y⁆ = a • ⁅x, y⁆ := lie_smul _ _ _

/-- Every actual root admits a compact-normalized `sl₂` triple: its
negative root vector is minus the conjugate of its positive root vector. -/
theorem exists_compact_normalized_root_triple (B : CompactForm g)
    (i : (complexifiedSubalgebra A).root) :
    ∃ e f : ℂ ⊗[ℝ] g,
      IsSl2Triple (coroot i.val : ℂ ⊗[ℝ] g) e f ∧
      e ∈ rootSpace (complexifiedSubalgebra A) i.val ∧
      f ∈ rootSpace (complexifiedSubalgebra A) (-i.val : _ → ℂ) ∧
      scalarConjugation e = -f := by
  let H := complexifiedSubalgebra A
  have hi : i.val.IsNonZero := (Finset.mem_filter.mp i.property).2
  obtain ⟨h, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hi
  obtain rfl := t.h_eq_coroot hi he hf
  let h : ℂ ⊗[ℝ] g := coroot i.val
  have hce := compact_conjugation_mem_opposite_rootSpace A B he
  have negOne : finrank ℂ (rootSpace H (-i.val : _ → ℂ)) = 1 :=
    finrank_rootSpace_eq_one (-i.val) (neg_ne_zero.mpr hi)
  obtain ⟨k, hk⟩ : ∃ k : ℂ, k • f = scalarConjugation e := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simpa using t.f_ne_zero)).mp
      negOne ⟨scalarConjugation e, hce⟩
  have hk0 : k ≠ 0 := by
    intro hk0
    have hz := congrArg scalarConjugation hk
    exact t.e_ne_zero (by simpa [hk0] using hz.symm)
  let v : ℂ ⊗[ℝ] g := ⁅scalarConjugation e, e⁆
  have hcv : scalarConjugation v = -v := by
    change scalarConjugation ⁅scalarConjugation e, e⁆ = -⁅scalarConjugation e, e⁆
    rw [scalarConjugation_lie, scalarConjugation_twice, lie_skew]
  have hv : v = (-k) • h := by
    change ⁅scalarConjugation e, e⁆ = (-k) • h
    rw [← hk, scaled_bracket_left k f e, ← lie_skew f e, t.lie_e_f, neg_smul, smul_neg]
  have hv0 : v ≠ 0 := hv ▸ smul_ne_zero (neg_ne_zero.mpr hk0) t.h_ne_zero
  have hfv : ⁅scalarConjugation e, v⁆ = (-2 * k) • scalarConjugation e := by
    have hfh : ⁅f, h⁆ = (2 : ℂ) • f := by
      rw [← lie_skew f h, t.lie_lie_smul_f ℂ, neg_neg]
    rw [← hk, hv, scaled_bracket_left k f _, scaled_bracket_right (-k) f h, hfh]
    simp only [smul_smul]
    ring_nf
  obtain ⟨a, ha, hae⟩ := positive_pairing B e t.e_ne_zero
  obtain ⟨b, hb, hbv⟩ := positive_pairing B v hv0
  have hform := complexified_invariantForm_invariant B.form B.invariant (scalarConjugation e) e v
  change (B.form.baseChange ℂ) v v = -(B.form.baseChange ℂ) e ⁅scalarConjugation e, v⁆ at hform
  rw [hcv, map_neg, hform, hfv, map_smul, smul_eq_mul, hae, neg_neg] at hbv
  let r := b / (2*a)
  have hr : 0 < r := div_pos hb (by positivity)
  have hkr : k = -(r : ℂ) := by
    dsimp [r]
    push_cast
    rw [← neg_div, eq_div_iff (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr ha.ne'))]
    linear_combination -hbv
  let d : ℂ := Real.sqrt r
  have hd0 : d ≠ 0 := by dsimp [d]; exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have hsq : d * d = (r : ℂ) := by
    dsimp only [d]
    exact_mod_cast Real.mul_self_sqrt hr.le
  refine ⟨d⁻¹ • e, d • f, ⟨t.h_ne_zero, ?_, ?_, ?_⟩,
    (rootSpace H _).smul_mem _ he, (rootSpace H _).smul_mem _ hf, ?_⟩
  · rw [scaled_bracket_left d⁻¹ e _, scaled_bracket_right d e f, t.lie_e_f, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  · rw [scaled_bracket_right d⁻¹ h e, t.lie_h_e_nsmul, smul_comm]
  · rw [scaled_bracket_right d h f, t.lie_h_f_nsmul, smul_neg, smul_comm]
  · rw [scalarConjugation_complex_smul, ← hk, smul_smul, hkr, ← hsq]
    have hcd : conj d = d := Complex.conj_ofReal _
    rw [map_inv₀, hcd, mul_neg, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul, neg_smul]


end

end CubicAnomaly.Classification.CompactChevalleyConjugation
