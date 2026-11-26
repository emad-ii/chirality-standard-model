import CubicAnomaly.Fixed.E8RadicalCentralizer
import CubicAnomaly.Fixed.E8RadicalIdentification

/-! The two compact ideals in the paper's original real isotropy algebra.
Their literal inclusions complexify to the two constructed complex factors. -/

namespace CubicAnomaly.Fixed.E8CompactFactors

open CubicAnomaly.Classification.Structural
open E8CanonicalPair E8CompactPair E8RadicalFamily E8Grading E8FullCubic
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

abbrev compactRadical := canonicalHalf.cubicRadical

/-- The orthogonal ideal to the real cubic radical in the compact isotropy. -/
def compactFamily : LieIdeal ℝ compactZero :=
  LieAlgebra.InvariantForm.orthogonal compactZeroForm.form compactZeroForm.invariant compactRadical

theorem e8_compact_factors_isCompl : IsCompl compactRadical.toSubmodule compactFamily.toSubmodule :=
  compact_orthogonal_complement_isCompl compactZeroForm (compactRadical : LieSubalgebra ℝ compactZero)

theorem e8_compact_factors_commute (a : compactRadical) (b : compactFamily) :
    ⁅a.val, b.val⁆ = 0 := by
  have hm : ⁅a.val, b.val⁆ ∈ compactRadical.toSubmodule ⊓ compactFamily.toSubmodule :=
    ⟨lie_mem_left ℝ compactZero _ _ _ a.property, compactFamily.lie_mem b.property⟩
  rwa [e8_compact_factors_isCompl.disjoint.eq_bot, Submodule.mem_bot] at hm

theorem e8_compact_family_real_finrank : Module.finrank ℝ compactFamily = 8 := by
  have h := Submodule.finrank_add_eq_of_isCompl e8_compact_factors_isCompl
  change Module.finrank ℝ canonicalHalf.cubicRadical + Module.finrank ℝ compactFamily =
    Module.finrank ℝ compactZero at h
  exact Nat.add_left_cancel (h.trans e8_compactZero_finrank |>.trans
    (congrArg (· + 8) e8_canonical_radical_real_finrank).symm)

private def extendIdeal {L : Type*} [LieRing L] [LieAlgebra ℝ L] (I : LieIdeal ℝ L) :
    (ℂ ⊗[ℝ] I) →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] L) where
  __ := I.toSubmodule.subtype.baseChange ℂ
  map_lie' {x y} := (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) I.incl).map_lie x y

/-- Extend the actual inclusion of a compact ideal to the degree-zero algebra. -/
def idealComplexification (I : LieIdeal ℝ compactZero) : (ℂ ⊗[ℝ] I) →ₗ⁅ℂ⁆ zeroSubalgebra :=
  zeroComplexificationEquiv.toLieHom.comp (extendIdeal I)

private theorem complexification_tmul (I : LieIdeal ℝ compactZero) (c : ℂ) (x : I) :
    idealComplexification I (c ⊗ₜ[ℝ] x) = c • compactZeroToComplex x.val :=
  e8_zeroComplexificationEquiv_tmul c x.val

private theorem complexification_injective (I : LieIdeal ℝ compactZero) :
    Function.Injective (idealComplexification I) :=
  zeroComplexificationEquiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap I.toSubmodule.subtype Subtype.val_injective)

private theorem complex_radical_range :
    (idealComplexification compactRadical).toLinearMap.range = fullRadical.toSubmodule := by
  change LinearMap.range (zeroComplexificationEquiv.toLinearEquiv.toLinearMap.comp
    (compactRadical.toSubmodule.subtype.baseChange ℂ)) = _
  rw [LinearMap.range_comp]
  exact e8_canonical_radical_complexification

/-- The original real cubic radical complexifies to the independent E₆ lattice model. -/
def compactRadicalComplexEquiv : (ℂ ⊗[ℝ] compactRadical) ≃ₗ⁅ℂ⁆ E6Lattice.Algebra :=
  ((LieEquiv.ofInjective _ (complexification_injective compactRadical)).trans
    (LieEquiv.ofEq _ (fullRadical : LieSubalgebra ℂ zeroSubalgebra)
      (congrArg (fun S : Submodule ℂ zeroSubalgebra => (S : Set zeroSubalgebra))
        complex_radical_range))).trans E6Lattice.radicalLieEquiv.symm

private theorem extended_factors_commute (v : ℂ ⊗[ℝ] compactRadical)
    (w : ℂ ⊗[ℝ] compactFamily) :
    ⁅idealComplexification compactRadical v, idealComplexification compactFamily w⁆ = 0 := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, add_lie, ha, hb, add_zero]
  | tmul c a =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, lie_add, hu, hv, add_zero]
    | tmul t b =>
      simp only [complexification_tmul, smul_lie, lie_smul, ← LieHom.map_lie,
        e8_compact_factors_commute, map_zero, smul_zero]

private theorem commutes_with_range {A B L : Type*} [LieRing L]
    (f : A → L) (g : B → L) (r : L) (w : B)
    (hr : ∃ v, f v = r) (h : ∀ v, ⁅f v, g w⁆ = 0) :
    ⁅g w, r⁆ = 0 := by
  obtain ⟨v, rfl⟩ := hr
  rw [← lie_skew, h, neg_zero]

private theorem complexification_finrank (M : Type*) [AddCommGroup M] [Module ℝ M] :
    Module.finrank ℂ (ℂ ⊗[ℝ] M) = Module.finrank ℝ M := Module.finrank_baseChange

private theorem complex_family_range :
    (idealComplexification compactFamily).toLinearMap.range = familySpace := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨w, rfl⟩
    apply (e8_centralizes_radical_iff _).mp
    intro r
    have hr : r.val ∈ (idealComplexification compactRadical).toLinearMap.range :=
      complex_radical_range.symm ▸ r.property
    exact commutes_with_range (idealComplexification compactRadical) (idealComplexification compactFamily)
      r.val w hr (fun v => extended_factors_commute v w)
  · rw [LinearMap.finrank_range_of_inj (complexification_injective compactFamily),
      complexification_finrank compactFamily, e8_compact_family_real_finrank, e8_familySpace_finrank]

/-- The complexification equivalence uses the given family embedding into
the actual zero algebra. -/
def compactFamilyComplexEquiv : (ℂ ⊗[ℝ] compactFamily) ≃ₗ⁅ℂ⁆ E8A2.sl3 :=
  ((LieEquiv.ofInjective _ (complexification_injective compactFamily)).trans
    (LieEquiv.ofEq _ E8A2.sl3ZeroEmbedding.range
      (congrArg (fun S : Submodule ℂ zeroSubalgebra => (S : Set zeroSubalgebra))
        complex_family_range))).trans
    (LieEquiv.ofInjective _ E8A2.e8_a2_sl3ZeroEmbedding_injective).symm

theorem e8_compact_family_embedding (x : compactFamily) :
    E8A2.sl3ZeroEmbedding (compactFamilyComplexEquiv (1 ⊗ₜ[ℝ] x)) =
      compactZeroToComplex x.val := by
  let e := LieEquiv.ofInjective _ E8A2.e8_a2_sl3ZeroEmbedding_injective
  let b := (LieEquiv.ofEq (idealComplexification compactFamily).range E8A2.sl3ZeroEmbedding.range
    (congrArg (fun S : Submodule ℂ zeroSubalgebra => (S : Set zeroSubalgebra)) complex_family_range))
  let a := LieEquiv.ofInjective _ (complexification_injective compactFamily)
  let v := b (a (1 ⊗ₜ[ℝ] x))
  have h := congrArg Subtype.val (e.apply_symm_apply v)
  exact h.trans (by simpa only [one_smul] using complexification_tmul compactFamily 1 x)

end

end CubicAnomaly.Fixed.E8CompactFactors
