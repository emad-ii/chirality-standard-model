import CubicAnomaly.Classification.Structural
import CubicAnomaly.Classification.Complexification
import CubicAnomaly.Classification.CompactSimple

/-!
# Absolute simplicity and the conjugate-intertwiner obstruction

The compact-centroid obstruction rules out the possible splitting of a real
simple algebra after extension to `ℂ`.  The proof uses actual complex ideals
and their real coordinate projections; it does not assume a classification
of compact real forms or complex simple Lie algebras.
-/

namespace CubicAnomaly.Classification.AbsoluteSimplicity

noncomputable section

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open scoped TensorProduct

section Anticomplex

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]

/-- There is no nonzero real equivariant map anticommuting with the complex
structure when the actual real commutant is `ℂ`. -/
theorem anticomplex_intertwiner_eq_zero
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ)
    (f : M →ₗ⁅ℝ,L⁆ M)
    (hf : ∀ x, f (commutantComplexStructure e x) =
      -commutantComplexStructure e (f x)) : f = 0 := by
  let J := commutantComplexStructure e
  let a : lieCommutant (L := L) (M := M) := ⟨f.toLinearMap, f.map_lie⟩
  have ha : a * e.symm Complex.I = e.symm Complex.I * a := by
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  ext x
  have hcomm : f (J x) = J (f x) :=
    congrArg (fun b : lieCommutant (L := L) (M := M) => (b : Module.End ℝ M) x) ha
  have hsum : J (f x) + J (f x) = 0 := by
    calc
      J (f x) + J (f x) = -J (f x) + J (f x) := by
        exact congrArg (fun y : M => y + J (f x)) (hcomm.symm.trans (hf x))
      _ = 0 := neg_add_cancel (J (f x))
  have htwo : (2 : ℝ) • J (f x) = 0 := by simpa only [two_smul] using hsum
  have hzero : J (f x) = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hsquare := commutant_complex_structure_square e (f x)
  change J (J (f x)) = -f x at hsquare
  rw [hzero, map_zero] at hsquare
  exact neg_eq_zero.mp hsquare.symm

end Anticomplex

section CompactSimple

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

private def realInclusion : g →ₗ⁅ℝ⁆ (ℂ ⊗[ℝ] g) where
  __ := TensorProduct.mk ℝ ℂ g 1
  map_lie' := by intro x y; simp

private def complexIdealAsReal (I : LieIdeal ℂ (ℂ ⊗[ℝ] g)) :
    LieIdeal ℝ (ℂ ⊗[ℝ] g) where
  __ := I.toSubmodule.restrictScalars ℝ
  lie_mem := I.lie_mem

private def pureRealIdeal (I : LieIdeal ℂ (ℂ ⊗[ℝ] g)) : LieIdeal ℝ g :=
  (complexIdealAsReal I).comap realInclusion

private theorem pureRealIdeal_top_implies_top (I : LieIdeal ℂ (ℂ ⊗[ℝ] g))
    (hI : pureRealIdeal I = ⊤) : I = ⊤ := by
  apply top_unique
  intro z _
  have hpure : ∀ x : g, 1 ⊗ₜ[ℝ] x ∈ I := by
    intro x
    change x ∈ pureRealIdeal I
    rw [hI]
    trivial
  rw [complexification_real_imag_decomposition g z]
  apply I.add_mem (hpure _)
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    I.smul_mem Complex.I (hpure (tensorImagPart g z))

private theorem realPart_real_bracket (x : g) (z : ℂ ⊗[ℝ] g) :
    tensorRealPart g ⁅(1 : ℂ) ⊗ₜ[ℝ] x, z⁆ = ⁅x, tensorRealPart g z⁆ := by
  change tensorRealPart g ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] g) (ℂ ⊗[ℝ] g)
    (1 ⊗ₜ[ℝ] x)) z) = ⁅x, tensorRealPart g z⁆
  induction z using TensorProduct.induction_on with
  | zero => simp only [lie_zero, map_zero]
  | tmul a y => simp [tensorRealPart]
  | add y z hy hz => simp only [map_add, hy, hz, lie_add]

private noncomputable def idealRealPart (I : LieIdeal ℂ (ℂ ⊗[ℝ] g)) :
    I →ₗ[ℝ] g :=
  (tensorRealPart g).comp (I.toSubmodule.subtype.restrictScalars ℝ)

private theorem idealRealPart_injective (I : LieIdeal ℂ (ℂ ⊗[ℝ] g))
    (hI : pureRealIdeal I = ⊥) : Function.Injective (idealRealPart I) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have hdecomp := complexification_real_imag_decomposition g (z : ℂ ⊗[ℝ] g)
  change tensorRealPart g z.val = 0 at hz
  rw [hz, TensorProduct.tmul_zero, zero_add] at hdecomp
  have him : 1 ⊗ₜ[ℝ] tensorImagPart g z.val ∈ I := by
    have ht := I.smul_mem (-Complex.I) z.property
    rw [hdecomp, TensorProduct.smul_tmul', smul_eq_mul, neg_mul,
      Complex.I_mul_I, neg_neg] at ht
    exact ht
  have himzero : tensorImagPart g z.val = 0 := by
    have hmem : tensorImagPart g z.val ∈ pureRealIdeal I := him
    rw [hI, LieSubmodule.mem_bot] at hmem
    exact hmem
  apply Subtype.ext
  exact (complexification_zero_iff_parts g z.val).mpr ⟨hz, himzero⟩

private noncomputable def realProjectedIdeal (I : LieIdeal ℂ (ℂ ⊗[ℝ] g)) :
    LieIdeal ℝ g where
  __ := LinearMap.range (idealRealPart I)
  lie_mem := by
    rintro x y ⟨z, rfl⟩
    refine ⟨⟨⁅1 ⊗ₜ[ℝ] x, z.val⁆, I.lie_mem z.property⟩, ?_⟩
    exact realPart_real_bracket x z.val

private theorem realProjectedIdeal_ne_bot (I : LieIdeal ℂ (ℂ ⊗[ℝ] g))
    (hne : I ≠ ⊥) (hinj : Function.Injective (idealRealPart I)) :
    realProjectedIdeal I ≠ ⊥ := by
  intro hzero
  apply hne
  apply le_antisymm _ bot_le
  intro z hz
  have hr : idealRealPart I (⟨z, hz⟩ : I) ∈ realProjectedIdeal I :=
    ⟨⟨z, hz⟩, rfl⟩
  rw [hzero, LieSubmodule.mem_bot] at hr
  have hmap : idealRealPart I (⟨z, hz⟩ : I) = idealRealPart I 0 := by simpa using hr
  exact congrArg Subtype.val (hinj hmap)

private noncomputable def idealTimesI (I : LieIdeal ℂ (ℂ ⊗[ℝ] g)) : I →ₗ[ℝ] I where
  toFun z := Complex.I • z
  map_add' x y := smul_add Complex.I x y
  map_smul' a z := smul_comm Complex.I a z

private def idealRealAction (I : LieIdeal ℂ (ℂ ⊗[ℝ] g)) (x : g) (z : I) : I :=
  ⟨⁅1 ⊗ₜ[ℝ] x, z.val⁆, I.lie_mem z.property⟩

private theorem idealRealPart_action (I : LieIdeal ℂ (ℂ ⊗[ℝ] g)) (x : g) (z : I) :
    idealRealPart I (idealRealAction I x z) = ⁅x, idealRealPart I z⁆ :=
  realPart_real_bracket x z.val

private theorem idealTimesI_action (I : LieIdeal ℂ (ℂ ⊗[ℝ] g)) (x : g) (z : I) :
    idealTimesI I (idealRealAction I x z) = idealRealAction I x (idealTimesI I z) := by
  apply Subtype.ext
  change Complex.I • ⁅1 ⊗ₜ[ℝ] x, z.val⁆ = ⁅1 ⊗ₜ[ℝ] x, Complex.I • z.val⁆
  exact (lie_smul _ _ _).symm

/-- The actual complexification of a compact real simple Lie algebra is
simple over `ℂ`.  No rank bound, classification theorem, or finite-dimensional
decomposition theorem is used. -/
theorem compact_real_simple_is_absolutely_simple (B : CompactForm g)
    [LieAlgebra.IsSimple ℝ g] : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g) := by
  constructor
  · intro I
    by_cases hIbot : I = ⊥
    · exact Or.inl hIbot
    right
    by_contra hItop
    have hreal : pureRealIdeal I = ⊥ :=
      (LieAlgebra.IsSimple.eq_bot_or_eq_top (R := ℝ) (L := g) _).resolve_right
        (fun htop => hItop (pureRealIdeal_top_implies_top I htop))
    have hinj := idealRealPart_injective I hreal
    have hrange : realProjectedIdeal I = ⊤ :=
      (LieAlgebra.IsSimple.eq_bot_or_eq_top (R := ℝ) (L := g) _).resolve_left
        (realProjectedIdeal_ne_bot I hIbot hinj)
    have hsurj : Function.Surjective (idealRealPart I) := by
      intro x
      have hx : x ∈ realProjectedIdeal I := by rw [hrange]; trivial
      exact hx
    let E : I ≃ₗ[ℝ] g := LinearEquiv.ofBijective (idealRealPart I) ⟨hinj, hsurj⟩
    let J : g →ₗ[ℝ] g := E.toLinearMap.comp ((idealTimesI I).comp E.symm.toLinearMap)
    have hJ : ∀ x, J (J x) = -x := by
      intro x
      change E (idealTimesI I (E.symm (E (idealTimesI I (E.symm x))))) = -x
      rw [E.symm_apply_apply]
      have hi : idealTimesI I (idealTimesI I (E.symm x)) = -E.symm x := by
        change Complex.I • (Complex.I • E.symm x) = -E.symm x
        rw [← mul_smul, Complex.I_mul_I, neg_one_smul]
      rw [hi, map_neg, E.apply_symm_apply]
    have hEsymm : ∀ x y : g,
        E.symm ⁅x, y⁆ = idealRealAction I x (E.symm y) := by
      intro x y
      apply E.injective
      rw [E.apply_symm_apply]
      change ⁅x, y⁆ = idealRealPart I (idealRealAction I x (E.symm y))
      rw [idealRealPart_action]
      change ⁅x, y⁆ = ⁅x, E (E.symm y)⁆
      rw [E.apply_symm_apply]
    have hcomm : ∀ x y : g, J ⁅x, y⁆ = ⁅x, J y⁆ := by
      intro x y
      change E (idealTimesI I (E.symm ⁅x, y⁆)) = ⁅x, E (idealTimesI I (E.symm y))⁆
      rw [hEsymm, idealTimesI_action]
      exact idealRealPart_action I x (idealTimesI I (E.symm y))
    exact LieAlgebra.IsSimple.non_abelian (R := ℝ) (L := g)
      (compact_complex_centroid_abelian B J hJ hcomm)
  · intro hab
    letI : IsLieAbelian (ℂ ⊗[ℝ] g) := hab
    apply LieAlgebra.IsSimple.non_abelian (R := ℝ) (L := g)
    constructor
    intro x y
    have ht : ⁅(1 : ℂ) ⊗ₜ[ℝ] x, (1 : ℂ) ⊗ₜ[ℝ] y⁆ = 0 :=
      trivial_lie_zero (ℂ ⊗[ℝ] g) (ℂ ⊗[ℝ] g) _ _
    have hpure : (1 : ℂ) ⊗ₜ[ℝ] ⁅x, y⁆ = 0 := by
      simpa only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] using ht
    have hre := congrArg (tensorRealPart g) hpure
    simpa [tensorRealPart] using hre

/-- For the original effective proper compact pair, the ambient algebra's
complexification is simple directly from the complex-commutant hypothesis. -/
theorem compact_pair_complexification_simple [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g) := by
  letI : LieAlgebra.IsSimple ℝ g :=
    CompactSimple.compact_pair_ambient_simple B h heff hproper e
  exact compact_real_simple_is_absolutely_simple B

end CompactSimple

end

end CubicAnomaly.Classification.AbsoluteSimplicity
