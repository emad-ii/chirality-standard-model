import CubicAnomaly.Fixed.E8CompactGrading
import CubicAnomaly.Fixed.E8Structure

/-!
# The actual compact degree-zero pair and its real complement

The degree-zero algebra is intersected with the previously constructed
compact real form. Its complexification is the actual degree-zero algebra.
The two nonzero grades form the complexification of a real invariant
complement, identified with degree one regarded as a real vector space.
-/

namespace CubicAnomaly.Fixed.E8CompactPair

open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8Compact
open CubicAnomaly.Fixed.E8CompactGrading
open CubicAnomaly.Classification.Structural
open scoped TensorProduct

noncomputable section

instance zeroSubalgebraReal : LieAlgebra ℝ zeroSubalgebra where
  lie_smul r x y := by
    apply Subtype.ext
    exact lie_smul r x.val y.val

instance gradeModuleReal (a : ZMod 3) : LieModule ℝ zeroSubalgebra (gradeModule a) where
  smul_lie r x v := by
    apply Subtype.ext
    exact smul_lie r x.val v.val
  lie_smul r x v := by
    apply Subtype.ext
    exact lie_smul r x.val v.val

/-- Literal homogeneous projection after the actual adjoint identification. -/
def actualProjection (a : ZMod 3) : E8Geck.lieAlgebra →ₗ[ℂ] E8Geck.lieAlgebra :=
  adjointEquiv.toLinearMap.comp ((gradeProjection a).comp adjointEquiv.symm.toLinearMap)

theorem e8_actualProjection_homogeneous (a : ZMod 3) (x : E8Geck.lieAlgebra) :
    actualProjection a x ∈ actualGrade a :=
  ⟨gradeProjection a (adjointEquiv.symm x), e8_gradeProjection_homogeneous _ _, rfl⟩

theorem e8_actualProjection_of_homogeneous (a b : ZMod 3) (x : E8Geck.lieAlgebra)
    (hx : x ∈ actualGrade b) : actualProjection a x = if a = b then x else 0 := by
  classical
  obtain ⟨v, hv, rfl⟩ := hx
  change adjointEquiv (gradeProjection a (adjointEquiv.symm (adjointEquiv v))) = _
  rw [adjointEquiv.symm_apply_apply, grade_projection_of_homogeneous a b v hv]
  split_ifs <;> simp

theorem e8_actualGrade_disjoint (a b : ZMod 3) (hab : a ≠ b) :
    Disjoint (actualGrade a) (actualGrade b) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  have h₁ := e8_actualProjection_of_homogeneous a a x hx
  have h₂ := e8_actualProjection_of_homogeneous a b x hy
  simpa only [if_pos rfl, if_neg hab] using h₁.symm.trans h₂

private theorem conjugation_zero (x : E8Geck.lieAlgebra) (hx : x ∈ actualGrade 0) :
    compactConjugation x ∈ actualGrade 0 := by
  simpa only [neg_zero] using e8_compact_conjugation_graded 0 x hx

private theorem conjugation_one (x : E8Geck.lieAlgebra) (hx : x ∈ actualGrade 1) :
    compactConjugation x ∈ actualGrade 2 := by
  simpa only [show -(1 : ZMod 3) = 2 from by decide] using
    e8_compact_conjugation_graded 1 x hx

private theorem conjugation_two (x : E8Geck.lieAlgebra) (hx : x ∈ actualGrade 2) :
    compactConjugation x ∈ actualGrade 1 := by
  simpa only [show -(2 : ZMod 3) = 1 from by decide] using
    e8_compact_conjugation_graded 2 x hx

/-- The actual compact degree-zero Lie subalgebra of the existing compact algebra. -/
def compactZero : LieSubalgebra ℝ compactRealAlgebra where
  carrier := {x | compactToComplex x ∈ actualGrade 0}
  zero_mem' := by simpa only [map_zero] using (actualGrade 0).zero_mem
  add_mem' := by
    intro x y hx hy
    simpa only [map_add] using (actualGrade 0).add_mem hx hy
  smul_mem' := by
    intro r x hx
    change compactToComplex (r • x) ∈ actualGrade 0
    rw [map_smul]
    exact ((actualGrade 0).restrictScalars ℝ).smul_mem r hx
  lie_mem' := by
    intro x y hx hy
    change compactToComplex ⁅x, y⁆ ∈ actualGrade 0
    rw [LieHom.map_lie]
    simpa only [add_zero] using e8_actual_bracket_graded 0 0 _ _ hx hy

theorem e8_mem_compactZero (x : compactRealAlgebra) :
    x ∈ compactZero ↔ compactToComplex x ∈ actualGrade 0 := Iff.rfl

/-- The literal real Lie inclusion into the actual complex degree-zero algebra. -/
def compactZeroToComplex : compactZero →ₗ⁅ℝ⁆ zeroSubalgebra where
  toFun x := ⟨compactToComplex x.val, x.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add compactToComplex x.val y.val
  map_smul' r x := by apply Subtype.ext; exact map_smul compactToComplex r x.val
  map_lie' := by intro x y; apply Subtype.ext; exact compactToComplex.map_lie x.val y.val

theorem e8_compactZeroToComplex_val (x : compactZero) :
    (compactZeroToComplex x).val = compactToComplex x.val := rfl

theorem e8_compactZeroToComplex_injective : Function.Injective compactZeroToComplex := by
  intro x y h
  apply Subtype.ext
  exact e8_compactToComplex_injective (congrArg Subtype.val h)

/-- Compactness is inherited from the actual positive invariant form. -/
def compactZeroForm : CompactForm compactZero := compactForm.restrict compactZero

/-- Explicit real and imaginary compact parts inside any conjugation-stable complex subspace. -/
theorem e8_compact_parts_in (S : Submodule ℂ E8Geck.lieAlgebra)
    (hS : ∀ x ∈ S, compactConjugation x ∈ S) (x : E8Geck.lieAlgebra) (hx : x ∈ S) :
    ∃ a b : compactRealAlgebra,
      compactToComplex a ∈ S ∧ compactToComplex b ∈ S ∧
      x = compactToComplex a + Complex.I • compactToComplex b := by
  let y := (2 : ℂ)⁻¹ • (x + compactConjugation x)
  let z := (-Complex.I * (2 : ℂ)⁻¹) • (x - compactConjugation x)
  have hy : compactConjugation y = y := by
    dsimp [y]
    rw [e8_compact_conjugation_smul, map_add, e8_compact_conjugation_involutive]
    simp only [star_inv₀, star_ofNat]
    module
  have hz : compactConjugation z = z := by
    dsimp [z]
    rw [e8_compact_conjugation_smul, map_sub, e8_compact_conjugation_involutive]
    simp only [star_mul, star_neg, Complex.star_def, Complex.conj_I, neg_neg,
      map_inv₀, map_ofNat]
    module
  refine ⟨compactOfFixed y hy, compactOfFixed z hz, ?_, ?_, ?_⟩
  · rw [e8_compactToComplex_ofFixed]
    exact S.smul_mem _ (S.add_mem hx (hS x hx))
  · rw [e8_compactToComplex_ofFixed]
    exact S.smul_mem _ (S.sub_mem hx (hS x hx))
  · rw [e8_compactToComplex_ofFixed, e8_compactToComplex_ofFixed]
    dsimp [y, z]
    rw [smul_smul]
    have hi : Complex.I * (-Complex.I * (2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
      rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
    rw [hi]
    module

/-- The compact degree-zero algebra spans the entire actual complex degree-zero algebra. -/
theorem e8_zero_skew_parts (x : zeroSubalgebra) :
    ∃ a b : compactZero,
      x = compactZeroToComplex a + Complex.I • compactZeroToComplex b := by
  obtain ⟨a, b, ha, hb, h⟩ := e8_compact_parts_in (actualGrade 0) conjugation_zero x.val x.property
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
  exact Subtype.ext h

/-- Complexify a literal real subspace inclusion into the existing compact algebra. -/
def subspaceComplexificationMap (N : Submodule ℝ compactRealAlgebra) :
    (ℂ ⊗[ℝ] N) →ₗ[ℂ] E8Geck.lieAlgebra :=
  complexificationEquiv.toLinearEquiv.toLinearMap.comp (N.subtype.baseChange ℂ)

theorem e8_subspaceComplexification_tmul (N : Submodule ℝ compactRealAlgebra)
    (c : ℂ) (x : N) :
    subspaceComplexificationMap N (c ⊗ₜ[ℝ] x) = c • compactToComplex x.val := by
  apply Subtype.ext
  change (complexificationEquiv (c ⊗ₜ[ℝ] x.val)).val =
    c • (compactToComplex x.val).val
  rw [e8_compact_complexification_tmul]
  exact map_smul operatorEquiv.symm c x.val.val

theorem e8_subspaceComplexification_injective (N : Submodule ℝ compactRealAlgebra) :
    Function.Injective (subspaceComplexificationMap N) :=
  complexificationEquiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap N.subtype Subtype.val_injective)

private theorem zero_complexification_mem (z : ℂ ⊗[ℝ] compactZero) :
    subspaceComplexificationMap compactZero.toSubmodule z ∈ zeroSubalgebra := by
  induction z using TensorProduct.induction_on with
  | zero => simpa using zeroSubalgebra.zero_mem
  | tmul c x =>
    rw [e8_subspaceComplexification_tmul]
    exact zeroSubalgebra.smul_mem c x.property
  | add x y hx hy => simpa only [map_add] using zeroSubalgebra.add_mem hx hy

set_option maxHeartbeats 1600000 in
/-- The actual inclusion extends to the complexification of the compact zero algebra. -/
def zeroComplexificationHom : (ℂ ⊗[ℝ] compactZero) →ₗ⁅ℂ⁆ zeroSubalgebra := {
  (subspaceComplexificationMap compactZero.toSubmodule).codRestrict
    zeroSubalgebra.toSubmodule zero_complexification_mem with
  map_lie' := by
    intro x y
    apply Subtype.ext
    change complexificationEquiv ((compactZero.incl.toLinearMap.baseChange ℂ) ⁅x, y⁆) =
      ⁅complexificationEquiv ((compactZero.incl.toLinearMap.baseChange ℂ) x),
        complexificationEquiv ((compactZero.incl.toLinearMap.baseChange ℂ) y)⁆
    exact (congrArg complexificationEquiv
      ((LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) compactZero.incl).map_lie x y)).trans
        (complexificationEquiv.map_lie _ _) }

theorem e8_zeroComplexificationHom_tmul (c : ℂ) (x : compactZero) :
    zeroComplexificationHom (c ⊗ₜ[ℝ] x) = c • compactZeroToComplex x := by
  apply Subtype.ext
  exact e8_subspaceComplexification_tmul compactZero.toSubmodule c x

set_option maxHeartbeats 1600000 in
/-- The actual complex zero algebra is the complexification of its compact real intersection. -/
def zeroComplexificationEquiv : (ℂ ⊗[ℝ] compactZero) ≃ₗ⁅ℂ⁆ zeroSubalgebra :=
  LieEquiv.ofBijective zeroComplexificationHom ⟨by
    intro x y h
    exact e8_subspaceComplexification_injective compactZero.toSubmodule
      (congrArg (fun z : zeroSubalgebra => z.val) h), by
    intro x
    obtain ⟨a, b, hab⟩ := e8_zero_skew_parts x
    refine ⟨1 ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b, ?_⟩
    calc
      zeroComplexificationHom (1 ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b) =
          zeroComplexificationHom (1 ⊗ₜ[ℝ] a) +
            zeroComplexificationHom (Complex.I ⊗ₜ[ℝ] b) := map_add _ _ _
      _ = (1 : ℂ) • compactZeroToComplex a + Complex.I • compactZeroToComplex b :=
        congrArg₂ (· + ·) (e8_zeroComplexificationHom_tmul 1 a)
          (e8_zeroComplexificationHom_tmul Complex.I b)
      _ = x := by simpa only [one_smul] using hab.symm⟩

theorem e8_zeroComplexificationEquiv_tmul (c : ℂ) (x : compactZero) :
    zeroComplexificationEquiv (c ⊗ₜ[ℝ] x) = c • compactZeroToComplex x :=
  e8_zeroComplexificationHom_tmul c x

theorem e8_compactZero_finrank : Module.finrank ℝ compactZero = 86 := by
  have h := zeroComplexificationEquiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange, e8_zeroSubalgebra_finrank] at h
  exact h

/-- The complex sum of the two nonzero homogeneous pieces. -/
def complementarySpace : Submodule ℂ E8Geck.lieAlgebra := actualGrade 1 ⊔ actualGrade 2

private theorem complementarySpace_invariant (x : zeroSubalgebra)
    (y : E8Geck.lieAlgebra) (hy : y ∈ complementarySpace) :
    ⁅x.val, y⁆ ∈ complementarySpace := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
  rw [lie_add]
  apply (complementarySpace).add_mem
  · exact (show actualGrade 1 ≤ complementarySpace from le_sup_left)
      (e8_grade_module_invariant 1 x u hu)
  · exact (show actualGrade 2 ≤ complementarySpace from le_sup_right)
      (e8_grade_module_invariant 2 x v hv)

theorem e8_complementarySpace_conjugation (x : E8Geck.lieAlgebra)
    (hx : x ∈ complementarySpace) : compactConjugation x ∈ complementarySpace := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact complementarySpace.add_mem
    ((show actualGrade 2 ≤ complementarySpace from le_sup_right) (conjugation_one u hu))
    ((show actualGrade 1 ≤ complementarySpace from le_sup_left) (conjugation_two v hv))

/-- The literal real invariant complement inside the existing compact algebra. -/
def compactComplement : LieSubmodule ℝ compactZero compactRealAlgebra where
  toSubmodule := (complementarySpace.restrictScalars ℝ).comap compactToComplex.toLinearMap
  lie_mem := by
    intro x y hy
    change compactToComplex ⁅x.val, y⁆ ∈ complementarySpace
    rw [LieHom.map_lie]
    exact complementarySpace_invariant (compactZeroToComplex x) (compactToComplex y) hy

theorem e8_mem_compactComplement (x : compactRealAlgebra) :
    x ∈ compactComplement ↔ compactToComplex x ∈ complementarySpace := Iff.rfl

private theorem realification_fixed (v : gradeModule 1) :
    compactConjugation (v.val + compactConjugation v.val) =
      v.val + compactConjugation v.val := by
  rw [map_add, e8_compact_conjugation_involutive, add_comm]

private def realificationOperatorMap : gradeModule 1 →ₗ[ℝ]
    Module.End ℂ E8Compact.DefiningSpace :=
  ((operatorEquiv.toLinearMap.comp E8Geck.lieAlgebra.incl.toLinearMap).restrictScalars ℝ).comp
    ((LinearMap.id + compactConjugation.toLinearEquiv.toLinearMap).comp
      ((gradeModule 1).toSubmodule.subtype.restrictScalars ℝ))

private def realificationAmbientMap : gradeModule 1 →ₗ[ℝ] compactRealAlgebra :=
  realificationOperatorMap.codRestrict compactRealAlgebra.toSubmodule (fun v =>
    (compactOfFixed (v.val + compactConjugation v.val) (realification_fixed v)).property)

set_option maxHeartbeats 1600000 in
/-- A degree-one vector and its compact conjugate give a literal real complement vector. -/
def realificationMap : gradeModule 1 →ₗ[ℝ] compactComplement :=
  realificationAmbientMap.codRestrict compactComplement.toSubmodule (fun v => by
    change compactToComplex
      (compactOfFixed (v.val + compactConjugation v.val) (realification_fixed v)) ∈ complementarySpace
    rw [e8_compactToComplex_ofFixed]
    exact complementarySpace.add_mem
      ((show actualGrade 1 ≤ complementarySpace from le_sup_left) v.property)
      ((show actualGrade 2 ≤ complementarySpace from le_sup_right)
        (conjugation_one v.val v.property)))

theorem e8_realificationMap_inclusion (v : gradeModule 1) :
    compactToComplex (realificationMap v).val = v.val + compactConjugation v.val :=
  e8_compactToComplex_ofFixed _ (realification_fixed v)

private theorem projection_realification (v : gradeModule 1) :
    actualProjection 1 (compactToComplex (realificationMap v).val) = v.val := by
  rw [e8_realificationMap_inclusion, map_add,
    e8_actualProjection_of_homogeneous 1 1 _ v.property,
    e8_actualProjection_of_homogeneous 1 2 _ (conjugation_one v.val v.property)]
  simp only [if_true, if_neg (show (1 : ZMod 3) ≠ 2 from by decide), add_zero]

theorem e8_realificationMap_injective : Function.Injective realificationMap := by
  intro v w h
  apply Subtype.ext
  have hh := congrArg (fun z : compactComplement =>
    actualProjection 1 (compactToComplex z.val)) h
  simpa only [projection_realification] using hh

set_option maxHeartbeats 1600000 in
theorem e8_realificationMap_surjective : Function.Surjective realificationMap := by
  intro w
  obtain ⟨u, hu, v, hv, he⟩ :=
    (Submodule.mem_sup (p := actualGrade 1) (p' := actualGrade 2)
      (x := compactToComplex w.val)).mp ((e8_mem_compactComplement w.val).mp w.property)
  have hσ : compactConjugation u + compactConjugation v = u + v := by
    rw [← map_add, he, e8_compactToComplex_fixed]
  have hp := congrArg (actualProjection 2) hσ
  simp only [map_add,
    e8_actualProjection_of_homogeneous 2 2 _ (conjugation_one u hu),
    e8_actualProjection_of_homogeneous 2 1 _ (conjugation_two v hv),
    e8_actualProjection_of_homogeneous 2 1 _ hu,
    e8_actualProjection_of_homogeneous 2 2 _ hv] at hp
  have hvu : compactConjugation u = v := by
    simpa only [if_true, if_pos rfl, if_neg (show (2 : ZMod 3) ≠ 1 from by decide),
      add_zero, zero_add] using hp
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  apply e8_compactToComplex_injective
  rw [e8_realificationMap_inclusion]
  change u + compactConjugation u = compactToComplex w.val
  rw [hvu]
  exact he

/-- The real complement is degree one with scalars restricted to the reals. -/
def realificationEquiv : gradeModule 1 ≃ₗ[ℝ] compactComplement :=
  LinearEquiv.ofBijective realificationMap
    ⟨e8_realificationMap_injective, e8_realificationMap_surjective⟩

set_option maxHeartbeats 1600000 in
/-- The identification preserves the literal action of the compact zero algebra. -/
theorem e8_realification_equivariant (x : compactZero) (v : gradeModule 1) :
    realificationEquiv ⁅compactZeroToComplex x, v⁆ = ⁅x, realificationEquiv v⁆ := by
  apply Subtype.ext
  apply e8_compactToComplex_injective
  change compactToComplex (realificationMap ⁅compactZeroToComplex x, v⁆).val =
    compactToComplex ⁅x.val, (realificationMap v).val⁆
  have hl := e8_realificationMap_inclusion ⁅compactZeroToComplex x, v⁆
  have hr := e8_realificationMap_inclusion v
  rw [hl, compactToComplex.map_lie, hr]
  change ⁅compactToComplex x.val, v.val⁆ + compactConjugation ⁅compactToComplex x.val, v.val⁆ = _
  rw [LieEquiv.map_lie, e8_compactToComplex_fixed, lie_add]

theorem e8_compactComplement_finrank : Module.finrank ℝ compactComplement = 162 := by
  rw [← realificationEquiv.finrank_eq, ← Module.finrank_mul_finrank ℝ ℂ (gradeModule 1),
    Complex.finrank_real_complex, e8_complementary_module_dimensions.1]

end

end CubicAnomaly.Fixed.E8CompactPair
