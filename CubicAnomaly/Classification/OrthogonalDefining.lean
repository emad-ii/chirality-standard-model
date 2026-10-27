import CubicAnomaly.Classification.InvolutionObstruction
import CubicAnomaly.Classification.AbsoluteIrreducibility
import CubicAnomaly.Classification.SelfDualAbsorption
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Irreducibility of an orthogonal defining module

An invariant proper orthogonal decomposition of a defining module gives a
reflection.  Conjugation by this reflection is a nonidentity involution of
the actual skew-adjoint Lie algebra and fixes the isotropy pointwise.  The
uniform involution obstruction therefore proves irreducibility of the
defining module, in every dimension, directly from the original pair
hypotheses.  No classification of block stabilizers is an input.
-/

namespace CubicAnomaly.Classification.OrthogonalDefining

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.InvolutionObstruction
open CubicAnomaly.Classification.CyclicBracket
open CubicAnomaly.Classification.AbsoluteIrreducibility
open CubicAnomaly.Classification.ComplexDuality
open CubicAnomaly.Classification.SelfDualAbsorption
open Submodule
open scoped TensorProduct

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The actual real orthogonal Lie algebra in its defining representation. -/
abbrev orthogonalAlgebra (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] :=
  skewAdjointLieSubalgebra (innerₗ W)

private theorem defining_nontrivial_of_proper
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) (hproper : h ≠ ⊤) : Nontrivial W := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · letI := hW
    exfalso
    apply hproper
    apply top_unique
    intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    simpa only [hx] using h.zero_mem
  · exact hW

private theorem skew_action (A : orthogonalAlgebra W) (u v : W) :
    inner ℝ (A.val u) v = -inner ℝ u (A.val v) := by
  have hA := (LinearMap.mem_skewAdjointSubmodule (B := innerₗ W) A.val).mp A.property
  simpa only [innerₗ_apply_apply, Pi.neg_apply, inner_neg_right] using hA u v

private theorem isometry_lieConj_mem (r : W ≃ₗᵢ[ℝ] W)
    (A : Module.End ℝ W) (hA : A ∈ orthogonalAlgebra W) :
    r.toLinearEquiv.lieConj A ∈ orthogonalAlgebra W := by
  apply (LinearMap.mem_skewAdjointSubmodule (B := innerₗ W) _).mpr
  intro u v
  obtain ⟨u, rfl⟩ := r.surjective u
  obtain ⟨v, rfl⟩ := r.surjective v
  change inner ℝ (r (A (r.symm (r u)))) (r v) =
    inner ℝ (r u) (-r (A (r.symm (r v))))
  rw [r.symm_apply_apply, r.symm_apply_apply]
  rw [inner_neg_right, r.inner_map_map, r.inner_map_map]
  exact skew_action ⟨A, hA⟩ u v

/-- An orthogonal change of defining coordinates acts on the actual
skew-adjoint Lie algebra by conjugation. -/
def orthogonalConjugation (r : W ≃ₗᵢ[ℝ] W) :
    orthogonalAlgebra W ≃ₗ⁅ℝ⁆ orthogonalAlgebra W :=
  r.toLinearEquiv.lieConj.ofSubalgebras _ _ (by
    ext A
    constructor
    · rintro ⟨C, hC, rfl⟩
      exact isometry_lieConj_mem r C hC
    · intro hA
      refine ⟨r.symm.toLinearEquiv.lieConj A, isometry_lieConj_mem r.symm A hA, ?_⟩
      exact r.toLinearEquiv.lieConj.apply_symm_apply A)

private theorem orthogonalConjugation_apply (r : W ≃ₗᵢ[ℝ] W)
    (A : orthogonalAlgebra W) (w : W) :
    (orthogonalConjugation r A).val w = r (A.val (r.symm w)) := rfl

private theorem orthogonalConjugation_reflection_involutive
    (U : Submodule ℝ W) [U.HasOrthogonalProjection] :
    Function.Involutive (orthogonalConjugation U.reflection) := by
  intro A
  apply Subtype.ext
  ext w
  simp only [orthogonalConjugation_apply, Submodule.reflection_symm,
    Submodule.reflection_reflection]

private def crossSkew (u v : W) : orthogonalAlgebra W :=
  ⟨(innerₗ W v).smulRight u - (innerₗ W u).smulRight v, by
    apply (LinearMap.mem_skewAdjointSubmodule (B := innerₗ W) _).mpr
    intro x y
    change inner ℝ ((inner ℝ v x) • u - (inner ℝ u x) • v) y =
      inner ℝ x (-((inner ℝ v y) • u - (inner ℝ u y) • v))
    simp only [inner_sub_left, inner_smul_left, inner_neg_right,
      inner_sub_right, inner_smul_right, conj_trivial]
    rw [real_inner_comm x u, real_inner_comm x v]
    ring⟩

private theorem orthogonal_reflection_conjugation_ne_refl
    [FiniteDimensional ℝ W] (U : Submodule ℝ W) (hU : U ≠ ⊥) (hUt : U ≠ ⊤) :
    orthogonalConjugation U.reflection ≠ LieEquiv.refl := by
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).mp hU
  have hV : Uᗮ ≠ ⊥ := fun hz => hUt (Submodule.orthogonal_eq_bot_iff.mp hz)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff Uᗮ).mp hV
  have huv : inner ℝ u v = 0 := U.inner_right_of_mem_orthogonal hu hv
  have hru := U.reflection_mem_subspace_eq_self hu
  have hrv := U.reflection_mem_subspace_orthogonalComplement_eq_neg hv
  intro heq
  have he := congrArg (fun s : orthogonalAlgebra W ≃ₗ⁅ℝ⁆ orthogonalAlgebra W =>
    (s (crossSkew u v)).val v) heq
  change U.reflection ((crossSkew u v).val (U.reflection v)) = (crossSkew u v).val v at he
  rw [hrv, map_neg] at he
  have hAv : (crossSkew u v).val v = (inner ℝ v v) • u := by
    change (inner ℝ v v) • u - (inner ℝ u v) • v = _
    rw [huv, zero_smul, sub_zero]
  rw [hAv, map_neg, map_smul, hru] at he
  have hz : (2 * inner ℝ v v) • u = 0 := by
    rw [mul_smul, two_smul]
    exact neg_eq_iff_add_eq_zero.mp he
  have hvv : inner ℝ v v ≠ 0 := fun hz => hv0 (inner_self_eq_zero.mp hz)
  exact hu0 ((smul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hvv))

private theorem invariant_orthogonal_mem
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) (U : LieSubmodule ℝ h W)
    (x : h) {v : W} (hv : v ∈ U.toSubmoduleᗮ) : ⁅x, v⁆ ∈ U.toSubmoduleᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  have hz := hv ⁅x, u⁆ (U.lie_mem hu)
  have hsk := skew_action x.val u v
  change inner ℝ ⁅x, u⁆ v = -inner ℝ u ⁅x, v⁆ at hsk
  rw [hz] at hsk
  exact neg_eq_zero.mp hsk.symm

private theorem reflection_conjugation_fixes_isotropy
    [FiniteDimensional ℝ W]
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) (U : LieSubmodule ℝ h W) :
    ∀ x : h, orthogonalConjugation U.toSubmodule.reflection x.val = x.val := by
  intro x
  apply Subtype.ext
  ext w
  obtain ⟨u, hu, v, hv, rfl⟩ := U.toSubmodule.exists_add_mem_mem_orthogonal w
  have hru := U.toSubmodule.reflection_mem_subspace_eq_self hu
  have hrv := U.toSubmodule.reflection_mem_subspace_orthogonalComplement_eq_neg hv
  have hxu := U.toSubmodule.reflection_mem_subspace_eq_self (U.lie_mem (x := x) hu)
  have hxv := U.toSubmodule.reflection_mem_subspace_orthogonalComplement_eq_neg
    (invariant_orthogonal_mem h U x hv)
  change U.toSubmodule.reflection (⁅x, U.toSubmodule.reflection (u + v)⁆) = ⁅x, u + v⁆
  rw [map_add, hru, hrv, lie_add, lie_neg, map_add, map_neg, hxu, hxv, neg_neg, lie_add]

/-- In the actual orthogonal Lie algebra, the original centreless compact
complex-type pair hypotheses force its defining real module to be
irreducible. -/
theorem orthogonal_defining_real_irreducible [FiniteDimensional ℝ W]
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥) : LieModule.IsIrreducible ℝ h W := by
  letI : Nontrivial W := defining_nontrivial_of_proper h hproper
  apply LieModule.IsIrreducible.mk
  intro U hU
  by_contra hUt
  have hU' : U.toSubmodule ≠ ⊥ := by
    intro hz
    exact hU ((LieSubmodule.toSubmodule_inj _ _).mp hz)
  have hUt' : U.toSubmodule ≠ ⊤ := by
    intro hz
    exact hUt ((LieSubmodule.toSubmodule_inj _ _).mp hz)
  exact orthogonal_reflection_conjugation_ne_refl U.toSubmodule hU' hUt'
    (compact_complex_type_involution_eq_refl B h heff hproper e hcenter
      (orthogonalConjugation U.toSubmodule.reflection)
      (orthogonalConjugation_reflection_involutive U.toSubmodule)
      (reflection_conjugation_fixes_isotropy h U))

/-- The defining-module conclusion follows directly from the original
nonzero full anomaly radical hypothesis. -/
theorem all_rank_orthogonal_defining_real_irreducible
    [FiniteDimensional ℝ W]
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieModule.IsIrreducible ℝ h W := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  exact orthogonal_defining_real_irreducible B h heff hproper e
    (LieAlgebra.center_eq_bot ℝ h)

private def adjointIntertwiner [FiniteDimensional ℝ W]
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) (J : W →ₗ⁅ℝ,h⁆ W) : W →ₗ⁅ℝ,h⁆ W where
  __ := J.toLinearMap.adjoint
  map_lie' := by
    intro x w
    apply ext_inner_right ℝ
    intro v
    change inner ℝ (J.toLinearMap.adjoint ⁅x, w⁆) v =
      inner ℝ ⁅x, J.toLinearMap.adjoint w⁆ v
    calc
      _ = inner ℝ ⁅x, w⁆ (J v) := J.toLinearMap.adjoint_inner_left v ⁅x, w⁆
      _ = -inner ℝ w ⁅x, J v⁆ := skew_action x.val w (J v)
      _ = -inner ℝ w (J ⁅x, v⁆) := by rw [J.map_lie]
      _ = -inner ℝ (J.toLinearMap.adjoint w) ⁅x, v⁆ := by
        rw [J.toLinearMap.adjoint_inner_left]
        rfl
      _ = inner ℝ ⁅x, J.toLinearMap.adjoint w⁆ v :=
        (skew_action x.val (J.toLinearMap.adjoint w) v).symm

/-- The defining module admits no equivariant complex structure.  The skew
part of any such structure would lie in the zero isotropy centralizer;
its vanishing would make a square root of `-1` self-adjoint. -/
theorem orthogonal_defining_no_complex_structure
    [FiniteDimensional ℝ W]
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    (J : W →ₗ⁅ℝ,h⁆ W) : ¬(∀ w, J (J w) = -w) := by
  letI : Nontrivial W := defining_nontrivial_of_proper h hproper
  intro hJ
  let f := J - adjointIntertwiner h J
  let z : orthogonalAlgebra W := ⟨f.toLinearMap, by
    apply (LinearMap.mem_skewAdjointSubmodule (B := innerₗ W) _).mpr
    intro u v
    change inner ℝ (J u - J.toLinearMap.adjoint u) v =
      inner ℝ u (-(J v - J.toLinearMap.adjoint v))
    simp only [inner_sub_left, inner_neg_right, inner_sub_right,
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right,
      LieModuleHom.coe_toLinearMap]
    ring⟩
  have hzc : ∀ x : h, ⁅x.val, z⁆ = 0 := by
    intro x
    apply Subtype.ext
    ext w
    change ⁅x, f w⁆ - f ⁅x, w⁆ = 0
    rw [f.map_lie, sub_self]
  let q := orthogonalComplement B h
  have hc := compact_orthogonal_complement_isCompl B h
  have hqne : q ≠ ⊥ := by
    intro hz
    have ht := hc.sup_eq_top
    have hz' : q.toSubmodule = ⊥ := congrArg LieSubmodule.toSubmodule hz
    rw [hz', sup_bot_eq] at ht
    exact hproper ((LieSubalgebra.toSubmodule_eq_top h).mp ht)
  letI : Nontrivial q := (LieSubmodule.nontrivial_iff_ne_bot ℝ h _).mpr hqne
  letI : LieModule.IsIrreducible ℝ h q := compact_complex_commutant_irreducible B h q e
  have hz := centralizer_vanishes_of_complex_complement h q hc
    (commutantComplexStructure e) (commutant_complex_structure_square e) hcenter z hzc
  have hJa : J.toLinearMap = J.toLinearMap.adjoint := by
    apply sub_eq_zero.mp
    exact congrArg Subtype.val hz
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hnorm := J.toLinearMap.adjoint_inner_right (J w) w
  rw [← hJa] at hnorm
  change inner ℝ (J w) (J w) = inner ℝ (J (J w)) w at hnorm
  rw [hJ, inner_neg_left] at hnorm
  have hp : 0 < inner ℝ w w := real_inner_self_pos.mpr hw
  have hn : 0 ≤ inner ℝ (J w) (J w) := real_inner_self_nonneg
  linarith

/-- The actual complexification of the orthogonal defining module is
irreducible.  This excludes real, complex and quaternionic splitting
possibilities without invoking a classification of division algebras. -/
theorem orthogonal_defining_complex_irreducible
    [FiniteDimensional ℝ W]
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥) :
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) := by
  letI : LieModule.IsIrreducible ℝ h W :=
    orthogonal_defining_real_irreducible B h heff hproper e hcenter
  exact complexification_irreducible_of_no_complex_structure
    (orthogonal_defining_no_complex_structure B h hproper e hcenter)

/-- The original nonzero full anomaly radical forces absolute
irreducibility of the actual orthogonal defining representation. -/
theorem all_rank_orthogonal_defining_complex_irreducible
    [FiniteDimensional ℝ W]
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  exact orthogonal_defining_complex_irreducible B h heff hproper e
    (LieAlgebra.center_eq_bot ℝ h)

/-- The complexified defining representation is genuinely self-dual via
the extended inner product, for every orthogonal isotropy subalgebra. -/
theorem orthogonal_defining_complex_self_dual [FiniteDimensional ℝ W]
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) :
    Nonempty ((ℂ ⊗[ℝ] W) ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ (ℂ ⊗[ℝ] W)) := by
  let Φ : LinearMap.BilinForm ℝ W := innerₗ W
  have hnd : Φ.Nondegenerate := by
    constructor <;> intro w hw <;> exact inner_self_eq_zero.mp (hw w)
  have hinv : Φ.lieInvariant h := by
    intro x u v
    exact skew_action x.val u v
  exact invariant_nondegenerate_form_self_dual (Φ.baseChange ℂ)
    (complexified_invariantForm_invariant _ hinv)
    (complexified_bilinForm_nondegenerate _ hnd)

/-- The orthogonal branch reaches the actual irreducible self-dual
defining module needed by the remaining highest-weight argument. -/
theorem all_rank_orthogonal_defining_irreducible_self_dual
    [FiniteDimensional ℝ W]
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) ∧
      Nonempty ((ℂ ⊗[ℝ] W) ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ (ℂ ⊗[ℝ] W)) :=
  ⟨all_rank_orthogonal_defining_complex_irreducible B h heff hproper e hradical,
    orthogonal_defining_complex_self_dual h⟩

end

end CubicAnomaly.Classification.OrthogonalDefining
