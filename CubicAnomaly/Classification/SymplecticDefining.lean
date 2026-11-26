import CubicAnomaly.Classification.SymplecticGeometry
import CubicAnomaly.Classification.UnitaryGeometry
import CubicAnomaly.Classification.ComplexDefining
import CubicAnomaly.Classification.HermitianRealization

/-!
# Irreducibility of the compact symplectic defining module

An invariant complex orthogonal projection must commute with the actual
quaternionic structure: otherwise its difference from its quaternionic
conjugate gives a nonzero element of the isotropy centralizer. A proper
quaternionic invariant splitting then gives a nonidentity reflection
involution fixing the isotropy, contradicting the all-rank obstruction.
-/

namespace CubicAnomaly.Classification.SymplecticDefining

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.CyclicBracket
open CubicAnomaly.Classification.InvolutionObstruction
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.SymplecticGeometry
open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.ComplexDefining
open scoped ComplexConjugate TensorProduct

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
/-- Every self-adjoint operator commuting with an isotropy algebra whose
ambient symplectic centralizer is zero preserves the quaternionic structure. -/
theorem self_adjoint_commutant_preserves_quaternionic
    (J : QuaternionicStructure W) (h : LieSubalgebra ℝ (symplecticAlgebra J))
    (hcentralizer : ∀ z : symplecticAlgebra J,
      (∀ x : h, ⁅x.val, z⁆ = 0) → z = 0)
    (S : Module.End ℂ W)
    (hS : ∀ u v, inner ℂ (S u) v = inner ℂ u (S v))
    (hcomm : ∀ (x : h) w, S ⁅x, w⁆ = ⁅x, S w⁆) :
    ∀ w, S (J w) = J (S w) := by
  let C := J.conjugateEnd S
  have hC (u v : W) : inner ℂ (C u) v = inner ℂ u (C v) := by
    rw [J.inner_conjugateEnd_left, J.inner_conjugateEnd_right, hS]
  let T := S - C
  let z : symplecticAlgebra J := ⟨Complex.I • T, by
    constructor
    · intro u v
      change inner ℂ (Complex.I • (S u - C u)) v =
        -inner ℂ u (Complex.I • (S v - C v))
      rw [inner_smul_left, inner_smul_right, Complex.conj_I,
        inner_sub_left, inner_sub_right, hS, hC]
      ring
    · intro w
      change Complex.I • (S (J w) - J.conjugateEnd S (J w)) =
        J (Complex.I • (S w - J.conjugateEnd S w))
      rw [J.apply_smul, Complex.conj_I, J.apply_sub,
        J.conjugateEnd_apply_image, J.image_conjugateEnd_apply]
      simp only [smul_sub, neg_smul]
      abel⟩
  have hcomm' (x : h) (w : W) : S (x.val.val w) = x.val.val (S w) := hcomm x w
  have hCcomm (x : h) (w : W) : C (x.val.val w) = x.val.val (C w) := by
    change -J (S (J (x.val.val w))) = x.val.val (-J (S (J w)))
    rw [← symplectic_commutes J x.val, hcomm', ← symplectic_commutes J x.val, map_neg]
  have hzc : ∀ x : h, ⁅x.val, z⁆ = 0 := by
    intro x
    apply Subtype.ext
    ext w
    change x.val.val (Complex.I • (S w - C w)) -
      Complex.I • (S (x.val.val w) - C (x.val.val w)) = 0
    rw [map_smul, map_sub, hcomm', hCcomm, sub_self]
  have hz := congrArg Subtype.val (hcentralizer z hzc)
  have hTzero : T = 0 := (smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  have hSC : S = J.conjugateEnd S := sub_eq_zero.mp hTzero
  intro w
  calc S (J w) = J.conjugateEnd S (J w) := congrArg (fun A : Module.End ℂ W => A (J w)) hSC
       _ = J (S w) := J.conjugateEnd_apply_image S w

private theorem projection_commutes_quaternionic
    (J : QuaternionicStructure W) (h : LieSubalgebra ℝ (symplecticAlgebra J))
    (hcentralizer : ∀ z : symplecticAlgebra J,
      (∀ x : h, ⁅x.val, z⁆ = 0) → z = 0)
    (U : LieSubmodule ℂ h W) :
    ∀ w, U.toSubmodule.starProjection (J w) = J (U.toSubmodule.starProjection w) := by
  apply self_adjoint_commutant_preserves_quaternionic J h hcentralizer
    U.toSubmodule.starProjection.toLinearMap
  · exact U.toSubmodule.inner_starProjection_left_eq_right
  · intro x w
    exact invariant_starProjection_commutes (fun x : h => x.val.val)
      (fun _ _ => rfl) (fun x => symplectic_skew_action J x.val) U x w

private theorem reflection_commutes_quaternionic
    (J : QuaternionicStructure W) (U : Submodule ℂ W)
    (hP : ∀ w, U.starProjection (J w) = J (U.starProjection w)) :
    ∀ w, U.reflection (J w) = J (U.reflection w) := by
  intro w
  simp only [Submodule.reflection_apply, two_smul, J.apply_sub, J.apply_add, hP]

private theorem symplectic_reflection_involutive
    (J : QuaternionicStructure W) (U : Submodule ℂ W)
    (hr : ∀ w, U.reflection (J w) = J (U.reflection w)) :
    Function.Involutive (symplecticConjugation J U.reflection hr) := by
  intro A
  apply Subtype.ext
  ext w
  simp only [symplecticConjugation_apply, Submodule.reflection_symm,
    Submodule.reflection_reflection]

private theorem symplectic_reflection_fixes_isotropy
    (J : QuaternionicStructure W) (h : LieSubalgebra ℝ (symplecticAlgebra J))
    (U : LieSubmodule ℂ h W)
    (hr : ∀ w, U.toSubmodule.reflection (J w) = J (U.toSubmodule.reflection w)) :
    ∀ x : h, symplecticConjugation J U.toSubmodule.reflection hr x.val = x.val := by
  intro x
  have hP (w : W) := invariant_starProjection_commutes (fun x : h => x.val.val)
    (fun _ _ => rfl) (fun x => symplectic_skew_action J x.val) U x w
  have hR (w : W) : U.toSubmodule.reflection (x.val.val w) =
      x.val.val (U.toSubmodule.reflection w) := by
    simp only [Submodule.reflection_apply, two_smul, map_add, map_sub, hP]
  apply Subtype.ext
  ext w
  change U.toSubmodule.reflection (x.val.val (U.toSubmodule.reflection w)) = x.val.val w
  rw [hR, Submodule.reflection_reflection]

private theorem symplectic_reflection_ne_refl
    (J : QuaternionicStructure W) (U : Submodule ℂ W)
    (hP : ∀ w, U.starProjection (J w) = J (U.starProjection w))
    (hU : U ≠ ⊥) (hUt : U ≠ ⊤) :
    symplecticConjugation J U.reflection (reflection_commutes_quaternionic J U hP) ≠
      LieEquiv.refl := by
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).mp hU
  have hV : Uᗮ ≠ ⊥ := fun hz => hUt (Submodule.orthogonal_eq_bot_iff.mp hz)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff Uᗮ).mp hV
  have hJu : J u ∈ U := by
    apply U.starProjection_eq_self_iff.mp
    rw [hP, U.starProjection_eq_self_iff.mpr hu]
  have huv : inner ℂ u v = 0 := U.inner_right_of_mem_orthogonal hu hv
  have huJv : inner ℂ u (J v) = 0 := by
    rw [J.inner_right, U.inner_right_of_mem_orthogonal hJu hv, map_zero, neg_zero]
  have hru := U.reflection_mem_subspace_eq_self hu
  have hrv := U.reflection_mem_subspace_orthogonalComplement_eq_neg hv
  intro heq
  have he := congrArg (fun s : symplecticAlgebra J ≃ₗ⁅ℝ⁆ symplecticAlgebra J =>
    (s (symplecticCrossSkew J u v)).val v) heq
  change U.reflection ((symplecticCrossSkew J u v).val (U.reflection v)) =
    (symplecticCrossSkew J u v).val v at he
  rw [hrv, map_neg, map_neg, symplecticCrossSkew_apply_right J u v huv huJv,
    map_smul, hru] at he
  have hz : ((2 : ℂ) * inner ℂ v v) • u = 0 := by
    rw [mul_smul, two_smul]
    exact neg_eq_iff_add_eq_zero.mp he
  have hvv : inner ℂ v v ≠ 0 := fun hz => hv0 (inner_self_eq_zero.mp hz)
  exact hu0 ((smul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hvv))

omit [FiniteDimensional ℂ W] in
private theorem defining_nontrivial_of_proper
    (J : QuaternionicStructure W) (h : LieSubalgebra ℝ (symplecticAlgebra J))
    (hproper : h ≠ ⊤) : Nontrivial W := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · letI := hW
    exfalso
    apply hproper
    apply top_unique
    intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    simpa only [hx] using h.zero_mem
  · exact hW

/-- The actual compact symplectic defining complex module is irreducible
under the original centreless compact complex-type pair hypotheses. -/
theorem symplectic_defining_irreducible
    (J : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra J))
    (h : LieSubalgebra ℝ (symplecticAlgebra J))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥) : LieModule.IsIrreducible ℂ h W := by
  letI : Nontrivial W := defining_nontrivial_of_proper J h hproper
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
  have hcentralizer := centralizer_vanishes_of_complex_complement h q hc
    (commutantComplexStructure e) (commutant_complex_structure_square e) hcenter
  apply LieModule.IsIrreducible.mk
  intro U hU
  by_contra hUt
  have hU' : U.toSubmodule ≠ ⊥ := by
    intro hz
    exact hU ((LieSubmodule.toSubmodule_inj _ _).mp hz)
  have hUt' : U.toSubmodule ≠ ⊤ := by
    intro hz
    exact hUt ((LieSubmodule.toSubmodule_inj _ _).mp hz)
  have hP := projection_commutes_quaternionic J h hcentralizer U
  have hr := reflection_commutes_quaternionic J U.toSubmodule hP
  exact symplectic_reflection_ne_refl J U.toSubmodule hP hU' hUt'
    (compact_complex_type_involution_eq_refl B h heff hproper e hcenter
      (symplecticConjugation J U.toSubmodule.reflection hr)
      (symplectic_reflection_involutive J U.toSubmodule hr)
      (symplectic_reflection_fixes_isotropy J h U hr))

/-- The compact symplectic defining-module conclusion follows in every
dimension directly from the original nonzero full anomaly radical. -/
theorem all_rank_symplectic_defining_irreducible
    (J : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra J))
    (h : LieSubalgebra ℝ (symplecticAlgebra J))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieModule.IsIrreducible ℂ h W := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  exact symplectic_defining_irreducible J B h heff hproper e (LieAlgebra.center_eq_bot ℝ h)

/-- The original symplectic defining representation, with the literal inclusions. -/
def symplecticDefiningRepresentation (J : QuaternionicStructure W)
    (h : LieSubalgebra ℝ (symplecticAlgebra J)) : h →ₗ⁅ℝ⁆ Module.End ℂ W :=
  (symplecticAlgebra J).incl.comp h.incl

/-- The same defining complex space is irreducible under the actual
complexification of the isotropy, with its constructed extended action. -/
theorem all_rank_symplectic_complexified_defining_irreducible
    (J : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra J))
    (h : LieSubalgebra ℝ (symplecticAlgebra J))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    letI := complexifiedDefiningAction (symplecticDefiningRepresentation J h)
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) W := by
  letI : LieModule.IsIrreducible ℂ h W :=
    all_rank_symplectic_defining_irreducible J B h heff hproper e hradical
  exact complexified_defining_irreducible (symplecticDefiningRepresentation J h)
    (fun _ _ => rfl)

end

end CubicAnomaly.Classification.SymplecticDefining
