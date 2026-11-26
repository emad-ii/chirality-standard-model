import CubicAnomaly.Classification.UnitaryGeometry
import CubicAnomaly.Classification.HermitianRealization
import CubicAnomaly.Classification.ComplexDefining

/-!
# Irreducibility of the special-unitary defining module

A proper invariant complex subspace gives an orthogonal projection `P`.
The operator `I • (dim(W) • P - dim(U) • id)` is an actual nonzero traceless
skew-Hermitian operator commuting with the isotropy.  The already proved
vanishing of the ambient centralizer therefore forces irreducibility.
No block-stabilizer classification or highest-weight witness is required.
-/

namespace CubicAnomaly.Classification.UnitaryDefining

set_option maxHeartbeats 800000

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.CyclicBracket
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.ComplexDefining
open scoped TensorProduct

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

private theorem defining_nontrivial_of_proper
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W)) (hproper : h ≠ ⊤) : Nontrivial W := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · letI := hW
    exfalso
    apply hproper
    apply top_unique
    intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    simpa only [hx] using h.zero_mem
  · exact hW

/-- A centerless actual special-unitary isotropy centralizer forces
irreducibility of the defining complex module. -/
theorem special_unitary_defining_irreducible_of_centralizer [Nontrivial W]
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))
    (hcentralizer : ∀ z : specialUnitaryAlgebra W,
      (∀ x : h, ⁅x.val, z⁆ = 0) → z = 0) :
    LieModule.IsIrreducible ℂ h W := by
  apply LieModule.IsIrreducible.mk
  intro U hU
  by_contra hUt
  have hU' : U.toSubmodule ≠ ⊥ := by
    intro hz
    exact hU ((LieSubmodule.toSubmodule_inj _ _).mp hz)
  have hUt' : U.toSubmodule ≠ ⊤ := by
    intro hz
    exact hUt ((LieSubmodule.toSubmodule_inj _ _).mp hz)
  let P : Module.End ℂ W := U.toSubmodule.starProjection.toLinearMap
  have hP : P.adjoint = P := U.toSubmodule.starProjection_isSymmetric.adjoint_eq
  have hPtrace : LinearMap.trace ℂ W P = (Module.finrank ℂ U : ℂ) := by
    apply LinearMap.IsProj.trace
    exact ⟨U.toSubmodule.starProjection_apply_mem,
      fun _ hu => U.toSubmodule.starProjection_eq_self_iff.mpr hu⟩
  let T : Module.End ℂ W :=
    (Module.finrank ℂ W) • P - (Module.finrank ℂ U) • LinearMap.id
  have hT : T.adjoint = T := by
    dsimp [T]
    rw [map_sub, map_nsmul, map_nsmul, hP, LinearMap.adjoint_id]
  have hTtrace : LinearMap.trace ℂ W T = 0 := by
    dsimp [T]
    rw [map_sub, map_nsmul, map_nsmul, hPtrace, LinearMap.trace_id]
    simp only [nsmul_eq_mul]
    ring
  let z : specialUnitaryAlgebra W := ⟨Complex.I • T, by
    constructor
    · rw [map_smulₛₗ, hT]
      simp
    · rw [map_smul, hTtrace, smul_zero]⟩
  have hPcomm (x : h) (w : W) : P ⁅x, w⁆ = ⁅x, P w⁆ := by
    exact invariant_starProjection_commutes (fun x : h => x.val.val)
      (fun _ _ => rfl) (fun x => special_unitary_skew_action x.val) U x w
  have hzc : ∀ x : h, ⁅x.val, z⁆ = 0 := by
    intro x
    apply Subtype.ext
    ext w
    change x.val.val ((Complex.I • T) w) - (Complex.I • T) (x.val.val w) = 0
    simp only [LinearMap.smul_apply, map_smul, sub_eq_zero]
    congr 1
    change x.val.val ((Module.finrank ℂ W) • P w - (Module.finrank ℂ U) • w) =
      (Module.finrank ℂ W) • P ⁅x, w⁆ - (Module.finrank ℂ U) • ⁅x, w⁆
    rw [map_sub, map_nsmul, map_nsmul, hPcomm]
    rfl
  have hz := congrArg Subtype.val (hcentralizer z hzc)
  have hTzero : T = 0 := (smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  have hV : U.toSubmoduleᗮ ≠ ⊥ := fun hz => hUt' (Submodule.orthogonal_eq_bot_iff.mp hz)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff U.toSubmoduleᗮ).mp hV
  have hpv : P v = 0 := by
    exact congrArg Subtype.val
      (U.toSubmodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hv)
  have hdim : Module.finrank ℂ U ≠ 0 := by
    letI : Nontrivial U := (LieSubmodule.nontrivial_iff_ne_bot ℂ h W).mpr hU
    exact (Module.finrank_pos (R := ℂ) (M := U)).ne'
  have he := congrArg (fun f : Module.End ℂ W => f v) hTzero
  change (Module.finrank ℂ W) • P v - (Module.finrank ℂ U) • v = 0 at he
  rw [hpv, nsmul_zero, zero_sub, neg_eq_zero] at he
  exact hv0 ((smul_eq_zero.mp (show (Module.finrank ℂ U : ℂ) • v = 0 by
    simpa only [Nat.cast_smul_eq_nsmul] using he)).resolve_left (Nat.cast_ne_zero.mpr hdim))

/-- The original compact complex-type pair hypotheses force the actual
special-unitary defining module to be complex irreducible. -/
theorem special_unitary_defining_irreducible
    (B : CompactForm (specialUnitaryAlgebra W))
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W)) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥) :
    LieModule.IsIrreducible ℂ h W := by
  letI : Nontrivial W := defining_nontrivial_of_proper h hproper
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
  exact special_unitary_defining_irreducible_of_centralizer h
    (centralizer_vanishes_of_complex_complement h q hc (commutantComplexStructure e)
      (commutant_complex_structure_square e) hcenter)

/-- The special-unitary defining-module conclusion follows in every
dimension directly from the original nonzero full anomaly radical. -/
theorem all_rank_special_unitary_defining_irreducible
    (B : CompactForm (specialUnitaryAlgebra W))
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieModule.IsIrreducible ℂ h W := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  exact special_unitary_defining_irreducible B h hproper e (LieAlgebra.center_eq_bot ℝ h)

/-- The original defining representation, including the literal inclusions. -/
def specialUnitaryDefiningRepresentation (h : LieSubalgebra ℝ (specialUnitaryAlgebra W)) :
    h →ₗ⁅ℝ⁆ Module.End ℂ W :=
  (specialUnitaryAlgebra W).incl.comp h.incl

/-- The same defining vector space is irreducible for the actual
complexification of the isotropy, with its constructed extended action. -/
theorem all_rank_special_unitary_complexified_defining_irreducible
    (B : CompactForm (specialUnitaryAlgebra W))
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    letI := complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) W := by
  letI : LieModule.IsIrreducible ℂ h W :=
    all_rank_special_unitary_defining_irreducible B h heff hproper e hradical
  exact complexified_defining_irreducible (specialUnitaryDefiningRepresentation h)
    (fun _ _ => rfl)

end

end CubicAnomaly.Classification.UnitaryDefining
