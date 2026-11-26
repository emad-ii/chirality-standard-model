import CubicAnomaly.Classification.TensorFactorActions

/-!
# Faithful ideal actions inside the actual inflated factors

The ambient factor actions generally have a kernel. Their restrictions
to the appropriate complementary ideals retain the originally proved
faithfulness. These lemmas expose the precise operator injections needed
by tensor parity separation, without asserting ambient faithfulness.
-/

namespace CubicAnomaly.Classification.TensorFactorFaithfulness

open Module LieModule
open CubicAnomaly.Classification.TensorFactorActions
open CubicAnomaly.Classification.TensorEvaluation

noncomputable section

section Inflation

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)
  [AddCommGroup M] [LieRingModule I M]

/-- The inflated ambient action restricts to the literal original ideal
action on its own ideal. -/
theorem idealInflation_self_action (x : I) (m : M) :
    letI := idealInflationLieRingModule (M := M) I J hIJ htop
    ⁅(x : L), m⁆ = ⁅x, m⁆ := by
  letI := idealInflationLieRingModule (M := M) I J hIJ htop
  change ⁅complementaryIdealProjection I J hIJ htop (x : L), m⁆ = ⁅x, m⁆
  rw [complementaryIdealProjection_left]

/-- Faithfulness of the original ideal module gives injectivity of the
actual ambient action operators restricted to that ideal. -/
theorem idealInflation_restrict_injective
    [Module K M] [LieModule K I M] [LieModule.IsFaithful K I M] :
    letI := idealInflationLieRingModule (M := M) I J hIJ htop
    letI := idealInflationLieModule (M := M) I J hIJ htop
    Function.Injective (fun x : I => toEnd K L M (x : L)) := by
  have hinj := LieModule.IsFaithful.injective_toEnd (R := K) (L := I) (M := M)
  letI := idealInflationLieRingModule (M := M) I J hIJ htop
  letI := idealInflationLieModule (M := M) I J hIJ htop
  intro x y hxy
  apply hinj
  ext m
  have h := LinearMap.congr_fun hxy m
  change ⁅complementaryIdealProjection I J hIJ htop (x : L), m⁆ =
    ⁅complementaryIdealProjection I J hIJ htop (y : L), m⁆ at h
  simpa only [complementaryIdealProjection_left] using h

end Inflation

section Multiplicity

variable {K L W U : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)
  [AddCommGroup U] [Module K U] [LieRingModule I U] [LieModule K I U]

omit [LieModule K I U] in
/-- The actual multiplicity factor retains faithful action by its own
ideal after inflation to the full ambient algebra. -/
theorem multiplicityAmbient_restrict_injective
    (hf : letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
      letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
      LieModule.IsFaithful K J (U →ₗ⁅K,I⁆ W)) :
    letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
    letI := multiplicityAmbientLieModule (U := U) (W := W) I J hIJ htop
    Function.Injective (fun x : J => toEnd K L (U →ₗ⁅K,I⁆ W) (x : L)) := by
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
  letI : LieModule.IsFaithful K J (U →ₗ⁅K,I⁆ W) := hf
  exact idealInflation_restrict_injective J I hIJ.symm (by simpa only [sup_comm] using htop)

end Multiplicity

end

end CubicAnomaly.Classification.TensorFactorFaithfulness
