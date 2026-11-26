import CubicAnomaly.Classification.CompactTensorExclusion
import CubicAnomaly.Classification.TensorFactorFaithfulness
import CubicAnomaly.Classification.TwoIdealTensorForms

/-!
# Excluding the actual two-ideal tensor package

The factor actions, their faithfulness, and their invariant forms are
unpacked from the previously constructed actual evaluation package.
Their exact inflation actions provide the operator injections and
complementary triviality needed by the compact tensor exclusion theorem.
No extra factorization, irreducibility, or form witness is assumed.
-/

namespace CubicAnomaly.Classification.ClassicalTensorPackageExclusion

open Module LieModule
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.CompactOperatorModel
open CubicAnomaly.Classification.CompactTensorExclusion
open CubicAnomaly.Classification.TensorFactorActions
open CubicAnomaly.Classification.TensorFactorFaithfulness
open CubicAnomaly.Classification.TensorEvaluation
open CubicAnomaly.Classification.TwoIdealTensorForms
open scoped TensorProduct

noncomputable section

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  {h : LieSubalgebra ℝ g}
  {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
  [LieRingModule (ℂ ⊗[ℝ] h) W] [LieModule ℂ (ℂ ⊗[ℝ] h) W]
  [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)]
  {Φ : LinearMap.BilinForm ℂ W}

set_option maxHeartbeats 1000000 in
/-- The actual tensor package constructed from two complementary atomic
ideals is incompatible with the original compact complex-type quotient.
Every factor action and form used in the contradiction comes from that
package and the actual ambient operator model. -/
theorem actual_two_ideal_tensor_forms_impossible
    (B : CompactForm g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (A : Model h Φ)
    (I J : LieIdeal ℂ (ℂ ⊗[ℝ] h)) (hI : IsAtom I) (hJ : IsAtom J)
    (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)
    (U : LieSubmodule ℂ I W)
    (hForms : ActualTwoIdealTensorForms I J hIJ htop Φ U) : False := by
  letI : LieRingModule I U := inferInstance
  letI : LieModule ℂ I U := inferInstance
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
  letI := idealInflationLieRingModule (M := U) I J hIJ htop
  letI := idealInflationLieModule (M := U) I J hIJ htop
  letI := multiplicityAmbientLieRingModule (U := U) (W := W) I J hIJ htop
  letI := multiplicityAmbientLieModule (U := U) (W := W) I J hIJ htop
  rcases hForms with ⟨hIU, hIfaith, hJN, hJfaith, hLU, hLN, hfinN,
    E, _hE, β, γ, hiβ, hiγ, hβ, hγ, hrβ, hrγ, hform⟩
  letI : LieModule.IsIrreducible ℂ I U := hIU
  letI : LieModule.IsFaithful ℂ I U := hIfaith
  letI : LieModule.IsIrreducible ℂ J (U →ₗ⁅ℂ,I⁆ W) := hJN
  letI : LieModule.IsFaithful ℂ J (U →ₗ⁅ℂ,I⁆ W) := hJfaith
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) U := hLU
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) (U →ₗ⁅ℂ,I⁆ W) := hLN
  letI : Module.Finite ℂ (U →ₗ⁅ℂ,I⁆ W) := hfinN
  letI : Nontrivial U := LieModule.nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) U
  have hMI : Function.Injective
      (fun x : I => toEnd ℂ (ℂ ⊗[ℝ] h) U (x : ℂ ⊗[ℝ] h)) :=
    idealInflation_restrict_injective I J hIJ htop
  have hNJ : Function.Injective
      (fun x : J => toEnd ℂ (ℂ ⊗[ℝ] h) (U →ₗ⁅ℂ,I⁆ W) (x : ℂ ⊗[ℝ] h)) :=
    multiplicityAmbient_restrict_injective I J hIJ htop hJfaith
  have hIN (x : I) (f : U →ₗ⁅ℂ,I⁆ W) : ⁅(x : ℂ ⊗[ℝ] h), f⁆ = 0 := by
    apply LieModuleHom.ext
    intro u
    change ⁅(complementaryIdealProjection J I hIJ.symm
      (by simpa only [sup_comm] using htop) (x : ℂ ⊗[ℝ] h) : ℂ ⊗[ℝ] h), f u⁆ = 0
    rw [complementaryIdealProjection_right]
    exact zero_lie _
  have hJM (y : J) (u : U) : ⁅(y : ℂ ⊗[ℝ] h), u⁆ = 0 := by
    change ⁅complementaryIdealProjection I J hIJ htop (y : ℂ ⊗[ℝ] h), u⁆ = 0
    rw [complementaryIdealProjection_right, zero_lie]
  exact compact_two_ideal_tensor_impossible B hproper e A E I J hI hJ htop
    β hiβ γ hiγ hβ hγ hrβ hrγ hform hMI hNJ hIN hJM

end

end CubicAnomaly.Classification.ClassicalTensorPackageExclusion
