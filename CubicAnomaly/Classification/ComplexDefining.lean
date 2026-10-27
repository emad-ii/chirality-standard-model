import CubicAnomaly.Classification.Complexification

/-!
# Extending an actual complex defining representation

A real Lie algebra acting by complex-linear operators on `W` acts on the
same `W` through its actual complexification.  Complex irreducibility of
the real action implies irreducibility of this extended action.
-/

namespace CubicAnomaly.Classification.ComplexDefining

open scoped TensorProduct

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]

/-- Extend a real-linear operator-valued map to the actual tensor
complexification of its domain. -/
noncomputable def complexifyEndMap {L : Type*} [AddCommGroup L] [Module ℝ L]
    (ρ : L →ₗ[ℝ] Module.End ℂ W) :
    (ℂ ⊗[ℝ] L) →ₗ[ℂ] Module.End ℂ W :=
  TensorProduct.AlgebraTensorModule.lift {
    toFun := fun a : ℂ => a • ρ
    map_add' := fun a b => add_smul a b ρ
    map_smul' := fun a b => mul_smul a b ρ }

/-- The extended representation acts on pure tensors by scalar multiplication. -/
theorem complexify_end_map_tmul {L : Type*} [AddCommGroup L] [Module ℝ L]
    (ρ : L →ₗ[ℝ] Module.End ℂ W) (a : ℂ) (x : L) :
    complexifyEndMap ρ (a ⊗ₜ[ℝ] x) = a • ρ x := rfl

/-- Extension preserves the actual Lie representation law. -/
noncomputable def complexifyEndRepresentation (ρ : L →ₗ⁅ℝ⁆ Module.End ℂ W) :
    (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ W := {
  complexifyEndMap ρ.toLinearMap with
  map_lie' := by
    intro x y
    change complexifyEndMap ρ.toLinearMap
        ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L) x) y) =
      (LieModule.toEnd ℂ (Module.End ℂ W) (Module.End ℂ W)
        (complexifyEndMap ρ.toLinearMap x)) (complexifyEndMap ρ.toLinearMap y)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
        simp [LieModule.toEnd_apply_apply, complexify_end_map_tmul,
          LieHom.map_lie, smul_smul, mul_comm]
      | add y z hy hz => simp only [map_add, hy, hz]
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz] }

/-- The actual extended action on the original complex vector space. -/
noncomputable abbrev complexifiedDefiningAction (ρ : L →ₗ⁅ℝ⁆ Module.End ℂ W) :
    LieRingModule (ℂ ⊗[ℝ] L) W :=
  LieRingModule.compLieHom W (complexifyEndRepresentation ρ)

/-- On the same complex vector space, the pure-tensor action is the
expected complex scalar multiple of the original defining action. -/
theorem complexified_defining_action_tmul (ρ : L →ₗ⁅ℝ⁆ Module.End ℂ W)
    (a : ℂ) (x : L) (w : W) :
    letI := complexifiedDefiningAction ρ
    ⁅a ⊗ₜ[ℝ] x, w⁆ = a • ρ x w := rfl

/-- The extended defining action is complex linear in both inputs. -/
theorem complexified_defining_lieModule (ρ : L →ₗ⁅ℝ⁆ Module.End ℂ W) :
    letI := complexifiedDefiningAction ρ
    LieModule ℂ (ℂ ⊗[ℝ] L) W :=
  LieModule.compLieHom W (complexifyEndRepresentation ρ)

/-- Irreducibility with respect to complex invariant subspaces survives
extension of the acting real algebra to its actual complexification. -/
theorem complexified_defining_irreducible [LieRingModule L W]
    [LieModule.IsIrreducible ℂ L W] (ρ : L →ₗ⁅ℝ⁆ Module.End ℂ W)
    (hact : ∀ x w, ρ x w = ⁅x, w⁆) :
    letI := complexifiedDefiningAction ρ
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] L) W := by
  letI : Nontrivial W := LieModule.nontrivial_of_isIrreducible ℂ L W
  letI := complexifiedDefiningAction ρ
  apply LieModule.IsIrreducible.mk
  intro U hU
  let T : LieSubmodule ℂ L W := {
    U.toSubmodule with
    lie_mem := by
      intro x w hw
      have h := U.lie_mem (x := 1 ⊗ₜ[ℝ] x) hw
      change ((1 : ℂ) • ρ x) w ∈ U at h
      simpa only [LinearMap.smul_apply, one_smul, hact] using h }
  have hT : T ≠ ⊥ := by
    intro hz
    apply hU
    apply LieSubmodule.toSubmodule_injective
    exact congrArg (fun S : LieSubmodule ℂ L W => S.toSubmodule) hz
  have ht : T = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top T).resolve_left hT
  apply LieSubmodule.toSubmodule_injective
  exact congrArg (fun S : LieSubmodule ℂ L W => S.toSubmodule) ht

end CubicAnomaly.Classification.ComplexDefining
