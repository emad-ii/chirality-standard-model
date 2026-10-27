import CubicAnomaly.Fixed.MatterChirality
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# A genuine chirality witness for the constructed family

The fifth trace of the actual primitive hypercharge operator is `4320`.
An equivariantly self-dual representation has zero odd fifth trace, so
the actual family is not self-dual even after restriction to the actual
Standard Model Lie algebra. No irreducible-character classification is
needed for this obstruction.
-/

namespace CubicAnomaly.Fixed.MatterNonSelfDual

open Matrix
open CubicAnomaly.Fixed.MatterBranching
open CubicAnomaly.Fixed.MatterSpectrum
open CubicAnomaly.Fixed.MatterLieAlgebra
open CubicAnomaly.Fixed.MatterChirality

noncomputable section

private theorem trace_fifth_prod {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    (f : Module.End ℂ M) (g : Module.End ℂ N) :
    LinearMap.trace ℂ (M × N) ((f.prodMap g) ^ 5) =
      LinearMap.trace ℂ M (f ^ 5) + LinearMap.trace ℂ N (g ^ 5) := by
  rw [show (f.prodMap g) ^ 5 = (f ^ 5).prodMap (g ^ 5) by rfl,
    LinearMap.trace_prodMap']

private theorem scalar_fifth_trace {M : Type*}
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (a : ℂ) :
    LinearMap.trace ℂ M ((a • (1 : Module.End ℂ M)) ^ 5) =
      a ^ 5 * (Module.finrank ℂ M : ℂ) := by
  rw [smul_pow, one_pow, map_smul, LinearMap.trace_one]
  rfl

private def hyperchargeBlocks :
    Module.End ℂ (((Fin 3 → ℂ) × (Matrix (Fin 3) (Fin 2) ℂ × ℂ)) ×
      ((Fin 3 → ℂ) × (Fin 2 → ℂ))) :=
  (((-4 : ℂ) • (1 : Module.End ℂ (Fin 3 → ℂ))).prodMap
    ((1 : Module.End ℂ (Matrix (Fin 3) (Fin 2) ℂ)).prodMap
      ((6 : ℂ) • (1 : Module.End ℂ ℂ)))).prodMap
    (((2 : ℂ) • (1 : Module.End ℂ (Fin 3 → ℂ))).prodMap
      ((-3 : ℂ) • (1 : Module.End ℂ (Fin 2 → ℂ))))

private theorem hypercharge_operator_coordinates :
    familyCoordinates.conj
      (LieModule.toEnd ℂ MatrixFive Family (standardModelGenerator 0 0 1)) =
      hyperchargeBlocks := by
  apply LinearMap.ext
  intro v
  change familyCoordinates ⁅standardModelGenerator 0 0 1, familyCoordinates.symm v⁆ = _
  rw [family_standard_model_action 0 0 1 (by simp) (by simp),
    familyCoordinates.apply_symm_apply]
  simp [hyperchargeBlocks, LinearMap.prodMap_apply, Module.End.one_apply]

/-- The actual family has a nonzero fifth hypercharge trace. -/
theorem family_hypercharge_fifth_trace :
    LinearMap.trace ℂ Family
      ((LieModule.toEnd ℂ MatrixFive Family (standardModelGenerator 0 0 1)) ^ 5) = 4320 := by
  have hp (f : Module.End ℂ Family) :
      familyCoordinates.conj (f ^ 5) = (familyCoordinates.conj f) ^ 5 :=
    map_pow familyCoordinates.conjRingEquiv f 5
  rw [← LinearMap.trace_conj' _ familyCoordinates, hp, hypercharge_operator_coordinates]
  simp only [hyperchargeBlocks, trace_fifth_prod, scalar_fifth_trace, one_pow,
    LinearMap.trace_one]
  norm_num [Module.finrank_matrix]

private theorem trace_dualMap {M : Type*}
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (f : Module.End ℂ M) :
    LinearMap.trace ℂ (Module.Dual ℂ M) f.dualMap = LinearMap.trace ℂ M f := by
  let b := Module.Free.chooseBasis ℂ M
  rw [LinearMap.trace_eq_matrix_trace ℂ b.dualBasis,
    LinearMap.trace_eq_matrix_trace ℂ b]
  simp [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]

private theorem self_dual_fifth_trace_zero {L M : Type*}
    [LieRing L] [LieAlgebra ℂ L] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] [LieRingModule L M] [LieModule ℂ L M]
    (e : M ≃ₗ⁅ℂ,L⁆ Module.Dual ℂ M) (x : L) :
    LinearMap.trace ℂ M ((LieModule.toEnd ℂ L M x) ^ 5) = 0 := by
  let T := LieModule.toEnd ℂ L M x
  let D := LieModule.toEnd ℂ L (Module.Dual ℂ M) x
  have hconj : e.toLinearEquiv.conj T = D := by
    apply LinearMap.ext
    intro f
    change e ⁅x, e.symm f⁆ = ⁅x, f⁆
    calc
      e ⁅x, e.symm f⁆ = ⁅x, e (e.symm f)⁆ := e.map_lie x (e.symm f)
      _ = ⁅x, f⁆ := by rw [e.apply_symm_apply]
  have hp : D ^ 5 = -(T ^ 5).dualMap := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro m
    simp [D, T, pow_succ, Module.End.mul_apply, LieModule.toEnd_apply_apply,
      Module.Dual.lie_apply, LinearMap.dualMap_apply]
  have ht : LinearMap.trace ℂ (Module.Dual ℂ M) (D ^ 5) =
      LinearMap.trace ℂ M (T ^ 5) := by
    have hp' : (e.toLinearEquiv.conj T) ^ 5 = e.toLinearEquiv.conj (T ^ 5) :=
      (map_pow e.toLinearEquiv.conjRingEquiv T 5).symm
    rw [← hconj, hp', LinearMap.trace_conj']
  rw [hp, map_neg, trace_dualMap] at ht
  change LinearMap.trace ℂ M (T ^ 5) = 0
  linear_combination (-1 / 2 : ℂ) * ht

/-- The actual fifteen-dimensional family is chiral for the actual
Standard Model algebra: it admits no equivariant self-duality. -/
theorem family_not_self_dual :
    ¬ Nonempty (Family ≃ₗ⁅ℂ,StandardModelAlgebra⁆ Module.Dual ℂ Family) := by
  rintro ⟨e⟩
  have hz := self_dual_fifth_trace_zero e
    (standardModelGeneratorElement 0 0 1 (by simp) (by simp))
  change LinearMap.trace ℂ Family
    ((LieModule.toEnd ℂ MatrixFive Family (standardModelGenerator 0 0 1)) ^ 5) = 0 at hz
  rw [family_hypercharge_fifth_trace] at hz
  norm_num at hz

private def threeCopyCoordinates (M : Type*) [AddCommGroup M] [Module ℂ M] :
    (Fin 3 → M) ≃ₗ[ℂ] M × (M × M) where
  toFun v := (v 0, v 1, v 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv p := rfl
  map_add' v w := rfl
  map_smul' c v := rfl

private theorem trace_fifth_three_copies {M : Type*}
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (f : Module.End ℂ M) :
    LinearMap.trace ℂ (Fin 3 → M) ((LinearMap.compLeft f (Fin 3)) ^ 5) =
      3 * LinearMap.trace ℂ M (f ^ 5) := by
  let e := threeCopyCoordinates M
  have hc : e.conj (LinearMap.compLeft f (Fin 3)) = f.prodMap (f.prodMap f) := by
    apply LinearMap.ext
    intro v
    rfl
  have hp (g : Module.End ℂ (Fin 3 → M)) :
      e.conj (g ^ 5) = (e.conj g) ^ 5 := map_pow e.conjRingEquiv g 5
  rw [← LinearMap.trace_conj' _ e, hp, hc, trace_fifth_prod, trace_fifth_prod]
  ring

/-- The actual extra states contribute zero fifth trace by their proved
self-duality, so the constructed twenty-seven retains the family witness. -/
theorem matter27_hypercharge_fifth_trace :
    LinearMap.trace ℂ Matter27
      ((LieModule.toEnd ℂ MatrixFive Matter27 (standardModelGenerator 0 0 1)) ^ 5) =
        4320 := by
  have h : LieModule.toEnd ℂ MatrixFive Matter27 (standardModelGenerator 0 0 1) =
      (LieModule.toEnd ℂ MatrixFive Family (standardModelGenerator 0 0 1)).prodMap
        (LieModule.toEnd ℂ MatrixFive Extras (standardModelGenerator 0 0 1)) := rfl
  rw [h, trace_fifth_prod, family_hypercharge_fifth_trace,
    self_dual_fifth_trace_zero extrasSelfDual]
  simp

/-- The full actual eighty-one has fifth hypercharge trace `3 * 4320`. -/
theorem matter81_hypercharge_fifth_trace :
    LinearMap.trace ℂ Matter81
      ((LieModule.toEnd ℂ MatrixFive Matter81 (standardModelGenerator 0 0 1)) ^ 5) =
        12960 := by
  change LinearMap.trace ℂ (Fin 3 → Matter27)
    ((LinearMap.compLeft
      (LieModule.toEnd ℂ MatrixFive Matter27 (standardModelGenerator 0 0 1)) (Fin 3)) ^ 5) = _
  rw [trace_fifth_three_copies, matter27_hypercharge_fifth_trace]
  norm_num

/-- The full constructed eighty-one remains genuinely chiral for the
actual Standard Model algebra, despite its self-dual additional matter. -/
theorem matter81_not_self_dual :
    ¬ Nonempty (Matter81 ≃ₗ⁅ℂ,StandardModelAlgebra⁆ Module.Dual ℂ Matter81) := by
  rintro ⟨e⟩
  have hz := self_dual_fifth_trace_zero e
    (standardModelGeneratorElement 0 0 1 (by simp) (by simp))
  change LinearMap.trace ℂ Matter81
    ((LieModule.toEnd ℂ MatrixFive Matter81 (standardModelGenerator 0 0 1)) ^ 5) = 0 at hz
  rw [matter81_hypercharge_fifth_trace] at hz
  norm_num at hz

end

end CubicAnomaly.Fixed.MatterNonSelfDual
