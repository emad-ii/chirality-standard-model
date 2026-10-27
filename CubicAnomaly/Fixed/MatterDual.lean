import CubicAnomaly.Fixed.MatterBranching
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The actual dual defining module and its Standard Model charges

Dual coordinates are evaluated on the canonical vector basis. The dual
Lie action is proved to be minus the transposed matrix action. Its colour
and weak blocks therefore carry integer hypercharges `2` and `-3`.
-/

namespace CubicAnomaly.Fixed.MatterDual

open Matrix
open CubicAnomaly.Fixed.MatterBranching

noncomputable section

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Coordinates of an actual linear functional, using the actual dual basis. -/
def dualCoordinates : Module.Dual ℂ (n → ℂ) ≃ₗ[ℂ] (n → ℂ) :=
  (Pi.basisFun ℂ n).dualBasis.equivFun

/-- A dual coordinate is evaluation on a standard basis vector. -/
@[simp] theorem dual_coordinates_apply (f : Module.Dual ℂ (n → ℂ)) (i : n) :
    dualCoordinates n f i = f (Pi.single i 1) := by
  simp [dualCoordinates, Module.Basis.dualBasis_equivFun, Pi.basisFun_apply]

/-- The actual dual action in standard coordinates is minus transpose. -/
theorem dual_matrix_action (A : Matrix n n ℂ) (f : Module.Dual ℂ (n → ℂ)) :
    dualCoordinates n ⁅A, f⁆ = -Aᵀ *ᵥ dualCoordinates n f := by
  ext i
  rw [dual_coordinates_apply, Module.Dual.lie_apply, Matrix.lie_apply]
  have hcol : A *ᵥ Pi.single i 1 =
      ∑ j, A j i • (Pi.single j 1 : n → ℂ) := by
    rw [Matrix.mulVec_single_one]
    exact pi_eq_sum_univ' _
  rw [hcol, map_sum]
  simp [Matrix.mulVec, dotProduct, map_smul, Finset.sum_neg_distrib]

end

noncomputable section

/-- The actual antifundamental five-dimensional representation space. -/
abbrev AntiFive := Module.Dual ℂ (FiveIndex → ℂ)

/-- Literal colour and weak coordinates of the antifundamental. -/
def antiFiveCoordinates : AntiFive ≃ₗ[ℂ] (Fin 3 → ℂ) × (Fin 2 → ℂ) :=
  (dualCoordinates FiveIndex).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 2) ℂ ℂ)

/-- The actual antifundamental decomposes into two dual block actions. -/
theorem anti_five_block_action (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (f : AntiFive) :
    antiFiveCoordinates ⁅Matrix.fromBlocks A 0 0 B, f⁆ =
      (-Aᵀ *ᵥ (antiFiveCoordinates f).1,
        -Bᵀ *ᵥ (antiFiveCoordinates f).2) := by
  simp only [antiFiveCoordinates, LinearEquiv.trans_apply, dual_matrix_action,
    Matrix.fromBlocks_transpose, transpose_zero]
  apply Prod.ext
  · ext i
    simp [LinearEquiv.sumArrowLequivProdArrow, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type]
  · ext i
    simp [LinearEquiv.sumArrowLequivProdArrow, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type]

/-- The Standard Model action on the antifundamental has integer charges
`2` on the dual colour space and `-3` on the dual weak space. -/
theorem anti_five_standard_model_action (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) (f : AntiFive) :
    antiFiveCoordinates ⁅standardModelGenerator A B q, f⁆ =
      (-Aᵀ *ᵥ (antiFiveCoordinates f).1 + (2 * q) • (antiFiveCoordinates f).1,
        -Bᵀ *ᵥ (antiFiveCoordinates f).2 + (-3 * q) • (antiFiveCoordinates f).2) := by
  rw [standardModelGenerator, anti_five_block_action]
  apply Prod.ext
  · ext i
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.neg_mulVec,
      Matrix.transpose_add, Matrix.transpose_smul]
    ring
  · ext i
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.neg_mulVec,
      Matrix.transpose_add, Matrix.transpose_smul]
    ring

/-- Literal primitive hypercharge action on the actual antifundamental. -/
theorem anti_five_hypercharge_action (f : AntiFive) :
    antiFiveCoordinates ⁅standardModelGenerator 0 0 1, f⁆ =
      ((2 : ℂ) • (antiFiveCoordinates f).1,
        (-3 : ℂ) • (antiFiveCoordinates f).2) := by
  simpa using anti_five_standard_model_action 0 0 1 f

/-- The invariant alternating form identifies the weak dual with the defining space. -/
def weakDualEquiv : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 1, -v 0]
  invFun v := ![-v 1, v 0]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' v w := by
    ext i
    fin_cases i
    all_goals simp
    abel
  map_smul' c v := by ext i; fin_cases i <;> simp

/-- Explicit determinant twist relating the dual and defining weak actions. -/
theorem weak_dual_action (B : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    weakDualEquiv (-Bᵀ *ᵥ v) =
      B *ᵥ weakDualEquiv v - Matrix.trace B • weakDualEquiv v := by
  ext i
  fin_cases i <;>
    simp [weakDualEquiv, Matrix.mulVec, dotProduct, Matrix.trace, Fin.sum_univ_succ] <;> ring

/-- On traceless weak generators this is an actual intertwining equivalence. -/
theorem weak_dual_traceless_action (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : Matrix.trace B = 0) (v : Fin 2 → ℂ) :
    weakDualEquiv (-Bᵀ *ᵥ v) = B *ᵥ weakDualEquiv v := by
  simp [weak_dual_action, hB]

/-- Antifundamental coordinates using the defining weak doublet. -/
def antiFiveSMCoordinates : AntiFive ≃ₗ[ℂ] (Fin 3 → ℂ) × (Fin 2 → ℂ) :=
  antiFiveCoordinates.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℂ _) weakDualEquiv)

/-- Actual down-antiquark and lepton-doublet actions, including their charges. -/
theorem anti_five_sm_action (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hB : Matrix.trace B = 0) (f : AntiFive) :
    antiFiveSMCoordinates ⁅standardModelGenerator A B q, f⁆ =
      (-Aᵀ *ᵥ (antiFiveSMCoordinates f).1 + (2 * q) • (antiFiveSMCoordinates f).1,
        B *ᵥ (antiFiveSMCoordinates f).2 + (-3 * q) • (antiFiveSMCoordinates f).2) := by
  simp only [antiFiveSMCoordinates, LinearEquiv.trans_apply,
    anti_five_standard_model_action, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, map_add, map_smul, weak_dual_traceless_action B hB]

end

end CubicAnomaly.Fixed.MatterDual
