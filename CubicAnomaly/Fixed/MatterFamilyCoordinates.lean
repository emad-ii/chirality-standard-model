import CubicAnomaly.Fixed.MatterCoordinates
import CubicAnomaly.Fixed.MatterFamilyAnomaly

/-!
# Explicit family coordinates for the actual coupled matter representation

The literal matrix action on the three copy labels agrees with the
previously constructed coupled representation. Integral family matrix-unit
coefficients are therefore attached to that actual representation.
-/

namespace CubicAnomaly.Fixed.MatterFamilyCoordinates

open Matrix
open CubicAnomaly.Fixed.MatterSpectrum
open CubicAnomaly.Fixed.MatterCoordinates
open CubicAnomaly.Fixed.MatterAnomaly
open CubicAnomaly.Fixed.MatterFamilyAnomaly
open CubicAnomaly.Fixed.FamilyAnomaly
open CubicAnomaly.Fixed.TensorAnomaly
open scoped BigOperators Kronecker

noncomputable section

/-- The literal family matrix action on the three existing matter copies. -/
def familyCopyAction (F : Matrix (Fin 3) (Fin 3) ℂ) (v : Matter81) : Matter81 :=
  fun i => ∑ j, F i j • v j

/-- The family copy action is bundled linearly in both the matrix and vector. -/
def familyCopyActionMap : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ Matter81 where
  toFun F := {
    toFun := familyCopyAction F
    map_add' := by
      intro v w
      funext i
      simp [familyCopyAction, smul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c v
      funext i
      simp only [familyCopyAction, Pi.smul_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact smul_comm _ _ _ }
  map_add' := by
    intro F G
    apply LinearMap.ext
    intro v
    funext i
    change familyCopyAction (F + G) v i = familyCopyAction F v i + familyCopyAction G v i
    simp only [familyCopyAction, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c F
    apply LinearMap.ext
    intro v
    funext i
    change familyCopyAction (c • F) v i = c • familyCopyAction F v i
    simp only [familyCopyAction, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

@[simp] theorem family_copy_action_map_apply (F : Matrix (Fin 3) (Fin 3) ℂ)
    (v : Matter81) : familyCopyActionMap F v = familyCopyAction F v := rfl

theorem matter_family_copy_coordinates (F : Matrix (Fin 3) (Fin 3) ℂ)
    (v : Matter81) (i : Fin 3) (d : MatterLabels.LocalIndex) :
    matter81ExplicitCoordinates (familyCopyAction F v) (i, d) =
      ∑ j, F i j * matter81ExplicitCoordinates v (j, d) := by
  change matter27ExplicitCoordinates (∑ j, F i j • v j) d = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    matter81_coordinates_apply]

/-- This is exactly the family action of the existing coupled anomaly module. -/
theorem coupled_family_copy_action (F : FamilyLie) (v : Matter81) :
    coupledMatterCoordinates (familyCopyAction F.val v) =
      coupledMatter81Representation (0, F) *ᵥ coupledMatterCoordinates v := by
  funext p
  change matter27Coordinates (∑ j, F.val p.2 j • v j) p.1 =
    (tensorAction (matter27MatrixRepresentation 0) F.val *ᵥ coupledMatterCoordinates v) p
  simp [tensorAction, coupledMatterCoordinates, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap, Matrix.one_apply, Fintype.sum_prod_type, ite_mul]

/-- The integral traceless-projected family matrix unit. -/
def familyUnitMatrix (p q : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  (3 : ℂ) • Matrix.single p q 1 - (MatterLabels.delta p q : ℂ) • 1

/-- The displayed family matrix unit is an actual element of `sl(3,ℂ)`. -/
def familyUnitElement (p q : Fin 3) : FamilyLie :=
  ⟨familyUnitMatrix p q, by
    change Matrix.trace (familyUnitMatrix p q) = 0
    by_cases h : p = q
    · subst q
      simp [familyUnitMatrix, MatterLabels.delta, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_single_eq_same]
    · simp [familyUnitMatrix, MatterLabels.delta, h, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_single_eq_of_ne p q 1 h]⟩

private theorem familyUnitMatrix_entry (p q r s : Fin 3) :
    familyUnitMatrix p q r s =
      ((3 * MatterLabels.delta p r * MatterLabels.delta q s -
        MatterLabels.delta p q * MatterLabels.delta r s : ℤ) : ℂ) := by
  simp only [familyUnitMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.single_apply, Matrix.one_apply, MatterLabels.delta, Int.cast_sub,
    Int.cast_mul, Int.cast_ofNat, Int.cast_ite, Int.cast_one, Int.cast_zero]
  split_ifs <;> simp_all

/-- The finite integer family witness interpreted as an actual complex matrix. -/
def familyMatterUnitMatrix (p q : Fin 3) :
    Matrix MatterLabels.Index MatterLabels.Index ℂ :=
  fun r s => (MatterLabels.familyUnitCoefficient p q r s : ℂ)

/-- The integer family coefficients give the actual family action on the eighty-one. -/
theorem matter81_family_unit_action (p q : Fin 3) (v : Matter81) :
    matter81ExplicitCoordinates (familyCopyAction (familyUnitElement p q).val v) =
      familyMatterUnitMatrix p q *ᵥ matter81ExplicitCoordinates v := by
  funext r
  rcases r with ⟨i, d⟩
  rw [matter_family_copy_coordinates]
  simp [familyUnitElement, familyMatterUnitMatrix, familyUnitMatrix_entry,
    MatterLabels.familyUnitCoefficient, MatterLabels.delta, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, mul_ite, ite_mul]

end

end CubicAnomaly.Fixed.MatterFamilyCoordinates
