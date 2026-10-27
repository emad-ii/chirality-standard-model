import CubicAnomaly.Fixed.MatterSpectrum
import CubicAnomaly.Fixed.MatterLabels

/-!
# Explicit coordinates for the actual matter module

The coordinates retain the alternating pairs, both dual five-dimensional
blocks, the defining five, the two trivial lines, and the three copy labels.
The integral matrices are proved to be the actual action of the traceless
matrix units, providing a semantic interface for the exceptional matching.
-/

namespace CubicAnomaly.Fixed.MatterCoordinates

open Matrix
open CubicAnomaly.Fixed.MatterAlternating
open CubicAnomaly.Fixed.MatterBranching
open CubicAnomaly.Fixed.MatterDual
open CubicAnomaly.Fixed.MatterSpectrum
open scoped BigOperators

noncomputable section

local instance fiveLinearOrder : LinearOrder FiveIndex :=
  LinearOrder.lift' MatterLabels.fiveIndexEquiv MatterLabels.fiveIndexEquiv.injective

private def familyExplicitCoordinates :
    Family ≃ₗ[ℂ] ((MatterLabels.PairIndex ⊕ FiveIndex) → ℂ) :=
  (LinearEquiv.prodCongr (alternatingCoordinates FiveIndex) (dualCoordinates FiveIndex)).trans
    (LinearEquiv.sumArrowLequivProdArrow MatterLabels.PairIndex FiveIndex ℂ ℂ).symm

private def pairExplicitCoordinates :
    VectorlikePair ≃ₗ[ℂ] ((FiveIndex ⊕ FiveIndex) → ℂ) :=
  (LinearEquiv.prodCongr (LinearEquiv.refl ℂ Five) (dualCoordinates FiveIndex)).trans
    (LinearEquiv.sumArrowLequivProdArrow FiveIndex FiveIndex ℂ ℂ).symm

/-- The explicit 10+5+5+5+2 coordinates of the already constructed twenty-seven. -/
def matter27ExplicitCoordinates : Matter27 ≃ₗ[ℂ] (MatterLabels.LocalIndex → ℂ) :=
  (LinearEquiv.prodCongr familyExplicitCoordinates
    ((LinearEquiv.prodCongr pairExplicitCoordinates
      (TrivialLieModule.equiv ℂ MatrixFive (Fin 2 → ℂ))).trans
        (LinearEquiv.sumArrowLequivProdArrow (FiveIndex ⊕ FiveIndex) (Fin 2) ℂ ℂ).symm)).trans
    (LinearEquiv.sumArrowLequivProdArrow (MatterLabels.PairIndex ⊕ FiveIndex)
      ((FiveIndex ⊕ FiveIndex) ⊕ Fin 2) ℂ ℂ).symm

@[simp] theorem matter27_coordinates_ten (v : Matter27) (p : MatterLabels.PairIndex) :
    matter27ExplicitCoordinates v (.inl (.inl p)) =
      alternatingCoordinates FiveIndex v.1.1 p := rfl

@[simp] theorem matter27_coordinates_first_dual (v : Matter27) (i : FiveIndex) :
    matter27ExplicitCoordinates v (.inl (.inr i)) = dualCoordinates FiveIndex v.1.2 i := rfl

@[simp] theorem matter27_coordinates_five (v : Matter27) (i : FiveIndex) :
    matter27ExplicitCoordinates v (.inr (.inl (.inl i))) = v.2.1.1 i := rfl

@[simp] theorem matter27_coordinates_second_dual (v : Matter27) (i : FiveIndex) :
    matter27ExplicitCoordinates v (.inr (.inl (.inr i))) =
      dualCoordinates FiveIndex v.2.1.2 i := rfl

@[simp] theorem matter27_coordinates_singlets (v : Matter27) (i : Fin 2) :
    matter27ExplicitCoordinates v (.inr (.inr i)) = v.2.2 i := rfl

/-- The three-copy coordinate equivalence uses the literal copy index. -/
def matter81ExplicitCoordinates : Matter81 ≃ₗ[ℂ] (MatterLabels.Index → ℂ) where
  toFun v p := matter27ExplicitCoordinates (v p.1) p.2
  invFun w j := matter27ExplicitCoordinates.symm (fun i => w (j, i))
  left_inv v := by
    funext j
    exact matter27ExplicitCoordinates.symm_apply_apply (v j)
  right_inv w := by
    funext p
    exact congrFun (matter27ExplicitCoordinates.apply_symm_apply (fun i => w (p.1, i))) p.2
  map_add' v w := by ext p; simp
  map_smul' c v := by ext p; simp

@[simp] theorem matter81_coordinates_apply (v : Matter81) (i : Fin 3)
    (d : MatterLabels.LocalIndex) :
    matter81ExplicitCoordinates v (i, d) = matter27ExplicitCoordinates (v i) d := rfl

/-- The actual traceless-projected matrix unit, with integral normalization. -/
def unitMatrix (p q : FiveIndex) : MatrixFive :=
  (5 : ℂ) • Matrix.single p q 1 - (MatterLabels.delta p q : ℂ) • 1

private def wedgeBasis (s : MatterLabels.PairIndex) : Ten :=
  ⟨Matrix.single s.val.1 s.val.2 1 - Matrix.single s.val.2 s.val.1 1, by
    change (Matrix.single s.val.1 s.val.2 (1 : ℂ) -
      Matrix.single s.val.2 s.val.1 1)ᵀ =
        -(Matrix.single s.val.1 s.val.2 1 - Matrix.single s.val.2 s.val.1 1)
    simp only [Matrix.transpose_sub, Matrix.transpose_single, neg_sub]⟩

private theorem wedgeBasis_coordinates (s : MatterLabels.PairIndex) :
    alternatingCoordinates FiveIndex (wedgeBasis s) = Pi.single s 1 := by
  classical
  funext r
  by_cases h : s = r
  · subst r
    have hs : s.val.1 ≠ s.val.2 := fun he =>
      s.property.ne (congrArg MatterLabels.fiveIndexEquiv he)
    simp [alternatingCoordinates, wedgeBasis, hs, Ne.symm hs]
  · have hforward : ¬(s.val.1 = r.val.1 ∧ s.val.2 = r.val.2) := by
      rintro ⟨h₁, h₂⟩
      exact h (Subtype.ext (Prod.ext h₁ h₂))
    have hreverse : ¬(s.val.2 = r.val.1 ∧ s.val.1 = r.val.2) := by
      rintro ⟨h₁, h₂⟩
      have hs := s.property
      rw [h₁, h₂] at hs
      exact (not_lt_of_gt r.property) hs
    simp [alternatingCoordinates, wedgeBasis, hforward, hreverse, Ne.symm h]

private theorem wedgeBasis_entry (s : MatterLabels.PairIndex) (i j : FiveIndex) :
    (wedgeBasis s).val i j =
      (MatterLabels.delta i s.val.1 : ℂ) * (MatterLabels.delta j s.val.2 : ℂ) -
        (MatterLabels.delta i s.val.2 : ℂ) * (MatterLabels.delta j s.val.1 : ℂ) := by
  by_cases h₁ : i = s.val.1 <;> by_cases h₂ : j = s.val.2 <;>
    by_cases h₃ : i = s.val.2 <;> by_cases h₄ : j = s.val.1 <;>
    simp [wedgeBasis, Matrix.single_apply, MatterLabels.delta, h₁, h₂, h₃, h₄, eq_comm]

private theorem wedgeBasis_coordinate_entry (r s : MatterLabels.PairIndex) :
    (wedgeBasis s).val r.val.1 r.val.2 = (MatterLabels.delta r s : ℂ) := by
  have h := congrFun (wedgeBasis_coordinates s) r
  simpa [alternatingCoordinates, Pi.single_apply, MatterLabels.delta, eq_comm] using h

private theorem single_mul_entry (p q i j : FiveIndex) (X : MatrixFive) :
    (Matrix.single p q (1 : ℂ) * X) i j = (MatterLabels.delta p i : ℂ) * X q j := by
  by_cases h : p = i
  · subst i
    simp [MatterLabels.delta]
  · rw [Matrix.single_mul_apply_of_ne 1 p q i j (Ne.symm h)]
    simp [MatterLabels.delta, h]

private theorem mul_single_entry (p q i j : FiveIndex) (X : MatrixFive) :
    (X * Matrix.single q p (1 : ℂ)) i j = (MatterLabels.delta p j : ℂ) * X i q := by
  by_cases h : p = j
  · subst j
    simp [MatterLabels.delta]
  · rw [Matrix.mul_single_apply_of_ne 1 q p i j (Ne.symm h)]
    simp [MatterLabels.delta, h]

private theorem wedge_unit_basis_action (p q : FiveIndex) (r s : MatterLabels.PairIndex) :
    alternatingCoordinates FiveIndex ⁅unitMatrix p q, wedgeBasis s⁆ r =
      (MatterLabels.wedgeUnitCoefficient p q r s : ℂ) := by
  change ((unitMatrix p q) * (wedgeBasis s).val +
    (wedgeBasis s).val * (unitMatrix p q)ᵀ) r.val.1 r.val.2 = _
  simp only [unitMatrix, sub_mul, Matrix.smul_mul, one_mul, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_single, Matrix.transpose_one,
    mul_sub, Matrix.mul_smul, mul_one, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, single_mul_entry, mul_single_entry]
  simp only [wedgeBasis_coordinate_entry r s]
  simp only [wedgeBasis_entry, MatterLabels.wedgeUnitCoefficient,
    Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  ring

private theorem wedge_expansion (X : Ten) :
    X = ∑ s : MatterLabels.PairIndex,
      alternatingCoordinates FiveIndex X s • wedgeBasis s := by
  apply (alternatingCoordinates FiveIndex).injective
  simp only [map_sum, map_smul, wedgeBasis_coordinates]
  exact pi_eq_sum_univ' _

private theorem wedge_unit_action (p q : FiveIndex) (X : Ten) :
    alternatingCoordinates FiveIndex ⁅unitMatrix p q, X⁆ =
      (fun r s => (MatterLabels.wedgeUnitCoefficient p q r s : ℂ)) *ᵥ
        alternatingCoordinates FiveIndex X := by
  funext r
  change alternatingCoordinates FiveIndex
    ((LieModule.toEnd ℂ MatrixFive Ten (unitMatrix p q)) X) r = _
  conv_lhs => rw [wedge_expansion X]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  simp only [LieModule.toEnd_apply_apply, smul_eq_mul, wedge_unit_basis_action,
    Matrix.mulVec, dotProduct, mul_comm]

private theorem unitMatrix_entry (p q r s : FiveIndex) :
    unitMatrix p q r s = (MatterLabels.fiveUnitCoefficient p q r s : ℂ) := by
  simp only [unitMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.single_apply, Matrix.one_apply, MatterLabels.fiveUnitCoefficient,
    MatterLabels.delta, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_ite,
    Int.cast_one, Int.cast_zero]
  split_ifs <;> simp_all

private theorem dualUnitMatrix_entry (p q r s : FiveIndex) :
    (-(unitMatrix p q)ᵀ) r s = (MatterLabels.dualUnitCoefficient p q r s : ℂ) := by
  simp only [Matrix.neg_apply, Matrix.transpose_apply, unitMatrix_entry,
    MatterLabels.fiveUnitCoefficient, MatterLabels.dualUnitCoefficient,
    Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_neg, Int.cast_ofNat]
  have hd : MatterLabels.delta s r = MatterLabels.delta r s := by
    simp only [MatterLabels.delta, eq_comm]
  rw [hd]
  ring

private theorem dual_unit_matrix (p q : FiveIndex) :
    -(unitMatrix p q)ᵀ = fun r s => (MatterLabels.dualUnitCoefficient p q r s : ℂ) := by
  ext r s
  exact dualUnitMatrix_entry p q r s

/-- The integer witness matrix on one explicitly coordinated matter copy. -/
def localUnitMatrix (p q : FiveIndex) :
    Matrix MatterLabels.LocalIndex MatterLabels.LocalIndex ℂ :=
  fun r s => (MatterLabels.localUnitCoefficient p q r s : ℂ)

/-- The finite integral coefficients are the actual action on the full twenty-seven. -/
theorem matter27_unit_action (p q : FiveIndex) (v : Matter27) :
    matter27ExplicitCoordinates ⁅unitMatrix p q, v⁆ =
      localUnitMatrix p q *ᵥ matter27ExplicitCoordinates v := by
  funext r
  rcases r with (r | r) | ((r | r) | r)
  · change alternatingCoordinates FiveIndex ⁅unitMatrix p q, v.1.1⁆ r = _
    have h := congrFun (wedge_unit_action p q v.1.1) r
    simpa [localUnitMatrix, MatterLabels.localUnitCoefficient, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type] using h
  · change dualCoordinates FiveIndex ⁅unitMatrix p q, v.1.2⁆ r = _
    have h := congrFun (dual_matrix_action FiveIndex (unitMatrix p q) v.1.2) r
    rw [dual_unit_matrix] at h
    simpa [localUnitMatrix, MatterLabels.localUnitCoefficient, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type] using h
  · change ((unitMatrix p q) *ᵥ v.2.1.1) r = _
    simp [localUnitMatrix, MatterLabels.localUnitCoefficient, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, unitMatrix_entry]
  · change dualCoordinates FiveIndex ⁅unitMatrix p q, v.2.1.2⁆ r = _
    have h := congrFun (dual_matrix_action FiveIndex (unitMatrix p q) v.2.1.2) r
    rw [dual_unit_matrix] at h
    simpa [localUnitMatrix, MatterLabels.localUnitCoefficient, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type] using h
  · change (0 : ℂ) = _
    simp [localUnitMatrix, MatterLabels.localUnitCoefficient, Matrix.mulVec, dotProduct]

/-- The integer witness matrix on all three explicit matter copies. -/
def matterUnitMatrix (p q : Fin 5) : Matrix MatterLabels.Index MatterLabels.Index ℂ :=
  fun r s => (MatterLabels.unitCoefficient p q r s : ℂ)

/-- Every integer witness entry is tied to the actual action on `Matter81`. -/
theorem matter81_unit_action (p q : Fin 5) (v : Matter81) :
    matter81ExplicitCoordinates
      ⁅unitMatrix (MatterLabels.fiveIndexEquiv.symm p) (MatterLabels.fiveIndexEquiv.symm q), v⁆ =
        matterUnitMatrix p q *ᵥ matter81ExplicitCoordinates v := by
  funext r
  have h := congrFun (matter27_unit_action (MatterLabels.fiveIndexEquiv.symm p)
    (MatterLabels.fiveIndexEquiv.symm q) (v r.1)) r.2
  simpa [matter81ExplicitCoordinates, matterUnitMatrix, localUnitMatrix,
    MatterLabels.unitCoefficient, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    ite_mul] using h

end

end CubicAnomaly.Fixed.MatterCoordinates
