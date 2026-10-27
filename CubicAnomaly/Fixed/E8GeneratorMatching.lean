import CubicAnomaly.Fixed.E8GeneratorCoordinates
import CubicAnomaly.Fixed.E8SparseModel

/-!
# Matching the finite exceptional generators to the actual Geck action

The finite integer generator tables act on the existing complex defining
module by exactly the actual Geck matrices. The proof uses the reconstructed
root-set binding and the norm-two coordinate formulas, rather than a second
unrelated representation or a hypothesis identifying their entries.
-/

namespace CubicAnomaly.Fixed.E8GeneratorMatching

open Matrix
open CubicAnomaly.Fixed.E8RootPairing
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8GeneratorCoordinates
open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8BracketBinding
open CubicAnomaly.Fixed.E8SparseModel
open RootPairing.GeckConstruction

noncomputable section

private def coordinateDataIndex : CoordIndex → DataIndex
  | .inl i => .inl i
  | .inr r => .inr (Vector.ofFn r.val)

private theorem dataIndex_coordinate (i : CoordIndex) :
    dataIndex (coordIndexEquiv i) = coordinateDataIndex i := by
  cases i <;> simp [dataIndex, coordinateDataIndex, coordIndexEquiv]

private theorem vectorOfFn_injective :
    Function.Injective (Vector.ofFn : (Fin 8 → ℤ) → RootVector) := by
  intro x y h
  funext i
  simpa using congrArg (fun v : RootVector => v[i]) h

private theorem vector_eq_simple (r : Root) (i : Fin 8) :
    Vector.ofFn r.val = simpleVector i ↔ r.val = Pi.single i (1 : ℤ) := by
  rw [simpleVector, vectorOfFn_injective.eq_iff]

private theorem root_coordinates_ne_zero (r : Root) : r.val ≠ 0 := by
  intro hr
  have h := coordinateRoots_norm_two r.val r.property
  rw [hr] at h
  norm_num [innerZ] at h

private theorem actual_root_isRoot (r : Root) : isRoot (Vector.ofFn r.val) = true := by
  apply (bracket_data_isRoot_iff_list _).mpr
  have h := e8_dataIndex_mem_basisList (Sum.inr r)
  simpa [dataIndex, basisList] using h

private theorem negate_simple (i : Fin 8) :
    negateVector (simpleVector i) = Vector.ofFn (-(Pi.single i (1 : ℤ))) := by
  ext j hj
  simp [negateVector, simpleVector]

private theorem add_simple (i : Fin 8) (r : Root) :
    addVector (simpleVector i) (Vector.ofFn r.val) =
      Vector.ofFn (Pi.single i (1 : ℤ) + r.val) := by
  ext j hj
  simp [addVector, simpleVector]

private theorem sub_simple (i : Fin 8) (r : Root) :
    subVector (Vector.ofFn r.val) (simpleVector i) =
      Vector.ofFn (r.val - Pi.single i (1 : ℤ)) := by
  ext j hj
  simp [subVector, simpleVector]

private theorem pairSimple_actual (r : Root) (i : Fin 8) :
    pairSimple (Vector.ofFn r.val) i = innerZ r.val (Pi.single i 1) := by
  simp [pairSimple, innerZ, Pi.single_apply]

/-- A proposed root shift contributes precisely at its actual root label.
The root-membership test cannot discard a shift which equals an actual root. -/
private theorem root_shift_coefficient (x : Fin 8 → ℤ) (r : Root) :
    ((coefficient
      (if isRoot (Vector.ofFn x) then E8BracketData.singleton (.inr (Vector.ofFn x)) 1 else [])
      (.inr (Vector.ofFn r.val))) : ℂ) =
        if r.val = x then 1 else 0 := by
  classical
  by_cases hx : r.val = x
  · subst x
    simp [actual_root_isRoot, E8BracketData.singleton, coefficient]
  · by_cases hr : isRoot (Vector.ofFn x) = true <;>
      simp [hr, E8BracketData.singleton, coefficient, vectorOfFn_injective.eq_iff, hx, Ne.symm hx]

private theorem h_coordinate_coefficients (i : Fin 8) (r s : CoordIndex) :
    hCoordinates i r s =
      (coefficient (genH i (coordinateDataIndex s)) (coordinateDataIndex r) : ℂ) := by
  classical
  cases r with
  | inl r =>
      cases s <;>
        simp [hCoordinates, coordinateDataIndex, genH, E8BracketData.singleton, coefficient]
  | inr r =>
      cases s with
      | inl s =>
          simp [hCoordinates, coordinateDataIndex, genH, coefficient]
      | inr s =>
          by_cases hrs : r = s <;>
            simp [hCoordinates, coordinateDataIndex, genH, E8BracketData.singleton, coefficient,
              pairSimple_actual, vectorOfFn_injective.eq_iff,
              Subtype.val_injective.eq_iff, eq_comm, hrs]

private theorem e_coordinate_coefficients (i : Fin 8) (r s : CoordIndex) :
    eCoordinates i r s =
      (coefficient (genE i (coordinateDataIndex s)) (coordinateDataIndex r) : ℂ) := by
  classical
  cases r with
  | inl j =>
      cases s with
      | inl k =>
          simp [eCoordinates, coordinateDataIndex, genE, E8BracketData.singleton, coefficient]
      | inr s =>
          simp only [eCoordinates, Matrix.fromBlocks_apply₁₂, coordinateDataIndex,
            genE, negate_simple, vectorOfFn_injective.eq_iff]
          by_cases hs : s.val = -(Pi.single i (1 : ℤ))
          · simp [hs, E8BracketData.singleton, coefficient, eq_comm]
          · rw [if_neg hs]
            by_cases hr : isRoot (addVector (simpleVector i) (Vector.ofFn s.val)) = true <;>
              simp [hs, hr, E8BracketData.singleton, coefficient]
  | inr r =>
      cases s with
      | inl k =>
          by_cases hr : r.val = Pi.single i (1 : ℤ) <;>
            simp [eCoordinates, coordinateDataIndex, genE, simpleVector,
              E8BracketData.singleton, coefficient, vectorOfFn_injective.eq_iff,
              hr, eq_comm]
      | inr s =>
          by_cases hs : s.val = -(Pi.single i (1 : ℤ))
          · simp [eCoordinates, coordinateDataIndex, genE, negate_simple,
              vectorOfFn_injective.eq_iff, hs, E8BracketData.singleton, coefficient,
              root_coordinates_ne_zero]
          · simp only [eCoordinates, Matrix.fromBlocks_apply₂₂, coordinateDataIndex,
              genE, negate_simple, vectorOfFn_injective.eq_iff, if_neg hs, add_simple]
            exact (root_shift_coefficient (Pi.single i (1 : ℤ) + s.val) r).symm

private theorem f_coordinate_coefficients (i : Fin 8) (r s : CoordIndex) :
    fCoordinates i r s =
      (coefficient (genF i (coordinateDataIndex s)) (coordinateDataIndex r) : ℂ) := by
  classical
  cases r with
  | inl j =>
      cases s with
      | inl k =>
          simp [fCoordinates, coordinateDataIndex, genF, E8BracketData.singleton, coefficient]
      | inr s =>
          simp only [fCoordinates, Matrix.fromBlocks_apply₁₂, coordinateDataIndex,
            genF, vector_eq_simple]
          by_cases hs : s.val = Pi.single i (1 : ℤ)
          · simp [hs, E8BracketData.singleton, coefficient, eq_comm]
          · rw [if_neg hs]
            by_cases hr : isRoot (subVector (Vector.ofFn s.val) (simpleVector i)) = true <;>
              simp [hs, hr, E8BracketData.singleton, coefficient]
  | inr r =>
      cases s with
      | inl k =>
          by_cases hr : r.val = -(Pi.single i (1 : ℤ)) <;>
            simp [fCoordinates, coordinateDataIndex, genF, negate_simple,
              E8BracketData.singleton, coefficient, vectorOfFn_injective.eq_iff,
              hr, eq_comm]
      | inr s =>
          by_cases hs : s.val = Pi.single i (1 : ℤ)
          · simp [fCoordinates, coordinateDataIndex, genF, simpleVector,
              vectorOfFn_injective.eq_iff, hs, E8BracketData.singleton, coefficient,
              root_coordinates_ne_zero]
          · simp only [fCoordinates, Matrix.fromBlocks_apply₂₂, coordinateDataIndex,
              genF, vector_eq_simple, if_neg hs, sub_simple]
            exact (root_shift_coefficient (s.val - Pi.single i (1 : ℤ)) r).symm

/-- The finite Cartan table is the actual Cartan action on every basis vector. -/
theorem geck_h_realize_basis (i : Fin 8) (k : Index) :
    h (simpleIndex i) *ᵥ Pi.single k (1 : ℂ) =
      realize (genH i (dataIndex k)) := by
  classical
  obtain ⟨s, rfl⟩ := coordIndexEquiv.surjective k
  ext j
  obtain ⟨r, rfl⟩ := coordIndexEquiv.surjective j
  rw [Matrix.mulVec_single_one, Matrix.col_apply, e8_realize_apply,
    dataIndex_coordinate, dataIndex_coordinate]
  change coordinateMatrix (h (simpleIndex i)) r s = _
  rw [e8_h_coordinate_formula]
  exact h_coordinate_coefficients i r s

/-- The finite raising table is the actual raising action on every basis vector. -/
theorem geck_e_realize_basis (i : Fin 8) (k : Index) :
    e (simpleIndex i) *ᵥ Pi.single k (1 : ℂ) =
      realize (genE i (dataIndex k)) := by
  classical
  obtain ⟨s, rfl⟩ := coordIndexEquiv.surjective k
  ext j
  obtain ⟨r, rfl⟩ := coordIndexEquiv.surjective j
  rw [Matrix.mulVec_single_one, Matrix.col_apply, e8_realize_apply,
    dataIndex_coordinate, dataIndex_coordinate]
  change coordinateMatrix (e (simpleIndex i)) r s = _
  rw [e8_e_coordinate_formula]
  exact e_coordinate_coefficients i r s

/-- The finite lowering table is the actual lowering action on every basis vector. -/
theorem geck_f_realize_basis (i : Fin 8) (k : Index) :
    f (simpleIndex i) *ᵥ Pi.single k (1 : ℂ) =
      realize (genF i (dataIndex k)) := by
  classical
  obtain ⟨s, rfl⟩ := coordIndexEquiv.surjective k
  ext j
  obtain ⟨r, rfl⟩ := coordIndexEquiv.surjective j
  rw [Matrix.mulVec_single_one, Matrix.col_apply, e8_realize_apply,
    dataIndex_coordinate, dataIndex_coordinate]
  change coordinateMatrix (f (simpleIndex i)) r s = _
  rw [e8_f_coordinate_formula]
  exact f_coordinate_coefficients i r s

end

end CubicAnomaly.Fixed.E8GeneratorMatching
