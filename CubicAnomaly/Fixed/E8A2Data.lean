import CubicAnomaly.Fixed.E8A4Data

/-!
# Explicit commuting family matrix units

The negative highest root and the last simple root form the family A2.
This ordering makes the degree-one eighty-one carry the defining family
orientation. Integral matrix-unit and recovery certificates provide the
same construction as for A4, with all denominators cleared by three.
-/

namespace CubicAnomaly.Fixed.E8A2Data

open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8A4Data (sparseBracket)
open scoped BigOperators

def familySimpleRoot (p : Fin 2) : RootVector :=
  if p = 0 then #v[-2, -3, -4, -6, -5, -4, -3, -2] else simpleVector 7

def familyUnitRoot (i j : Fin 3) : RootVector :=
  Vector.ofFn fun k =>
    (if i < j then 1 else -1) *
      ∑ p : Fin 2, if min i.val j.val ≤ p.val ∧ p.val < max i.val j.val then
        (familySimpleRoot p)[k] else 0

def familyUnitSign (i j : Fin 3) : ℤ :=
  !![0, -1, 1; 1, 0, -1; 1, 1, 0] i j

/-- Three times each projected family matrix-unit vector. -/
def familyUnitData (i j : Fin 3) : Sparse :=
  if i = j then
    (List.finRange 8).map fun k =>
      (.inl k, diagramSign k *
        ∑ p : Fin 2,
          (3 * (if i.val ≤ p.val then 1 else 0) - ((p.val : ℤ) + 1)) *
            (familySimpleRoot p)[k])
  else E8BracketData.singleton (.inr (familyUnitRoot i j)) (3 * familyUnitSign i j)

theorem e8_a2_unit_bracket_certificate : ∀ i j k l : Fin 3,
    sparseEq (sparseBracket (familyUnitData i j) (familyUnitData k l))
      (scale 3 ((if j = k then familyUnitData i l else []) ++
        scale (-1) (if l = i then familyUnitData k j else []))) = true := by
  native_decide

theorem e8_a2_unit_support_certificate : ∀ i j : Fin 3,
    supported (familyUnitData i j) = true ∧
      (familyUnitData i j).all (fun p => match p.1 with
        | .inl _ => true
        | .inr v => v[6] % 3 == 0) = true := by
  native_decide

/-- The two explicit matrix algebras commute inside the exceptional bracket. -/
theorem e8_a4_a2_commuting_certificate : ∀ (i j : Fin 5) (k l : Fin 3),
    sparseEq (sparseBracket (E8A4Data.unitData i j) (familyUnitData k l)) [] = true := by
  native_decide

/-- Twice a left inverse on family coordinates, vanishing on the A4 coordinates. -/
def familyRecoverCoefficient (a b : Fin 3) : DataIndex → ℤ
  | .inl k =>
    if a = b then
      (if k = 0 then -1 else 0) *
        ((if a = 0 then 1 else 0) - (if a = 1 then 1 else 0)) +
      ((if k = 7 then 2 else 0) - (if k = 0 then 2 else 0)) *
        ((if a = 1 then 1 else 0) - (if a = 2 then 1 else 0))
    else 0
  | .inr v => if a ≠ b ∧ v = familyUnitRoot a b then 2 * familyUnitSign a b else 0

def familyRecoverSparse (xs : Sparse) (a b : Fin 3) : ℤ :=
  (xs.map fun p => p.2 * familyRecoverCoefficient a b p.1).sum

theorem e8_a2_unit_recovery_certificate : ∀ i j a b : Fin 3,
    familyRecoverSparse (familyUnitData i j) a b =
      6 * (if a = i ∧ b = j then 1 else 0) -
        2 * (if i = j ∧ a = b then 1 else 0) := by
  native_decide

theorem e8_a2_recovery_vanishes_on_a4_certificate :
    ∀ (i j : Fin 5) (a b : Fin 3),
      familyRecoverSparse (E8A4Data.unitData i j) a b = 0 := by
  native_decide

end CubicAnomaly.Fixed.E8A2Data
