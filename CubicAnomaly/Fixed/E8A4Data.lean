import CubicAnomaly.Fixed.E8BracketData

/-!
# Explicit matrix units in the fixed exceptional algebra

The four selected simple roots form a chain. These sparse vectors describe
five times the traceless projections of all twenty-five matrix units. The
commutator, support, and recovery identities are checked on the literal data.
The factor five keeps every finite witness integral.
-/

namespace CubicAnomaly.Fixed.E8A4Data

open CubicAnomaly.Fixed.E8BracketData
open scoped BigOperators

def chain (i : Fin 4) : Fin 8 := ![1, 3, 4, 5] i

def unitRoot (i j : Fin 5) : RootVector :=
  Vector.ofFn fun k =>
    (if i < j then 1 else -1) *
      ∑ p : Fin 4, if min i.val j.val ≤ p.val ∧ p.val < max i.val j.val ∧
        chain p = k then 1 else 0

def unitSign (i j : Fin 5) : ℤ :=
  !![0, 1, -1, 1, -1;
    -1, 0, -1, 1, -1;
    -1, 1, 0, 1, -1;
    -1, 1, -1, 0, -1;
    -1, 1, -1, 1, 0] i j

/-- Five times the projected matrix-unit vector, in the signed Geck basis. -/
def unitData (i j : Fin 5) : Sparse :=
  if i = j then
    (List.finRange 4).map fun p =>
      (.inl (chain p),
        (5 * (if i.val ≤ p.val then 1 else 0) - ((p.val : ℤ) + 1)) *
          diagramSign (chain p))
  else E8BracketData.singleton (.inr (unitRoot i j)) (5 * unitSign i j)

def sparseBracket (xs ys : Sparse) : Sparse :=
  applySparse (fun x => applySparse (bracket x) ys) xs

/-- The elementary matrix commutator rule, with its denominator cleared. -/
theorem e8_a4_unit_bracket_certificate : ∀ i j k l : Fin 5,
    sparseEq (sparseBracket (unitData i j) (unitData k l))
      (scale 5 ((if j = k then unitData i l else []) ++
        scale (-1) (if l = i then unitData k j else []))) = true := by
  native_decide

/-- Every unit image is a valid grade-zero coordinate vector. -/
theorem e8_a4_unit_support_certificate : ∀ i j : Fin 5,
    supported (unitData i j) = true ∧
      (unitData i j).all (fun p => match p.1 with
        | .inl _ => true
        | .inr v => v[6] == 0) = true := by
  native_decide

/-- A coordinate recovery map on the ambient exceptional basis. -/
def recoverCoefficient (a b : Fin 5) : DataIndex → ℤ
  | .inl k =>
    if a = b then
      ∑ p : Fin 4, if k = chain p then
        diagramSign k * ((if a.val = p.val then 1 else 0) -
          (if a.val = p.val + 1 then 1 else 0)) else 0
    else 0
  | .inr v => if a ≠ b ∧ v = unitRoot a b then unitSign a b else 0

def recoverSparse (xs : Sparse) (a b : Fin 5) : ℤ :=
  (xs.map fun p => p.2 * recoverCoefficient a b p.1).sum

/-- Recovery is exactly five times the traceless projection of each unit. -/
theorem e8_a4_unit_recovery_certificate : ∀ i j a b : Fin 5,
    recoverSparse (unitData i j) a b =
      5 * (if a = i ∧ b = j then 1 else 0) -
        (if i = j ∧ a = b then 1 else 0) := by
  native_decide

/-- The off-diagonal simple units are exactly the selected raising/lowering data. -/
theorem e8_a4_simple_unit_certificate : ∀ p : Fin 4,
    unitData ⟨p.val, by omega⟩ ⟨p.val + 1, by omega⟩ =
      E8BracketData.singleton (.inr (simpleVector (chain p)))
        (-5 * diagramSign (chain p)) ∧
    unitData ⟨p.val + 1, by omega⟩ ⟨p.val, by omega⟩ =
      E8BracketData.singleton (.inr (negateVector (simpleVector (chain p))))
        (5 * diagramSign (chain p)) := by
  native_decide

end CubicAnomaly.Fixed.E8A4Data
