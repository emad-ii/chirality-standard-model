import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Sum.Order
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Explicit coordinate labels and integral matrix-unit action for matter

The labels follow the already constructed three copies of
`(Ten × AntiFive) × ((Five × AntiFive) × TwoSinglets)`.
The integral coefficients represent the traceless-projected matrix unit
`5 Eᵢⱼ - δᵢⱼ I` on that actual matter module.
-/

namespace CubicAnomaly.Fixed.MatterLabels

abbrev FiveIndex := Fin 3 ⊕ Fin 2

/-- The colour coordinates precede the weak coordinates. -/
def fiveIndexEquiv : FiveIndex ≃ Fin 5 := finSumFinEquiv

/-- Independent alternating entries in the numeric colour-then-weak order. -/
abbrev PairIndex :=
  {p : FiveIndex × FiveIndex // fiveIndexEquiv p.1 < fiveIndexEquiv p.2}
abbrev LocalIndex := (PairIndex ⊕ FiveIndex) ⊕ ((FiveIndex ⊕ FiveIndex) ⊕ Fin 2)
abbrev Index := Fin 3 × LocalIndex

instance : DecidableEq PairIndex := inferInstance
instance : DecidableEq LocalIndex := inferInstance
instance : DecidableEq Index := inferInstance

theorem matter_pair_label_card : Fintype.card PairIndex = 10 := by decide
theorem matter_local_label_card : Fintype.card LocalIndex = 27 := by decide
theorem matter_label_card : Fintype.card Index = 81 := by decide

/-- Integral Kronecker delta. -/
def delta {α : Type*} [DecidableEq α] (i j : α) : ℤ := if i = j then 1 else 0

/-- Action on one independent alternating-tensor coordinate. -/
def wedgeUnitCoefficient (p q : FiveIndex) (r s : PairIndex) : ℤ :=
  5 * (delta p r.val.1 * delta q s.val.1 * delta r.val.2 s.val.2 +
    delta p r.val.2 * delta q s.val.2 * delta r.val.1 s.val.1 -
    delta p r.val.1 * delta q s.val.2 * delta r.val.2 s.val.1 -
    delta p r.val.2 * delta q s.val.1 * delta r.val.1 s.val.2) -
      2 * delta p q * delta r s

/-- Action on the defining five-dimensional block. -/
def fiveUnitCoefficient (p q r s : FiveIndex) : ℤ :=
  5 * delta p r * delta q s - delta p q * delta r s

/-- Action on either dual five-dimensional block. -/
def dualUnitCoefficient (p q r s : FiveIndex) : ℤ :=
  -5 * delta q r * delta p s + delta p q * delta r s

/-- One full twenty-seven-dimensional block, with the two trivial lines. -/
def localUnitCoefficient (p q : FiveIndex) : LocalIndex → LocalIndex → ℤ
  | .inl (.inl r), .inl (.inl s) => wedgeUnitCoefficient p q r s
  | .inl (.inr r), .inl (.inr s) => dualUnitCoefficient p q r s
  | .inr (.inl (.inl r)), .inr (.inl (.inl s)) => fiveUnitCoefficient p q r s
  | .inr (.inl (.inr r)), .inr (.inl (.inr s)) => dualUnitCoefficient p q r s
  | _, _ => 0

/-- The integral matrix of `5 Eᵢⱼ - δᵢⱼ I` on all three matter copies. -/
def unitCoefficient (p q : Fin 5) (r s : Index) : ℤ :=
  if r.1 = s.1 then
    localUnitCoefficient (fiveIndexEquiv.symm p) (fiveIndexEquiv.symm q) r.2 s.2
  else 0

/-- The family action of `3 Eᵢⱼ - δᵢⱼ I`, identical on every local matter block. -/
def familyUnitCoefficient (p q : Fin 3) (r s : Index) : ℤ :=
  (3 * delta p r.1 * delta q s.1 - delta p q * delta r.1 s.1) * delta r.2 s.2

end CubicAnomaly.Fixed.MatterLabels
