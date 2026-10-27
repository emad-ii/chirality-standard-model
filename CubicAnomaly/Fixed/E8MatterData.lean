import CubicAnomaly.Fixed.E8A2Data
import CubicAnomaly.Fixed.E8GradingData
import CubicAnomaly.Fixed.MatterLabels

/-!
# An exact signed basis matching the exceptional eighty-one to matter

The finite table identifies every degree-one root with a coordinate of the
actual three-copy matter module. Its signs intertwine all twenty-five A4
matrix units and all nine commuting family matrix units. The first family
slice is chosen by its family highest weight; the other two are transported
by the actual family lowering operators.
-/

namespace CubicAnomaly.Fixed.E8MatterData

open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8A4Data
open CubicAnomaly.Fixed.E8A2Data
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.MatterLabels

private def root8 (a b c d e f g h : ℤ) : RootVector :=
  #v[a, b, c, d, e, f, g, h]

private def rootFamily0 : Vector RootVector 27 := #v[
  root8 (-1) (-1) (-2) (-2) (-2) (-2) (-2) (-1),
  root8 (-1) (-1) (-2) (-3) (-2) (-2) (-2) (-1),
  root8 (-1) (-1) (-2) (-3) (-3) (-2) (-2) (-1),
  root8 (-1) (-1) (-2) (-3) (-3) (-3) (-2) (-1),
  root8 (-1) (-2) (-2) (-3) (-2) (-2) (-2) (-1),
  root8 (-1) (-2) (-2) (-3) (-3) (-2) (-2) (-1),
  root8 (-1) (-2) (-2) (-3) (-3) (-3) (-2) (-1),
  root8 (-1) (-2) (-2) (-4) (-3) (-2) (-2) (-1),
  root8 (-1) (-2) (-2) (-4) (-3) (-3) (-2) (-1),
  root8 (-1) (-2) (-2) (-4) (-4) (-3) (-2) (-1),
  root8 (-2) (-3) (-3) (-5) (-4) (-3) (-2) (-1),
  root8 (-2) (-2) (-3) (-5) (-4) (-3) (-2) (-1),
  root8 (-2) (-2) (-3) (-4) (-4) (-3) (-2) (-1),
  root8 (-2) (-2) (-3) (-4) (-3) (-3) (-2) (-1),
  root8 (-2) (-2) (-3) (-4) (-3) (-2) (-2) (-1),
  root8 (-2) (-2) (-4) (-5) (-4) (-3) (-2) (-1),
  root8 (-2) (-3) (-4) (-5) (-4) (-3) (-2) (-1),
  root8 (-2) (-3) (-4) (-6) (-4) (-3) (-2) (-1),
  root8 (-2) (-3) (-4) (-6) (-5) (-3) (-2) (-1),
  root8 (-2) (-3) (-4) (-6) (-5) (-4) (-2) (-1),
  root8 (-1) (-3) (-3) (-5) (-4) (-3) (-2) (-1),
  root8 (-1) (-2) (-3) (-5) (-4) (-3) (-2) (-1),
  root8 (-1) (-2) (-3) (-4) (-4) (-3) (-2) (-1),
  root8 (-1) (-2) (-3) (-4) (-3) (-3) (-2) (-1),
  root8 (-1) (-2) (-3) (-4) (-3) (-2) (-2) (-1),
  root8 (-1) (-1) (-1) (-2) (-2) (-2) (-2) (-1),
  root8 0 (-1) (-1) (-2) (-2) (-2) (-2) (-1)]

private def rootFamily1 : Vector RootVector 27 := #v[
  root8 1 2 2 4 3 2 1 1,
  root8 1 2 2 3 3 2 1 1,
  root8 1 2 2 3 2 2 1 1,
  root8 1 2 2 3 2 1 1 1,
  root8 1 1 2 3 3 2 1 1,
  root8 1 1 2 3 2 2 1 1,
  root8 1 1 2 3 2 1 1 1,
  root8 1 1 2 2 2 2 1 1,
  root8 1 1 2 2 2 1 1 1,
  root8 1 1 2 2 1 1 1 1,
  root8 0 0 1 1 1 1 1 1,
  root8 0 1 1 1 1 1 1 1,
  root8 0 1 1 2 1 1 1 1,
  root8 0 1 1 2 2 1 1 1,
  root8 0 1 1 2 2 2 1 1,
  root8 0 1 0 1 1 1 1 1,
  root8 0 0 0 1 1 1 1 1,
  root8 0 0 0 0 1 1 1 1,
  root8 0 0 0 0 0 1 1 1,
  root8 0 0 0 0 0 0 1 1,
  root8 1 0 1 1 1 1 1 1,
  root8 1 1 1 1 1 1 1 1,
  root8 1 1 1 2 1 1 1 1,
  root8 1 1 1 2 2 1 1 1,
  root8 1 1 1 2 2 2 1 1,
  root8 1 2 3 4 3 2 1 1,
  root8 2 2 3 4 3 2 1 1]

private def rootFamily2 : Vector RootVector 27 := #v[
  root8 1 2 2 4 3 2 1 0,
  root8 1 2 2 3 3 2 1 0,
  root8 1 2 2 3 2 2 1 0,
  root8 1 2 2 3 2 1 1 0,
  root8 1 1 2 3 3 2 1 0,
  root8 1 1 2 3 2 2 1 0,
  root8 1 1 2 3 2 1 1 0,
  root8 1 1 2 2 2 2 1 0,
  root8 1 1 2 2 2 1 1 0,
  root8 1 1 2 2 1 1 1 0,
  root8 0 0 1 1 1 1 1 0,
  root8 0 1 1 1 1 1 1 0,
  root8 0 1 1 2 1 1 1 0,
  root8 0 1 1 2 2 1 1 0,
  root8 0 1 1 2 2 2 1 0,
  root8 0 1 0 1 1 1 1 0,
  root8 0 0 0 1 1 1 1 0,
  root8 0 0 0 0 1 1 1 0,
  root8 0 0 0 0 0 1 1 0,
  root8 0 0 0 0 0 0 1 0,
  root8 1 0 1 1 1 1 1 0,
  root8 1 1 1 1 1 1 1 0,
  root8 1 1 1 2 1 1 1 0,
  root8 1 1 1 2 2 1 1 0,
  root8 1 1 1 2 2 2 1 0,
  root8 1 2 3 4 3 2 1 0,
  root8 2 2 3 4 3 2 1 0]

private def rootTable : Vector (Vector RootVector 27) 3 :=
  #v[rootFamily0, rootFamily1, rootFamily2]

private def signTable : Vector (Vector ℤ 27) 3 :=
  #v[#v[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1],
    #v[-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1],
    #v[-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1]]

/-- Lexicographic number of an independent alternating coordinate. -/
def pairNumber (p : PairIndex) : Fin 10 :=
  let a := (fiveIndexEquiv p.val.1).val
  let b := (fiveIndexEquiv p.val.2).val
  ⟨if a = 0 then b - 1 else if a = 1 then b + 2 else if a = 2 then b + 4 else 9,
    by have hb := (fiveIndexEquiv p.val.2).isLt; split_ifs <;> omega⟩

/-- The local order is ten, dual five, five, dual five, two singlets. -/
def localNumber : LocalIndex → Fin 27
  | .inl (.inl p) => ⟨(pairNumber p).val, by have h := (pairNumber p).isLt; omega⟩
  | .inl (.inr q) => ⟨10 + (fiveIndexEquiv q).val,
      by have h := (fiveIndexEquiv q).isLt; omega⟩
  | .inr (.inl (.inl q)) => ⟨15 + (fiveIndexEquiv q).val,
      by have h := (fiveIndexEquiv q).isLt; omega⟩
  | .inr (.inl (.inr q)) => ⟨20 + (fiveIndexEquiv q).val,
      by have h := (fiveIndexEquiv q).isLt; omega⟩
  | .inr (.inr q) => ⟨25 + q.val, by have h := q.isLt; omega⟩

/-- The exceptional root assigned to each actual matter coordinate. -/
def rootOfLabel (i : MatterLabels.Index) : RootVector :=
  (rootTable[i.1])[localNumber i.2]

/-- The explicitly transported basis sign. -/
def signOfLabel (i : MatterLabels.Index) : ℤ :=
  (signTable[i.1])[localNumber i.2]

def rootLabel (i : MatterLabels.Index) : DataIndex := .inr (rootOfLabel i)

def basisData (i : MatterLabels.Index) : Sparse :=
  E8BracketData.singleton (rootLabel i) (signOfLabel i)

private def fiveLabels : List FiveIndex :=
  (List.finRange 5).map fiveIndexEquiv.symm

private def pairLabels : List PairIndex :=
  (List.finRange 5).flatMap fun i =>
    (List.finRange 5).filterMap fun j =>
      if h : i < j then
        some ⟨(fiveIndexEquiv.symm i, fiveIndexEquiv.symm j), by simpa using h⟩
      else none

private def localLabels : List LocalIndex :=
  pairLabels.map (fun p => .inl (.inl p)) ++
    fiveLabels.map (fun q => .inl (.inr q)) ++
    fiveLabels.map (fun q => .inr (.inl (.inl q))) ++
    fiveLabels.map (fun q => .inr (.inl (.inr q))) ++
    (List.finRange 2).map (fun q => .inr (.inr q))

/-- A computable enumeration of all target coordinates, with no repeated label. -/
def labelList : List MatterLabels.Index :=
  (List.finRange 3).flatMap fun i => localLabels.map fun j => (i, j)

theorem e8_matter_labelList_nodup : labelList.Nodup := by decide

theorem e8_matter_labelList_toFinset : labelList.toFinset = Finset.univ := by decide

/-- A target matrix column realized in the signed exceptional basis. -/
def matrixColumnData (c : MatterLabels.Index → ℤ) : Sparse :=
  labelList.filterMap fun r =>
    if c r = 0 then none else some (rootLabel r, c r * signOfLabel r)

theorem e8_matter_labels_injective : Function.Injective rootOfLabel := by
  native_decide

theorem e8_matter_labels_exact :
    (Finset.univ.image rootLabel) = gradeLabels 1 := by
  native_decide

theorem e8_matter_basis_sign_sq : ∀ i : MatterLabels.Index,
    signOfLabel i * signOfLabel i = 1 := by
  native_decide

theorem e8_matter_rootLabel_injective : Function.Injective rootLabel := by
  intro i j h
  exact e8_matter_labels_injective (Sum.inr.inj h)

theorem e8_matter_label_mem_grade (i : MatterLabels.Index) :
    rootLabel i ∈ gradeLabels 1 := by
  rw [← e8_matter_labels_exact]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem e8_matter_label_mem_basis (i : MatterLabels.Index) :
    rootLabel i ∈ basisList :=
  ((e8_mem_gradeLabels 1 _).mp (e8_matter_label_mem_grade i)).1

theorem e8_matter_label_grade (i : MatterLabels.Index) : grade (rootLabel i) = 1 :=
  ((e8_mem_gradeLabels 1 _).mp (e8_matter_label_mem_grade i)).2

/-- Every scaled A4 matrix unit has the exact existing matter-module action. -/
theorem e8_matter_a4_unit_match_certificate :
    ∀ (p q : Fin 5) (s : MatterLabels.Index),
      sparseEq (sparseBracket (unitData p q) (basisData s))
        (matrixColumnData (fun r => unitCoefficient p q r s)) = true := by
  native_decide

/-- Every scaled family unit acts on precisely the three-copy coordinate. -/
theorem e8_matter_family_unit_match_certificate :
    ∀ (p q : Fin 3) (s : MatterLabels.Index),
      sparseEq (sparseBracket (familyUnitData p q) (basisData s))
        (matrixColumnData (fun r => familyUnitCoefficient p q r s)) = true := by
  native_decide

end CubicAnomaly.Fixed.E8MatterData
