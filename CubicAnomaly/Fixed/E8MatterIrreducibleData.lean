import CubicAnomaly.Fixed.E8MatterData

/-!
# Finite spectral and rooted-tree certificates for the actual exceptional half

The diagonal is an explicit integer Cartan combination. Every tree edge is
an actual degree-zero root vector, and its two directions act nontrivially
between the displayed signed matter basis vectors.
-/

namespace CubicAnomaly.Fixed.E8MatterIrreducibleData

open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8A4Data
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8MatterData

private theorem labelList_length : labelList.length = 81 := by decide

def labelAt (i : Fin 81) : MatterLabels.Index :=
  labelList[i.val]'(by rw [labelList_length]; exact i.isLt)

def number (i : MatterLabels.Index) : Fin 81 :=
  ⟨27 * i.1.val + (localNumber i.2).val,
    by have hf := i.1.isLt; have hl := (localNumber i.2).isLt; omega⟩

private def parentTable : Vector (Fin 81) 81 := #v[0, 0, 1, 2, 1, 4, 5, 5, 7, 8, 11, 12, 13, 14, 24, 11, 10, 16, 17, 18, 21, 22, 23, 24, 7, 0, 25, 0, 27, 28, 29, 28, 31, 32, 32, 34, 35, 38, 39, 40, 41, 51, 38, 37, 43, 44, 45, 48, 49, 50, 51, 34, 27, 52, 27, 54, 55, 56, 55, 58, 59, 59, 61, 62, 65, 66, 67, 68, 78, 65, 64, 70, 71, 72, 75, 76, 77, 78, 61, 54, 79]

private def rankTable : Vector ℕ 81 := #v[0, 2, 5, 7, 4, 6, 9, 8, 11, 14, 21, 19, 17, 15, 12, 22, 23, 24, 25, 26, 20, 18, 16, 13, 10, 1, 3, 27, 29, 32, 34, 31, 33, 36, 35, 38, 41, 48, 46, 44, 42, 39, 49, 50, 51, 52, 53, 47, 45, 43, 40, 37, 28, 30, 54, 56, 59, 61, 58, 60, 63, 62, 65, 68, 75, 73, 71, 69, 66, 76, 77, 78, 79, 80, 74, 72, 70, 67, 64, 55, 57]

def baseLabel : MatterLabels.Index := labelAt 0

def parent (i : MatterLabels.Index) : MatterLabels.Index := labelAt parentTable[number i]

def rank (i : MatterLabels.Index) : ℕ := rankTable[number i]

/-- The separating Cartan combination, in the signed zero-root basis. -/
def diagonalData : Sparse :=
  (List.finRange 8).map fun j => (.inl j, (3 : ℤ) ^ j.val * diagramSign j)

def eigenvalue (i : MatterLabels.Index) : ℤ :=
  ∑ j : Fin 8, (3 : ℤ) ^ j.val * pairSimple (rootOfLabel i) j

/-- The root joining a vertex to its already reached parent. -/
def edgeRoot (i : MatterLabels.Index) : RootVector :=
  subVector (rootOfLabel i) (rootOfLabel (parent i))

def forwardData (i : MatterLabels.Index) : Sparse :=
  E8BracketData.singleton (.inr (edgeRoot i)) 1

def reverseData (i : MatterLabels.Index) : Sparse :=
  E8BracketData.singleton (.inr (negateVector (edgeRoot i))) 1

def forwardCoefficient (i : MatterLabels.Index) : ℤ :=
  coefficient (sparseBracket (forwardData i) (basisData (parent i))) (rootLabel i) *
    signOfLabel i

def reverseCoefficient (i : MatterLabels.Index) : ℤ :=
  coefficient (sparseBracket (reverseData i) (basisData i)) (rootLabel (parent i)) *
    signOfLabel (parent i)

/-- The explicit Cartan element has a distinct integer eigenvalue on every
one of the eighty-one signed basis vectors. -/
theorem e8_matter_separating_diagonal_certificate :
    supported diagonalData = true ∧
    diagonalData.all (fun p => grade p.1 == 0) = true ∧
    Function.Injective eigenvalue ∧
    ∀ i : MatterLabels.Index,
      sparseEq (sparseBracket diagonalData (basisData i))
        (scale (eigenvalue i) (basisData i)) = true := by
  native_decide

/-- Each non-base label has a strictly earlier parent and actual nonzero
root actions in both directions, entirely inside degree zero. -/
theorem e8_matter_action_tree_certificate :
    ∀ i : MatterLabels.Index, i ≠ baseLabel →
      rank (parent i) < rank i ∧
      supported (forwardData i) = true ∧
      supported (reverseData i) = true ∧
      (forwardData i).all (fun p => grade p.1 == 0) = true ∧
      (reverseData i).all (fun p => grade p.1 == 0) = true ∧
      forwardCoefficient i ≠ 0 ∧ reverseCoefficient i ≠ 0 ∧
      sparseEq (sparseBracket (forwardData i) (basisData (parent i)))
        (scale (forwardCoefficient i) (basisData i)) = true ∧
      sparseEq (sparseBracket (reverseData i) (basisData i))
        (scale (reverseCoefficient i) (basisData (parent i))) = true := by
  native_decide

end CubicAnomaly.Fixed.E8MatterIrreducibleData
