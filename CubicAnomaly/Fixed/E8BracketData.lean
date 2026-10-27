import Mathlib.Data.Matrix.Cartan
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic
import Std.Data.HashMap.Basic

/-!
# Exact sparse data for the fixed exceptional adjoint matching

The entries below are witnesses, not assumptions. Finite certificates check
their signs, support, generator images, and compatibility of the candidate
bilinear bracket with every simple generator. The semantic realization is
handled separately; no Jacobi identity is assumed here.
-/

namespace CubicAnomaly.Fixed.E8BracketData

open scoped BigOperators

abbrev RootVector := Vector ℤ 8
abbrev DataIndex := Fin 8 ⊕ RootVector
abbrev Sparse := List (DataIndex × ℤ)

instance : Hashable RootVector where
  hash v := hash v.toArray

private def root8 (a b c d e f g h : ℤ) : RootVector :=
  #v[a, b, c, d, e, f, g, h]

private def signBlock0 : List (RootVector × ℤ) := [
  (root8 (-2) (-3) (-4) (-6) (-5) (-4) (-3) (-2), -1),
  (root8 (-2) (-3) (-4) (-6) (-5) (-4) (-3) (-1), 1),
  (root8 (-2) (-3) (-4) (-6) (-5) (-4) (-2) (-1), -1),
  (root8 (-2) (-3) (-4) (-6) (-5) (-3) (-2) (-1), 1),
  (root8 (-2) (-3) (-4) (-6) (-4) (-3) (-2) (-1), -1),
  (root8 (-2) (-3) (-4) (-5) (-4) (-3) (-2) (-1), 1),
  (root8 (-2) (-3) (-3) (-5) (-4) (-3) (-2) (-1), 1),
  (root8 (-2) (-2) (-4) (-5) (-4) (-3) (-2) (-1), -1),
  (root8 (-2) (-2) (-3) (-5) (-4) (-3) (-2) (-1), -1),
  (root8 (-2) (-2) (-3) (-4) (-4) (-3) (-2) (-1), -1)
]

private def signBlock1 : List (RootVector × ℤ) := [
  (root8 (-2) (-2) (-3) (-4) (-3) (-3) (-2) (-1), -1),
  (root8 (-2) (-2) (-3) (-4) (-3) (-2) (-2) (-1), -1),
  (root8 (-2) (-2) (-3) (-4) (-3) (-2) (-1) (-1), -1),
  (root8 (-2) (-2) (-3) (-4) (-3) (-2) (-1) 0, -1),
  (root8 (-1) (-3) (-3) (-5) (-4) (-3) (-2) (-1), 1),
  (root8 (-1) (-2) (-3) (-5) (-4) (-3) (-2) (-1), -1),
  (root8 (-1) (-2) (-3) (-4) (-4) (-3) (-2) (-1), -1),
  (root8 (-1) (-2) (-3) (-4) (-3) (-3) (-2) (-1), -1),
  (root8 (-1) (-2) (-3) (-4) (-3) (-2) (-2) (-1), -1),
  (root8 (-1) (-2) (-3) (-4) (-3) (-2) (-1) (-1), -1)
]

private def signBlock2 : List (RootVector × ℤ) := [
  (root8 (-1) (-2) (-3) (-4) (-3) (-2) (-1) 0, -1),
  (root8 (-1) (-2) (-2) (-4) (-4) (-3) (-2) (-1), -1),
  (root8 (-1) (-2) (-2) (-4) (-3) (-3) (-2) (-1), -1),
  (root8 (-1) (-2) (-2) (-4) (-3) (-2) (-2) (-1), -1),
  (root8 (-1) (-2) (-2) (-4) (-3) (-2) (-1) (-1), -1),
  (root8 (-1) (-2) (-2) (-4) (-3) (-2) (-1) 0, -1),
  (root8 (-1) (-2) (-2) (-3) (-3) (-3) (-2) (-1), -1),
  (root8 (-1) (-2) (-2) (-3) (-3) (-2) (-2) (-1), -1),
  (root8 (-1) (-2) (-2) (-3) (-3) (-2) (-1) (-1), -1),
  (root8 (-1) (-2) (-2) (-3) (-3) (-2) (-1) 0, -1)
]

private def signBlock3 : List (RootVector × ℤ) := [
  (root8 (-1) (-2) (-2) (-3) (-2) (-2) (-2) (-1), -1),
  (root8 (-1) (-2) (-2) (-3) (-2) (-2) (-1) (-1), -1),
  (root8 (-1) (-2) (-2) (-3) (-2) (-2) (-1) 0, -1),
  (root8 (-1) (-2) (-2) (-3) (-2) (-1) (-1) (-1), -1),
  (root8 (-1) (-2) (-2) (-3) (-2) (-1) (-1) 0, -1),
  (root8 (-1) (-2) (-2) (-3) (-2) (-1) 0 0, -1),
  (root8 (-1) (-1) (-2) (-3) (-3) (-3) (-2) (-1), -1),
  (root8 (-1) (-1) (-2) (-3) (-3) (-2) (-2) (-1), -1),
  (root8 (-1) (-1) (-2) (-3) (-3) (-2) (-1) (-1), -1),
  (root8 (-1) (-1) (-2) (-3) (-3) (-2) (-1) 0, -1)
]

private def signBlock4 : List (RootVector × ℤ) := [
  (root8 (-1) (-1) (-2) (-3) (-2) (-2) (-2) (-1), -1),
  (root8 (-1) (-1) (-2) (-3) (-2) (-2) (-1) (-1), -1),
  (root8 (-1) (-1) (-2) (-3) (-2) (-2) (-1) 0, -1),
  (root8 (-1) (-1) (-2) (-3) (-2) (-1) (-1) (-1), -1),
  (root8 (-1) (-1) (-2) (-3) (-2) (-1) (-1) 0, -1),
  (root8 (-1) (-1) (-2) (-3) (-2) (-1) 0 0, -1),
  (root8 (-1) (-1) (-2) (-2) (-2) (-2) (-2) (-1), -1),
  (root8 (-1) (-1) (-2) (-2) (-2) (-2) (-1) (-1), -1),
  (root8 (-1) (-1) (-2) (-2) (-2) (-2) (-1) 0, -1),
  (root8 (-1) (-1) (-2) (-2) (-2) (-1) (-1) (-1), -1)
]

private def signBlock5 : List (RootVector × ℤ) := [
  (root8 (-1) (-1) (-2) (-2) (-2) (-1) (-1) 0, -1),
  (root8 (-1) (-1) (-2) (-2) (-2) (-1) 0 0, -1),
  (root8 (-1) (-1) (-2) (-2) (-1) (-1) (-1) (-1), -1),
  (root8 (-1) (-1) (-2) (-2) (-1) (-1) (-1) 0, -1),
  (root8 (-1) (-1) (-2) (-2) (-1) (-1) 0 0, -1),
  (root8 (-1) (-1) (-2) (-2) (-1) 0 0 0, -1),
  (root8 (-1) (-1) (-1) (-2) (-2) (-2) (-2) (-1), 1),
  (root8 (-1) (-1) (-1) (-2) (-2) (-2) (-1) (-1), 1),
  (root8 (-1) (-1) (-1) (-2) (-2) (-2) (-1) 0, 1),
  (root8 (-1) (-1) (-1) (-2) (-2) (-1) (-1) (-1), 1)
]

private def signBlock6 : List (RootVector × ℤ) := [
  (root8 (-1) (-1) (-1) (-2) (-2) (-1) (-1) 0, 1),
  (root8 (-1) (-1) (-1) (-2) (-2) (-1) 0 0, 1),
  (root8 (-1) (-1) (-1) (-2) (-1) (-1) (-1) (-1), 1),
  (root8 (-1) (-1) (-1) (-2) (-1) (-1) (-1) 0, 1),
  (root8 (-1) (-1) (-1) (-2) (-1) (-1) 0 0, 1),
  (root8 (-1) (-1) (-1) (-2) (-1) 0 0 0, 1),
  (root8 (-1) (-1) (-1) (-1) (-1) (-1) (-1) (-1), 1),
  (root8 (-1) (-1) (-1) (-1) (-1) (-1) (-1) 0, 1),
  (root8 (-1) (-1) (-1) (-1) (-1) (-1) 0 0, 1),
  (root8 (-1) (-1) (-1) (-1) (-1) 0 0 0, 1)
]

private def signBlock7 : List (RootVector × ℤ) := [
  (root8 (-1) (-1) (-1) (-1) 0 0 0 0, 1),
  (root8 (-1) 0 (-1) (-1) (-1) (-1) (-1) (-1), -1),
  (root8 (-1) 0 (-1) (-1) (-1) (-1) (-1) 0, -1),
  (root8 (-1) 0 (-1) (-1) (-1) (-1) 0 0, -1),
  (root8 (-1) 0 (-1) (-1) (-1) 0 0 0, -1),
  (root8 (-1) 0 (-1) (-1) 0 0 0 0, -1),
  (root8 (-1) 0 (-1) 0 0 0 0 0, -1),
  (root8 (-1) 0 0 0 0 0 0 0, -1),
  (root8 0 (-1) (-1) (-2) (-2) (-2) (-2) (-1), -1),
  (root8 0 (-1) (-1) (-2) (-2) (-2) (-1) (-1), -1)
]

private def signBlock8 : List (RootVector × ℤ) := [
  (root8 0 (-1) (-1) (-2) (-2) (-2) (-1) 0, -1),
  (root8 0 (-1) (-1) (-2) (-2) (-1) (-1) (-1), -1),
  (root8 0 (-1) (-1) (-2) (-2) (-1) (-1) 0, -1),
  (root8 0 (-1) (-1) (-2) (-2) (-1) 0 0, -1),
  (root8 0 (-1) (-1) (-2) (-1) (-1) (-1) (-1), -1),
  (root8 0 (-1) (-1) (-2) (-1) (-1) (-1) 0, -1),
  (root8 0 (-1) (-1) (-2) (-1) (-1) 0 0, -1),
  (root8 0 (-1) (-1) (-2) (-1) 0 0 0, -1),
  (root8 0 (-1) (-1) (-1) (-1) (-1) (-1) (-1), -1),
  (root8 0 (-1) (-1) (-1) (-1) (-1) (-1) 0, -1)
]

private def signBlock9 : List (RootVector × ℤ) := [
  (root8 0 (-1) (-1) (-1) (-1) (-1) 0 0, -1),
  (root8 0 (-1) (-1) (-1) (-1) 0 0 0, -1),
  (root8 0 (-1) (-1) (-1) 0 0 0 0, -1),
  (root8 0 (-1) 0 (-1) (-1) (-1) (-1) (-1), 1),
  (root8 0 (-1) 0 (-1) (-1) (-1) (-1) 0, 1),
  (root8 0 (-1) 0 (-1) (-1) (-1) 0 0, 1),
  (root8 0 (-1) 0 (-1) (-1) 0 0 0, 1),
  (root8 0 (-1) 0 (-1) 0 0 0 0, 1),
  (root8 0 (-1) 0 0 0 0 0 0, 1),
  (root8 0 0 (-1) (-1) (-1) (-1) (-1) (-1), 1)
]

private def signBlock10 : List (RootVector × ℤ) := [
  (root8 0 0 (-1) (-1) (-1) (-1) (-1) 0, 1),
  (root8 0 0 (-1) (-1) (-1) (-1) 0 0, 1),
  (root8 0 0 (-1) (-1) (-1) 0 0 0, 1),
  (root8 0 0 (-1) (-1) 0 0 0 0, 1),
  (root8 0 0 (-1) 0 0 0 0 0, 1),
  (root8 0 0 0 (-1) (-1) (-1) (-1) (-1), -1),
  (root8 0 0 0 (-1) (-1) (-1) (-1) 0, -1),
  (root8 0 0 0 (-1) (-1) (-1) 0 0, -1),
  (root8 0 0 0 (-1) (-1) 0 0 0, -1),
  (root8 0 0 0 (-1) 0 0 0 0, -1)
]

private def signBlock11 : List (RootVector × ℤ) := [
  (root8 0 0 0 0 (-1) (-1) (-1) (-1), 1),
  (root8 0 0 0 0 (-1) (-1) (-1) 0, 1),
  (root8 0 0 0 0 (-1) (-1) 0 0, 1),
  (root8 0 0 0 0 (-1) 0 0 0, 1),
  (root8 0 0 0 0 0 (-1) (-1) (-1), -1),
  (root8 0 0 0 0 0 (-1) (-1) 0, -1),
  (root8 0 0 0 0 0 (-1) 0 0, -1),
  (root8 0 0 0 0 0 0 (-1) (-1), 1),
  (root8 0 0 0 0 0 0 (-1) 0, 1),
  (root8 0 0 0 0 0 0 0 (-1), -1)
]

private def signBlock12 : List (RootVector × ℤ) := [
  (root8 0 0 0 0 0 0 0 1, -1),
  (root8 0 0 0 0 0 0 1 0, 1),
  (root8 0 0 0 0 0 0 1 1, -1),
  (root8 0 0 0 0 0 1 0 0, -1),
  (root8 0 0 0 0 0 1 1 0, 1),
  (root8 0 0 0 0 0 1 1 1, -1),
  (root8 0 0 0 0 1 0 0 0, 1),
  (root8 0 0 0 0 1 1 0 0, -1),
  (root8 0 0 0 0 1 1 1 0, 1),
  (root8 0 0 0 0 1 1 1 1, -1)
]

private def signBlock13 : List (RootVector × ℤ) := [
  (root8 0 0 0 1 0 0 0 0, -1),
  (root8 0 0 0 1 1 0 0 0, 1),
  (root8 0 0 0 1 1 1 0 0, -1),
  (root8 0 0 0 1 1 1 1 0, 1),
  (root8 0 0 0 1 1 1 1 1, -1),
  (root8 0 0 1 0 0 0 0 0, 1),
  (root8 0 0 1 1 0 0 0 0, -1),
  (root8 0 0 1 1 1 0 0 0, 1),
  (root8 0 0 1 1 1 1 0 0, -1),
  (root8 0 0 1 1 1 1 1 0, 1)
]

private def signBlock14 : List (RootVector × ℤ) := [
  (root8 0 0 1 1 1 1 1 1, -1),
  (root8 0 1 0 0 0 0 0 0, 1),
  (root8 0 1 0 1 0 0 0 0, -1),
  (root8 0 1 0 1 1 0 0 0, 1),
  (root8 0 1 0 1 1 1 0 0, -1),
  (root8 0 1 0 1 1 1 1 0, 1),
  (root8 0 1 0 1 1 1 1 1, -1),
  (root8 0 1 1 1 0 0 0 0, -1),
  (root8 0 1 1 1 1 0 0 0, 1),
  (root8 0 1 1 1 1 1 0 0, -1)
]

private def signBlock15 : List (RootVector × ℤ) := [
  (root8 0 1 1 1 1 1 1 0, 1),
  (root8 0 1 1 1 1 1 1 1, -1),
  (root8 0 1 1 2 1 0 0 0, -1),
  (root8 0 1 1 2 1 1 0 0, 1),
  (root8 0 1 1 2 1 1 1 0, -1),
  (root8 0 1 1 2 1 1 1 1, 1),
  (root8 0 1 1 2 2 1 0 0, -1),
  (root8 0 1 1 2 2 1 1 0, 1),
  (root8 0 1 1 2 2 1 1 1, -1),
  (root8 0 1 1 2 2 2 1 0, -1)
]

private def signBlock16 : List (RootVector × ℤ) := [
  (root8 0 1 1 2 2 2 1 1, 1),
  (root8 0 1 1 2 2 2 2 1, -1),
  (root8 1 0 0 0 0 0 0 0, -1),
  (root8 1 0 1 0 0 0 0 0, 1),
  (root8 1 0 1 1 0 0 0 0, -1),
  (root8 1 0 1 1 1 0 0 0, 1),
  (root8 1 0 1 1 1 1 0 0, -1),
  (root8 1 0 1 1 1 1 1 0, 1),
  (root8 1 0 1 1 1 1 1 1, -1),
  (root8 1 1 1 1 0 0 0 0, -1)
]

private def signBlock17 : List (RootVector × ℤ) := [
  (root8 1 1 1 1 1 0 0 0, 1),
  (root8 1 1 1 1 1 1 0 0, -1),
  (root8 1 1 1 1 1 1 1 0, 1),
  (root8 1 1 1 1 1 1 1 1, -1),
  (root8 1 1 1 2 1 0 0 0, -1),
  (root8 1 1 1 2 1 1 0 0, 1),
  (root8 1 1 1 2 1 1 1 0, -1),
  (root8 1 1 1 2 1 1 1 1, 1),
  (root8 1 1 1 2 2 1 0 0, -1),
  (root8 1 1 1 2 2 1 1 0, 1)
]

private def signBlock18 : List (RootVector × ℤ) := [
  (root8 1 1 1 2 2 1 1 1, -1),
  (root8 1 1 1 2 2 2 1 0, -1),
  (root8 1 1 1 2 2 2 1 1, 1),
  (root8 1 1 1 2 2 2 2 1, -1),
  (root8 1 1 2 2 1 0 0 0, -1),
  (root8 1 1 2 2 1 1 0 0, 1),
  (root8 1 1 2 2 1 1 1 0, -1),
  (root8 1 1 2 2 1 1 1 1, 1),
  (root8 1 1 2 2 2 1 0 0, -1),
  (root8 1 1 2 2 2 1 1 0, 1)
]

private def signBlock19 : List (RootVector × ℤ) := [
  (root8 1 1 2 2 2 1 1 1, -1),
  (root8 1 1 2 2 2 2 1 0, -1),
  (root8 1 1 2 2 2 2 1 1, 1),
  (root8 1 1 2 2 2 2 2 1, -1),
  (root8 1 1 2 3 2 1 0 0, 1),
  (root8 1 1 2 3 2 1 1 0, -1),
  (root8 1 1 2 3 2 1 1 1, 1),
  (root8 1 1 2 3 2 2 1 0, 1),
  (root8 1 1 2 3 2 2 1 1, -1),
  (root8 1 1 2 3 2 2 2 1, 1)
]

private def signBlock20 : List (RootVector × ℤ) := [
  (root8 1 1 2 3 3 2 1 0, -1),
  (root8 1 1 2 3 3 2 1 1, 1),
  (root8 1 1 2 3 3 2 2 1, -1),
  (root8 1 1 2 3 3 3 2 1, 1),
  (root8 1 2 2 3 2 1 0 0, -1),
  (root8 1 2 2 3 2 1 1 0, 1),
  (root8 1 2 2 3 2 1 1 1, -1),
  (root8 1 2 2 3 2 2 1 0, -1),
  (root8 1 2 2 3 2 2 1 1, 1),
  (root8 1 2 2 3 2 2 2 1, -1)
]

private def signBlock21 : List (RootVector × ℤ) := [
  (root8 1 2 2 3 3 2 1 0, 1),
  (root8 1 2 2 3 3 2 1 1, -1),
  (root8 1 2 2 3 3 2 2 1, 1),
  (root8 1 2 2 3 3 3 2 1, -1),
  (root8 1 2 2 4 3 2 1 0, -1),
  (root8 1 2 2 4 3 2 1 1, 1),
  (root8 1 2 2 4 3 2 2 1, -1),
  (root8 1 2 2 4 3 3 2 1, 1),
  (root8 1 2 2 4 4 3 2 1, -1),
  (root8 1 2 3 4 3 2 1 0, 1)
]

private def signBlock22 : List (RootVector × ℤ) := [
  (root8 1 2 3 4 3 2 1 1, -1),
  (root8 1 2 3 4 3 2 2 1, 1),
  (root8 1 2 3 4 3 3 2 1, -1),
  (root8 1 2 3 4 4 3 2 1, 1),
  (root8 1 2 3 5 4 3 2 1, -1),
  (root8 1 3 3 5 4 3 2 1, -1),
  (root8 2 2 3 4 3 2 1 0, -1),
  (root8 2 2 3 4 3 2 1 1, 1),
  (root8 2 2 3 4 3 2 2 1, -1),
  (root8 2 2 3 4 3 3 2 1, 1)
]

private def signBlock23 : List (RootVector × ℤ) := [
  (root8 2 2 3 4 4 3 2 1, -1),
  (root8 2 2 3 5 4 3 2 1, 1),
  (root8 2 2 4 5 4 3 2 1, -1),
  (root8 2 3 3 5 4 3 2 1, 1),
  (root8 2 3 4 5 4 3 2 1, -1),
  (root8 2 3 4 6 4 3 2 1, -1),
  (root8 2 3 4 6 5 3 2 1, -1),
  (root8 2 3 4 6 5 4 2 1, -1),
  (root8 2 3 4 6 5 4 3 1, -1),
  (root8 2 3 4 6 5 4 3 2, -1)
]

/-- Root coordinates and a verified change of basis to lattice-cocycle signs. -/
def signEntries : List (RootVector × ℤ) :=
  [signBlock0, signBlock1, signBlock2, signBlock3, signBlock4, signBlock5, signBlock6, signBlock7, signBlock8, signBlock9, signBlock10, signBlock11, signBlock12, signBlock13, signBlock14, signBlock15, signBlock16, signBlock17, signBlock18, signBlock19, signBlock20, signBlock21, signBlock22, signBlock23].flatten

def rootList : List RootVector := signEntries.map Prod.fst

def signMap : Std.HashMap RootVector ℤ := Std.HashMap.ofList signEntries

def rootSign (v : RootVector) : ℤ := signMap.getD v 0

def isRoot (v : RootVector) : Bool := signMap.contains v

def basisList : List DataIndex :=
  (List.finRange 8).map Sum.inl ++ rootList.map Sum.inr

def simpleVector (i : Fin 8) : RootVector := Vector.ofFn (Pi.single i 1)

def negateVector (v : RootVector) : RootVector := Vector.ofFn fun i => -v[i]

def addVector (v w : RootVector) : RootVector := Vector.ofFn fun i => v[i] + w[i]

def subVector (v w : RootVector) : RootVector := Vector.ofFn fun i => v[i] - w[i]

def diagramSign (i : Fin 8) : ℤ := (#v[1, -1, -1, 1, -1, 1, -1, 1] : RootVector)[i]

def pairSimple (v : RootVector) (i : Fin 8) : ℤ :=
  ∑ j : Fin 8, v[j] * CartanMatrix.E₈ j i

/-- A lower-triangular integral half of the even Cartan form. -/
def cocyclePair (v w : RootVector) : ℤ :=
  ∑ i : Fin 8, v[i] * (w[i] +
    ∑ j : Fin 8, if j.val < i.val then CartanMatrix.E₈ i j * w[j] else 0)

def cocycleSign (v w : RootVector) : ℤ :=
  if cocyclePair v w % 2 = 0 then 1 else -1

def singleton (i : DataIndex) (c : ℤ) : Sparse := [(i, c)]

def scale (c : ℤ) (v : Sparse) : Sparse := v.map fun p => (p.1, c * p.2)

def coefficient (v : Sparse) (i : DataIndex) : ℤ :=
  (v.map fun p => if p.1 = i then p.2 else 0).sum

def applySparse (f : DataIndex → Sparse) (v : Sparse) : Sparse :=
  v.flatMap fun p => scale p.2 (f p.1)

def sparseEq (v w : Sparse) : Bool :=
  (v ++ w).all fun p => coefficient v p.1 == coefficient w p.1

def supported (v : Sparse) : Bool := v.all fun p => basisList.contains p.1

/-- Candidate bracket written in the same signed zero/root basis as Geck. -/
def bracket : DataIndex → DataIndex → Sparse
  | .inl _, .inl _ => []
  | .inl i, .inr v => singleton (.inr v) (diagramSign i * pairSimple v i)
  | .inr v, .inl j => singleton (.inr v) (-diagramSign j * pairSimple v j)
  | .inr v, .inr w =>
    if w = negateVector v then
      (List.finRange 8).map fun i =>
        (.inl i, -rootSign v * rootSign w * v[i] * diagramSign i)
    else
      let u := addVector v w
      if isRoot u then
        singleton (.inr u) (rootSign v * rootSign w * rootSign u * cocycleSign v w)
      else []

def genH (i : Fin 8) : DataIndex → Sparse
  | .inl _ => []
  | .inr v => singleton (.inr v) (pairSimple v i)

def genE (i : Fin 8) : DataIndex → Sparse
  | .inl j => singleton (.inr (simpleVector i)) |CartanMatrix.E₈ i j|
  | .inr v =>
    if v = negateVector (simpleVector i) then singleton (.inl i) 1
    else
      let w := addVector (simpleVector i) v
      if isRoot w then singleton (.inr w) 1 else []

def genF (i : Fin 8) : DataIndex → Sparse
  | .inl j => singleton (.inr (negateVector (simpleVector i))) |CartanMatrix.E₈ i j|
  | .inr v =>
    if v = simpleVector i then singleton (.inl i) 1
    else
      let w := subVector v (simpleVector i)
      if isRoot w then singleton (.inr w) 1 else []

def derivationCheck (g : DataIndex → Sparse) (x y : DataIndex) : Bool :=
  sparseEq (applySparse g (bracket x y))
    (applySparse (fun z => bracket z y) (g x) ++
      applySparse (bracket x) (g y))

def signCheck : Bool :=
  rootList.all (fun v => (rootSign v == 1 || rootSign v == -1)) &&
  (List.finRange 8).all (fun i =>
    rootList.contains (simpleVector i) && rootList.contains (negateVector (simpleVector i)) &&
    rootSign (simpleVector i) == -diagramSign i &&
    rootSign (negateVector (simpleVector i)) == -diagramSign i)

def supportCheck : Bool :=
  basisList.all (fun x => basisList.all fun y => supported (bracket x y)) &&
  (List.finRange 8).all (fun i => basisList.all fun x =>
    supported (genH i x) && supported (genE i x) && supported (genF i x))

def generatorImageCheck : Bool :=
  (List.finRange 8).all fun i => basisList.all fun x =>
    sparseEq (bracket (.inl i) x) (scale (diagramSign i) (genH i x)) &&
    sparseEq (bracket (.inr (simpleVector i)) x) (scale (-diagramSign i) (genE i x)) &&
    sparseEq (bracket (.inr (negateVector (simpleVector i))) x)
      (scale (diagramSign i) (genF i x))

def generatorDerivationCheck : Bool :=
  (List.finRange 8).all fun i => basisList.all fun x => basisList.all fun y =>
    derivationCheck (genH i) x y && derivationCheck (genE i) x y &&
    derivationCheck (genF i) x y

theorem bracket_data_root_list_nodup : rootList.Nodup := by native_decide

theorem bracket_data_root_list_length : rootList.length = 240 := by rfl

theorem bracket_data_sign_certificate : signCheck = true := by native_decide

theorem bracket_data_support_certificate : supportCheck = true := by native_decide

theorem bracket_data_generator_image_certificate : generatorImageCheck = true := by native_decide

theorem bracket_data_generator_derivation_certificate : generatorDerivationCheck = true := by
  native_decide

end CubicAnomaly.Fixed.E8BracketData
