import CubicAnomaly.Fixed.E8RadicalIdentificationData

/-! Exact adjoint-action words for simplicity of the E₆ lattice algebra. -/

namespace CubicAnomaly.Fixed.E6Lattice

abbrev Word := List (Fin 72)
abbrev Expansion := List (Index × ℤ)

/-- Root-generator paths carrying the first simple root to each root. -/
private def outward : Vector Word 72 :=
  #v[[], [13, 1, 4], [23, 24], [16, 34], [4, 1], [13], [13, 16], [4, 23],
    [23, 28], [16, 35], [35, 40], [28, 45], [4], [13, 1], [13, 24], [4, 34],
    [16, 1], [23], [13, 28], [4, 35], [23, 40], [16, 45], [16], [23, 1],
    [24, 1], [13, 36], [34], [4, 44], [28, 1], [35], [13, 40], [4, 45],
    [24], [28], [34, 1], [35, 1], [36, 1], [13, 47], [44], [4, 53],
    [40, 1], [45], [36], [40], [44, 1], [45, 1], [46, 1], [47, 1],
    [52], [53], [46], [47], [52, 1], [53, 1], [54, 1], [59],
    [4, 46], [54], [13, 52], [59, 1], [60, 1], [65], [4, 54], [60],
    [13, 59], [65, 1], [4, 60], [13, 65], [16, 60], [23, 65], [24, 60], [34, 65]]

/-- Root-generator paths returning to the negative first simple root, followed
by two applications of the first root's adjoint. The last two brackets kill
every direction except that opposite root. -/
private def inward : Vector Word 72 :=
  #v[[13, 1, 4, 0, 0], [0, 0], [34, 16, 0, 0], [24, 23, 0, 0], [13, 0, 0], [1, 4, 0, 0], [23, 4, 0, 0], [16, 13, 0, 0],
    [35, 16, 0, 0], [28, 23, 0, 0], [45, 28, 0, 0], [40, 35, 0, 0], [1, 13, 0, 0], [4, 0, 0], [34, 4, 0, 0], [24, 13, 0, 0],
    [23, 0, 0], [1, 16, 0, 0], [35, 4, 0, 0], [28, 13, 0, 0], [45, 16, 0, 0], [40, 23, 0, 0], [1, 23, 0, 0], [16, 0, 0],
    [34, 0, 0], [44, 4, 0, 0], [1, 24, 0, 0], [36, 13, 0, 0], [35, 0, 0], [1, 28, 0, 0], [45, 4, 0, 0], [40, 13, 0, 0],
    [1, 34, 0, 0], [1, 35, 0, 0], [24, 0, 0], [28, 0, 0], [44, 0, 0], [53, 4, 0, 0], [1, 36, 0, 0], [47, 13, 0, 0],
    [45, 0, 0], [1, 40, 0, 0], [1, 44, 0, 0], [1, 45, 0, 0], [36, 0, 0], [40, 0, 0], [52, 0, 0], [53, 0, 0],
    [1, 46, 0, 0], [1, 47, 0, 0], [1, 52, 0, 0], [1, 53, 0, 0], [46, 0, 0], [47, 0, 0], [59, 0, 0], [1, 54, 0, 0],
    [52, 13, 0, 0], [1, 59, 0, 0], [46, 4, 0, 0], [54, 0, 0], [65, 0, 0], [1, 60, 0, 0], [59, 13, 0, 0], [1, 65, 0, 0],
    [54, 4, 0, 0], [60, 0, 0], [65, 13, 0, 0], [60, 4, 0, 0], [65, 23, 0, 0], [60, 16, 0, 0], [65, 34, 0, 0], [60, 24, 0, 0]]

/-- Coefficients that recover individual Cartan coordinates from simple-root
evaluations, accounting for the signs of the six returning paths. -/
private def dualCartan : Matrix (Fin 6) (Fin 6) ℤ :=
  !![-4, -3, 5, 6, 4, 2;
    -3, -6, 6, 9, 6, 3;
    -5, -6, 10, 12, 8, 4;
    -6, -9, 12, 18, 12, 6;
    -4, -6, 8, 12, 10, 5;
    -2, -3, 4, 6, 5, 4]

private def simple (i : Fin 6) : Fin 72 := ⟨2 * i.val, by omega⟩
private def negSimple (i : Fin 6) : Fin 72 := ⟨2 * i.val + 1, by omega⟩

def generateWord : Index → Word
  | .inr r => outward[r]
  | .inl i => outward[simple i] ++ [negSimple i]

def coordinateWords : Index → List (ℤ × Word)
  | .inr r => [(1, inward[r])]
  | .inl i => (List.finRange 6).map fun j => (dualCartan i j, simple j :: inward[simple j])

def applyRoot (r : Fin 72) (xs : Expansion) : Expansion :=
  xs.flatMap fun p => (products (.inr r) p.1).map fun q => (q.1, p.2 * q.2)

def applyWord : Word → Expansion → Expansion
  | [], xs => xs
  | r :: w, xs => applyWord w (applyRoot r xs)

def applyWords (ws : List (ℤ × Word)) (xs : Expansion) : Expansion :=
  ws.flatMap fun p => (applyWord p.2 xs).map fun q => (q.1, p.1 * q.2)

def coeff (xs : Expansion) (i : Index) : ℤ :=
  (xs.map fun p => if p.1 = i then p.2 else 0).sum

/-- Equality of sparse sums, checking every label occurring on either side. -/
def equal (xs ys : Expansion) : Bool :=
  (xs ++ ys).all fun p => coeff xs p.1 == coeff ys p.1

def firstRoot : Index := .inr 0

def generateCoeff (i : Index) : ℤ := coeff (applyWord (generateWord i) [(firstRoot, 1)]) i
def coordinateCoeff (i : Index) : ℤ := coeff (applyWords (coordinateWords i) [(i, 1)]) firstRoot

/-- The first root generates all directions. Conversely there is a linear
combination of adjoint words extracting each coordinate into that first root. -/
theorem e6_adjoint_words_certificate :
    products (.inl 0) firstRoot = [(firstRoot, 2)] ∧
    (∀ i, generateCoeff i ≠ 0 ∧
      equal (applyWord (generateWord i) [(firstRoot, 1)]) [(i, generateCoeff i)] = true) ∧
    (∀ i, coordinateCoeff i ≠ 0 ∧ ∀ j,
      equal (applyWords (coordinateWords i) [(j, 1)])
        [(firstRoot, if i = j then coordinateCoeff i else 0)] = true) := by
  native_decide

end CubicAnomaly.Fixed.E6Lattice
