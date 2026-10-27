import CubicAnomaly.Fixed.E8Adjoints

/-!
# Integer-coordinate formulas for the actual exceptional generators

The actual Geck matrices are reindexed by the eight simple coordinates and
the actual root vectors. Norm-two root strings make their root-shift entries
equal to one. These formulas connect sparse integer data to the constructed
complex representation without assuming the representation's matrix entries.
-/

namespace CubicAnomaly.Fixed.E8GeneratorCoordinates

open Matrix
open CubicAnomaly.Fixed.E8RootPairing
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8Adjoints
open RootPairing.GeckConstruction

noncomputable section

abbrev CoordIndex := Fin 8 ⊕ Root

/-- The actual simple-base indexing equivalence, extended by the root identity. -/
def coordIndexEquiv : CoordIndex ≃ Index :=
  Equiv.sumCongr simpleIndexEquiv (Equiv.refl Root)

/-- An actual matrix expressed in the fixed coordinate labels. -/
def coordinateMatrix (A : Matrix Index Index ℂ) : Matrix CoordIndex CoordIndex ℂ :=
  A.submatrix coordIndexEquiv coordIndexEquiv

/-- Integer pairings of the actual root system are the literal coordinate form. -/
theorem e8_pairingIn_coordinates (x y : Root) :
    rootPairing.pairingIn ℤ x y = innerZ x.val y.val := by
  apply Int.cast_injective (α := ℂ)
  change algebraMap ℤ ℂ (rootPairing.pairingIn ℤ x y) = _
  rw [rootPairing.algebraMap_pairingIn, rootPairing_pairing]

theorem e8_negative_simple_coordinates (i : Fin 8) :
    (rootPairing.reflectionPerm (simpleRoot i) (simpleRoot i)).val =
      -(Pi.single i (1 : ℤ)) := by
  change reflectZ (Pi.single i 1) (Pi.single i 1) = _
  rw [reflectZ_eq, coordinateRoots_norm_two _ (simpleRoots_mem i)]
  module

private theorem e8_root_eq_simple_iff (x : Root) (i : Fin 8) :
    x = simpleRoot i ↔ x.val = Pi.single i (1 : ℤ) :=
  Subtype.ext_iff

private theorem simpleIndex_root (i : Fin 8) :
    (simpleIndex i : Root) = simpleRoot i := rfl

private theorem e8_root_eq_negative_simple_iff (x : Root) (i : Fin 8) :
    x = rootPairing.reflectionPerm (simpleRoot i) (simpleRoot i) ↔
      x.val = -(Pi.single i (1 : ℤ)) := by
  rw [Subtype.ext_iff, e8_negative_simple_coordinates]

private theorem e8_root_add_coordinates (x y : Root) (i : Fin 8) :
    rootPairing.root x = rootPairing.root (simpleRoot i) + rootPairing.root y ↔
      x.val = Pi.single i (1 : ℤ) + y.val := by
  constructor
  · intro h
    ext j
    apply Int.cast_injective (α := ℂ)
    simpa [rootPairing_root, rootVector, simpleRoot] using congrFun h j
  · intro h
    ext j
    simp [rootPairing_root, rootVector, simpleRoot, h]

private theorem e8_root_sub_coordinates (x y : Root) (i : Fin 8) :
    rootPairing.root x = rootPairing.root y - rootPairing.root (simpleRoot i) ↔
      x.val = y.val - Pi.single i (1 : ℤ) := by
  constructor
  · intro h
    ext j
    apply Int.cast_injective (α := ℂ)
    simpa [rootPairing_root, rootVector, simpleRoot] using congrFun h j
  · intro h
    ext j
    simp [rootPairing_root, rootVector, simpleRoot, h]

/-- The coordinate formula for the actual Cartan generators. -/
def hCoordinates (i : Fin 8) : Matrix CoordIndex CoordIndex ℂ :=
  fromBlocks 0 0 0 (diagonal fun r : Root => (innerZ r.val (Pi.single i 1) : ℂ))

/-- The coordinate formula for the actual raising generators. -/
def eCoordinates (i : Fin 8) : Matrix CoordIndex CoordIndex ℂ :=
  fromBlocks 0
    (fun j r => if j = i ∧ r.val = -(Pi.single i (1 : ℤ)) then 1 else 0)
    (fun r j => if r.val = Pi.single i (1 : ℤ) then (|CartanMatrix.E₈ i j| : ℤ) else 0)
    (fun r s => if r.val = Pi.single i (1 : ℤ) + s.val then 1 else 0)

/-- The coordinate formula for the actual lowering generators. -/
def fCoordinates (i : Fin 8) : Matrix CoordIndex CoordIndex ℂ :=
  fromBlocks 0
    (fun j r => if j = i ∧ r.val = Pi.single i (1 : ℤ) then 1 else 0)
    (fun r j => if r.val = -(Pi.single i (1 : ℤ)) then (|CartanMatrix.E₈ i j| : ℤ) else 0)
    (fun r s => if r.val = s.val - Pi.single i (1 : ℤ) then 1 else 0)

theorem e8_h_coordinate_formula (i : Fin 8) :
    coordinateMatrix (h (simpleIndex i)) = hCoordinates i := by
  classical
  ext (j | j) (k | k) <;>
    simp [coordinateMatrix, coordIndexEquiv, h, hCoordinates,
      e8_pairingIn_coordinates, simpleIndexEquiv, simpleIndex, simpleRoot,
      Matrix.diagonal_apply]

theorem e8_e_coordinate_formula (i : Fin 8) :
    coordinateMatrix (e (simpleIndex i)) = eCoordinates i := by
  classical
  letI := rootPairing.indexNeg
  ext (j | j) (k | k)
  · simp [coordinateMatrix, coordIndexEquiv, e, eCoordinates]
  · simp [coordinateMatrix, coordIndexEquiv, e, eCoordinates, simpleIndexEquiv,
      simpleIndex_bijective.1.eq_iff, simpleIndex_root, e8_root_eq_negative_simple_iff]
  · simp [coordinateMatrix, coordIndexEquiv, e, eCoordinates, simpleIndexEquiv,
      base, simpleBase_cartanMatrix, simpleIndex_root, e8_root_eq_simple_iff]
  · simp only [coordinateMatrix, coordIndexEquiv, e, eCoordinates,
      Matrix.submatrix_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, simpleIndex_root]
    by_cases hh : rootPairing.root j = rootPairing.root (simpleRoot i) + rootPairing.root k
    · have hz := (e8_root_string_coefficients (simpleRoot i) k j hh).1
      simp only [if_pos hh, if_pos ((e8_root_add_coordinates j k i).mp hh), hz,
        zero_add, Nat.cast_zero]
    · simp only [if_neg hh, if_neg (mt (e8_root_add_coordinates j k i).mpr hh)]

theorem e8_f_coordinate_formula (i : Fin 8) :
    coordinateMatrix (f (simpleIndex i)) = fCoordinates i := by
  classical
  letI := rootPairing.indexNeg
  ext (j | j) (k | k)
  · simp [coordinateMatrix, coordIndexEquiv, f, fCoordinates]
  · simp [coordinateMatrix, coordIndexEquiv, f, fCoordinates, simpleIndexEquiv,
      simpleIndex_bijective.1.eq_iff, simpleIndex_root, e8_root_eq_simple_iff]
  · simp [coordinateMatrix, coordIndexEquiv, f, fCoordinates, simpleIndexEquiv,
      base, simpleBase_cartanMatrix, simpleIndex_root, e8_root_eq_negative_simple_iff]
  · simp only [coordinateMatrix, coordIndexEquiv, f, fCoordinates,
      Matrix.submatrix_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, simpleIndex_root]
    by_cases hh : rootPairing.root j = rootPairing.root k - rootPairing.root (simpleRoot i)
    · have hs : rootPairing.root k = rootPairing.root (simpleRoot i) + rootPairing.root j := by
        rw [hh]
        abel
      have hz := (e8_root_string_coefficients (simpleRoot i) j k hs).2
      simp only [if_pos hh, if_pos ((e8_root_sub_coordinates j k i).mp hh), hz,
        zero_add, Nat.cast_zero]
    · simp only [if_neg hh, if_neg (mt (e8_root_sub_coordinates j k i).mpr hh)]

end

end CubicAnomaly.Fixed.E8GeneratorCoordinates
