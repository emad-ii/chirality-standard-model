import CubicAnomaly.Classification.RootCharacterCoordinates
import CubicAnomaly.Classification.RootCubicKernel
import CubicAnomaly.Classification.IntrinsicCartanBasis

/-!
# The intrinsic finite integer-coordinate cubic matrix

The actual roots have constructed integer coordinates. Filtering them by
the coordinate dot product with a toral character gives a finite integer
cubic matrix. Its entries are the sums of three coordinate products, each
actual root counted once. This module identifies that finite coordinate
calculation with the actual root cubic on the same Cartan.
-/

namespace CubicAnomaly.Classification.CoordinateCubic

open LieAlgebra LieModule Module Matrix
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.ToralCharacter
open CubicAnomaly.Classification.RootLatticeBasis
open CubicAnomaly.Classification.RootCharacterCoordinates
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.RootSupportDimension
open CubicAnomaly.Classification.RootSupportTrace
open CubicAnomaly.Classification.RootCubicKernel
open CubicAnomaly.Classification.IntrinsicCartanBasis

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The actual roots selected by a finite coordinate assignment and grade. -/
noncomputable def coordinateGradeRoots (values : Fin (finrank K H) → ZMod 3)
    (grade : ZMod 3) : Set H.root :=
  {α | (∑ j, (intrinsicRootCoordinates H α j : ZMod 3) * values j) = grade}

/-- Coordinate-filtered actual roots are exactly the roots contained in
the actual character grade. The equivalence preserves the root function. -/
def coordinateGradeSupportEquiv (character : rootLattice H →+ ZMod 3)
    (grade : ZMod 3) :
    coordinateGradeRoots H (fun i => character (intrinsicRootBasis H i)) grade ≃
      containedRoots H (rootCharacterGrade H character grade) where
  toFun α := ⟨α.val.val,
    (root_mem_grade_iff_coordinate_dot H character α.val grade).mpr α.property⟩
  invFun β :=
    let α : H.root := ⟨Weight.mk β.val β.property.2.1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, β.property.1⟩⟩
    ⟨α, (root_mem_grade_iff_coordinate_dot H character α grade).mp β.property⟩
  left_inv α := by apply Subtype.ext; apply Subtype.ext; apply Weight.ext; intro x; rfl
  right_inv β := by apply Subtype.ext; rfl

/-- The intrinsic cubic matrix is literally an integer finite sum. The
coordinate assignment is an arbitrary point of the finite character space. -/
noncomputable def intrinsicCoordinateCubicMatrix
    (values : Fin (finrank K H) → ZMod 3) (grade : ZMod 3) :
    Matrix (Fin (finrank K H) × Fin (finrank K H)) (Fin (finrank K H)) ℤ := by
  classical
  letI := (Set.toFinite (coordinateGradeRoots H values grade)).fintype
  exact fun jk i => ∑ α : coordinateGradeRoots H values grade,
    intrinsicRootCoordinates H α.val i * intrinsicRootCoordinates H α.val jk.1 *
      intrinsicRootCoordinates H α.val jk.2

/-- The actual root cubic is the finite sum over exactly the roots selected
by the coordinate dot-product test. -/
theorem actual_root_cubic_eq_coordinate_grade_sum
    (character : rootLattice H →+ ZMod 3) (grade : ZMod 3) (x y z : H) :
    actualRootCubic H (rootCharacterGrade H character grade) x y z =
      letI := (Set.toFinite (coordinateGradeRoots H
        (fun i => character (intrinsicRootBasis H i)) grade)).fintype
      ∑ α : coordinateGradeRoots H (fun i => character (intrinsicRootBasis H i)) grade,
        α.val.val x * α.val.val y * α.val.val z := by
  classical
  letI := (containedRoots_finite H (rootCharacterGrade H character grade)).fintype
  letI := (Set.toFinite (coordinateGradeRoots H
    (fun i => character (intrinsicRootBasis H i)) grade)).fintype
  exact ((coordinateGradeSupportEquiv H character grade).sum_comp
    (fun α : containedRoots H (rootCharacterGrade H character grade) =>
      α.val x * α.val y * α.val z)).symm

/-- In the intrinsic Cartan basis, the actual root-cubic matrix is the
entrywise scalar cast of the finite integer-coordinate matrix. Thus every
entry used by the toral kernel test is supplied by an exact integer sum. -/
theorem actual_root_cubic_matrix_eq_intrinsic_coordinates
    (character : rootLattice H →+ ZMod 3) (grade : ZMod 3) :
    actualRootCubicMatrix H (rootCharacterGrade H character grade) (intrinsicCartanBasis H) =
      (intrinsicCoordinateCubicMatrix H
        (fun i => character (intrinsicRootBasis H i)) grade).map (Int.castRingHom K) := by
  classical
  ext jk i
  change actualRootCubic H (rootCharacterGrade H character grade)
    (intrinsicCartanBasis H i) (intrinsicCartanBasis H jk.1) (intrinsicCartanBasis H jk.2) = _
  rw [actual_root_cubic_eq_coordinate_grade_sum]
  simp only [root_apply_intrinsic_cartan_basis, Matrix.map_apply, intrinsicCoordinateCubicMatrix,
    Int.coe_castRingHom, Int.cast_sum, Int.cast_mul]

end CubicAnomaly.Classification.CoordinateCubic
