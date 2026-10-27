import CubicAnomaly.Classification.RootLatticeBasis
import CubicAnomaly.Classification.RootSupportDimension

/-!
# Exact root-coordinate semantics for the intrinsic toral census

An actual root belongs to a character grade exactly when the dot product
of its constructed integer coordinates with the character's basis values
has that residue. The actual root-support counts and graph displacements
therefore have literal finite-coordinate interpretations, before identifying
any root system with an authored classical or exceptional table.
-/

namespace CubicAnomaly.Classification.RootCharacterCoordinates

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.ToralCharacter
open CubicAnomaly.Classification.RootLatticeBasis
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.RootSupportGraph
open CubicAnomaly.Classification.RootSupportDimension

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- An actual nonzero root, as an element of its actual integer root lattice. -/
def rootLatticeElement (α : H.root) : rootLattice H :=
  ⟨α.val, root_mem_rootLattice H α.val.genWeightSpace_ne_bot⟩

/-- Integer coordinates of an actual root in the constructed lattice basis. -/
noncomputable def intrinsicRootCoordinates (α : H.root) : Fin (finrank K H) → ℤ :=
  fun i => (intrinsicRootBasis H).repr (rootLatticeElement H α) i

/-- Intrinsic integer coordinates distinguish actual roots. -/
theorem intrinsic_root_coordinates_injective : Function.Injective (intrinsicRootCoordinates H) := by
  intro α β h
  have he : rootLatticeElement H α = rootLatticeElement H β :=
    (intrinsicRootBasis H).repr.injective (Finsupp.ext (congrFun h))
  apply Subtype.ext
  apply Weight.ext
  exact congrFun (congrArg Subtype.val he)

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
/-- Nonzero actual root spaces occupy exactly their character's grade. -/
theorem root_space_le_character_grade_iff (character : rootLattice H →+ ZMod 3)
    (α : H.root) (i : ZMod 3) :
    (rootSpace H α.val).toSubmodule ≤ rootCharacterGrade H character i ↔
      character (rootLatticeElement H α) = i := by
  constructor
  · intro hle
    by_contra hne
    have hother : rootCharacterGrade H character i ≤
        ⨆ (β : H → K) (_ : β ≠ α.val), (rootSpace H β).toSubmodule := by
      refine iSup_le fun β => iSup_le fun hβ => ?_
      have hβα : (β : H → K) ≠ α.val := by
        intro he
        have he' : (⟨β, root_mem_rootLattice H β.genWeightSpace_ne_bot⟩ : rootLattice H) =
            rootLatticeElement H α := Subtype.ext he
        exact hne (he' ▸ hβ)
      exact le_iSup_of_le (β : H → K) (le_iSup_of_le hβα le_rfl)
    have hind : iSupIndep (fun β : H → K => (rootSpace H β).toSubmodule) :=
      LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace K H L)
    have hd := (hind (α.val : H → K)).mono_right hother
    obtain ⟨x, hx, hx0⟩ := α.val.exists_ne_zero
    have hxin : x ∈ (rootSpace H α.val).toSubmodule ⊓ rootCharacterGrade H character i :=
      ⟨hx, hle hx⟩
    exact hx0 (by simpa only [hd.eq_bot, Submodule.mem_bot] using hxin)
  · intro hχ
    exact le_iSup_of_le α.val (le_iSup_of_le hχ le_rfl)

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
/-- Actual root support is precisely the finite character-level set. -/
theorem root_mem_character_grade_iff (character : rootLattice H →+ ZMod 3)
    (α : H.root) (i : ZMod 3) :
    (α.val : H → K) ∈ containedRoots H (rootCharacterGrade H character i) ↔
      character (rootLatticeElement H α) = i := by
  constructor
  · intro hα
    exact (root_space_le_character_grade_iff H character α i).mp hα.2.2
  · intro hχ
    exact ⟨(Finset.mem_filter.mp α.property).2, α.val.genWeightSpace_ne_bot,
      (root_space_le_character_grade_iff H character α i).mpr hχ⟩

/-- Root degrees are literal integer-coordinate dot products modulo three. -/
theorem root_character_coordinate_formula (character : rootLattice H →+ ZMod 3)
    (α : H.root) :
    character (rootLatticeElement H α) = ∑ i,
      (intrinsicRootCoordinates H α i : ZMod 3) * character (intrinsicRootBasis H i) :=
  intrinsic_root_character_formula H character (rootLatticeElement H α)

/-- The root membership test used in a coordinate census is equivalent to
membership of the actual root space in the actual character grade. -/
theorem root_mem_grade_iff_coordinate_dot (character : rootLattice H →+ ZMod 3)
    (α : H.root) (i : ZMod 3) :
    (α.val : H → K) ∈ containedRoots H (rootCharacterGrade H character i) ↔
      (∑ j, (intrinsicRootCoordinates H α j : ZMod 3) *
        character (intrinsicRootBasis H j)) = i := by
  rw [root_mem_character_grade_iff, root_character_coordinate_formula]

/-- Integer-coordinate subtraction is exactly subtraction of actual root functions. -/
theorem root_coordinates_sub_eq_iff (α β γ : H.root) :
    intrinsicRootCoordinates H β - intrinsicRootCoordinates H α = intrinsicRootCoordinates H γ ↔
      (β.val : H → K) - (α.val : H → K) = (γ.val : H → K) := by
  have he : intrinsicRootCoordinates H β - intrinsicRootCoordinates H α =
      intrinsicRootCoordinates H γ ↔
      rootLatticeElement H β - rootLatticeElement H α = rootLatticeElement H γ := by
    constructor
    · intro h
      apply (intrinsicRootBasis H).repr.injective
      ext i
      simpa only [map_sub, Finsupp.sub_apply] using congrFun h i
    · intro h
      funext i
      have hi := congrArg (fun x : rootLattice H => (intrinsicRootBasis H).repr x i) h
      simpa only [map_sub, Finsupp.sub_apply] using hi
  rw [he]
  exact Subtype.ext_iff

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
/-- The entire actual supported-root set is the image of the finite
character-level set of actual nonzero roots. -/
theorem character_grade_roots_eq_image (character : rootLattice H →+ ZMod 3)
    (i : ZMod 3) :
    containedRoots H (rootCharacterGrade H character i) =
      (fun α : H.root => (α.val : H → K)) ''
        {α | character (rootLatticeElement H α) = i} := by
  ext β
  constructor
  · intro hβ
    let α : H.root := ⟨Weight.mk β hβ.2.1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ.1⟩⟩
    exact ⟨α, (root_mem_character_grade_iff H character α i).mp hβ, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact (root_mem_character_grade_iff H character α i).mpr hα

/-- Actual grade root counts equal the finite coordinate-filter counts. -/
theorem character_grade_root_count_eq_coordinate_filter
    (character : rootLattice H →+ ZMod 3) (i : ZMod 3) :
    (containedRoots H (rootCharacterGrade H character i)).ncard =
      Nat.card {α : H.root // (∑ j, (intrinsicRootCoordinates H α j : ZMod 3) *
        character (intrinsicRootBasis H j)) = i} := by
  have hinj : Function.Injective (fun α : H.root => (α.val : H → K)) := by
    intro α β h
    exact Subtype.ext (Weight.ext (congrFun h))
  rw [character_grade_roots_eq_image, Set.ncard_image_of_injective _ hinj]
  simp only [root_character_coordinate_formula]
  rfl

/-- Graph edges in the actual grade-one support are exactly coordinate
differences belonging to the actual zero-root list. -/
theorem support_adjacency_iff_root_coordinates
    (character : rootLattice H →+ ZMod 3) (S : LieSubalgebra K L)
    (hS : S.toSubmodule = rootCharacterGrade H character 0) (α β : H.root) :
    SupportAdjacent H S (rootCharacterGrade H character 1)
        (α.val : H → K) (β.val : H → K) ↔
      character (rootLatticeElement H α) = 1 ∧
      character (rootLatticeElement H β) = 1 ∧
      ∃ γ : H.root, character (rootLatticeElement H γ) = 0 ∧
        intrinsicRootCoordinates H β - intrinsicRootCoordinates H α =
          intrinsicRootCoordinates H γ := by
  unfold SupportAdjacent
  rw [root_mem_character_grade_iff, root_mem_character_grade_iff, hS,
    character_grade_roots_eq_image]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨γ, hγ, he⟩
    exact ⟨γ, hγ, (root_coordinates_sub_eq_iff H α β γ).mpr he.symm⟩
  · rintro ⟨γ, hγ, he⟩
    exact ⟨γ, hγ, ((root_coordinates_sub_eq_iff H α β γ).mp he).symm⟩

end CubicAnomaly.Classification.RootCharacterCoordinates
