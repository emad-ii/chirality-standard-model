import CubicAnomaly.Classification.ToralCharacter
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# An intrinsic integer basis for the actual Lie root lattice

The function-valued lattice used by the grading construction is identified
with the integer root span of Mathlib's actual root pairing.  It is finite
free of rank equal to the dimension of the Cartan.  Consequently the basis
for intrinsic toral character enumeration can be constructed, rather than
supplied as an extra witness.  Identifying it with any authored coordinate
table remains a separate classification problem.
-/

namespace CubicAnomaly.Classification.RootLatticeBasis

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.RootSaturation
open CubicAnomaly.Classification.ToralCharacter

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

private def rootFormToFunction : Dual K H →+ (H → K) where
  toFun := fun φ => φ
  map_zero' := rfl
  map_add' := fun _ _ => rfl

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
    [H.IsCartanSubalgebra] [IsTriangularizable K H L] in
private theorem rootFormToFunction_injective : Function.Injective (rootFormToFunction H) :=
  fun _ _ h => LinearMap.ext (congrFun h)

private theorem root_span_map_eq_rootLattice :
    ((rootSystem H).rootSpan ℤ).toAddSubgroup.map (rootFormToFunction H) =
      rootLattice H := by
  rw [RootPairing.rootSpan, Submodule.span_int_eq_addSubgroupClosure,
    AddMonoidHom.map_closure]
  change AddSubgroup.closure ((rootFormToFunction H) '' Set.range (rootSystem H).root) = _
  rw [← Set.range_comp]
  change AddSubgroup.closure
    (Set.range fun α : H.root => ((rootSystem H).root α : H → K)) = _
  rw [lie_weight_root_range]
  rfl

/-- The actual function-valued root lattice is the actual integer root span
of the Lie root pairing, with matching scalar multiplication. -/
noncomputable def rootSpanEquivRootLattice :
    (rootSystem H).rootSpan ℤ ≃ₗ[ℤ] rootLattice H :=
  ((((rootSystem H).rootSpan ℤ).toAddSubgroup.equivMapOfInjective
    (rootFormToFunction H) (rootFormToFunction_injective H)).trans
      (AddEquiv.addSubgroupCongr (root_span_map_eq_rootLattice H))).toIntLinearEquiv

instance rootLattice_finite : Module.Finite ℤ (rootLattice H) := by
  letI : Module.Finite ℤ ((rootSystem H).rootSpan ℤ) :=
    Module.Finite.of_fg (Submodule.fg_span (Set.finite_range _))
  exact Module.Finite.equiv (rootSpanEquivRootLattice H)

instance rootLattice_free : Module.Free ℤ (rootLattice H) :=
  Module.free_of_finite_type_torsion_free'

/-- The integer rank of the actual root lattice equals the actual Cartan
dimension. This uses the crystallographic root pairing, not a type label. -/
theorem actual_root_lattice_finrank :
    finrank ℤ (rootLattice H) = finrank K H := by
  rw [← (rootSpanEquivRootLattice H).finrank_eq,
    (rootSystem H).finrank_rootSpanIn_int, Subspace.dual_finrank_eq]

/-- A constructed integer basis for the actual root lattice, indexed by
the finite set of size equal to the actual Cartan dimension. -/
noncomputable def intrinsicRootBasis :
    Basis (Fin (finrank K H)) ℤ (rootLattice H) :=
  Module.finBasisOfFinrankEq ℤ (rootLattice H) (actual_root_lattice_finrank H)

/-- Every actual root-lattice character has unique intrinsic coordinate
values, with no supplied integer basis. -/
noncomputable def intrinsicRootCharacterEquiv :
    (rootLattice H →+ ZMod 3) ≃ (Fin (finrank K H) → ZMod 3) :=
  rootCharacterBasisEquiv H (intrinsicRootBasis H)

/-- Exactly `3 ^ dim H` actual root-lattice characters occur. -/
theorem card_actual_root_lattice_characters :
    Nat.card (rootLattice H →+ ZMod 3) = 3 ^ finrank K H := by
  simpa using card_root_lattice_characters H (intrinsicRootBasis H)

/-- Evaluation of a toral character is the coordinate dot product in the
constructed intrinsic integer basis. -/
theorem intrinsic_root_character_formula (character : rootLattice H →+ ZMod 3)
    (x : rootLattice H) :
    character x = ∑ i : Fin (finrank K H),
      ((intrinsicRootBasis H).repr x i : ZMod 3) * character (intrinsicRootBasis H i) :=
  root_character_basis_formula H (intrinsicRootBasis H) character x

/-- Nontrivial actual characters are precisely nonzero intrinsic coordinate
assignments. -/
theorem intrinsic_root_character_ne_zero_iff (character : rootLattice H →+ ZMod 3) :
    character ≠ 0 ↔ ∃ i, character (intrinsicRootBasis H i) ≠ 0 :=
  root_character_ne_zero_iff_basis_value H (intrinsicRootBasis H) character

end CubicAnomaly.Classification.RootLatticeBasis
