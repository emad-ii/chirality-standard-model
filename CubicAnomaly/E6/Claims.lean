import CubicAnomaly.E6.Checker

/-!
Lean-checked finite claims from the E6 incidence calculation.

Every field below is decided by compiled evaluation through `native_decide`
under the disclosed Lean compiler/interpreter trust boundary. There are no
`sorry`, `admit`, custom axioms, or theorem-valued inputs.
-/

namespace CubicAnomaly.E6

def FiniteCertificateClaims : Prop :=
  rootTableValid = true ∧
  subsystemOrbitsValid = true ∧
  tripleUniverse.size = 38880 ∧
  uniqueArray tripleUniverse = true ∧
  observedCellCounts = expectedCellCounts ∧
  cellPartitionValid = true ∧
  cellOrbitClassificationValid = true ∧
  extremaValid = true ∧
  colorClassificationValid = true ∧
  commonMultiplicityValid pairwiseMaximal 720 6 = true ∧
  commonMultiplicityValid commonMaximal 1080 2 = true ∧
  contextValid = true ∧
  inclusionValid = true

/-- The complete Lean-checked finite certificate surface. -/
theorem finite_certificate_valid : FiniteCertificateClaims := by
  unfold FiniteCertificateClaims
  native_decide

theorem e6_root_table_valid : rootTableValid = true :=
  finite_certificate_valid.1

/-- The three reconstructed orbits consist of closed subsystems whose exact
root-count/rank signatures are those conventionally identified, by the
simply-laced classification, as D5, A5+A1, and A2^3; their orbit sizes are
27, 36, and 40. -/
theorem subsystem_orbit_types_and_sizes_valid : subsystemOrbitsValid = true :=
  finite_certificate_valid.2.1

theorem subsystem_orbit_sizes_valid : subsystemOrbitsValid = true :=
  subsystem_orbit_types_and_sizes_valid

theorem triple_space_has_38880_elements : tripleUniverse.size = 38880 :=
  finite_certificate_valid.2.2.1

theorem triple_space_has_38880_distinct_elements :
    tripleUniverse.size = 38880 ∧ uniqueArray tripleUniverse = true :=
  ⟨finite_certificate_valid.2.2.1, finite_certificate_valid.2.2.2.1⟩

theorem six_cell_distribution_valid : observedCellCounts = expectedCellCounts :=
  finite_certificate_valid.2.2.2.2.1

theorem six_weyl_orbits_partition_triple_space : cellPartitionValid = true :=
  finite_certificate_valid.2.2.2.2.2.1

theorem six_cell_orbits_classified_valid : cellOrbitClassificationValid = true :=
  finite_certificate_valid.2.2.2.2.2.2.1

theorem extrema_counts_and_bounds_valid : extremaValid = true :=
  finite_certificate_valid.2.2.2.2.2.2.2.1

/-- An irreducible component with six roots and rank two occurs exactly on the
two extremal cells.  The standard simply-laced classification identifies it
as type A2.  This checks component signatures, not merely adjacent root pairs. -/
theorem a2_occurs_exactly_on_two_extremal_cells : colorClassificationValid = true :=
  finite_certificate_valid.2.2.2.2.2.2.2.2.1

theorem pairwise_common_multiplicity_valid :
    commonMultiplicityValid pairwiseMaximal 720 6 = true :=
  finite_certificate_valid.2.2.2.2.2.2.2.2.2.1

theorem common_maximal_multiplicity_valid :
    commonMultiplicityValid commonMaximal 1080 2 = true :=
  finite_certificate_valid.2.2.2.2.2.2.2.2.2.2.1

theorem context_counts_valid : contextValid = true :=
  finite_certificate_valid.2.2.2.2.2.2.2.2.2.2.2.1

theorem labelled_containments_valid : inclusionValid = true :=
  finite_certificate_valid.2.2.2.2.2.2.2.2.2.2.2.2

end CubicAnomaly.E6
