import CubicAnomaly.E6.Checker

/-!
Lean-checked finite claims from the E6 incidence calculation.

Every field below is decided by compiled evaluation through `native_decide`
under the disclosed Lean compiler/interpreter trust boundary. There are no
`sorry`, `admit`, custom axioms, or theorem-valued inputs.
-/

namespace CubicAnomaly.E6

/-- All pair ranks are evaluated from integer root coordinates. -/
theorem intrinsic_pair_data_valid : intrinsicPairDataValid = true := by
  native_decide

/-- Exact root-count/rank signatures for every pair of reconstructed witnesses. -/
theorem intrinsic_pair_signatures :
    (∀ d ∈ dOrbit, ∀ a ∈ aOrbit,
      (maskSize (d &&& a) = 16 ∧ rootRank (d &&& a) = 5) ∨
      (maskSize (d &&& a) = 20 ∧ rootRank (d &&& a) = 4)) ∧
    (∀ d ∈ dOrbit, ∀ theta ∈ thetaOrbit,
      maskSize (d &&& theta) = 10 ∧ rootRank (d &&& theta) = 4) ∧
    (∀ a ∈ aOrbit, ∀ theta ∈ thetaOrbit,
      (maskSize (a &&& theta) = 6 ∧ rootRank (a &&& theta) = 3) ∨
      (maskSize (a &&& theta) = 14 ∧ rootRank (a &&& theta) = 5)) := by
  simpa [intrinsicPairDataValid, pairSignaturesValid, Array.all_eq_true',
    Array.contains_iff_mem, and_assoc, -Array.all_eq_true] using intrinsic_pair_data_valid

/-- Membership in the reconstructed product, with no supplied incidence data. -/
theorem triple_universe_orbit_membership (triple : Triple)
    (h : triple ∈ tripleUniverse) :
    triple.d ∈ dOrbit ∧ triple.a ∈ aOrbit ∧ triple.theta ∈ thetaOrbit := by
  have checked : tripleUniverse.all (fun t =>
      dOrbit.contains t.d && aOrbit.contains t.a && thetaOrbit.contains t.theta) = true := by
    native_decide
  have allMembers := Array.all_eq_true'.mp checked triple h
  simpa only [Bool.and_eq_true, Array.contains_iff_mem, and_assoc] using allMembers

/-- The D-A pair is intrinsically the unique largest pair by root count on the
entire Cartesian product of reconstructed D, A and Theta witnesses. -/
theorem intrinsic_da_root_count_ordering_of_orbit_membership
    (triple : Triple) (hd : triple.d ∈ dOrbit) (ha : triple.a ∈ aOrbit)
    (htheta : triple.theta ∈ thetaOrbit) :
    intersectionSize triple.d triple.a > intersectionSize triple.d triple.theta ∧
    intersectionSize triple.d triple.a > intersectionSize triple.a triple.theta := by
  have hda := intrinsic_pair_signatures.1 triple.d hd triple.a ha
  have hdt := intrinsic_pair_signatures.2.1 triple.d hd triple.theta htheta
  have hat := intrinsic_pair_signatures.2.2 triple.a ha triple.theta htheta
  rcases hda with ⟨hda, _⟩ | ⟨hda, _⟩ <;>
    rcases hat with ⟨hat, _⟩ | ⟨hat, _⟩ <;>
    simp only [intersectionSize, hda, hdt.1, hat] <;> decide

/-- Exact rank-plus-root-count dimensions on every reconstructed triple.
This is numerical root data, not a formalization of the Lie-algebra bridge. -/
theorem intrinsic_pair_dimensions_of_orbit_membership
    (triple : Triple) (hd : triple.d ∈ dOrbit) (ha : triple.a ∈ aOrbit)
    (htheta : triple.theta ∈ thetaOrbit) :
    (rootGeneratedDimension (triple.d &&& triple.a) = 21 ∨
      rootGeneratedDimension (triple.d &&& triple.a) = 24) ∧
    rootGeneratedDimension (triple.d &&& triple.theta) = 14 ∧
    (rootGeneratedDimension (triple.a &&& triple.theta) = 9 ∨
      rootGeneratedDimension (triple.a &&& triple.theta) = 19) := by
  have hda := intrinsic_pair_signatures.1 triple.d hd triple.a ha
  have hdt := intrinsic_pair_signatures.2.1 triple.d hd triple.theta htheta
  have hat := intrinsic_pair_signatures.2.2 triple.a ha triple.theta htheta
  refine ⟨?_, ?_, ?_⟩
  · rcases hda with ⟨count, rank⟩ | ⟨count, rank⟩ <;>
      simp only [rootGeneratedDimension, count, rank] <;> decide
  · simp only [rootGeneratedDimension, hdt.1, hdt.2]
  · rcases hat with ⟨count, rank⟩ | ⟨count, rank⟩ <;>
      simp only [rootGeneratedDimension, count, rank] <;> decide

/-- Root-count ordering for each actual element of the 38880-element universe. -/
theorem intrinsic_da_root_count_ordering (triple : Triple)
    (h : triple ∈ tripleUniverse) :
    intersectionSize triple.d triple.a > intersectionSize triple.d triple.theta ∧
    intersectionSize triple.d triple.a > intersectionSize triple.a triple.theta := by
  obtain ⟨hd, ha, htheta⟩ := triple_universe_orbit_membership triple h
  exact intrinsic_da_root_count_ordering_of_orbit_membership triple hd ha htheta

/-- The same intrinsic choice is strictly largest by independently computed
rank plus root count, throughout the actual 38880-element triple universe. -/
theorem intrinsic_da_dimension_ordering (triple : Triple)
    (h : triple ∈ tripleUniverse) :
    rootGeneratedDimension (triple.d &&& triple.a) >
      rootGeneratedDimension (triple.d &&& triple.theta) ∧
    rootGeneratedDimension (triple.d &&& triple.a) >
      rootGeneratedDimension (triple.a &&& triple.theta) := by
  obtain ⟨hd, ha, htheta⟩ := triple_universe_orbit_membership triple h
  obtain ⟨hda, hdt, hat⟩ := intrinsic_pair_dimensions_of_orbit_membership triple hd ha htheta
  rcases hda with hda | hda <;> rcases hat with hat | hat <;>
    simp only [hda, hdt, hat] <;> decide

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

/-- The original finite certificate surface; intrinsic ordering is checked separately. -/
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
