import CubicAnomaly.Classification.Exceptional

/-!
# The unique survivor of the finite exceptional cubic census

This module turns the already checked table into universal selection and
existence-and-uniqueness statements.  The universe is explicitly the five
authored exceptional Cartan data and the rows returned by their finite toral
census.  It does not assert that an arbitrary compact Lie-algebra pair reaches
this universe; that is the remaining classification bridge.

The selected row has grade-zero components of signatures `(6, 2)` and
`(72, 6)`, a grade-one space of dimension `81`, and exactly the `(72, 6)`
component in its Cartan-cubic null list.  Interpreting the null list as an
ideal-valued radical of an actual Lie representation is a separate bridge.
-/

namespace CubicAnomaly.Classification.Selection

open CubicAnomaly.Classification.Exceptional

/-- The precise finite ambient universe checked in `Exceptional.lean`. -/
def IsExceptionalCensusDatum (datum : RootDatum) : Prop :=
  datum = g2Datum ∨ datum = f4Datum ∨ datum = e6Datum ∨
    datum = e7Datum ∨ datum = e8Datum

/-- The unique row with a nonempty Cartan-cubic null-component list. -/
def selectedE8CubicSignature : CubicSignature := {
  row := {
    gradeZeroRoots := 78
    gradeOneRoots := 81
    componentRootCountRanks := #[(6, 2), (72, 6)] }
  cartanCubicNullRootCountRanks := #[(72, 6)]
}

/-- Every row in the five computed exceptional censuses with a nonempty
Cartan-cubic null-component list is the indicated `E8` row. -/
theorem finite_cubic_selection_unique (datum : RootDatum)
    (hdatum : IsExceptionalCensusDatum datum) (row : CubicSignature)
    (hrow : row ∈ fullRankOrderThreeCubicSignatures datum)
    (hnull : row.cartanCubicNullRootCountRanks ≠ #[]) :
    datum = e8Datum ∧ row = selectedE8CubicSignature := by
  obtain ⟨_, _, _, _, _, hg2, hf4, he6, he7, he8⟩ := cartan_cubic_selector
  rcases hdatum with rfl | rfl | rfl | rfl | rfl
  · rw [hg2] at hrow
    simp only [Array.mem_singleton] at hrow
    subst row
    exact False.elim (hnull rfl)
  · rw [hf4] at hrow
    simp only [Array.mem_singleton] at hrow
    subst row
    exact False.elim (hnull rfl)
  · rw [he6] at hrow
    simp only [Array.mem_singleton] at hrow
    subst row
    exact False.elim (hnull rfl)
  · rw [he7] at hrow
    simp only [Array.mem_singleton] at hrow
    subst row
    exact False.elim (hnull rfl)
  · rw [he8] at hrow
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact False.elim (hnull rfl)

/-- The selected row is actually present, and its null-component list is
nonempty.  This supplies the converse of the finite uniqueness result. -/
theorem finite_cubic_selection_exists :
    selectedE8CubicSignature ∈ fullRankOrderThreeCubicSignatures e8Datum ∧
      selectedE8CubicSignature.cartanCubicNullRootCountRanks ≠ #[] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, he8⟩ := cartan_cubic_selector
  constructor
  · rw [he8]
    simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl rfl
  · decide

/-- A complete characterization of selection inside the explicitly stated
finite census, with both directions proved. -/
theorem finite_cubic_selection_iff (datum : RootDatum) (row : CubicSignature) :
    (IsExceptionalCensusDatum datum ∧
      row ∈ fullRankOrderThreeCubicSignatures datum ∧
      row.cartanCubicNullRootCountRanks ≠ #[]) ↔
    datum = e8Datum ∧ row = selectedE8CubicSignature := by
  constructor
  · rintro ⟨hdatum, hrow, hnull⟩
    exact finite_cubic_selection_unique datum hdatum row hrow hnull
  · rintro ⟨rfl, rfl⟩
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), finite_cubic_selection_exists⟩

/-- There exists exactly one selected `(ambient datum, cubic row)` pair in
the finite exceptional census.  This is not an assertion of uniqueness over
all compact Lie-algebra embeddings. -/
theorem finite_cubic_selection_exists_unique :
    ∃! p : RootDatum × CubicSignature,
      IsExceptionalCensusDatum p.1 ∧
      p.2 ∈ fullRankOrderThreeCubicSignatures p.1 ∧
      p.2.cartanCubicNullRootCountRanks ≠ #[] := by
  refine ⟨(e8Datum, selectedE8CubicSignature), ?_, ?_⟩
  · exact (finite_cubic_selection_iff _ _).mpr ⟨rfl, rfl⟩
  · intro p hp
    obtain ⟨hdatum, hrow⟩ := (finite_cubic_selection_iff _ _).mp hp
    exact Prod.ext hdatum hrow

end CubicAnomaly.Classification.Selection
