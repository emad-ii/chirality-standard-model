import CubicAnomaly.Classification.RootClassificationBoundedLift
import CubicAnomaly.Classification.RootClassificationClassicalAB
import CubicAnomaly.Classification.RootClassificationClassicalCD
import CubicAnomaly.Classification.RootClassificationDynkin

/-! The four classical Cartan matrices cannot occur at full rank. The
coordinate lifts apply to the actual character on the actual simple roots. -/

namespace CubicAnomaly.Classification.RootClassificationClassical

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open RootClassificationBoundedLift RootClassificationClassicalAB RootClassificationClassicalCD
open RootClassificationExceptional RootGrading RootCharacterCoordinates ToralCharacter
open FullRankRoots CompactGeometry Structural HermitianRealization

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L] (H : LieSubalgebra K L)
  [H.IsCartanSubalgebra] [IsTriangularizable K H L] (b : (rootSystem H).Base)

private theorem reindexed_bounded_lift {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (e : b.support ≃ Fin n) (he : b.cartanMatrix.reindex e e = C)
    (hl : ∀ a : Fin n → ZMod 3, ∃ (F : Set (Fin n → ℤ)) (w : Fin n → ℤ),
      w ∈ F ∧ (∀ i, (w i : ZMod 3) = a i) ∧ (∀ v ∈ F, ∀ i, -2 ≤ v i ∧ v i ≤ 2) ∧
        ∀ v ∈ F, ∀ i, (fun j => v j - C j i * v i) ∈ F)
    (χ : rootLattice H →+ ZMod 3) (S : LieSubalgebra K L)
    (hzero : S.toSubmodule = rootCharacterGrade H χ 0)
    (hspan : Submodule.span K (containedRootForms H S) = ⊤) : χ = 0 := by
  obtain ⟨F, w, hw, hm, hb, hr⟩ := hl (fun i => χ (rootLatticeElement H (e.symm i)))
  apply full_zero_grade_span_forces_zero_character H b e.symm χ S hzero hspan F w hw hm hb
  intro v hv i
  have hC (j : Fin n) : b.cartanMatrix (e.symm j) (e.symm i) = C j i :=
    congrFun (congrFun he j) i
  simpa only [hC] using hr v hv i

/-- A nontrivial mod-three character of an actual Cartan of classical type has
zero roots spanning a proper subspace of the Cartan dual, in every rank. -/
theorem classical_cartan_character_span_obstruction (hc : ClassicalCartan b.cartanMatrix)
    (χ : rootLattice H →+ ZMod 3) (S : LieSubalgebra K L)
    (hzero : S.toSubmodule = rootCharacterGrade H χ 0)
    (hspan : Submodule.span K (containedRootForms H S) = ⊤) : χ = 0 := by
  rcases hc with ⟨n, e, h⟩ | ⟨n, e, h⟩ | ⟨n, e, h⟩ | ⟨n, e, h⟩
  · exact reindexed_bounded_lift H b e h typeA_bounded_reflection_family χ S hzero hspan
  · exact reindexed_bounded_lift H b e h typeB_bounded_reflection_family χ S hzero hspan
  · exact reindexed_bounded_lift H b e h typeC_bounded_reflection_family χ S hzero hspan
  · exact reindexed_bounded_lift H b e h typeD_bounded_reflection_family χ S hzero hspan

end CubicAnomaly.Classification.RootClassificationClassical
