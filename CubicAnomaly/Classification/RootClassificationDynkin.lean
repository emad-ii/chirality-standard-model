import CubicAnomaly.Classification.DynkinClassification.RootSystem
import CubicAnomaly.Classification.DynkinClassification.Classification
import CubicAnomaly.Classification.RootClassificationGrades
import CubicAnomaly.Classification.RootSimple

/-!
# Classification of the Cartan matrices of actual simple Lie algebras

The positive integral symmetrizer and irreducibility of an actual root
system supply the hypotheses of the finite Cartan classification. In the
exceptional cases the reindexing is composed with the numbering used by
the census, including reversal of the two indices in type G2.
-/

namespace CubicAnomaly.Classification.RootClassificationExceptional

open CubicAnomaly.Classification.DynkinClassification
open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.Selection
open LieAlgebra LieModule Module LieAlgebra.IsKilling

/-- The four uniform classical possibilities for an indexed simple Cartan matrix. -/
def ClassicalCartan {ι : Type*} (C : Matrix ι ι ℤ) : Prop :=
  (∃ (n : ℕ) (e : ι ≃ Fin n), C.reindex e e = CartanMatrix.A n) ∨
  (∃ (n : ℕ) (e : ι ≃ Fin n), C.reindex e e = CartanMatrix.B n) ∨
  (∃ (n : ℕ) (e : ι ≃ Fin n), C.reindex e e = CartanMatrix.C n) ∨
  (∃ (n : ℕ) (e : ι ≃ Fin n), C.reindex e e = CartanMatrix.D n)

/-- Any simple Cartan matrix is classical or matches one of the actual
numbered exceptional census matrices. The reindexing is a bijection of
simple roots, with equality at every matrix entry. -/
theorem root_system_classical_or_exceptional
    {ι K M N : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [Fintype ι] [DecidableEq ι] {P : RootPairing ι K M N} [P.IsCrystallographic]
    [P.IsRootSystem] [P.IsReduced] [P.IsIrreducible] (b : P.Base) :
    ClassicalCartan b.cartanMatrix ∨
      ∃ d : RootDatum, IsExceptionalCensusDatum d ∧
        ∃ s : Index d ≃ b.support, ∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j := by
  obtain ⟨hc, hi⟩ := actual_finite_indecomposable_cartan b
  rcases hc.exists_A_or_B_or_C_or_D_or_E_or_F_or_G hi with
    h | h | h | h | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  · refine Or.inr ⟨e6Datum, Or.inr (Or.inr (Or.inl rfl)), e.symm, fun i j => ?_⟩
    exact (congrFun (congrFun he i) j).trans (by decide +revert)
  · refine Or.inr ⟨e7Datum, Or.inr (Or.inr (Or.inr (Or.inl rfl))), e.symm, fun i j => ?_⟩
    exact (congrFun (congrFun he i) j).trans (by decide +revert)
  · refine Or.inr ⟨e8Datum, Or.inr (Or.inr (Or.inr (Or.inr rfl))), e.symm, fun i j => ?_⟩
    exact (congrFun (congrFun he i) j).trans (by decide +revert)
  · refine Or.inr ⟨f4Datum, Or.inr (Or.inl rfl), e.symm, fun i j => ?_⟩
    exact (congrFun (congrFun he i) j).trans (by decide +revert)
  · refine Or.inr ⟨g2Datum, Or.inl rfl, (Fin.revPerm.trans e.symm), fun i j => ?_⟩
    exact (congrFun (congrFun he (Fin.rev i)) (Fin.rev j)).trans (by decide +revert)

/-- Applied to a splitting Cartan of an actual simple Killing Lie algebra,
the Dynkin classification yields a classical matrix or an actual
grade-preserving bijection with an enumerated exceptional root system. -/
theorem simple_lie_classical_or_exceptional_census
    {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
    [FiniteDimensional K L] [LieAlgebra.IsKilling K L] [LieAlgebra.IsSimple K L]
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base) :
    ClassicalCartan b.cartanMatrix ∨
      ∃ d : RootDatum, IsExceptionalCensusDatum d ∧
        ∃ s : Index d ≃ b.support,
        (∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j) ∧
        ∃ e : ↥(table d) ≃ H.root, ∀ v, (rootSystem H).root (e v) = realize b s v.val := by
  classical
  rcases root_system_classical_or_exceptional b with hc | ⟨d, hd, s, hs⟩
  · exact Or.inl hc
  · obtain ⟨e, he, -⟩ := actual_exceptional_root_grade_equiv H b s hd hs
    exact Or.inr ⟨d, hd, s, hs, e, he⟩

end CubicAnomaly.Classification.RootClassificationExceptional
