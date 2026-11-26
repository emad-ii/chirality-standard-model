import CubicAnomaly.Classification.ClassicalConstituentDiagram

/-!
# Simple Cartan families with nontrivial opposition

The bounded opposition certificate handles ranks through eight. At higher
rank the Dynkin classification leaves the four classical families, and
diagram rigidity excludes the two marked paths. The accidental diagram
D₃ is explicitly reindexed to A₃.
-/

namespace CubicAnomaly.Classification.ClassicalOrthogonalCartanFamilies

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open WeylDualityObstruction ClassicalConstituentDiagram

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [IsKilling ℂ L] [IsSimple ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  (b : (rootSystem H).Base)

/-- A simple complex algebra whose Weyl action does not contain negation
has a numbered Cartan of type A in rank at least two, D in rank at least
five, or E₆. -/
theorem orthogonal_cartan_families (hn : ¬ ∃ w : List H.root, ∀ z : H, applyWord H w z = -z) :
    (∃ n, 2 ≤ n ∧ ∃ s : Fin n ≃ b.support,
      ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.A n i j) ∨
    (∃ n, 5 ≤ n ∧ ∃ s : Fin n ≃ b.support,
      ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.D n i j) ∨
    (∃ s : Fin 6 ≃ b.support, ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.E₆ i j) := by
  classical
  have hrank {n : ℕ} (e : b.support ≃ Fin n) : finrank ℂ H = n :=
    (finrank_eq_card_basis (b.toCoweightBasis.reindex e)).trans (Fintype.card_fin n)
  have small {n : ℕ} (e : b.support ≃ Fin n) : 2 ≤ n := by
    obtain ⟨δ,⟨i,hi⟩,-⟩ := exists_nontrivial_diagram_symmetry H b hn
    have he : (e (δ i)).val ≠ (e i).val := fun h => hi (e.injective (Fin.ext h))
    have h₁ := (e (δ i)).isLt
    have h₂ := (e i).isLt
    omega
  by_cases hsmall : finrank ℂ H ≤ 8
  · rcases cartan_types_of_no_negation H b hsmall hn with
      ⟨n,e,h₂,hm⟩ | ⟨n,e,hodd,hm⟩ | ⟨e,hm⟩
    · exact Or.inl ⟨n,h₂,e.symm,fun i j => congrFun (congrFun hm i) j⟩
    · by_cases h₅ : 5 ≤ n
      · exact Or.inr (Or.inl ⟨n,h₅,e.symm,fun i j => congrFun (congrFun hm i) j⟩)
      · have := small e
        obtain ⟨k,hk⟩ := hodd
        obtain rfl : n = 3 := by omega
        let p := Equiv.swap (0 : Fin 3) 1
        have hd : ∀ i j, CartanMatrix.D 3 (p i) (p j) = CartanMatrix.A 3 i j := by decide
        exact Or.inl ⟨3,by decide,p.trans e.symm,fun i j =>
          (congrFun (congrFun hm (p i)) (p j)).trans (hd i j)⟩
    · exact Or.inr (Or.inr ⟨e.symm,fun i j => congrFun (congrFun hm i) j⟩)
  · obtain ⟨hC,hi⟩ := DynkinClassification.actual_finite_indecomposable_cartan b
    rcases hC.exists_A_or_B_or_C_or_D_or_E_or_F_or_G hi with
      ⟨n,e,hm⟩ | ⟨n,e,hm⟩ | ⟨n,e,hm⟩ | ⟨n,e,hm⟩ | ⟨e,hm⟩ | ⟨e,hm⟩ | ⟨e,hm⟩ | ⟨e,hm⟩ | ⟨e,hm⟩
    · exact Or.inl ⟨n,small e,e.symm,fun i j => congrFun (congrFun hm i) j⟩
    · exact ((not_type_B_or_C H b hn e).1 hm).elim
    · exact ((not_type_B_or_C H b hn e).2 hm).elim
    · have := hrank e
      exact Or.inr (Or.inl ⟨n,by omega,e.symm,fun i j => congrFun (congrFun hm i) j⟩)
    all_goals have := hrank e; omega

end CubicAnomaly.Classification.ClassicalOrthogonalCartanFamilies
