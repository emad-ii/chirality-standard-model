import CubicAnomaly.Classification.ExceptionalSieveNormalization
import CubicAnomaly.Classification.RootClassificationDynkin

/-!
# Coverage of the rank-deficient simple-factor catalog

Every actual simple Cartan of rank at most seven matches a numbered
matrix in the finite factor catalog. The disconnected matrix D₂ is
excluded by indecomposability and E₈ by the rank bound.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveFactorTypes

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open Exceptional RootClassificationExceptional ExceptionalSieveCatalog
open DynkinClassification Selection

private def klass (k : Fin 4) (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  ![CartanMatrix.A n, CartanMatrix.B n, CartanMatrix.C n, CartanMatrix.D n] k

private theorem classical_matches : ∀ (k : Fin 4) (n : Fin 8), 0 < n.val →
    (k ≠ 3 ∨ n.val ≠ 2) →
    ∃ (t : Factor) (s : Index t.datum ≃ Fin n.val), ∀ i j,
      klass k n.val (s i) (s j) = matrix t.datum i j := by
  native_decide

private theorem d2_disconnected : ¬(CartanMatrix.D 2).IsIndecomposable := by
  intro hd
  have step {x y : Fin 2} (p : Relation.ReflTransGen (fun i j => CartanMatrix.D 2 i j ≠ 0) x y) :
      x = y := by
    induction p with
    | refl => rfl
    | tail _ edge ih =>
      exact ih.trans ((show ∀ i j : Fin 2, CartanMatrix.D 2 i j ≠ 0 → i = j by decide) _ _ edge)
  exact (by decide : (0 : Fin 2) ≠ 1) (step (hd 0 1))

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] [LieAlgebra.IsSimple ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

/-- A matrix match with the catalog follows from the rank bound on the
actual simple factor, including the low-rank classical coincidences. -/
theorem simple_factor_matches_catalog (hr : finrank ℂ H ≤ 7) :
    ∃ (t : Factor) (s : Index t.datum ≃ b.support),
      ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j := by
  classical
  have hrank {n : ℕ} (e : b.support ≃ Fin n) : finrank ℂ H = n :=
    (finrank_eq_card_basis (b.toCoweightBasis.reindex e)).trans (Fintype.card_fin n)
  have hcl (k : Fin 4) (n : ℕ) (e : b.support ≃ Fin n) (h : b.cartanMatrix.reindex e e = klass k n) :
      ∃ (t : Factor) (s : Index t.datum ≃ b.support),
        ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j := by
    have hi := (actual_finite_indecomposable_cartan b).2
    have hk := Matrix.IsFiniteCartan.isIndecomposable_of_reindex hi e h
    have hp : 0 < n := by
      letI := RootPairing.IsIrreducible.nontrivial' (rootSystem H)
      rw [← hrank e]
      exact finrank_pos
    have hd : k ≠ 3 ∨ n ≠ 2 := by
      by_contra! hbad
      obtain ⟨rfl,rfl⟩ := hbad
      exact d2_disconnected hk
    obtain ⟨t, s, hs⟩ := classical_matches k ⟨n, by have := hrank e; omega⟩ hp hd
    exact ⟨t, s.trans e.symm, fun i j => (congrFun (congrFun h (s i)) (s j)).trans (hs i j)⟩
  rcases root_system_classical_or_exceptional b with hc | ⟨d, hd, s, hs⟩
  · rcases hc with ⟨n,e,he⟩ | ⟨n,e,he⟩ | ⟨n,e,he⟩ | ⟨n,e,he⟩
    · exact hcl 0 n e he
    · exact hcl 1 n e he
    · exact hcl 2 n e he
    · exact hcl 3 n e he
  · rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact ⟨.g2, s, hs⟩
    · exact ⟨.f4, s, hs⟩
    · exact ⟨.e6, s, hs⟩
    · exact ⟨.e7, s, hs⟩
    · have : finrank ℂ H = 8 := hrank s.symm
      omega

end CubicAnomaly.Classification.ExceptionalSieveFactorTypes
