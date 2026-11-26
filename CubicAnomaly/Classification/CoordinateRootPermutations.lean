import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Dual.Defs

/-! Stability under neighboring simple reflections gives arbitrary relabelings
of coordinate weights and realizes the two-coordinate Weyl orbits. -/

namespace CubicAnomaly.Classification.CoordinateRootPermutations

open Equiv

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (ε : Fin (n+1) → V) (R : Set V)
    (adj : ∀ j : Fin n, ∃ T : V ≃ₗ[K] V,
      (∀ i, T (ε i) = ε (swap j.castSucc j.succ i)) ∧ Set.MapsTo T R R)

include adj in
theorem coordinate_permutation_action (p : Equiv.Perm (Fin (n+1))) :
    ∃ T : V ≃ₗ[K] V, (∀ i, T (ε i) = ε (p i)) ∧ Set.MapsTo T R R := by
  have hp : p ∈ Submonoid.closure (Set.range fun i : Fin n => swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hp using Submonoid.closure_induction with
  | mem p hp => obtain ⟨j,rfl⟩ := hp; exact adj j
  | one => exact ⟨LinearEquiv.refl _ _, fun _ => rfl, fun _ hx => hx⟩
  | mul p q _ _ hp hq =>
    obtain ⟨P, hP, hp'⟩ := hp
    obtain ⟨Q, hQ, hq'⟩ := hq
    exact ⟨Q.trans P, fun i => by simp [hP, hQ], hp'.comp hq'⟩

theorem exists_perm_pair {α : Type*} [DecidableEq α] {a b i j : α}
    (hab : a ≠ b) (hij : i ≠ j) : ∃ p : Equiv.Perm α, p a = i ∧ p b = j := by
  let P := swap a i
  have hn : i ≠ P b := by
    rw [show i = P a from (swap_apply_left a i).symm]
    exact P.injective.ne hab
  refine ⟨P.trans (swap (P b) j), ?_, ?_⟩
  · change swap (P b) j (P a) = i
    simpa only [P, swap_apply_left] using (swap_apply_of_ne_of_ne hn hij)
  · exact swap_apply_left _ _

include adj in
theorem signed_pair_orbit {a b : Fin (n+1)} (hab : a ≠ b) {c : K}
    (hroot : ε a + c • ε b ∈ R) (i j : Fin (n+1)) (hij : i ≠ j) : ε i + c • ε j ∈ R := by
  obtain ⟨p,hi,hj⟩ := exists_perm_pair hab hij
  obtain ⟨T,hT,hr⟩ := coordinate_permutation_action ε R adj p
  simpa only [map_add, map_smul, hT, hi, hj] using hr hroot

end CubicAnomaly.Classification.CoordinateRootPermutations
