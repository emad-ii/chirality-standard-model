import CubicAnomaly.Classification.TypeCCartanCoordinates
import CubicAnomaly.Classification.CoordinateRootPermutations

/-! The long and short roots of an actual symplectic Cartan, obtained by
simple reflections of its actual simple roots. -/

namespace CubicAnomaly.Classification.TypeCRootOrbit

open LieAlgebra LieAlgebra.IsKilling LieModule Module TypeCCartanCoordinates SymplecticMatrixGenerators
open Equiv

variable {n : ℕ} {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  (s : b.support ≃ Fin (n+1)) (hm : b.cartanMatrix.reindex s s = CartanMatrix.C (n+1))

include hm in
theorem adjacent_reflection (j : Fin n) (i : Fin (n+1)) :
    (rootSystem H).reflection (s.symm j.castSucc) (epsilon H b s i) =
      epsilon H b s (swap j.castSucc j.succ i) := by
  rw [RootPairing.reflection_apply]
  change epsilon H b s i - epsilon H b s i (coroot (s.symm j.castSucc).val.val) • _ = _
  rw [epsilon_apply, coordinates_coroot H b s hm, epsilon_simple]
  simp only [corootVector, Fin.lastCases_castSucc, Pi.sub_apply, Pi.single_apply]
  by_cases hi : i = j.castSucc
  · subst i
    simp [Fin.castSucc_lt_succ.ne]
  · by_cases hj : i = j.succ
    · subst i
      simp [Fin.castSucc_lt_succ.ne']
    · simp [hi, hj, swap_apply_of_ne_of_ne]

include hm in
theorem final_reflection (i : Fin (n+1)) :
    (rootSystem H).reflection (s.symm (Fin.last n)) (epsilon H b s i) =
      if i = Fin.last n then -epsilon H b s i else epsilon H b s i := by
  rw [RootPairing.reflection_apply]
  change epsilon H b s i - epsilon H b s i (coroot (s.symm (Fin.last n)).val.val) • _ = _
  rw [epsilon_apply, coordinates_coroot H b s hm, epsilon_last]
  by_cases hi : i = Fin.last n
  · subst i
    simp [corootVector, two_smul]
  · simp [corootVector, hi]

include hm in
/-- Every ordinary permutation of the signed coordinates is induced by
a product of adjacent simple reflections preserving the actual roots. -/
theorem permutation_action (p : Equiv.Perm (Fin (n+1))) :
    ∃ T : Dual ℂ H ≃ₗ[ℂ] Dual ℂ H, (∀ i, T (epsilon H b s i) = epsilon H b s (p i)) ∧
      Set.MapsTo T (Set.range (rootSystem H).root) (Set.range (rootSystem H).root) := by
  exact CoordinateRootPermutations.coordinate_permutation_action _ _ (fun j =>
    ⟨_, adjacent_reflection H b s hm j, (rootSystem H).mapsTo_reflection_root _⟩) p

include hm in
theorem long_root (i : Fin (n+1)) : 2 • epsilon H b s i ∈ Set.range (rootSystem H).root := by
  obtain ⟨T, hT, hr⟩ := permutation_action H b s hm (swap (Fin.last n) i)
  have h := hr (Set.mem_range_self ((s.symm (Fin.last n)).val))
  rwa [epsilon_last, map_nsmul, hT, swap_apply_left] at h

include hm in
theorem difference_root (i j : Fin (n+1)) (hij : i ≠ j) :
    epsilon H b s i - epsilon H b s j ∈ Set.range (rootSystem H).root := by
  have hn : 0 < n := by
    by_contra! hn
    obtain rfl := Nat.eq_zero_of_le_zero hn
    exact hij (Fin.ext (by omega))
  let k : Fin n := ⟨0,hn⟩
  obtain ⟨p, hpi, hpj⟩ := CoordinateRootPermutations.exists_perm_pair (Fin.castSucc_lt_succ (i := k)).ne hij
  obtain ⟨T, hT, hr⟩ := permutation_action H b s hm p
  have h := hr (Set.mem_range_self ((s.symm k.castSucc).val))
  rwa [epsilon_simple, map_sub, hT, hT, hpi, hpj] at h

include hm in
theorem sum_root (i j : Fin (n+1)) :
    epsilon H b s i + epsilon H b s j ∈ Set.range (rootSystem H).root := by
  by_cases he : i = j
  · subst j; simpa only [two_smul] using long_root H b s hm i
  let p := swap j (Fin.last n)
  have hni : p i ≠ Fin.last n := by
    rw [show Fin.last n = p j from (swap_apply_left _ _).symm]
    exact p.injective.ne he
  have hd := difference_root H b s hm (p i) (Fin.last n) hni
  have hsum := (rootSystem H).mapsTo_reflection_root (s.symm (Fin.last n)).val hd
  rw [map_sub, final_reflection H b s hm, final_reflection H b s hm,
    if_neg hni, if_pos rfl, sub_neg_eq_add] at hsum
  obtain ⟨T, hT, hr⟩ := permutation_action H b s hm p
  have h := hr hsum
  simpa only [map_add, hT, p, swap_apply_self, swap_apply_right] using h

theorem negative_root {a : Dual ℂ H} (ha : a ∈ Set.range (rootSystem H).root) :
    -a ∈ Set.range (rootSystem H).root := by
  obtain ⟨i,rfl⟩ := ha
  exact ⟨_, ((rootSystem H).root_reflectionPerm i i).trans ((rootSystem H).reflection_apply_self i)⟩

end CubicAnomaly.Classification.TypeCRootOrbit
