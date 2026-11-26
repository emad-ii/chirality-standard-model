import CubicAnomaly.Classification.OddOrthogonalMatrixGenerators
import CubicAnomaly.Classification.ClassicalCartanCoordinates
import CubicAnomaly.Classification.CoordinateRootPermutations
import CubicAnomaly.Classification.OrthogonalRootCounts
import CubicAnomaly.Classification.KillingDimension

/-! The signed one- and two-coordinate actual roots of a type-B Cartan. -/
namespace CubicAnomaly.Classification.TypeBCartanCoordinates

open LieAlgebra LieAlgebra.IsKilling LieModule Module OddOrthogonalMatrixGenerators Equiv

variable {n : ℕ}

private def weightMap : (Fin (n+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ) where
  toFun d i := weight i d
  map_add' d e := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [weight]
    | cast j => simp [weight]; ring
  map_smul' c d := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [weight]
    | cast j => simp [weight, mul_sub]

private noncomputable def weightEquiv : (Fin (n+1) → ℂ) ≃ₗ[ℂ] (Fin (n+1) → ℂ) := by
  have hinj : Function.Injective (weightMap (n := n)) := by
    intro d e he
    have hv (i : Fin (n+1)) : weight i d = weight i e := congrFun he i
    ext i
    induction i using Fin.reverseInduction with
    | last => simpa [weight] using hv (Fin.last n)
    | cast j ih =>
      have hj := hv j.castSucc
      simp [weight, ih] at hj
      exact hj
  exact LinearEquiv.ofBijective weightMap ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  (s : b.support ≃ Fin (n+1)) (hm : b.cartanMatrix.reindex s s = CartanMatrix.B (n+1))

noncomputable def coordinates : H ≃ₗ[ℂ] (Fin (n+1) → ℂ) := ClassicalCartanCoordinates.coordinates H b s weightEquiv

theorem typeB_weight_coordinates (h : H) (i : Fin (n+1)) :
    weight i (coordinates H b s h) = (s.symm i).val.val h := ClassicalCartanCoordinates.value_coordinates H b s weightEquiv h i

include hm in
theorem typeB_coordinates_coroot (i : Fin (n+1)) :
    coordinates H b s (coroot (s.symm i).val.val) = corootVector i :=
  ClassicalCartanCoordinates.classical_coordinates_coroot H b s weightEquiv _ hm _ typeB_weight_coroot i

noncomputable def epsilon (i : Fin (n+1)) : Dual ℂ H :=
  (LinearMap.proj i).comp (coordinates H b s).toLinearMap

theorem typeB_epsilon_apply (i : Fin (n+1)) (h : H) : epsilon H b s i h = coordinates H b s h i := rfl

theorem typeB_epsilon_simple (i : Fin n) :
    (rootSystem H).root (s.symm i.castSucc) = epsilon H b s i.castSucc - epsilon H b s i.succ := by
  ext h
  simpa only [weight, Fin.lastCases_castSucc] using (typeB_weight_coordinates H b s h i.castSucc).symm

theorem typeB_epsilon_last : (rootSystem H).root (s.symm (Fin.last n)) = epsilon H b s (Fin.last n) := by
  ext h
  simpa only [weight, Fin.lastCases_last] using (typeB_weight_coordinates H b s h (Fin.last n)).symm

include hm in
theorem typeB_adjacent_reflection (j : Fin n) (i : Fin (n+1)) :
    (rootSystem H).reflection (s.symm j.castSucc) (epsilon H b s i) =
      epsilon H b s (swap j.castSucc j.succ i) := by
  rw [RootPairing.reflection_apply]
  change epsilon H b s i - epsilon H b s i (coroot (s.symm j.castSucc).val.val) • _ = _
  rw [typeB_epsilon_apply, typeB_coordinates_coroot H b s hm, typeB_epsilon_simple]
  simp only [corootVector, Fin.lastCases_castSucc, Pi.sub_apply, Pi.single_apply]
  by_cases hi : i = j.castSucc
  · subst i
    simp [Fin.castSucc_lt_succ.ne]
  · by_cases hj : i = j.succ
    · subst i
      simp [Fin.castSucc_lt_succ.ne']
    · simp [hi, hj, swap_apply_of_ne_of_ne]

include hm in
theorem typeB_final_reflection (i : Fin (n+1)) :
    (rootSystem H).reflection (s.symm (Fin.last n)) (epsilon H b s i) =
      if i = Fin.last n then -epsilon H b s i else epsilon H b s i := by
  rw [RootPairing.reflection_apply]
  change epsilon H b s i - epsilon H b s i (coroot (s.symm (Fin.last n)).val.val) • _ = _
  rw [typeB_epsilon_apply, typeB_coordinates_coroot H b s hm, typeB_epsilon_last]
  by_cases hi : i = Fin.last n
  · subst i
    simp [corootVector, two_smul]
  · simp [corootVector, hi]

include hm in
/-- Every ordinary permutation of the signed coordinates is induced by
a product of adjacent simple reflections preserving the actual roots. -/
theorem typeB_permutation_action (p : Equiv.Perm (Fin (n+1))) :
    ∃ T : Dual ℂ H ≃ₗ[ℂ] Dual ℂ H, (∀ i, T (epsilon H b s i) = epsilon H b s (p i)) ∧
      Set.MapsTo T (Set.range (rootSystem H).root) (Set.range (rootSystem H).root) := by
  exact CoordinateRootPermutations.coordinate_permutation_action _ _ (fun j =>
    ⟨_, typeB_adjacent_reflection H b s hm j, (rootSystem H).mapsTo_reflection_root _⟩) p

include hm in
theorem short_root (i : Fin (n+1)) : epsilon H b s i ∈ Set.range (rootSystem H).root := by
  obtain ⟨T, hT, hr⟩ := typeB_permutation_action H b s hm (swap (Fin.last n) i)
  have h := hr (Set.mem_range_self ((s.symm (Fin.last n)).val))
  rwa [typeB_epsilon_last, hT, swap_apply_left] at h

include hm in
theorem typeB_difference_root (i j : Fin (n+1)) (hij : i ≠ j) :
    epsilon H b s i - epsilon H b s j ∈ Set.range (rootSystem H).root := by
  have hn : 0 < n := by
    by_contra! hn
    obtain rfl := Nat.eq_zero_of_le_zero hn
    exact hij (Fin.ext (by omega))
  let k : Fin n := ⟨0,hn⟩
  obtain ⟨p, hpi, hpj⟩ := CoordinateRootPermutations.exists_perm_pair (Fin.castSucc_lt_succ (i := k)).ne hij
  obtain ⟨T, hT, hr⟩ := typeB_permutation_action H b s hm p
  have h := hr (Set.mem_range_self ((s.symm k.castSucc).val))
  rwa [typeB_epsilon_simple, map_sub, hT, hT, hpi, hpj] at h

include hm in
theorem typeB_sum_root (i j : Fin (n+1)) (he : i ≠ j) :
    epsilon H b s i + epsilon H b s j ∈ Set.range (rootSystem H).root := by
  let p := swap j (Fin.last n)
  have hni : p i ≠ Fin.last n := by
    rw [show Fin.last n = p j from (swap_apply_left _ _).symm]
    exact p.injective.ne he
  have hd := typeB_difference_root H b s hm (p i) (Fin.last n) hni
  have hsum := (rootSystem H).mapsTo_reflection_root (s.symm (Fin.last n)).val hd
  rw [map_sub, typeB_final_reflection H b s hm, typeB_final_reflection H b s hm,
    if_neg hni, if_pos rfl, sub_neg_eq_add] at hsum
  obtain ⟨T, hT, hr⟩ := typeB_permutation_action H b s hm p
  have h := hr hsum
  simpa only [map_add, hT, p, swap_apply_self, swap_apply_right] using h

theorem typeB_negative_root {a : Dual ℂ H} (ha : a ∈ Set.range (rootSystem H).root) :
    -a ∈ Set.range (rootSystem H).root := by
  obtain ⟨i,rfl⟩ := ha
  exact ⟨_, ((rootSystem H).root_reflectionPerm i i).trans ((rootSystem H).reflection_apply_self i)⟩


include hm in
theorem typeB_source_dimension : (n+1) * (2*(n+1)+1) ≤ finrank ℂ L := by
  let T := coordinates H b s
  let u (i : Fin (n+1)) := T.symm (Pi.single i 1)
  have hv (i j : Fin (n+1)) : epsilon H b s i (u j) = if i = j then 1 else 0 := by
    change T (T.symm (Pi.single j 1)) i = _
    simp [Pi.single_apply]
  have hw (i : Fin (n+1)) : epsilon H b s i (T.symm (fun _ => 1)) = 1 := by
    change T (T.symm (fun _ => 1)) i = _
    simp
  have hc := OrthogonalRootCounts.odd_bound (fun a : H.root => (rootSystem H).root a)
    (epsilon H b s) u hv (typeB_difference_root H b s hm) (typeB_sum_root H b s hm)
    (fun i j h => typeB_negative_root H (typeB_sum_root H b s hm i j h)) _ hw (short_root H b s hm)
    (fun i => typeB_negative_root H (short_root H b s hm i))
  rw [KillingDimension.killing_finrank_eq_cartan_add_roots H, KillingDimension.actual_root_count_eq_card H,
    finrank_eq_card_basis (b.toCoweightBasis.reindex s), Fintype.card_fin]
  nlinarith

end CubicAnomaly.Classification.TypeBCartanCoordinates
