import CubicAnomaly.Classification.OrthogonalMatrixGenerators
import CubicAnomaly.Classification.ClassicalCartanCoordinates
import CubicAnomaly.Classification.CoordinateRootPermutations
import CubicAnomaly.Classification.OrthogonalRootCounts
import CubicAnomaly.Classification.KillingDimension

/-! The signed pair roots of an actual Cartan with type-D Cartan matrix. -/

namespace CubicAnomaly.Classification.TypeDCartanCoordinates

open LieAlgebra LieAlgebra.IsKilling LieModule Module OrthogonalMatrixGenerators Equiv

variable {n : ℕ}

private def weightMap : (Fin (n+2) → ℂ) →ₗ[ℂ] (Fin (n+2) → ℂ) where
  toFun d i := weight i d
  map_add' d e := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [weight, add_add_add_comm]
    | cast j => simp [weight]; ring
  map_smul' c d := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [weight, mul_add]
    | cast j => simp [weight, mul_sub]

private noncomputable def weightEquiv : (Fin (n+2) → ℂ) ≃ₗ[ℂ] (Fin (n+2) → ℂ) := by
  have hinj : Function.Injective (weightMap (n := n)) := by
    intro d e he
    have hv (i : Fin (n+2)) : weight i d = weight i e := congrFun he i
    have h₁ := hv (Fin.last (n+1))
    have h₂ := hv (Fin.last n).castSucc
    simp only [weight, Fin.lastCases_last, Fin.lastCases_castSucc, Fin.succ_last] at h₁ h₂
    have hend : d (terminal n) = e (terminal n) := by
      change d (penultimate n) - d (terminal n) = e (penultimate n) - e (terminal n) at h₂
      linear_combination (h₁ - h₂) / 2
    ext i
    induction i using Fin.reverseInduction with
    | last => exact hend
    | cast j ih =>
      have hj := hv j.castSucc
      simp [weight, ih] at hj
      exact hj
  exact LinearEquiv.ofBijective weightMap ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  (s : b.support ≃ Fin (n+2)) (hm : b.cartanMatrix.reindex s s = CartanMatrix.D (n+2))

noncomputable def coordinates : H ≃ₗ[ℂ] (Fin (n+2) → ℂ) := ClassicalCartanCoordinates.coordinates H b s weightEquiv

theorem typeD_weight_coordinates (h : H) (i : Fin (n+2)) :
    weight i (coordinates H b s h) = (s.symm i).val.val h := ClassicalCartanCoordinates.value_coordinates H b s weightEquiv h i

include hm in
theorem typeD_coordinates_coroot (i : Fin (n+2)) :
    coordinates H b s (coroot (s.symm i).val.val) = corootVector i :=
  ClassicalCartanCoordinates.classical_coordinates_coroot H b s weightEquiv _ hm _ typeD_weight_coroot i

noncomputable def epsilon (i : Fin (n+2)) : Dual ℂ H :=
  (LinearMap.proj i).comp (coordinates H b s).toLinearMap

theorem typeD_epsilon_apply (i : Fin (n+2)) (h : H) : epsilon H b s i h = coordinates H b s h i := rfl

theorem typeD_epsilon_simple (i : Fin (n+1)) :
    (rootSystem H).root (s.symm i.castSucc) = epsilon H b s i.castSucc - epsilon H b s i.succ := by
  ext h
  simpa only [weight, Fin.lastCases_castSucc] using (typeD_weight_coordinates H b s h i.castSucc).symm

theorem typeD_epsilon_last : (rootSystem H).root (s.symm (terminal n)) =
    epsilon H b s (penultimate n) + epsilon H b s (terminal n) := by
  ext h
  simpa only [weight, terminal, Fin.lastCases_last] using (typeD_weight_coordinates H b s h (terminal n)).symm

include hm in
theorem typeD_adjacent_reflection (j : Fin (n+1)) (i : Fin (n+2)) :
    (rootSystem H).reflection (s.symm j.castSucc) (epsilon H b s i) =
      epsilon H b s (swap j.castSucc j.succ i) := by
  rw [RootPairing.reflection_apply]
  change epsilon H b s i - epsilon H b s i (coroot (s.symm j.castSucc).val.val) • _ = _
  rw [typeD_epsilon_apply, typeD_coordinates_coroot H b s hm, typeD_epsilon_simple]
  simp only [corootVector, Fin.lastCases_castSucc, Pi.sub_apply, Pi.single_apply]
  by_cases hi : i = j.castSucc
  · subst i
    simp [Fin.castSucc_lt_succ.ne]
  · by_cases hj : i = j.succ
    · subst i
      simp [Fin.castSucc_lt_succ.ne']
    · simp [hi, hj, swap_apply_of_ne_of_ne]


include hm in
theorem pair_roots (i j : Fin (n+2)) (hij : i ≠ j) :
    epsilon H b s i - epsilon H b s j ∈ Set.range (rootSystem H).root ∧
    epsilon H b s i + epsilon H b s j ∈ Set.range (rootSystem H).root := by
  have adj (k : Fin (n+1)) : ∃ T : Dual ℂ H ≃ₗ[ℂ] Dual ℂ H,
      (∀ l, T (epsilon H b s l) = epsilon H b s (swap k.castSucc k.succ l)) ∧
      Set.MapsTo T (Set.range (rootSystem H).root) (Set.range (rootSystem H).root) :=
    ⟨_, typeD_adjacent_reflection H b s hm k, (rootSystem H).mapsTo_reflection_root _⟩
  have hd := Set.mem_range_self (f := (rootSystem H).root) (s.symm (penultimate n)).val
  rw [typeD_epsilon_simple, Fin.succ_last] at hd
  have hs := Set.mem_range_self (f := (rootSystem H).root) (s.symm (terminal n)).val
  rw [typeD_epsilon_last] at hs
  have hol (c : ℂ) := CoordinateRootPermutations.signed_pair_orbit (c := c) (epsilon H b s) _ adj (Fin.castSucc_ne_last (Fin.last n))
  constructor
  · simpa [sub_eq_add_neg] using hol (-1) (by simpa [sub_eq_add_neg] using hd) i j hij
  · simpa using hol 1 (by simpa using hs) i j hij

include hm in
theorem typeD_source_dimension : (n+2) * (2*(n+2)-1) ≤ finrank ℂ L := by
  let T := coordinates H b s
  let u (i : Fin (n+2)) := T.symm (Pi.single i 1)
  have hv (i j : Fin (n+2)) : epsilon H b s i (u j) = if i = j then 1 else 0 := by
    change T (T.symm (Pi.single j 1)) i = _
    simp [Pi.single_apply]
  have hc := OrthogonalRootCounts.even_bound (fun a : H.root => (rootSystem H).root a) (epsilon H b s) u hv
    (fun i j h => (pair_roots H b s hm i j h).1) (fun i j h => (pair_roots H b s hm i j h).2)
    (fun i j h => by
      obtain ⟨a,ha⟩ := (pair_roots H b s hm i j h).2
      rw [← ha]; exact ⟨_, ((rootSystem H).root_reflectionPerm a a).trans ((rootSystem H).reflection_apply_self a)⟩)
  rw [KillingDimension.killing_finrank_eq_cartan_add_roots H, KillingDimension.actual_root_count_eq_card H,
    finrank_eq_card_basis (b.toCoweightBasis.reindex s), Fintype.card_fin]
  have ht : 2*(n+2)-1 = 2*n+3 := by omega
  rw [ht]
  nlinarith

end CubicAnomaly.Classification.TypeDCartanCoordinates
