import CubicAnomaly.Classification.RootClassificationClassicalAB

/-!
# Integral lifts of mod-three simple weights in types C and D

Use signed coordinates in the interval from minus one to one. The simple
weights are successive differences, with final row twice the last coordinate
in type C and the sum of the final two coordinates in type D. The simple
reflections act on coordinates by signed permutations.
-/

namespace CubicAnomaly.Classification.RootClassificationClassicalCD

open CubicAnomaly.Classification.RootClassificationClassicalAB

private def Small (x : ℕ → ℤ) : Prop := ∀ k, -1 ≤ x k ∧ x k ≤ 1

private def swapPair (x : ℕ → ℤ) (i k : ℕ) : ℤ :=
  if k = i then x (i + 1) else if k = i + 1 then x i else x k

private def flipLast (x : ℕ → ℤ) (m k : ℕ) : ℤ :=
  if k = m then -x m else x k

private def flipPair (x : ℕ → ℤ) (m k : ℕ) : ℤ :=
  if k = m then -x (m + 1) else if k = m + 1 then -x m else x k

private def cWeight (m : ℕ) (x : ℕ → ℤ) (j : Fin (m + 1)) : ℤ :=
  if j.val = m then 2 * x m else x j.val - x (j.val + 1)

private def dWeight (m : ℕ) (x : ℕ → ℤ) (j : Fin (m + 2)) : ℤ :=
  if j.val = m + 1 then x m + x (m + 1) else x j.val - x (j.val + 1)

private theorem c_reflection (m : ℕ) (x : ℕ → ℤ) (i j : Fin (m + 1)) :
    cWeight m (if i.val = m then flipLast x m else swapPair x i.val) j =
      cWeight m x j - CartanMatrix.C (m + 1) j i * cWeight m x i := by
  simp only [cWeight, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Nat.add_sub_cancel]
  grind [flipLast, swapPair]

private theorem d_reflection (m : ℕ) (x : ℕ → ℤ) (i j : Fin (m + 2)) :
    dWeight m (if i.val = m + 1 then flipPair x m else swapPair x i.val) j =
      dWeight m x j - CartanMatrix.D (m + 2) j i * dWeight m x i := by
  by_cases hi : i.val = m + 1 <;> by_cases hj : j.val = m + 1 <;>
    simp only [dWeight, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, hi, hj,
      if_true, if_false] <;> grind (splits := 24) [flipPair, swapPair]

private theorem swap_small {x : ℕ → ℤ} (hx : Small x) (i : ℕ) : Small (swapPair x i) := by
  intro k
  unfold swapPair
  split_ifs <;> apply hx

private theorem flip_last_small {x : ℕ → ℤ} (hx : Small x) (m : ℕ) : Small (flipLast x m) := by
  intro k
  unfold flipLast
  split_ifs
  · have := hx m
    omega
  · exact hx k

private theorem flip_pair_small {x : ℕ → ℤ} (hx : Small x) (m : ℕ) : Small (flipPair x m) := by
  intro k
  unfold flipPair
  split_ifs
  · have := hx (m + 1)
    omega
  · have := hx m
    omega
  · exact hx k


private theorem double_twice (r : ZMod 3) : 2 * (2 * r) = r := by
  fin_cases r <;> decide

/-- Every mod-three assignment for a C diagram lifts to an integral family
preserved by simple reflections, with all coordinates between −2 and 2. -/
theorem typeC_bounded_reflection_family {n : ℕ} (a : Fin n → ZMod 3) :
    ∃ (F : Set (Fin n → ℤ)) (w : Fin n → ℤ), w ∈ F ∧ (∀ i, (w i : ZMod 3) = a i) ∧
      (∀ v ∈ F, ∀ i, -2 ≤ v i ∧ v i ≤ 2) ∧
      ∀ v ∈ F, ∀ i, (fun j => v j - CartanMatrix.C n j i * v i) ∈ F := by
  cases n with
  | zero =>
    rw [show CartanMatrix.C 0 = CartanMatrix.A 0 by decide]
    exact typeA_bounded_reflection_family a
  | succ m =>
    obtain ⟨x, hx, _, hend, hdiff⟩ := bounded_tail_coordinates
      (fun i : Fin m => a i.castSucc) (2 * a (Fin.last m))
    let F : Set (Fin (m + 1) → ℤ) := {v | ∃ y, Small y ∧ v = cWeight m y}
    refine ⟨F, cWeight m x, ⟨x, hx, rfl⟩, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i.val = m
      · have : i = Fin.last m := Fin.ext hi
        subst i
        simpa [cWeight, hend] using double_twice (a (Fin.last m))
      · let j : Fin m := ⟨i.val, by omega⟩
        simpa [cWeight, hi, j] using hdiff j
    · rintro _ ⟨y, hy, rfl⟩ i
      have := hy i
      have := hy (i.val + 1)
      have := hy m
      unfold cWeight
      split_ifs <;> omega
    · rintro _ ⟨y, hy, rfl⟩ i
      refine ⟨if i.val = m then flipLast y m else swapPair y i.val, ?_, ?_⟩
      · split_ifs
        · exact flip_last_small hy _
        · exact swap_small hy _
      · exact funext (fun j => (c_reflection m y i j).symm)

/-- Every mod-three assignment for a D diagram lifts through its two terminal
weights. Their sum/difference determines the final signed coordinate since
2 is invertible modulo 3. -/
theorem typeD_bounded_reflection_family {n : ℕ} (a : Fin n → ZMod 3) :
    ∃ (F : Set (Fin n → ℤ)) (w : Fin n → ℤ), w ∈ F ∧ (∀ i, (w i : ZMod 3) = a i) ∧
      (∀ v ∈ F, ∀ i, -2 ≤ v i ∧ v i ≤ 2) ∧
      ∀ v ∈ F, ∀ i, (fun j => v j - CartanMatrix.D n j i * v i) ∈ F := by
  cases n with
  | zero =>
    rw [show CartanMatrix.D 0 = CartanMatrix.A 0 by decide]
    exact typeA_bounded_reflection_family a
  | succ n =>
    cases n with
    | zero =>
      rw [CartanMatrix.D_one]
      exact typeA_bounded_reflection_family a
    | succ m =>
      let last := Fin.last (m + 1)
      let nextLast := (Fin.last m).castSucc
      obtain ⟨x, hx, _, hend, hdiff⟩ := bounded_tail_coordinates
        (fun i : Fin (m + 1) => a i.castSucc) (2 * (a last - a nextLast))
      let F : Set (Fin (m + 2) → ℤ) := {v | ∃ y, Small y ∧ v = dWeight m y}
      refine ⟨F, dWeight m x, ⟨x, hx, rfl⟩, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i.val = m + 1
        · have hil : i = last := Fin.ext hi
          have hprev : (x m : ZMod 3) - x (m + 1) = a nextLast := hdiff (Fin.last m)
          rw [dWeight, if_pos hi, Int.cast_add, hil]
          calc
            _ = ((x m : ZMod 3) - x (m + 1)) + 2 * x (m + 1) := by ring
            _ = a last := by rw [hprev, hend, double_twice]; ring
        · let j : Fin (m + 1) := ⟨i.val, by omega⟩
          simpa [dWeight, hi, j] using hdiff j
      · rintro _ ⟨y, hy, rfl⟩ i
        have := hy i
        have := hy (i.val + 1)
        have := hy m
        have := hy (m + 1)
        unfold dWeight
        split_ifs <;> omega
      · rintro _ ⟨y, hy, rfl⟩ i
        refine ⟨if i.val = m + 1 then flipPair y m else swapPair y i.val, ?_, ?_⟩
        · split_ifs
          · exact flip_pair_small hy _
          · exact swap_small hy _
        · exact funext (fun j => (d_reflection m y i j).symm)

end CubicAnomaly.Classification.RootClassificationClassicalCD
