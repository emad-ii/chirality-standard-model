import CubicAnomaly.Classification.ClassicalToral
import Mathlib.Data.Matrix.Cartan

/-!
# Bounded integral grading coordinates for the A and B Cartan matrices

Consecutive differences of coordinates in `{-1,0,1}` realize all ternary
assignments to simple roots. The reflections exchange two consecutive
coordinates, with a sign change at the short end of the B diagram.
-/

namespace CubicAnomaly.Classification.RootClassificationClassicalAB

open CubicAnomaly.Classification.Classical

private theorem lift_reduces (r : ZMod 3) : (ternaryLift r : ZMod 3) = r := by
  fin_cases r <;> decide

/-- Integrate the prescribed simple differences with a chosen terminal
residue, then lift every coordinate to `{-1,0,1}`. -/
theorem bounded_tail_coordinates {n : ℕ} (a : Fin n → ZMod 3) (c : ZMod 3) :
    ∃ x : ℕ → ℤ, (∀ k, -1 ≤ x k ∧ x k ≤ 1) ∧ x n = ternaryLift c ∧
      ((x n : ℤ) : ZMod 3) = c ∧
      ∀ i : Fin n, ((x i : ℤ) : ZMod 3) - x (i.val + 1) = a i := by
  let p (k : ℕ) : ZMod 3 := ∑ j ∈ Finset.range k, if hj : j < n then a ⟨j, hj⟩ else 0
  let x (k : ℕ) := ternaryLift (c + p n - p k)
  refine ⟨x, ?_, by simp [x], by simp [x, lift_reduces], ?_⟩
  · intro k
    dsimp [x, ternaryLift]
    split_ifs <;> decide
  · intro i
    have hstep : p (i.val + 1) = p i + a i := by simp [p, Finset.sum_range_succ, i.isLt]
    simp only [x, lift_reduces, hstep]
    abel

private def diffs {n : ℕ} (x : ℕ → ℤ) (i : Fin n) := x i - x (i.val + 1)

private def swapNext (x : ℕ → ℤ) (i k : ℕ) :=
  if k = i then x (i + 1) else if k = i + 1 then x i else x k

private theorem swapNext_bounds (x : ℕ → ℤ) (hx : ∀ k, -1 ≤ x k ∧ x k ≤ 1) (i k : ℕ) :
    -1 ≤ swapNext x i k ∧ swapNext x i k ≤ 1 := by
  unfold swapNext
  split_ifs <;> exact hx _

private theorem swapNext_diffs {n : ℕ} (x : ℕ → ℤ) (i j : Fin n) :
    diffs (swapNext x i) j = diffs x j - CartanMatrix.A n j i * diffs x i := by
  simp only [swapNext, diffs, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | omega | (simp_all <;> omega)

private def orbits (n : ℕ) (lastZero : Bool) : Set (Fin n → ℤ) :=
  {w | ∃ x : ℕ → ℤ, (∀ k, -1 ≤ x k ∧ x k ≤ 1) ∧ (lastZero = true → x n = 0) ∧ w = diffs x}

private theorem orbit_lift (n : ℕ) (lastZero : Bool) (a : Fin n → ZMod 3) :
    ∃ w ∈ orbits n lastZero, ∀ i, (w i : ZMod 3) = a i := by
  obtain ⟨x, hx, hn, _, hd⟩ := bounded_tail_coordinates a 0
  refine ⟨diffs x, ⟨x, hx, fun _ => by simpa [ternaryLift] using hn, rfl⟩, ?_⟩
  intro i
  simpa [diffs] using hd i

private theorem orbit_bounds (n : ℕ) (b : Bool) (v : Fin n → ℤ) (hv : v ∈ orbits n b)
    (i : Fin n) : -2 ≤ v i ∧ v i ≤ 2 := by
  obtain ⟨x, hx, _, rfl⟩ := hv
  have := hx i
  have := hx (i.val + 1)
  dsimp [diffs]
  omega

/-- For every ternary grading on an A diagram there is a bounded integral
lift inside a family stable under all actual simple Cartan reflections. -/
theorem typeA_bounded_reflection_family {n : ℕ} (a : Fin n → ZMod 3) :
    ∃ (F : Set (Fin n → ℤ)) (w : Fin n → ℤ), w ∈ F ∧ (∀ i, (w i : ZMod 3) = a i) ∧
      (∀ v ∈ F, ∀ i, -2 ≤ v i ∧ v i ≤ 2) ∧
      ∀ v ∈ F, ∀ i, (fun j => v j - CartanMatrix.A n j i * v i) ∈ F := by
  obtain ⟨w, hw, ha⟩ := orbit_lift n false a
  refine ⟨orbits n false, w, hw, ha, orbit_bounds n false, ?_⟩
  rintro _ ⟨x, hx, _, rfl⟩ i
  exact ⟨swapNext x i, swapNext_bounds x hx i, by simp, funext (fun j => (swapNext_diffs x i j).symm)⟩

private def flipAt (x : ℕ → ℤ) (i k : ℕ) := if k = i then -x i else x k

private theorem flipLast_diffs {n : ℕ} (x : ℕ → ℤ) (hx : x n = 0) (i j : Fin n)
    (hi : i.val + 1 = n) :
    diffs (flipAt x i) j = diffs x j - CartanMatrix.B n j i * diffs x i := by
  have hj := j.isLt
  have hii := i.isLt
  have h' : i.val = n - 1 := by omega
  simp only [flipAt, diffs, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, h']
  split_ifs <;> first | omega | (simp_all; omega)

/-- The B family uses a zero terminal coordinate. Interior reflections swap
neighbours and the last reflection negates the last free coordinate. -/
theorem typeB_bounded_reflection_family {n : ℕ} (a : Fin n → ZMod 3) :
    ∃ (F : Set (Fin n → ℤ)) (w : Fin n → ℤ), w ∈ F ∧ (∀ i, (w i : ZMod 3) = a i) ∧
      (∀ v ∈ F, ∀ i, -2 ≤ v i ∧ v i ≤ 2) ∧
      ∀ v ∈ F, ∀ i, (fun j => v j - CartanMatrix.B n j i * v i) ∈ F := by
  obtain ⟨w, hw, ha⟩ := orbit_lift n true a
  refine ⟨orbits n true, w, hw, ha, orbit_bounds n true, ?_⟩
  rintro _ ⟨x, hx, hn, rfl⟩ i
  have hxn := hn rfl
  have hii := i.isLt
  by_cases hi : i.val + 1 = n
  · refine ⟨flipAt x i, ?_, ?_, funext (fun j => (flipLast_diffs x hxn i j hi).symm)⟩
    · intro k
      simp only [flipAt]
      split_ifs <;> first | exact hx _ | have := hx i; omega
    · intro _
      simp [flipAt, ne_of_gt hii, hxn]
  · have hn' : i.val ≠ n - 1 := by omega
    refine ⟨swapNext x i, swapNext_bounds x hx i, fun _ => ?_, ?_⟩
    · simp [swapNext, ne_of_gt hii, Ne.symm hi, hxn]
    · funext j
      rw [swapNext_diffs]
      simp only [CartanMatrix.B, CartanMatrix.A, Matrix.of_apply, hn', ↓reduceIte]
      split_ifs <;> simp_all

end CubicAnomaly.Classification.RootClassificationClassicalAB
