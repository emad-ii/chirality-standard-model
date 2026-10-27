import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Realizing exact sparse coefficient lists

Finite integer coefficient lists can be checked computationally, then
realized in any additive module. Equality is checked on the union of the
lists' supports, which suffices for equality of their actual realizations.
-/

namespace CubicAnomaly.Fixed.SparseRealization

variable {D M : Type*} [DecidableEq D] [AddCommGroup M]

abbrev Sparse (D : Type*) := List (D × ℤ)

def coefficient (xs : Sparse D) (d : D) : ℤ :=
  (xs.map fun p => if p.1 = d then p.2 else 0).sum

def realize (basis : D → M) (xs : Sparse D) : M :=
  (xs.map fun p => p.2 • basis p.1).sum

def scale (n : ℤ) (xs : Sparse D) : Sparse D :=
  xs.map fun p => (p.1, n * p.2)

def linearExtend (f : D → Sparse D) (xs : Sparse D) : Sparse D :=
  xs.flatMap fun p => scale p.2 (f p.1)

omit [DecidableEq D] in
theorem sparse_realize_nil (basis : D → M) : realize basis [] = 0 := rfl

omit [DecidableEq D] in
theorem sparse_realize_cons (basis : D → M) (p : D × ℤ) (xs : Sparse D) :
    realize basis (p :: xs) = p.2 • basis p.1 + realize basis xs := rfl

omit [DecidableEq D] in
theorem sparse_realize_append (basis : D → M) (xs ys : Sparse D) :
    realize basis (xs ++ ys) = realize basis xs + realize basis ys := by
  simp [realize]

omit [DecidableEq D] in
theorem sparse_realize_scale (basis : D → M) (n : ℤ) (xs : Sparse D) :
    realize basis (scale n xs) = n • realize basis xs := by
  induction xs with
  | nil => simp [realize, scale]
  | cons p xs ih =>
      change realize basis ((p.1, n * p.2) :: scale n xs) =
        n • realize basis (p :: xs)
      rw [sparse_realize_cons, sparse_realize_cons, ih]
      simp [mul_smul, smul_add]

omit [DecidableEq D] in
theorem sparse_realize_linearExtend (basis : D → M) (f : D → Sparse D)
    (xs : Sparse D) :
    realize basis (linearExtend f xs) = realize (fun d => realize basis (f d)) xs := by
  induction xs with
  | nil => simp [linearExtend, realize]
  | cons p xs ih =>
      change realize basis (scale p.2 (f p.1) ++ linearExtend f xs) =
        realize (fun d => realize basis (f d)) (p :: xs)
      rw [sparse_realize_append, sparse_realize_scale, sparse_realize_cons, ih]

omit [DecidableEq D] in
theorem sparse_map_realize {N : Type*} [AddCommGroup N]
    (basis : D → M) (A : M →+ N) (xs : Sparse D) :
    A (realize basis xs) = realize (fun d => A (basis d)) xs := by
  induction xs with
  | nil => simp [realize]
  | cons p xs ih =>
      rw [sparse_realize_cons, sparse_realize_cons, map_add, map_zsmul, ih]

omit [DecidableEq D] in
/-- A sparse action agrees with an actual additive map once they agree on
the labels occurring in the input. -/
theorem sparse_realize_action (basis : D → M) (A : M →+ M)
    (f : D → Sparse D) (xs : Sparse D)
    (h : ∀ p ∈ xs, A (basis p.1) = realize basis (f p.1)) :
    A (realize basis xs) = realize basis (linearExtend f xs) := by
  rw [sparse_map_realize, sparse_realize_linearExtend]
  unfold realize
  congr 1
  apply List.map_congr_left
  intro p hp
  change p.2 • A (basis p.1) = p.2 • realize basis (f p.1)
  rw [h p hp]

private noncomputable def freeCoefficients (xs : Sparse D) : D →₀ ℤ :=
  (xs.map fun p => Finsupp.single p.1 p.2).sum

private theorem freeCoefficients_apply (xs : Sparse D) (d : D) :
    freeCoefficients xs d = coefficient xs d := by
  induction xs with
  | nil => simp [freeCoefficients, coefficient]
  | cons p xs ih =>
      change (Finsupp.single p.1 p.2 + freeCoefficients xs) d =
        (if p.1 = d then p.2 else 0) + coefficient xs d
      simp [Finsupp.single_apply, ih]

omit [DecidableEq D] in
private theorem realize_eq_linearCombination (basis : D → M) (xs : Sparse D) :
    realize basis xs = Finsupp.linearCombination ℤ basis (freeCoefficients xs) := by
  induction xs with
  | nil => simp [realize, freeCoefficients]
  | cons p xs ih =>
      change p.2 • basis p.1 + realize basis xs =
        Finsupp.linearCombination ℤ basis (Finsupp.single p.1 p.2 + freeCoefficients xs)
      rw [map_add, Finsupp.linearCombination_single, ih]

/-- Coefficient equality gives equality in every actual additive module. -/
theorem sparse_realize_eq_of_coefficients (basis : D → M) (xs ys : Sparse D)
    (h : ∀ d, coefficient xs d = coefficient ys d) :
    realize basis xs = realize basis ys := by
  rw [realize_eq_linearCombination, realize_eq_linearCombination]
  congr 1
  ext d
  simpa [freeCoefficients_apply] using h d

private theorem coefficient_zero_of_not_mem (xs : Sparse D) (d : D)
    (h : ∀ p ∈ xs, p.1 ≠ d) : coefficient xs d = 0 := by
  apply List.sum_eq_zero
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  simp [h p hp]

/-- Checking only the entries occurring in either list is exhaustive. -/
theorem sparse_coefficients_eq_of_support (xs ys : Sparse D)
    (h : ∀ p ∈ xs ++ ys, coefficient xs p.1 = coefficient ys p.1) :
    ∀ d, coefficient xs d = coefficient ys d := by
  intro d
  by_cases hd : ∃ p ∈ xs ++ ys, p.1 = d
  · obtain ⟨p, hp, rfl⟩ := hd
    exact h p hp
  · have hx : ∀ p ∈ xs, p.1 ≠ d := by
      intro p hp he
      exact hd ⟨p, List.mem_append_left _ hp, he⟩
    have hy : ∀ p ∈ ys, p.1 ≠ d := by
      intro p hp he
      exact hd ⟨p, List.mem_append_right _ hp, he⟩
    rw [coefficient_zero_of_not_mem xs d hx, coefficient_zero_of_not_mem ys d hy]

end CubicAnomaly.Fixed.SparseRealization
