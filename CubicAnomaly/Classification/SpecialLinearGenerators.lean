import Mathlib.Algebra.Lie.Classical
import Mathlib.Tactic

/-!
# Neighboring matrix units generate the traceless matrices

Brackets along a path give every off-diagonal matrix unit. Opposite units
then give diagonal differences, which span all trace-zero diagonals.
-/

namespace CubicAnomaly.Classification.SpecialLinearGenerators

open LieAlgebra.SpecialLinear

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All off-diagonal units suffice to generate the complex special-linear algebra. -/
theorem eq_top_of_offdiag [Nonempty ι] (S : LieSubalgebra ℂ (sl ι ℂ))
    (h : ∀ i j (hij : i ≠ j), single i j hij (1 : ℂ) ∈ S) : S = ⊤ := by
  classical
  let o := Classical.choice (inferInstance : Nonempty ι)
  let U := S.map (sl ι ℂ).incl
  have hU (i j : ι) (hij : i ≠ j) : Matrix.single i j (1 : ℂ) ∈ U :=
    ⟨_, h i j hij, rfl⟩
  have hD (i : ι) : Matrix.single i i (1 : ℂ) - Matrix.single o o 1 ∈ U := by
    by_cases hi : i = o
    · simp [hi]
    · have hh := U.lie_mem (hU i o hi) (hU o i (Ne.symm hi))
      simpa only [Ring.lie_def, Matrix.single_mul_single_same, mul_one] using hh
  refine top_unique (fun X _ => ?_)
  have term (i j : ι) : Matrix.single i j (X.val i j) -
      (if i = j then Matrix.single o o (X.val i j) else 0) ∈ U := by
    by_cases hij : i = j
    · subst j
      simpa [Matrix.smul_single, smul_sub] using U.smul_mem (X.val i i) (hD i)
    · simpa [hij, Matrix.smul_single] using U.smul_mem (X.val i j) (hU i j hij)
  have hh := U.toSubmodule.sum_mem fun i (_ : i ∈ Finset.univ) =>
    U.toSubmodule.sum_mem fun j (_ : j ∈ Finset.univ) => term i j
  have hz : ∑ i, X.val i i = 0 := X.property
  have ho : (∑ i, Matrix.single o o (X.val i i)) = 0 := by
    change ∑ i, Matrix.singleLinearMap ℂ o o (X.val i i) = _
    rw [← map_sum, hz, map_zero]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.matrix_eq_sum_single X.val |>.symm, ho, sub_zero] at hh
  obtain ⟨y, hy, hey⟩ := hh
  exact Subtype.ext hey ▸ hy

variable {n : ℕ}

/-- The adjacent upper matrix units for the rank-n Cartan matrix. -/
def raising (i : Fin n) : sl (Fin (n+1)) ℂ :=
  single i.castSucc i.succ (by intro h; have := congrArg Fin.val h; simp at this) 1

/-- The adjacent lower matrix units. -/
def lowering (i : Fin n) : sl (Fin (n+1)) ℂ :=
  single i.succ i.castSucc (by intro h; have := congrArg Fin.val h; simp at this) 1

/-- The adjacent traceless diagonal differences. -/
def diagonal (i : Fin n) : sl (Fin (n+1)) ℂ := singleSubSingle i.castSucc i.succ 1

private theorem chain {i j k : Fin (n+1)} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅single i j hij (1 : ℂ), single j k hjk (1 : ℂ)⁆ = single i k hik (1 : ℂ) := by
  apply Subtype.ext
  simp [Ring.lie_def, Ne.symm hik, Matrix.single_mul_single_of_ne]

/-- The adjacent matrix units in both directions generate every traceless matrix. -/
theorem neighboring_generate :
    LieSubalgebra.lieSpan ℂ (sl (Fin (n+1)) ℂ)
      (Set.range (raising (n := n)) ∪ Set.range lowering) = ⊤ := by
  let S := LieSubalgebra.lieSpan ℂ (sl (Fin (n+1)) ℂ)
    (Set.range (raising (n := n)) ∪ Set.range lowering)
  have adj (j : Fin n) : raising j ∈ S ∧ lowering j ∈ S :=
    ⟨LieSubalgebra.subset_lieSpan (Or.inl ⟨j,rfl⟩), LieSubalgebra.subset_lieSpan (Or.inr ⟨j,rfl⟩)⟩
  have allPairs (i j : Fin (n+1)) (h : i < j) :
      single i j h.ne (1 : ℂ) ∈ S ∧ single j i h.ne' 1 ∈ S := by
    induction j using Fin.induction with
    | zero => exact (Fin.not_lt_zero i h).elim
    | succ j ih =>
      by_cases he : i = j.castSucc
      · subst i; exact adj j
      · have h' : i < j.castSucc := by
          change i.val < j.val + 1 at h
          change i.val < j.val
          exact lt_of_le_of_ne (Nat.le_of_lt_succ h) (fun q => he (Fin.ext q))
        obtain ⟨hi, hj⟩ := ih h'
        refine ⟨?_, ?_⟩
        · rw [← chain h'.ne (Fin.castSucc_lt_succ (i := j)).ne h.ne]
          exact S.lie_mem hi (adj j).1
        · rw [← chain (Fin.castSucc_lt_succ (i := j)).ne' h'.ne' h.ne']
          exact S.lie_mem (adj j).2 hj
  apply eq_top_of_offdiag S
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact (allPairs i j h).1
  · exact (allPairs j i h).2

end CubicAnomaly.Classification.SpecialLinearGenerators
