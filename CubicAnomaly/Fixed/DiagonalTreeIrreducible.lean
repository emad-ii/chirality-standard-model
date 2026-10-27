import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Irreducibility from a separating diagonal and a rooted action tree

Distinct diagonal eigenvalues isolate every nonzero coordinate of an invariant
subspace. A rooted tree of reversible nonzero basis actions then propagates
membership to the whole standard basis. No semisimplicity or classification
hypothesis is used.
-/

namespace CubicAnomaly.Fixed.DiagonalTreeIrreducible

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- A polynomial in a diagonal operator annihilates prescribed coordinates. -/
theorem diagonal_product_mem (W : Submodule K (ι → K)) (μ : ι → K)
    (hD : ∀ v ∈ W, (fun i => μ i * v i) ∈ W)
    (v : ι → K) (hv : v ∈ W) (s : Finset ι) :
    (fun i => (∏ j ∈ s, (μ i - μ j)) * v i) ∈ W := by
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | @insert j s hj ih =>
      have hh := W.sub_mem (hD _ ih) (W.smul_mem (μ j) ih)
      convert hh using 1
      ext i
      simp only [Finset.prod_insert hj, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring

/-- A nonzero coordinate of a diagonal-invariant vector yields its basis vector. -/
theorem single_mem_of_diagonal (W : Submodule K (ι → K)) (μ : ι → K)
    (hμ : Function.Injective μ)
    (hD : ∀ v ∈ W, (fun i => μ i * v i) ∈ W)
    (v : ι → K) (hv : v ∈ W) (i : ι) (hi : v i ≠ 0) :
    Pi.single i (1 : K) ∈ W := by
  let c : K := (∏ j ∈ Finset.univ.erase i, (μ i - μ j)) * v i
  have hc : c ≠ 0 := by
    apply mul_ne_zero _ hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (hμ.ne (Finset.ne_of_mem_erase hj).symm)
  have hm := diagonal_product_mem W μ hD v hv (Finset.univ.erase i)
  have he : (fun k => (∏ j ∈ Finset.univ.erase i, (μ k - μ j)) * v k) =
      c • (Pi.single i (1 : K) : ι → K) := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [c]
    · have hz : (∏ j ∈ Finset.univ.erase i, (μ k - μ j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (sub_self _)
      simp [hz, hk]
  rw [he] at hm
  exact (W.smul_mem_iff hc).mp hm

/-- A separating diagonal and a rooted reversible basis-action tree force every
nonzero invariant coordinate subspace to be the whole space. -/
theorem eq_top_of_diagonal_and_tree (W : Submodule K (ι → K)) (μ : ι → K)
    (hμ : Function.Injective μ)
    (hD : ∀ v ∈ W, (fun i => μ i * v i) ∈ W)
    (base : ι) (parent : ι → ι) (rank : ι → ℕ)
    (hparent : ∀ i, i ≠ base → rank (parent i) < rank i)
    (hstep : ∀ i, i ≠ base →
      (Pi.single (parent i) (1 : K) ∈ W ↔ Pi.single i (1 : K) ∈ W))
    (hW : W ≠ ⊥) : W = ⊤ := by
  have hb : ∀ i, Pi.single i (1 : K) ∈ W ↔ Pi.single base (1 : K) ∈ W := by
    intro i
    induction i using (measure rank).wf.induction with
    | h i ih =>
        by_cases hi : i = base
        · subst i
          rfl
        · exact (hstep i hi).symm.trans (ih (parent i) (hparent i hi))
  obtain ⟨v, hv, hv0⟩ := W.ne_bot_iff.mp hW
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv0 (funext h)
  have hbase := (hb i).mp (single_mem_of_diagonal W μ hμ hD v hv i hi)
  apply top_unique
  rw [← (Pi.basisFun K ι).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  simpa using (hb j).mpr hbase

end CubicAnomaly.Fixed.DiagonalTreeIrreducible
