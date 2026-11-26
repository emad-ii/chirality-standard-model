/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Jonathan Reich

Adapted to the repository's Lean 4.28 and mathlib pin. See NOTICE.md.
-/
import Mathlib
import CubicAnomaly.Classification.DynkinClassification.Indecomposable
import CubicAnomaly.Classification.DynkinClassification.PosDefIntCast

/-! Finite Cartan matrices and their bonds, adapted on the project mathlib pin. -/

open Function Matrix Set

namespace CartanMatrix

/-! ### Exceptional Cartan matrices -/

/-- The generalized Cartan matrix of type Eₙ, extending E₆, E₇, E₈ by the same Dynkin-diagram
pattern. -/
def E (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  .of fun i j =>
    if i = j then 2
    else if (i.val = 0 ∧ j.val = 2) ∨ (j.val = 0 ∧ i.val = 2) ∨
      (i.val = 1 ∧ j.val = 3) ∨ (j.val = 1 ∧ i.val = 3) ∨
      (2 ≤ i.val ∧ i.val + 1 = j.val) ∨ (2 ≤ j.val ∧ j.val + 1 = i.val)
    then -1 else 0
variable (n : ℕ)

/-- Reversing the order of the indices is a symmetry of the path `Aₙ`. -/
theorem A_submatrix_revPerm :
    (A n).submatrix Fin.revPerm Fin.revPerm = A n := by
  ext i j
  simp [A, Fin.ext_iff]
  lia

/-- Swapping the two short arms `n-2` and `n-1` is a symmetry of `Dₙ`. -/
theorem D_submatrix_swap (hn : n ≠ 0) :
    (D n).submatrix (Equiv.swap ⟨n - 2, by lia⟩ ⟨n - 1, by lia⟩)
      (Equiv.swap ⟨n - 2, by lia⟩ ⟨n - 1, by lia⟩) = D n := by
  ext i j
  simp only [D, submatrix_apply, of_apply, Equiv.swap_apply_def, Fin.ext_iff]
  by_cases hi1 : (i : ℕ) = n - 2 <;> by_cases hi2 : (i : ℕ) = n - 1 <;>
    by_cases hj1 : (j : ℕ) = n - 2 <;> by_cases hj2 : (j : ℕ) = n - 1 <;>
    simp only [hi1, hi2, hj1, hj2, ite_true, ite_false] <;> grind

@[simp] theorem E_diag (n : ℕ) (i : Fin n) : E n i i = 2 := by
  simp [E]
@[simp] theorem E_transpose (n : ℕ) : (E n).transpose = E n := by
  ext i j
  simp only [E, transpose_apply, of_apply]
  grind

end CartanMatrix

/-- The proposition that a matrix is a generalized Cartan matrix. -/
structure Matrix.IsGeneralizedCartan {ι : Type*}
    (M : Matrix ι ι ℤ) : Prop where
  diag (i : ι) : M i i = 2
  offDiag_nonpos (i j : ι) : i ≠ j → M i j ≤ 0
  zero_comm (i j : ι) : M i j = 0 ↔ M j i = 0

/-- The proposition that a matrix is a finite-type Cartan matrix. -/
structure Matrix.IsFiniteCartan {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    extends IsGeneralizedCartan M where
  exists_posDef' : ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ ∀ x ≠ 0, 0 < x ⬝ᵥ ((diagonal d * M) *ᵥ x)

namespace CartanMatrix

/-- The five pairs `(Mᵢⱼ, Mⱼᵢ)` that can occur between two distinct joined indices of a finite
Cartan matrix (see `Matrix.IsFiniteCartan.apply_cases`): a simple bond, a double bond in either
direction, or a triple bond in either direction. -/
def bonds : Finset (ℤ × ℤ) := {(-1, -1), (-1, -2), (-2, -1), (-1, -3), (-3, -1)}

/-- `IsBond a b` says that `(a, b)` is one of the five `CartanMatrix.bonds`. -/
def IsBond (a b : ℤ) : Prop := (a, b) ∈ bonds

instance : DecidableRel IsBond := fun a b ↦ inferInstanceAs (Decidable ((a, b) ∈ bonds))

/-- A bond is a pair of entries one of which is `-1` and the other `-1`, `-2` or `-3`. -/
lemma isBond_iff {a b : ℤ} :
    IsBond a b ↔ a = -1 ∧ b ∈ Set.Icc (-3) (-1) ∨ b = -1 ∧ a ∈ Set.Icc (-3) (-1) := by
  simp only [IsBond, bonds, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Set.mem_Icc]
  lia

namespace IsBond

variable {a b : ℤ}

lemma swap (h : IsBond a b) : IsBond b a := by
  rw [isBond_iff] at *; tauto

lemma one_le_mul (h : IsBond a b) : 1 ≤ a * b :=
  (by decide : ∀ p ∈ bonds, 1 ≤ p.1 * p.2) _ h

/-- A bond is either simple or has at least two bonds. -/
lemma eq_neg_one_or_two_le_mul (h : IsBond a b) : a = -1 ∧ b = -1 ∨ 2 ≤ a * b := by
  simpa using (by decide : ∀ p ∈ bonds, p = (-1, -1) ∨ 2 ≤ p.1 * p.2) _ h

end IsBond

end CartanMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℤ}

namespace Matrix.IsFiniteCartan

lemma mk_of_exists_posDef (diag : ∀ i, M i i = 2) (offDiag_nonpos : ∀ i j, i ≠ j → M i j ≤ 0)
   (exists_posDef : ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ (diagonal d * M).PosDef) :
    M.IsFiniteCartan where
  diag := diag
  offDiag_nonpos := offDiag_nonpos
  zero_comm i j := by
    obtain ⟨_, _, h⟩ := exists_posDef
    grind [h.isHermitian.apply i j, diagonal_mul, star_trivial, mul_eq_zero]
  exists_posDef' := by
    obtain ⟨d, hd, hd'⟩ := exists_posDef
    exact ⟨d, hd, fun x hx ↦ by simpa using hd'.dotProduct_mulVec_pos hx⟩

variable (hM : M.IsFiniteCartan)
include hM

omit hM in
private theorem dotProduct_diagonal_mul_mulVec (d x : ι → ℤ) :
    x ⬝ᵥ ((diagonal d * M) *ᵥ x) = ∑ i, d i * (x i * (M *ᵥ x) i) := by
  simp only [← mulVec_mulVec, mulVec_diagonal, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma eq_zero_iff_forall {x : ι → ℤ} :
    x = 0 ↔ ∀ i, x i * (M *ᵥ x) i ≤ 0 := by
  refine ⟨by rintro rfl; simp, fun h ↦ ?_⟩
  obtain ⟨d, hd, hd'⟩ := hM.exists_posDef'
  by_contra hx
  refine (hd' x hx).not_ge ?_
  simp_rw [dotProduct_diagonal_mul_mulVec]
  exact Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (hd i).le (h i)

lemma eq_zero_iff_forall' {x : ι → ℤ} :
    x = 0 ↔ ∀ i, x i * (M *ᵥ x) i = 0 :=
  ⟨by rintro rfl; simp, fun h ↦ hM.eq_zero_iff_forall.mpr fun i ↦ (h i).le⟩

lemma exists_mul_mulVec_pos {x : ι → ℤ} (hx : x ≠ 0) :
    ∃ i, 0 < x i * (M *ᵥ x) i := by
  by_contra! hc
  exact hx <| hM.eq_zero_iff_forall.mpr hc

lemma det_ne_zero : M.det ≠ 0 := by
  by_contra h
  obtain ⟨v, hv, hMv⟩ := exists_mulVec_eq_zero_iff.mpr h
  simpa [hMv] using hM.exists_mul_mulVec_pos hv

protected theorem submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] {f : κ → ι} (hf : Injective f) :
    (M.submatrix f f).IsFiniteCartan where
  diag i := hM.diag (f i)
  offDiag_nonpos i j h := hM.offDiag_nonpos (f i) (f j) (hf.ne h)
  zero_comm i j := hM.zero_comm (f i) (f j)
  exists_posDef' := by
    obtain ⟨d, hd, h⟩ := hM.exists_posDef'
    refine ⟨d ∘ f, fun i ↦ hd (f i), fun x hx ↦ ?_⟩
    let y := extend f x 0
    have hy : y ∘ f = x := extend_comp hf x 0
    have hy₀ (i) (hi : i ∉ range f) : y i = 0 := extend_apply' _ _ _ hi
    have hmul : M.submatrix f f *ᵥ x = (M *ᵥ y) ∘ f :=
      funext fun k ↦ Fintype.sum_of_injective f hf _ _ (by aesop) (by aesop)
    convert h y (fun h0 ↦ hx <| by simp [← hy, h0]) using 1
    simp only [dotProduct_diagonal_mul_mulVec, hmul]
    exact Fintype.sum_of_injective f hf _ _ (by aesop) (by aesop)

lemma exists_apply_ne_zero_and [Nonempty ι] :
    ∃ i j, M i j ≠ 0 ∧ ∀ k ≠ i, M i k ≠ 0 → k = j := by
  by_contra! h
  obtain ⟨i, hi⟩ := hM.exists_mul_mulVec_pos zero_ne_one.symm
  obtain ⟨j, hji, hij, -⟩ := h i i (by simp [hM.diag])
  obtain ⟨k, hki, _, hkj⟩ := h i j hij
  have hsum := Finset.sum_le_sum_of_subset_of_nonpos (s := {i, j, k}) (t := Finset.univ) (by simp)
    <| fun l _ _ ↦ hM.offDiag_nonpos i l (by grind)
  rw [Finset.sum_insert (by simp [hji.symm, hki.symm]), Finset.sum_pair hkj.symm] at hsum
  have : 0 < ∑ l ∈ Finset.univ, M i l := by simpa [mulVec, dotProduct] using hi
  grind [hM.offDiag_nonpos i j hji.symm, hM.offDiag_nonpos i k hki.symm, hM.diag i]

/-- Removing a vertex of degree at most one gives a positive symmetrizer by induction.
The scale on the remaining vertices clears the ratio at the deleted vertex. -/
private lemma exists_symmetrizer :
    ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ ∀ i j, d i * M i j = d j * M j i := by
  classical
  induction hcard : Fintype.card ι using Nat.strong_induction_on generalizing ι with | h n ih =>
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  obtain ⟨v, w, hvw, hv⟩ := hM.exists_apply_ne_zero_and
  obtain ⟨e, he, hsub⟩ := ih _
    ((Fintype.card_subtype_lt (p := (· ≠ v)) (x := v) (by simp)).trans_eq hcard)
    (hM.submatrix Subtype.val_injective) rfl
  let e' (i : ι) : ℤ := if hi : i = v then 1 else e ⟨i, hi⟩
  have he' i : 0 < e' i := by by_cases hi : i = v <;> simp [e', hi, he]
  let d (i : ι) := if i = v then |M w v| * e' w else |M v w| * e' i
  have hposwv : 0 < |M w v| := abs_pos.mpr ((hM.zero_comm v w).not.mp hvw)
  have hposvw : 0 < |M v w| := abs_pos.mpr hvw
  have hvj (j : ι) (hj : j ≠ v) : d v * M v j = d j * M j v := by
    simp only [d, hj, if_true, if_false]
    by_cases h : M v j = 0
    · rw [h, (hM.zero_comm v j).mp h]; simp
    · obtain rfl := hv j hj h
      rw [abs_of_nonpos (hM.offDiag_nonpos j v hj), abs_of_nonpos (hM.offDiag_nonpos v j hj.symm)]
      ring
  refine ⟨d, fun i => ?_, fun i j => ?_⟩
  · by_cases hi : i = v <;> simp only [d, hi, if_true, if_false]
    · exact mul_pos hposwv (he' _)
    · exact mul_pos hposvw (he' _)
  · by_cases hi : i = v
    · subst i
      by_cases hj : j = v
      · rw [hj]
      · exact hvj _ hj
    by_cases hj : j = v
    · subst j
      exact (hvj i hi).symm
    simpa only [d, e', hi, hj, if_false, dif_neg, mul_assoc] using
      congrArg (|M v w| * ·) (hsub ⟨i, hi⟩ ⟨j, hj⟩)

lemma exists_pos_and_mulVec_pos : ∃ u : ι → ℤ, (∀ i, 0 < u i) ∧ (∀ i, 0 < (M *ᵥ u) i) := by
  obtain ⟨u, hMu⟩ : ∃ u, ∀ i, 0 < (M *ᵥ u) i :=
    ⟨M.adjugate *ᵥ M.det, by simp [mul_adjugate, mul_self_pos.mpr hM.det_ne_zero]⟩
  have hu : 0 ≤ u := by
    suffices u ⊓ 0 = 0 from inf_eq_right.mp this
    have h₁ : u ⊓ 0 ≤ u := inf_le_left
    have h₂ : u ⊓ 0 ≤ 0 := inf_le_right
    refine hM.eq_zero_iff_forall.mpr fun i ↦
      (mul_nonpos_of_nonpos_of_nonneg (h₂ i) (hMu i).le).trans' ?_
    simp_rw [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rcases eq_or_ne i j with rfl | hij
    · rcases le_total (u i) 0 with h | h <;> simp [h]
    · exact mul_le_mul_of_nonpos_left
        (mul_le_mul_of_nonpos_left (h₁ j) (hM.offDiag_nonpos i j hij)) (h₂ i)
  refine ⟨u, fun i ↦ ?_, hMu⟩
  suffices 0 < ∑ j ∈ {i}, M i j * u j by simpa [hM.diag] using this
  exact (hMu i).trans_le <| Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ _)
    fun j _ hj ↦ mul_nonpos_of_nonpos_of_nonneg (hM.offDiag_nonpos i j <| by aesop) (hu j)

open Finset in
theorem exists_posDef : ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ (diagonal d * M).PosDef := by
  obtain ⟨u, hu, hMu⟩ := hM.exists_pos_and_mulVec_pos
  obtain ⟨d, hd, hd'⟩ := hM.exists_symmetrizer
  suffices ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (diagonal d * M) *ᵥ x by
    refine ⟨d, hd, posDef_iff_dotProduct_mulVec.mpr ⟨by ext; simp [diagonal_mul, hd'], ?_⟩⟩
    exact fun x hx ↦ (this (star x) hx)
  intro x hx
  let y i := (∏ k ∈ univ.erase i, u k) * x i
  have hy : u * y = (∏ k, u k) • x := funext fun _ ↦ by simp [y, ← mul_assoc, mul_prod_erase]
  suffices 0 < (u * y) ⬝ᵥ (diagonal d * M) *ᵥ (u * y) by simpa only [hy, smul_dotProduct,
    dotProduct_smul, mulVec_smul, smul_eq_mul, mul_pos_iff_of_pos_left (prod_pos fun k _ ↦ hu k)]
  let C i j := d i * M i j * u i * u j
  have h₁ : ∑ i, ∑ j, C i j * y j ^ 2 = ∑ i, ∑ j, C i j * y i ^ 2 := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by simp only [C]; rw [hd' i j]; ring
  have h₂ : 2 * (u * y) ⬝ᵥ (diagonal d * M) *ᵥ (u * y) = ∑ i, ∑ j, C i j * y i ^ 2 +
      ∑ i, ∑ j, C i j * y j ^ 2 - ∑ i, ∑ j, C i j * (y i - y j) ^ 2 := by
    simp only [C, mulVec, dotProduct, diagonal_mul, mul_sum, Pi.mul_apply, ← sum_add_distrib,
      ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  have h₃ : ∑ i, ∑ j, C i j * (y i - y j) ^ 2 ≤ 0 := by
    refine sum_nonpos fun i _ ↦ sum_nonpos fun j _ ↦ ?_
    rcases eq_or_ne i j with rfl | hij
    · simp
    · linarith [mul_nonpos_of_nonpos_of_nonneg (hM.offDiag_nonpos i j hij) <|
        mul_nonneg (mul_pos (hd i) (mul_pos (hu i) (hu j))).le (sq_nonneg (y i - y j))]
  have h₄ : 0 < ∑ i, ∑ j, C i j * y i ^ 2 := by
    have hr j : ∑ k, C j k * y j ^ 2 = d j * u j * (M *ᵥ u) j * y j ^ 2 := by
      simp only [C, mulVec, dotProduct, mul_sum, sum_mul]
      exact sum_congr rfl fun _ _ ↦ by ring
    have hr' j : 0 < d j * u j * (M *ᵥ u) j := mul_pos (mul_pos (hd j) (hu j)) (hMu j)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have : y i ≠ 0 := mul_ne_zero (prod_pos fun k _ ↦ hu k).ne' hi
    simpa only [hr] using sum_pos' (fun j _ ↦ mul_nonneg (hr' j).le (sq_nonneg _))
      ⟨i, mem_univ i, mul_pos (hr' i) <| by positivity⟩
  linarith

lemma det_pos :
    0 < M.det := by
  obtain ⟨d, hd, hd'⟩ := hM.exists_posDef
  replace hd : 0 < (diagonal d).det := by simpa using Finset.prod_pos fun i a ↦ hd i
  replace hd' : 0 < (diagonal d).det * M.det := by
    have hr := hd'.map_intCast_real.det_pos
    change 0 < ((Int.castRingHom ℝ).mapMatrix (diagonal d * M)).det at hr
    rw [← RingHom.map_det] at hr
    rw [← det_mul]
    change (0 : ℝ) < ((diagonal d * M).det : ℤ) at hr
    exact_mod_cast hr
  nlinarith

protected lemma transpose :
    Mᵀ.IsFiniteCartan := by
  obtain ⟨d, hd_pos, hdM⟩ := hM.exists_posDef
  set d' : ι → ℤ := fun i ↦ ∏ j ∈ Finset.univ.erase i, d j with hd'
  have hd'_pos (i : ι) : 0 < d' i := Finset.prod_pos fun j _ ↦ hd_pos j
  suffices ∀ x ≠ 0, 0 < x ⬝ᵥ ((diagonal d' * Mᵀ) *ᵥ x) from
    { diag i := by simpa using hM.diag i
      offDiag_nonpos i j hij := by simpa using hM.offDiag_nonpos j i hij.symm
      zero_comm i j := by simpa using hM.zero_comm j i
      exists_posDef' := ⟨d', hd'_pos, this⟩ }
  set C : ℤ := ∏ j, d j with hC
  have hCd (i : ι) : d i * d' i = C := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hsymm (i j : ι) : d' i * M j i = d' j * M i j := by
    apply mul_left_cancel₀ (a := d i * d j) (by simp [(hd_pos _).ne'])
    have aux : d i * M i j = d j * M j i := by simpa using hdM.isHermitian.apply j i
    linear_combination (d j * M j i) * hCd i - (d i * M i j) * hCd j - C * aux
  intro v hv
  have key : (d' * v) ⬝ᵥ (diagonal d * M) *ᵥ (d' * v) = C * (v ⬝ᵥ (diagonal d' * Mᵀ) *ᵥ v) := by
    simp only [dotProduct, mulVec, diagonal_mul, transpose_apply, Finset.mul_sum, Pi.mul_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    linear_combination (M i j * d' j * v i * v j) * hCd i - (C * v i * v j) * hsymm i j
  have hpos := hdM.dotProduct_mulVec_pos (x := d' * v) <|
    fun h ↦ hv (funext fun i ↦ by simpa [(hd'_pos i).ne'] using congr_fun h i)
  rw [star_trivial, key] at hpos
  have hCpos : 0 < C := Finset.prod_pos fun j _ ↦ hd_pos j
  rwa [← mul_pos_iff_of_pos_left hCpos]

omit hM in
@[simp] protected lemma transpose_iff :
    Mᵀ.IsFiniteCartan ↔ M.IsFiniteCartan :=
  ⟨fun h ↦ by simpa using h.transpose, IsFiniteCartan.transpose⟩

section Submatrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A relabelling of a finite Cartan matrix is a finite Cartan matrix. -/
protected lemma reindex (e : ι ≃ κ) : (M.reindex e e).IsFiniteCartan :=
  hM.submatrix e.symm.injective

omit hM in
@[simp] lemma submatrix_equiv_iff {σ : κ ≃ ι} :
    (M.submatrix σ σ).IsFiniteCartan ↔ M.IsFiniteCartan := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.submatrix σ.injective⟩
  simpa using h.submatrix σ.symm.injective

end Submatrix

/-- Two distinct indices are joined by at most three bonds: the `2 × 2` principal minor
`4 - Mᵢⱼ Mⱼᵢ` is positive. -/
lemma mul_lt_four {i j : ι} (hij : i ≠ j) : M i j * M j i < 4 := by
  have h := (hM.submatrix (injective_pair_iff_ne.mpr hij)).det_pos
  rw [det_fin_two] at h
  simp [hM.diag] at h
  linarith

lemma mul_nonneg_of_ne {i j : ι} (hij : i ≠ j) : 0 ≤ M i j * M j i :=
  mul_nonneg_of_nonpos_of_nonpos (hM.offDiag_nonpos i j hij) (hM.offDiag_nonpos j i hij.symm)

/-- Two distinct indices are either not joined, or joined by one of the five bonds. -/
lemma apply_cases {i j : ι} (hij : i ≠ j) :
    M i j = 0 ∧ M j i = 0 ∨ CartanMatrix.IsBond (M i j) (M j i) := by
  have h₁ := hM.offDiag_nonpos i j hij
  have h₂ := hM.offDiag_nonpos j i hij.symm
  have h₃ := hM.mul_lt_four hij
  obtain h | h := eq_or_ne (M i j) 0
  · exact .inl ⟨h, (hM.zero_comm i j).mp h⟩
  have h' : M j i ≠ 0 := by simpa [hM.zero_comm] using h
  have : -3 ≤ M i j := by nlinarith [show M j i ≤ -1 by lia]
  have : -3 ≤ M j i := by nlinarith [show M i j ≤ -1 by lia]
  right
  rw [CartanMatrix.isBond_iff, Set.mem_Icc, Set.mem_Icc]
  interval_cases M i j <;> interval_cases M j i <;> lia

end Matrix.IsFiniteCartan
