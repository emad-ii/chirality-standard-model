import CubicAnomaly.Classification.TypeACompactRecognition

/-! The normalized traceless matrix units and their transport to an actual
complex Lie algebra with a matched type-A Cartan matrix. -/
namespace CubicAnomaly.Classification.TypeAMatrixUnits

open LieAlgebra LieModule LieAlgebra.SpecialLinear SpecialLinearGenerators
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Remove the scalar part of a matrix. This preserves the Lie bracket. -/
noncomputable def traceless : Matrix ι ι ℂ →ₗ⁅ℂ⁆ sl ι ℂ where
  toFun A := ⟨A - (A.trace / Fintype.card ι) • (1 : Matrix ι ι ℂ), by
    change (A - (A.trace / Fintype.card ι) • (1 : Matrix ι ι ℂ)).trace = 0
    simp [Matrix.trace_one, Nat.cast_ne_zero.mpr Fintype.card_ne_zero]⟩
  map_add' A B := by
    apply Subtype.ext
    simp [add_div, add_smul]; abel
  map_smul' c A := by
    apply Subtype.ext
    simp [smul_sub, smul_smul, mul_div_assoc]
  map_lie' {A B} := by
    apply Subtype.ext
    change ⁅A,B⁆ - (Matrix.trace ⁅A,B⁆ / Fintype.card ι) • (1 : Matrix ι ι ℂ) =
      ⁅A - (A.trace / Fintype.card ι) • 1, B - (B.trace / Fintype.card ι) • 1⁆
    rw [sub_lie, lie_sub, lie_sub]
    simp [Ring.lie_def, Matrix.trace_mul_comm A B, smul_smul, mul_comm (A.trace / Fintype.card ι) (B.trace / Fintype.card ι)]

noncomputable def unit (i j : ι) : sl ι ℂ := traceless (Matrix.single i j 1)

theorem bracket (i j k l : ι) : ⁅unit i j, unit k l⁆ =
    (if j = k then unit i l else 0) - (if l = i then unit k j else 0) := by
  unfold unit
  rw [← LieHom.map_lie]
  by_cases hj : j = k <;> by_cases hl : l = i <;> simp_all [Ring.lie_def, Matrix.single_mul_single_of_ne]

theorem expand (A : sl ι ℂ) : A = ∑ i, ∑ j, A.val i j • unit i j := by
  calc
    A = traceless A.val := Subtype.ext (by
      change A.val = A.val - (A.val.trace / Fintype.card ι) • 1
      rw [show A.val.trace = 0 from A.property]; simp)
    _ = _ := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single A.val]
      simp only [map_sum]
      congr! 2 with i
      unfold unit
      rw [← map_smul]
      simp [Matrix.smul_single]

variable {K : Type*} [LieRing K] [LieAlgebra ℂ K]

/-- Pull the normalized units back through a Lie equivalence to traceless matrices. -/
noncomputable def family (Φ : K ≃ₗ⁅ℂ⁆ sl ι ℂ) (i j : ι) : K := Φ.symm (unit i j)

theorem family_bracket (Φ : K ≃ₗ⁅ℂ⁆ sl ι ℂ) (i j k l : ι) : ⁅family Φ i j, family Φ k l⁆ =
    (if j = k then family Φ i l else 0) - (if l = i then family Φ k j else 0) := by
  simp only [family, ← LieEquiv.map_lie, bracket, map_sub]
  split_ifs <;> simp

theorem family_span (Φ : K ≃ₗ⁅ℂ⁆ sl ι ℂ) :
    Submodule.span ℂ (Set.range fun ij : ι × ι => family Φ ij.1 ij.2) = ⊤ := by
  apply top_unique
  intro x _
  have h := congrArg Φ.symm (expand (Φ x))
  rw [Φ.symm_apply_apply] at h
  rw [h]
  simp only [map_sum, map_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,j),rfl⟩)

theorem offdiagonal {i j : ι} (hij : i ≠ j) : unit i j = single i j hij 1 := by
  apply Subtype.ext
  change Matrix.single i j (1 : ℂ) - (Matrix.trace (Matrix.single i j (1 : ℂ)) / Fintype.card ι) • 1 = _
  simp [Matrix.trace_single_eq_of_ne, hij]

theorem adjacent_difference {n : ℕ} (i : Fin n) :
    unit i.castSucc i.castSucc - unit i.succ i.succ = diagonal i := by
  apply Subtype.ext
  change (Matrix.single i.castSucc i.castSucc (1 : ℂ) - (Matrix.trace (Matrix.single i.castSucc i.castSucc (1 : ℂ)) / (Fintype.card (Fin (n+1)) : ℂ)) • 1) -
    (Matrix.single i.succ i.succ (1 : ℂ) - (Matrix.trace (Matrix.single i.succ i.succ (1 : ℂ)) / (Fintype.card (Fin (n+1)) : ℂ)) • 1) = Matrix.single i.castSucc i.castSucc (1 : ℂ) - Matrix.single i.succ i.succ 1
  simp

variable {n : ℕ} (Φ : K ≃ₗ⁅ℂ⁆ sl (Fin (n+1)) ℂ)
  {M : Type*} [AddCommGroup M] [Module ℂ M] [LieRingModule K M] [LieModule ℂ K M]

omit [Module ℂ M] [LieModule ℂ K M] in
/-- Annihilation by the matched adjacent raising operators implies annihilation
by every upper-triangular root operator. -/
theorem upper_kills (v : M) (hp : ∀ i : Fin n, ⁅Φ.symm (raising i), v⁆ = 0)
    (i j : Fin (n+1)) (hij : i < j) : ⁅family Φ i j, v⁆ = 0 := by
  have hadj (i : Fin n) : ⁅family Φ i.castSucc i.succ, v⁆ = 0 := by
    rw [family, offdiagonal Fin.castSucc_lt_succ.ne]
    exact hp i
  induction j using Fin.induction with
  | zero => exact (Fin.not_lt_zero i hij).elim
  | succ j ih =>
    by_cases he : i = j.castSucc
    · exact he ▸ hadj j
    · have h' : i < j.castSucc := by
        change i.val < j.val + 1 at hij
        change i.val < j.val
        exact lt_of_le_of_ne (Nat.le_of_lt_succ hij) (fun q => he (Fin.ext q))
      have hb := family_bracket Φ i j.castSucc j.castSucc j.succ
      simp [hij.ne'] at hb
      rw [← hb, lie_lie, hadj, ih h', lie_zero, lie_zero, sub_zero]

theorem sum_diagonal (Φ : K ≃ₗ⁅ℂ⁆ sl ι ℂ) : ∑ i, family Φ i i = 0 := by
  simp only [family, unit, ← map_sum, Matrix.sum_single_one]
  have ht : (traceless (1 : Matrix ι ι ℂ)) = 0 := by
    apply Subtype.ext
    change 1 - ((1 : Matrix ι ι ℂ).trace / Fintype.card ι) • 1 = 0
    simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
  rw [ht, map_zero]

/-- A weight vector for the adjacent diagonal differences is a weight
vector for every traceless diagonal unit. -/
theorem diagonal_eigenvalues (v : M)
    (hd : ∀ i : Fin n, ∃ u : ℂ, ⁅Φ.symm (diagonal i), v⁆ = u • v) :
    ∃ u : Fin (n+1) → ℂ, ∀ i, ⁅family Φ i i, v⁆ = u i • v := by
  classical
  let U := (ℂ ∙ v).comap ((toEnd ℂ K M).toLinearMap.flip v)
  have adj (i : Fin n) : family Φ i.castSucc i.castSucc - family Φ i.succ i.succ ∈ U := by
    change (⁅Φ.symm (unit i.castSucc i.castSucc) - Φ.symm (unit i.succ i.succ), v⁆ : M) ∈ ℂ ∙ v
    rw [← map_sub, adjacent_difference]
    obtain ⟨c, hc⟩ := hd i
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have diff (i : Fin (n+1)) : family Φ 0 0 - family Φ i i ∈ U := by
    induction i using Fin.induction with
    | zero => simp [U]
    | succ j ih =>
      convert U.add_mem ih (adj j) using 1
      abel
  have allDiff (i j : Fin (n+1)) : family Φ i i - family Φ j j ∈ U := by
    convert U.sub_mem (diff j) (diff i) using 1
    abel
  have hmem (i : Fin (n+1)) : family Φ i i ∈ U := by
    have h := U.sum_mem (fun j (_ : j ∈ Finset.univ) => allDiff i j)
    rw [Finset.sum_sub_distrib, sum_diagonal, sub_zero, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ] at h
    exact (U.smul_mem_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mp h
  choose u hu using fun i => Submodule.mem_span_singleton.mp
    (show (⁅family Φ i i, v⁆ : M) ∈ ℂ ∙ v from hmem i)
  exact ⟨u, fun i => (hu i).symm⟩

end CubicAnomaly.Classification.TypeAMatrixUnits
