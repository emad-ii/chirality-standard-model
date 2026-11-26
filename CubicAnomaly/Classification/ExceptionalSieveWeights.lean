import CubicAnomaly.Classification.SieveBounds

/-!
# Integral coroot labels for the exceptional dimension sieve

An actual finite-dimensional module supplies integral labels at every coroot.
A raising string through an arbitrary eigenvector ends at a primitive vector;
its lowering string consists of independent eigenvectors. Applying the same
argument to the opposite triple bounds both signs of the original label.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveWeights

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling

section Strings

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M] {h e f : L} {v : M} {μ : K}

private theorem primitive_label_lt_finrank (t : IsSl2Triple h e f)
    (p : t.HasPrimitiveVectorWith v μ) {n : ℕ} (hn : μ = n) :
    n < finrank K M := by
  let w (i : Fin (n + 1)) : M := ((toEnd K L M f) ^ (i : ℕ)) v
  have hind : LinearIndependent K w := by
    apply (toEnd K L M h).eigenvectors_linearIndependent' (fun i : Fin (n + 1) => μ - 2 * (i : ℕ)) _
    · intro i
      exact ⟨Module.End.mem_eigenspace_iff.mpr (p.lie_h_pow_toEnd_f i),
        p.pow_toEnd_f_ne_zero_of_eq_nat hn (by omega)⟩
    · intro i j hij
      apply Fin.ext
      simpa using hij
  simpa using hind.fintype_card_le_finrank

private theorem eigenvalue_upper (t : IsSl2Triple h e f)
    (hv : (toEnd K L M h).HasEigenvector μ v) :
    ∃ z : ℤ, μ = (z : K) ∧ z < (finrank K M : ℤ) := by
  let w (i : ℕ) : M := ((toEnd K L M e) ^ i) v
  have hs (i : ℕ) : ⁅h, w i⁆ = (μ + 2 * i) • w i := by
    induction i with
    | zero => simpa [w] using Module.End.mem_eigenspace_iff.mp hv.1
    | succ i ih =>
      have hw : w (i + 1) = ⁅e, w i⁆ := by simp [w, pow_succ']
      rw [hw, leibniz_lie, t.lie_h_e_smul K, smul_lie, ih, lie_smul, ← add_smul]
      congr 1
      push_cast
      ring
  have hz : ∃ i, w i = 0 := by
    by_contra! hne
    have hind : LinearIndependent K (fun i : Fin (finrank K M + 1) => w i) := by
      apply (toEnd K L M h).eigenvectors_linearIndependent'
        (fun i : Fin (finrank K M + 1) => μ + 2 * (i : ℕ)) _
      · intro i
        exact ⟨Module.End.mem_eigenspace_iff.mpr (hs i), hne i⟩
      · intro i j hij
        apply Fin.ext
        simpa using hij
    simpa using hind.fintype_card_le_finrank
  obtain ⟨i, hi, hi'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (show w 0 ≠ 0 by simpa [w] using hv.2) hz
  have p : t.HasPrimitiveVectorWith (w i) (μ + 2 * i) :=
    ⟨hi, hs i, by simpa [w, pow_succ'] using hi'⟩
  obtain ⟨n, hn⟩ := p.exists_nat
  have hn' := primitive_label_lt_finrank t p hn
  refine ⟨(n : ℤ) - 2 * i, ?_, by omega⟩
  push_cast
  linear_combination hn

/-- Every eigenvalue of the semisimple element of an actual sl₂ triple is an
integer of absolute value strictly less than the module dimension. -/
theorem sl2_eigenvalue_mem_integer_interval (t : IsSl2Triple h e f)
    (hμ : (toEnd K L M h).HasEigenvalue μ) :
    ∃ z : ℤ, μ = (z : K) ∧ -(finrank K M : ℤ) < z ∧ z < (finrank K M : ℤ) := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  obtain ⟨z, hz, hub⟩ := eigenvalue_upper t hv
  have hv' : (toEnd K L M (-h)).HasEigenvector (-μ) v := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv.2⟩
    simpa using congrArg Neg.neg (Module.End.mem_eigenspace_iff.mp hv.1)
  obtain ⟨z', hz', hlb⟩ := eigenvalue_upper t.symm hv'
  have huu : -z = z' := by
    apply Int.cast_injective (α := K)
    simpa [← hz] using hz'
  exact ⟨z, hz, by omega, hub⟩

end Strings

section Weights

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

/-- Each Cartan weight of an actual module has a bounded integral value on
every coroot. This applies to generalized Cartan weight spaces as well. -/
theorem weight_coroot_mem_integer_interval (χ : Weight K H M) (α : H.root) :
    ∃ z : ℤ, χ (coroot α.val) = (z : K) ∧
      -(finrank K M : ℤ) < z ∧ z < (finrank K M : ℤ) := by
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨h, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have ht := t.h_eq_coroot hα he hf
  subst h
  exact sl2_eigenvalue_mem_integer_interval t (χ.hasEigenvalueAt (coroot α.val))

end Weights

section HighestWeight

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [FiniteDimensional ℂ M] [Nontrivial M]

/-- The sum of simple-root coordinates is evaluation at an actual Cartan element. -/
theorem exists_height_element (b : (rootSystem H).Base) :
    ∃ H₀ : H, ∀ α : H.root, α.val H₀ = (b.height α : ℂ) := by
  classical
  let F := b.toWeightBasis.constr ℂ (fun _ => (1 : ℂ))
  let H₀ := (Module.evalEquiv ℂ H).symm F
  refine ⟨H₀, fun α => ?_⟩
  change (rootSystem H).root α H₀ = _
  rw [Module.apply_evalEquiv_symm_apply ℂ H]
  obtain ⟨c, -, -, hc⟩ := b.exists_root_eq_sum_int α
  rw [b.height_eq_sum hc, hc, map_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : F ((rootSystem H).root j) = 1 := by
    change F ((rootSystem H).root (⟨j, hj⟩ : b.support)) = _
    rw [← b.toWeightBasis_apply]
    exact b.toWeightBasis.constr_basis ℂ _ _
  rw [map_zsmul, hj', zsmul_eq_mul, mul_one]

/-- Relative to any base of the actual root system there is a common
eigenvector killed by all positive root spaces. Its simple-coroot values
are natural numbers in the dimension-bounded box. -/
theorem exists_bounded_dominant_highest_weight (b : (rootSystem H).Base) :
    ∃ (χ : Weight ℂ H M) (v : M) (a : b.support → Fin (finrank ℂ M)),
      v ≠ 0 ∧ (∀ x : H, ⁅x, v⁆ = χ x • v) ∧
      (∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, v⁆ = 0) ∧
      ∀ j : b.support, χ (coroot j.val.val) = ((a j : ℕ) : ℂ) := by
  classical
  obtain ⟨H₀, hH₀⟩ := exists_height_element H b
  haveI : Nonempty (Weight ℂ H M) := by
    by_contra! he
    simpa only [iSup_of_empty, bot_ne_top] using iSup_genWeightSpace_eq_top' ℂ H M
  obtain ⟨χ, -, hχ⟩ := Finset.univ.exists_max_image
    (fun χ : Weight ℂ H M => (χ H₀).re) Finset.univ_nonempty
  obtain ⟨v, hv, hev⟩ := exists_forall_lie_eq_smul ℂ H M χ
  have hmem : v ∈ genWeightSpace M χ :=
    weightSpace_le_genWeightSpace M χ ((mem_weightSpace χ v).mpr hev)
  have hkill (α : H.root) (hpos : b.IsPos α) (x : L) (hx : x ∈ rootSpace H α.val) :
      ⁅x, v⁆ = 0 := by
    have hshift := mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace ℂ L H M
      α.val χ hx hmem
    by_contra! hne
    have hspace : genWeightSpace M (⇑α.val + ⇑χ) ≠ ⊥ := by
      intro hz
      rw [hz] at hshift
      exact hne hshift
    have hmax := hχ (⟨_, hspace⟩ : Weight ℂ H M) (Finset.mem_univ _)
    change ((α.val H₀ + χ H₀).re) ≤ (χ H₀).re at hmax
    rw [hH₀] at hmax
    simp only [Complex.add_re, Complex.intCast_re, add_le_iff_nonpos_left] at hmax
    exact (not_le_of_gt hpos) (by exact_mod_cast hmax)
  have hlabels (j : b.support) :
      ∃ a : Fin (finrank ℂ M), χ (coroot j.val.val) = ((a : ℕ) : ℂ) := by
    have hα : j.val.val.IsNonZero := (Finset.mem_filter.mp j.val.property).2
    obtain ⟨s, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
    have hs := t.h_eq_coroot hα he hf
    subst s
    have p : t.HasPrimitiveVectorWith v (χ (coroot j.val.val)) :=
      ⟨hv, hev _, hkill _ (RootPairing.Base.isPos_of_mem_support j.property) e he⟩
    obtain ⟨n, hn⟩ := p.exists_nat
    exact ⟨⟨n, primitive_label_lt_finrank t p hn⟩, hn⟩
  exact ⟨χ, v, fun j => (hlabels j).choose, hv, hev, hkill, fun j => (hlabels j).choose_spec⟩

end HighestWeight

section CompactPair

open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.CanonicalCoroot
open CubicAnomaly.Classification.SieveBounds
open CubicAnomaly.Classification.ComplexDuality

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

set_option maxHeartbeats 800000 in
/-- The original compact-pair hypotheses produce an actual highest weight
of the canonical complex half, in the same isotropy Cartan as a null coroot.
The respective label bounds at the four exceptional ambient dimensions are
strict, since a label of size n requires at least n+1 string vectors. -/
theorem all_rank_exceptional_highest_weight_bounds
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    ∃ hK : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h),
      letI := hK
      ∃ (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) (hH : H.IsCartanSubalgebra),
        letI := hH
        (∃ α : H.root, (coroot α.val : ℂ ⊗[ℝ] h) ≠ 0 ∧
          ∀ i j, canonicalCorootCubic B h e H (Module.finBasis ℂ H) α i j = 0) ∧
        ∃ (b : (rootSystem H).Base) (χ : Weight ℂ H V) (v : V)
          (a : b.support → Fin (finrank ℂ V)), v ≠ 0 ∧ (∀ x : H, ⁅x, v⁆ = χ x • v) ∧
          (∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, v⁆ = 0) ∧
          ∀ j : b.support, χ (coroot j.val.val) = ((a j : ℕ) : ℂ) ∧
            (finrank ℝ g = 52 → (a j : ℕ) < 23) ∧
            (finrank ℝ g = 78 → (a j : ℕ) < 36) ∧
            (finrank ℝ g = 133 → (a j : ℕ) < 65) ∧
            (finrank ℝ g = 248 → (a j : ℕ) < 121) := by
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  obtain ⟨hK, H, hH, α, hne, hnull⟩ := all_rank_exists_null_coroot B h heff hproper e hradical
  letI := hK
  letI := hH
  haveI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) V :=
    (compact_complement_complex_type_decomposition B h hproper e).2.1
  letI : Nontrivial V := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) V
  obtain ⟨b⟩ := RootPairing.nonempty_base (rootSystem H)
  obtain ⟨χ, v, a, hv, hev, hpos, hlabel⟩ :=
    exists_bounded_dominant_highest_weight (M := V) H b
  obtain ⟨h52, h78, h133, h248⟩ := all_rank_exceptional_size_half_bounds B h heff hproper e hradical
  refine ⟨hK, H, hH, ⟨α, hne, hnull⟩, b, χ, v, a, hv, hev, hpos, fun j =>
    ⟨hlabel j, fun h => (a j).isLt.trans_le (h52 h), fun h => (a j).isLt.trans_le (h78 h),
      fun h => (a j).isLt.trans_le (h133 h), fun h => (a j).isLt.trans_le (h248 h)⟩⟩

end CompactPair

end CubicAnomaly.Classification.ExceptionalSieveWeights
