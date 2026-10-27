import CubicAnomaly.Fixed.E8Metric

/-!
# Weighted adjoints of the actual exceptional generators

Norm two excludes simultaneous addition and subtraction in a root string.
The resulting simply-laced coefficients identify the raising and lowering
matrices as adjoints for the explicitly positive Hermitian metric.
-/

namespace CubicAnomaly.Fixed.E8Adjoints

open Matrix
open CubicAnomaly.Fixed.E8RootPairing
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8Metric
open RootPairing.GeckConstruction

noncomputable section

private theorem coordinate_unsigned_abs (i j : Fin 8) :
    (4 - CartanMatrix.E₈) i j = |CartanMatrix.E₈ i j| := by
  fin_cases i <;> fin_cases j <;> decide

theorem simple_gram_apply (i j : base.support) :
    simpleGram i j = ((|base.cartanMatrix i j| : ℤ) : ℂ) := by
  obtain ⟨i, rfl⟩ := simpleIndexEquiv.surjective i
  obtain ⟨j, rfl⟩ := simpleIndexEquiv.surjective j
  change (((4 - base.cartanMatrix) (simpleIndexEquiv i) (simpleIndexEquiv j) : ℤ) : ℂ) = _
  have h := coordinate_unsigned_abs i j
  exact_mod_cast (by
    simpa [simpleGram, base, simpleIndexEquiv, simpleBase_cartanMatrix,
      Matrix.ofNat_apply, simpleIndex_bijective.1.eq_iff] using h :
      (4 - base.cartanMatrix) (simpleIndexEquiv i) (simpleIndexEquiv j) =
        |base.cartanMatrix (simpleIndexEquiv i) (simpleIndexEquiv j)|)

private theorem simple_cartan_symm (i j : base.support) :
    base.cartanMatrix i j = base.cartanMatrix j i := by
  obtain ⟨i, rfl⟩ := simpleIndexEquiv.surjective i
  obtain ⟨j, rfl⟩ := simpleIndexEquiv.surjective j
  simpa [base, simpleIndexEquiv, simpleBase_cartanMatrix] using
    (CartanMatrix.E₈_isSymm.apply i j).symm

/-- Norm two rules out a root in both adjacent directions of a root string. -/
theorem root_add_sub_exclusive (a b : Root) :
    ¬ (rootPairing.root b + rootPairing.root a ∈ Set.range rootPairing.root ∧
      rootPairing.root b - rootPairing.root a ∈ Set.range rootPairing.root) := by
  rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
  have ha : form (rootPairing.root a) (rootPairing.root a) = 2 :=
    rootPairing.root_coroot_two a
  have hb : form (rootPairing.root b) (rootPairing.root b) = 2 :=
    rootPairing.root_coroot_two b
  have hplus : form (rootPairing.root c) (rootPairing.root c) = 2 :=
    rootPairing.root_coroot_two c
  have hminus : form (rootPairing.root d) (rootPairing.root d) = 2 :=
    rootPairing.root_coroot_two d
  rw [hc] at hplus
  rw [hd] at hminus
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at hplus hminus
  have h : (4 : ℂ) = 0 := by linear_combination hplus + hminus - 2 * ha - 2 * hb
  norm_num at h

/-- Every nonzero simply-laced raising entry has coefficient one, and its
reverse lowering entry has coefficient one as well. -/
theorem e8_root_string_coefficients (i k l : Root)
    (h : rootPairing.root l = rootPairing.root i + rootPairing.root k) :
    rootPairing.chainBotCoeff i k = 0 ∧ rootPairing.chainTopCoeff i l = 0 := by
  constructor
  · apply rootPairing.chainBotCoeff_eq_zero_iff.mpr
    right
    intro hsub
    exact root_add_sub_exclusive i k ⟨⟨l, by simpa [add_comm] using h⟩, hsub⟩
  · apply rootPairing.chainTopCoeff_eq_zero_iff.mpr
    right
    intro hadd
    exact root_add_sub_exclusive i l ⟨hadd, ⟨k, by rw [h]; simp⟩⟩

/-- The actual raising and lowering generators are weighted adjoints. -/
theorem geck_raising_weighted_adjoint (i : base.support) :
    (e i)ᴴ * gramMatrix = gramMatrix * f i := by
  classical
  letI := rootPairing.indexNeg
  rw [e, f, gramMatrix, fromBlocks_conjTranspose, fromBlocks_multiply,
    fromBlocks_multiply]
  ext (j | j) (k | k)
  · simp
  · by_cases hk : k = (i : Root) <;>
      simp [hk, Matrix.conjTranspose_apply, Matrix.mul_apply, simple_gram_apply,
        simple_cartan_symm, apply_ite]
  · by_cases hj : j = rootPairing.reflectionPerm i i <;>
      simp [hj, Matrix.conjTranspose_apply, Matrix.mul_apply, simple_gram_apply, apply_ite]
  · simp only [add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.fromBlocks_apply₂₂]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, apply_ite]
    have hc : rootPairing.root k = rootPairing.root i + rootPairing.root j ↔
        rootPairing.root j = rootPairing.root k - rootPairing.root i := by
      rw [eq_sub_iff_add_eq, add_comm (rootPairing.root j), eq_comm]
    by_cases h : rootPairing.root k = rootPairing.root i + rootPairing.root j
    · have hz := e8_root_string_coefficients i j k h
      simp only [if_pos h, if_pos (hc.mp h), hz.1, hz.2, Nat.cast_zero, zero_add,
        star_one]
    · simp only [if_neg h, if_neg (mt hc.mpr h), star_zero]

/-- Cartan generators are self-adjoint for the same positive metric. -/
theorem geck_cartan_weighted_adjoint (i : base.support) :
    (h i)ᴴ * gramMatrix = gramMatrix * h i := by
  classical
  simp [h, gramMatrix, fromBlocks_conjTranspose, fromBlocks_multiply]

/-- Lowering and raising are adjoints in the reverse direction as well. -/
theorem geck_lowering_weighted_adjoint (i : base.support) :
    (f i)ᴴ * gramMatrix = gramMatrix * e i := by
  have hh := congrArg Matrix.conjTranspose (geck_raising_weighted_adjoint i)
  simpa [Matrix.conjTranspose_mul, gramMatrix_hermitian.eq] using hh.symm

end

end CubicAnomaly.Fixed.E8Adjoints
