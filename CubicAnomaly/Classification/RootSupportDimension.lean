import CubicAnomaly.Classification.RootSupportGraph
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Set.Card

/-!
# Dimensions from the cardinalities of actual root supports

The actual ambient root spaces are one-dimensional and independent. A
Cartan-stable subspace disjoint from the Cartan therefore has dimension equal
to the number of roots it contains. A Cartan-containing subalgebra has
dimension equal to the Cartan dimension plus its actual contained-root count.
No authored coordinate array or root-type dimension formula is used.
-/

namespace CubicAnomaly.Classification.RootSupportDimension

open LieAlgebra LieModule Module
open scoped DirectSum
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.EqualRank

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
/-- The actual supported roots form a finite set. -/
theorem containedRoots_finite (N : Submodule K L) : (containedRoots H N).Finite :=
  (finite_genWeightSpace_ne_bot K H L).subset fun _ hα => hα.2.1

omit [CharZero K] [LieAlgebra.IsKilling K L] in
private theorem finrank_iSup_independent {ι : Type*} [Fintype ι]
    (A : ι → Submodule K L) (hA : iSupIndep A) :
    finrank K (⨆ i, A i : Submodule K L) = ∑ i, finrank K (A i) := by
  classical
  let E := LinearEquiv.ofInjective (DirectSum.coeLinearMap A) hA.dfinsupp_lsum_injective
  have hdim := E.finrank_eq.symm
  change finrank K (DirectSum.coeLinearMap A).range =
    finrank K (⨁ i, A i) at hdim
  rw [DirectSum.range_coeLinearMap, Module.finrank_directSum] at hdim
  exact hdim

/-- An independent sum of actual supported root spaces has exactly one
dimension for each actual supported root. -/
theorem finrank_supported_root_sum (N : Submodule K L) :
    finrank K (⨆ α : containedRoots H N, (rootSpace H α.val).toSubmodule : Submodule K L) =
      (containedRoots H N).ncard := by
  classical
  letI := (containedRoots_finite H N).fintype
  have hind : iSupIndep (fun α : H → K => (rootSpace H α).toSubmodule) :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace K H L)
  have hs : iSupIndep (fun α : containedRoots H N => (rootSpace H α.val).toSubmodule) :=
    hind.comp Subtype.val_injective
  rw [finrank_iSup_independent _ hs]
  have hone (α : containedRoots H N) : finrank K (rootSpace H α.val).toSubmodule = 1 :=
    finrank_rootSpace_eq_one (Weight.mk α.val α.property.2.1) α.property.1
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  exact Nat.card_eq_fintype_card.symm

/-- A Cartan-stable subspace with no zero-weight vectors is the sum of
exactly the actual root spaces it contains. -/
theorem cartan_submodule_eq_supported_root_sum (N : LieSubmodule K H L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule) :
    N.toSubmodule = ⨆ α : containedRoots H N.toSubmodule, (rootSpace H α.val).toSubmodule := by
  apply le_antisymm
  · intro x hx
    suffices hall : ∀ y : N, (y : L) ∈
        ⨆ α : containedRoots H N.toSubmodule, (rootSpace H α.val).toSubmodule from hall ⟨x, hx⟩
    intro y
    have hy : y ∈ ⨆ α : H → K, genWeightSpace N α := by
      rw [iSup_genWeightSpace_eq_top]
      trivial
    induction hy using LieSubmodule.iSup_induction' with
    | mem α y hy =>
      have hr : (y : L) ∈ rootSpace H α :=
        map_genWeightSpace_le N.incl ((LieSubmodule.mem_map _).mpr ⟨y, hy, rfl⟩)
      by_cases hy0 : (y : L) = 0
      · simpa only [hy0] using (⨆ α : containedRoots H N.toSubmodule,
          (rootSpace H α.val).toSubmodule).zero_mem
      have hα : α ≠ 0 := by
        intro ha
        have hyH : (y : L) ∈ H := by
          simpa only [ha, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hr
        have hm : (y : L) ∈ H.toSubmodule ⊓ N.toSubmodule := ⟨hyH, y.property⟩
        exact hy0 (by simpa only [hdis.eq_bot, Submodule.mem_bot] using hm)
      have hsupp : α ∈ containedRoots H N.toSubmodule := ⟨hα,
        by intro hb; exact hy0 (by simpa only [hb, LieSubmodule.mem_bot] using hr),
        root_space_le_of_nonzero_mem H N.toSubmodule hα hr y.property hy0⟩
      have hle : (rootSpace H α).toSubmodule ≤
          ⨆ α : containedRoots H N.toSubmodule, (rootSpace H α.val).toSubmodule :=
        le_iSup_of_le ⟨α, hsupp⟩ le_rfl
      exact hle hr
    | zero => simp
    | add x y _ _ hx hy =>
      exact (⨆ α : containedRoots H N.toSubmodule,
        (rootSpace H α.val).toSubmodule).add_mem hx hy
  · exact iSup_le fun α => α.property.2.2

/-- The dimension of an actual root-space module with no zero weight is
exactly its actual root-support cardinality. -/
theorem finrank_eq_supported_root_count (N : LieSubmodule K H L)
    (hdis : Disjoint H.toSubmodule N.toSubmodule) :
    finrank K N = (containedRoots H N.toSubmodule).ncard := by
  change finrank K N.toSubmodule = _
  conv_lhs => rw [cartan_submodule_eq_supported_root_sum H N hdis]
  exact finrank_supported_root_sum H N.toSubmodule

/-- A Cartan-containing subalgebra has dimension equal to the Cartan
dimension plus the number of its actual contained roots. -/
theorem subalgebra_finrank_eq_cartan_add_root_count
    (S : LieSubalgebra K L) (hHS : H ≤ S) :
    finrank K S = finrank K H + (containedRoots H S.toSubmodule).ncard := by
  let R := ⨆ α : containedRoots H S.toSubmodule, (rootSpace H α.val).toSubmodule
  have hS : S.toSubmodule = H.toSubmodule ⊔ R := by
    simpa only [R, iSup_subtype] using subalgebra_eq_root_decomposition H S hHS
  have hind : iSupIndep (fun α : H → K => (rootSpace H α).toSubmodule) :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace K H L)
  have hle : R ≤ ⨆ (α : H → K) (_ : α ≠ 0), (rootSpace H α).toSubmodule := by
    exact iSup_le fun α => le_iSup_of_le α.val (le_iSup_of_le α.property.1 le_rfl)
  have hdis : Disjoint H.toSubmodule R := by
    have hd := (hind (0 : H → K)).mono_right hle
    simpa only [rootSpace_zero_eq] using hd
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq H.toSubmodule R
  rw [← hS, hdis.eq_bot, finrank_bot, add_zero] at hdim
  change finrank K S = finrank K H + _ at hdim
  rw [finrank_supported_root_sum H S.toSubmodule] at hdim
  exact hdim

section CompactPair

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.ComplexDuality
open CubicAnomaly.Classification.CompactGeometry
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- Actual root counts recover the isotropy and half dimensions. The two
half-support counts agree by their proved equivariant duality. These are
semantic identities for actual roots, before a coordinate census is chosen. -/
theorem compact_common_cartan_root_count_formulas
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) :
    let q := orthogonalComplement B h
    let J := commutantComplexStructure e
    let P := ambientComplexifiedHalf q J Complex.I
    let Q := ambientComplexifiedHalf q J (-Complex.I)
    finrank ℝ h = finrank ℂ H + (containedRoots H (h.toSubmodule.baseChange ℂ)).ncard ∧
    finrank ℂ P = (containedRoots H P.toSubmodule).ncard ∧
    finrank ℂ Q = (containedRoots H Q.toSubmodule).ncard ∧
    (containedRoots H P.toSubmodule).ncard = (containedRoots H Q.toSubmodule).ncard := by
  let q := orthogonalComplement B h
  let J := commutantComplexStructure e
  let P₀ := ambientComplexifiedHalf q J Complex.I
  let Q₀ := ambientComplexifiedHalf q J (-Complex.I)
  let S := complexifiedSubalgebra h
  let P := imageActionSubmodule h P₀
  let Q := imageActionSubmodule h Q₀
  have hgcenter := (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) :=
    compact_complexification_isKilling B hgcenter
  have hPQ : P.toSubmodule ⊔ Q.toSubmodule = q.toSubmodule.baseChange ℂ :=
    congrArg LieSubmodule.toSubmodule
      (ambient_complex_halves_sup q J (commutant_complex_structure_square e))
  have hdis : Disjoint S.toSubmodule (P.toSubmodule ⊔ Q.toSubmodule) := by
    rw [hPQ]
    exact (compact_pair_complexification_isCompl B h).disjoint
  have hHS : H.toSubmodule ≤ S.toSubmodule := hH
  have hP := finrank_eq_supported_root_count H (restrictCartanSubmodule H S hH P)
    ((hdis.mono_left hHS).mono_right le_sup_left)
  have hQ := finrank_eq_supported_root_count H (restrictCartanSubmodule H S hH Q)
    ((hdis.mono_left hHS).mono_right le_sup_right)
  have hS := subalgebra_finrank_eq_cartan_add_root_count H S hH
  change finrank ℂ (h.toSubmodule.baseChange ℂ) =
    finrank ℂ H + (containedRoots H (h.toSubmodule.baseChange ℂ)).ncard at hS
  rw [complexification_submodule_finrank] at hS
  change finrank ℂ P₀ = (containedRoots H P₀.toSubmodule).ncard at hP
  change finrank ℂ Q₀ = (containedRoots H Q₀.toSubmodule).ncard at hQ
  refine ⟨hS, hP, hQ, ?_⟩
  rw [← hP, ← hQ]
  obtain ⟨D⟩ := (compact_complement_complex_type_decomposition B h hproper e).2.2.2.1
  have hD := D.toLinearEquiv.finrank_eq
  rw [Subspace.dual_finrank_eq] at hD
  calc
    finrank ℂ P₀ = finrank ℂ (invariantEigenspace (complexifiedEnd J) Complex.I) :=
      (ambientHalfEquiv q J Complex.I).toLinearEquiv.finrank_eq.symm
    _ = finrank ℂ (invariantEigenspace (complexifiedEnd J) (-Complex.I)) := hD.symm
    _ = finrank ℂ Q₀ := (ambientHalfEquiv q J (-Complex.I)).toLinearEquiv.finrank_eq

end CompactPair

end CubicAnomaly.Classification.RootSupportDimension
