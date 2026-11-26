import CubicAnomaly.Classification.SieveBounds
import CubicAnomaly.Classification.CompactCartan

/-!
# The rank-one and rank-two parity obstruction

A reduced actual root system on a one-dimensional Cartan has exactly two
roots. Hence the actual Killing Lie algebra has dimension three. Applied
to a compact pair of strictly smaller geometric isotropy rank inside ambient
rank two, this makes the isotropy dimension odd. The actual dual-half
dimension equation excludes every even-dimensional ambient algebra in this
rank-deficient branch, without a Lie-type classification.
-/

namespace CubicAnomaly.Classification.RankOneObstruction

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.KillingDimension

section ComplexGeometry

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- A reduced actual root system on a one-dimensional Cartan has precisely
two roots. The argument uses reducedness and linear dependence, not a type list. -/
theorem rank_one_actual_root_count (hrank : finrank K H = 1) : Fintype.card H.root = 2 := by
  classical
  let P := rootSystem H
  letI := P.indexNeg
  obtain ⟨n, hn, hcount⟩ := root_count_eq_twice_positive H
  rw [actual_root_count_eq_card H] at hcount
  have hpos : 0 < Fintype.card H.root := by omega
  obtain ⟨α⟩ := Fintype.card_pos_iff.mp hpos
  have hall (β : H.root) : β = α ∨ β = -α := by
    have hind : ¬LinearIndependent K ![P.root β, P.root α] := by
      intro hi
      have hb := hi.fintype_card_le_finrank
      rw [Subspace.dual_finrank_eq, hrank] at hb
      norm_num at hb
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) β α hind with h | h
    · exact Or.inl (P.root.injective h)
    · exact Or.inr ((RootPairing.root_eq_neg_iff (P := P)).mp h)
  have hu : (Finset.univ : Finset H.root) = {α, -α} := by
    ext β
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hall β
  have hne : α ≠ -α := P.ne_neg α
  rw [← Finset.card_univ, hu, Finset.card_pair hne]

/-- An actual splitting Cartan of dimension one forces actual algebra
dimension three. -/
theorem rank_one_killing_finrank_eq_three (hrank : finrank K H = 1) : finrank K L = 3 := by
  rw [killing_finrank_eq_cartan_add_roots H, hrank, actual_root_count_eq_card H,
    rank_one_actual_root_count H hrank]

end ComplexGeometry

section Compact

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.CompactCartan
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.SieveBounds
open CubicAnomaly.Classification.QuadraticRestriction
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- A nonzero compact algebra has positive geometric abelian rank. -/
theorem compact_abelianRank_pos [Nontrivial g] (B : CompactForm g) : 0 < abelianRank ℝ g := by
  obtain ⟨A, hA, hdim⟩ := exists_abelian_finrank_eq_abelianRank ℝ g
  letI := hA
  letI : A.IsCartanSubalgebra := compact_maximum_abelian_isCartan B A hdim
  rw [← hdim]
  exact finrank_pos

/-- A centreless compact algebra of geometric abelian rank one has actual
real dimension three. -/
theorem compact_abelianRank_one_finrank_eq_three
    (B : CompactForm g) (hcenter : LieAlgebra.center ℝ g = ⊥)
    (hrank : abelianRank ℝ g = 1) : finrank ℝ g = 3 := by
  obtain ⟨A, hA, hdim⟩ := exists_abelian_finrank_eq_abelianRank ℝ g
  letI := hA
  letI : A.IsCartanSubalgebra := compact_maximum_abelian_isCartan B A hdim
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) := compact_complexification_isKilling B hcenter
  let H := complexifiedSubalgebra A
  letI : H.IsCartanSubalgebra := complexified_abelian_cartan A
  have hHdim : finrank ℂ H = 1 := by
    change finrank ℂ (A.toSubmodule.baseChange ℂ) = 1
    rw [complexification_submodule_finrank]
    change finrank ℝ A = 1
    exact hdim.trans hrank
  have h := rank_one_killing_finrank_eq_three H hHdim
  rwa [Module.finrank_baseChange] at h

/-- Original anomalous compact pairs in even ambient dimension and ambient
geometric rank two cannot have strictly smaller isotropy rank. This excludes
the smallest rank-deficient branch without naming the ambient Lie type. -/
theorem all_rank_even_rank_two_not_rank_deficient
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (hrank : abelianRank ℝ g = 2) (heven : Even (finrank ℝ g)) :
    ¬abelianRank ℝ h < abelianRank ℝ g := by
  intro hlt
  have hthree := (all_rank_isotropy_dimension_bounds B h heff hproper e hradical).1
  letI : Nontrivial h := finrank_pos_iff.mp (by omega : 0 < finrank ℝ h)
  have hpos := compact_abelianRank_pos (B.restrict h)
  have hhrank : abelianRank ℝ h = 1 := by omega
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  have hhdim := compact_abelianRank_one_finrank_eq_three (B.restrict h)
    (LieAlgebra.center_eq_bot ℝ h) hhrank
  have hdim := compact_pair_dimension_equation B h hproper e
  obtain ⟨k, hk⟩ := heven
  omega

end Compact

end CubicAnomaly.Classification.RankOneObstruction
