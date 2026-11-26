import CubicAnomaly.Classification.AllRankGrading
import CubicAnomaly.Classification.FullRankRoots
import CubicAnomaly.Classification.RootLatticeBasis
import CubicAnomaly.Classification.RootSupportDimension
import CubicAnomaly.Classification.IntrinsicAnomaly

/-!
# The intrinsic finite toral reduction from the original hypotheses

The equal-geometric-rank branch constructs one actual ambient Cartan and
one nonzero character of its integer root lattice. On that same Cartan it
derives the full rational rank of the zero-grade roots, connected support
graphs for both actual complex halves, and all dimension/root-count
identities. The original full anomaly gives a nonzero vector annihilating
the actual grade-one root cubic on this same Cartan. The integer lattice
basis, the dual Cartan basis, the finite character enumeration and a nonzero
rational kernel of the integer root-coordinate cubic matrix are constructed
as well. Identifying this intrinsic data with authored
classical or exceptional coordinates remains a classification problem.
-/

namespace CubicAnomaly.Classification.IntrinsicToral

open LieAlgebra LieModule Module Matrix
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.CompactCartan
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.ToralCharacter
open CubicAnomaly.Classification.FullRankRoots
open CubicAnomaly.Classification.RootLatticeBasis
open CubicAnomaly.Classification.RootSupportGraph
open CubicAnomaly.Classification.RootSupportDimension
open CubicAnomaly.Classification.RootSupportTrace
open CubicAnomaly.Classification.RootCubicKernel
open CubicAnomaly.Classification.IntrinsicCartanBasis
open CubicAnomaly.Classification.CoordinateCubic
open CubicAnomaly.Classification.RationalKernel
open CubicAnomaly.Classification.IntrinsicAnomaly
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- All intrinsic toral data are conclusions: actual root degrees, full
zero-root rank, connected half-supports, exact counts, the full anomaly, and coordinates in
a constructed integer basis. No table-membership field is included. -/
def IntrinsicToralData (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) : Prop :=
  ∃ hK : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g),
    letI := hK
    ∃ (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H.IsCartanSubalgebra),
      letI := hH
      H ≤ complexifiedSubalgebra h ∧ finrank ℂ H = abelianRank ℝ g ∧
      (let q := orthogonalComplement B h
       let J := commutantComplexStructure e
       let P := ambientComplexifiedHalf q J Complex.I
       let Q := ambientComplexifiedHalf q J (-Complex.I)
       let S := complexifiedSubalgebra h
       ∃ character : rootLattice H →+ ZMod 3,
         character ≠ 0 ∧
         DirectSum.IsInternal (rootCharacterGrade H character) ∧
         rootCharacterGrade H character 0 = h.toSubmodule.baseChange ℂ ∧
         rootCharacterGrade H character 1 = P.toSubmodule ∧
         rootCharacterGrade H character (-1) = Q.toSubmodule ∧
         (∀ (i j : ZMod 3) (x y : ℂ ⊗[ℝ] g),
           x ∈ rootCharacterGrade H character i →
           y ∈ rootCharacterGrade H character j →
           ⁅x, y⁆ ∈ rootCharacterGrade H character (i + j)) ∧
         Submodule.span ℂ (containedRootForms H S) = ⊤ ∧
         finrank ℚ (Submodule.span ℚ (containedRootForms H S)) = finrank ℂ H ∧
         SupportConnected H S P.toSubmodule ∧ SupportConnected H S Q.toSubmodule ∧
         finrank ℝ h = finrank ℂ H + (containedRoots H (h.toSubmodule.baseChange ℂ)).ncard ∧
         finrank ℂ P = (containedRoots H P.toSubmodule).ncard ∧
         finrank ℂ Q = (containedRoots H Q.toSubmodule).ncard ∧
         (containedRoots H P.toSubmodule).ncard = (containedRoots H Q.toSubmodule).ncard ∧
         (∃ x : H, x ≠ 0 ∧ ∀ y z : H, actualRootCubic H P.toSubmodule x y z = 0) ∧
         Nat.card (rootLattice H →+ ZMod 3) = 3 ^ finrank ℂ H ∧
         ∃ values : Fin (finrank ℂ H) → ZMod 3,
           values ≠ 0 ∧
           (∀ x : rootLattice H,
             character x = ∑ i, ((intrinsicRootBasis H).repr x i : ZMod 3) * values i) ∧
           ∃ v : Fin (finrank ℂ H) → ℚ, v ≠ 0 ∧
             (intrinsicCoordinateCubicMatrix H values 1).map (Int.cast : ℤ → ℚ) *ᵥ v = 0)

/-- Equal geometric abelian ranks derive every intrinsic toral filter and
dimension interpretation on one constructed ambient Cartan. -/
theorem equal_abelianRank_intrinsic_toral_data
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (hrank : abelianRank ℝ h = abelianRank ℝ g) :
    IntrinsicToralData B h e := by
  have hgcenter := (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).2.2.1
  let hK := compact_complexification_isKilling B hgcenter
  letI := hK
  obtain ⟨H, hH, hContained, hdim⟩ :=
    compact_equal_abelianRank_exists_complex_cartan B h hrank
  letI := hH
  obtain ⟨character, hchar, hdir, hzero, hone, hneg, hbracket⟩ :=
    compact_common_cartan_root_character B h heff hproper e hradical H hContained
  obtain ⟨hPgraph, hQgraph⟩ :=
    compact_common_cartan_half_support_connected B h heff hproper e H hContained
  obtain ⟨hSdim, hPdim, hQdim, hPQcard⟩ :=
    compact_common_cartan_root_count_formulas B h heff hproper e H hContained
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  have hcubic := (canonical_anomaly_iff_actual_root_cubic B h heff hproper e
    (LieAlgebra.center_eq_bot ℝ h)
    H hContained).mp hradical
  have hrat := (canonical_anomaly_iff_intrinsic_rational_kernel B h heff hproper e
    (LieAlgebra.center_eq_bot ℝ h) H hContained character hone).mp hradical
  refine ⟨hK, H, hH, hContained, hdim, character, hchar, hdir, hzero, hone, hneg,
    hbracket, compact_common_cartan_root_forms_span_eq_top B h heff hproper e hradical H
      hContained,
    compact_common_cartan_root_forms_finrank_rat B h heff hproper e hradical H hContained,
    hPgraph, hQgraph, hSdim, hPdim, hQdim, hPQcard, hcubic,
    card_actual_root_lattice_characters H, ?_⟩
  refine ⟨fun i => character (intrinsicRootBasis H i), ?_,
    intrinsic_root_character_formula H character, hrat⟩
  · intro hz
    obtain ⟨i, hi⟩ := (intrinsic_root_character_ne_zero_iff H character).mp hchar
    exact hi (congrFun hz i)

/-- In every rank, the original hypotheses yield either a genuinely
rank-deficient pair or the complete intrinsic finite toral data above. -/
theorem all_rank_rank_deficient_or_intrinsic_toral_data
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    abelianRank ℝ h < abelianRank ℝ g ∨ IntrinsicToralData B h e := by
  rcases (abelianRank_subalgebra_le ℝ g h).lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr (equal_abelianRank_intrinsic_toral_data B h heff hproper e hradical heq)

end CubicAnomaly.Classification.IntrinsicToral
