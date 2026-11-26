import CubicAnomaly.Classification.ClassicalModuleBridge
import CubicAnomaly.Classification.SimpleIdealStructure
import CubicAnomaly.Classification.IdealTripleProduct
import CubicAnomaly.Classification.IdealTensorExtensions
import CubicAnomaly.Classification.IdealTensorDuality
import CubicAnomaly.Classification.AnomalyComplexification

/-!
# At most two simple isotropy factors in the form-preserving branches

Three pairwise disjoint atomic isotropy ideals give an actual irreducible
self-dual triple tensor module. Their defining action product is nonzero
and, as a product of three commuting skew operators, preserves the actual
defining bilinear form. It therefore lifts to the original complexified
ambient algebra. Absorption puts it in the isotropy, whereas perfectness
forces every such triple-to-adjoint map to vanish.

The final alternatives use only the original compact-pair hypotheses.
They leave the two-factor case explicit; they do not assert that this
remaining case is impossible.
-/

namespace CubicAnomaly.Classification.ClassicalIsotropyFactors

open LieAlgebra LieModule
open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.AnomalyComplexification
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.OrthogonalDefining
open CubicAnomaly.Classification.OrthogonalComplexification
open CubicAnomaly.Classification.SymplecticGeometry
open CubicAnomaly.Classification.SymplecticDefining
open CubicAnomaly.Classification.SymplecticForm
open CubicAnomaly.Classification.ClassicalModuleBridge
open CubicAnomaly.Classification.SimpleIdealStructure
open CubicAnomaly.Classification.IdealTripleProduct
open CubicAnomaly.Classification.IdealTensorExtensions
open CubicAnomaly.Classification.IdealTensorDuality
open CubicAnomaly.Classification.SelfDualAbsorption

private theorem complexified_isotropy_nontrivial
    {g : Type*} [LieRing g] [LieAlgebra ℝ g]
    (h : LieSubalgebra ℝ g) {q : LieSubmodule ℝ h g}
    (V : CubicAnomaly.Classification.AllRank.HermitianHalf h q)
    (hradical : V.cubicRadical ≠ ⊥) : Nontrivial (ℂ ⊗[ℝ] h) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  letI := hs
  exact ((hermitian_complex_radical_ne_bot_iff V).mpr hradical)
    (Subsingleton.elim _ _)

section Orthogonal

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

set_option maxHeartbeats 1000000 in
/-- The original orthogonal hypotheses exclude three actual pairwise
disjoint atomic ideals of the complexified isotropy, in every dimension. -/
theorem all_rank_orthogonal_no_three_isotropy_atoms
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (I J T : LieIdeal ℂ (ℂ ⊗[ℝ] h))
    (hI : IsAtom I) (hJ : IsAtom J) (hT : IsAtom T)
    (hIJ : Disjoint I J) (hIT : Disjoint I T) (hJT : Disjoint J T) : False := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  letI : LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) :=
    orthogonal_complexified_defining_faithful h
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] W) :=
    all_rank_orthogonal_defining_complex_irreducible B h heff hproper e hradical
  letI : LieAlgebra.IsSimple ℂ I := LieAlgebra.IsSemisimple.isSimple_of_isAtom I hI
  letI : LieAlgebra.IsSimple ℂ J := LieAlgebra.IsSemisimple.isSimple_of_isAtom J hJ
  letI : LieAlgebra.IsSimple ℂ T := LieAlgebra.IsSemisimple.isSimple_of_isAtom T hT
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) ((I ⊗[ℂ] J) ⊗[ℂ] T) :=
    pairwise_disjoint_simple_ideal_triple_irreducible I J T hIJ hIT hJT
  let μ := idealTripleProductMap (W := ℂ ⊗[ℝ] W) I J T
  have hform : ∀ t, μ t ∈ orthogonalExtendedAlgebra (W := W) := by
    intro t
    exact ideal_triple_product_map_mem_skewAdjointLieSubalgebra
      (orthogonalExtendedForm (W := W)) (orthogonal_complexified_defining_form_invariant h)
      I J T hIJ hIT hJT t
  let f := liftOrthogonalEquivariant h μ hform
  have habs := compact_self_dual_irreducible_ambient_range_le B h hproper e
    (atomic_ideal_triple_self_dual I J T hI hJ hT) f
  apply semisimple_ideal_triple_product_range_not_le_action_range
    (W := ℂ ⊗[ℝ] W) I J T hI.1 hJ.1 hT.1 hIJ hIT hJT
  exact lift_orthogonal_range_le_action_range h μ hform habs

/-- The actual complexified orthogonal isotropy is simple, or is the sum
of exactly two disjoint atomic ideals. No list of Lie types is supplied. -/
theorem all_rank_orthogonal_isotropy_simple_or_two_atoms
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h) ∨
      ∃ I J : LieIdeal ℂ (ℂ ⊗[ℝ] h),
        IsAtom I ∧ IsAtom J ∧ Disjoint I J ∧ I ⊔ J = ⊤ := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  letI := complexified_isotropy_nontrivial h (hermitianHalfOfCommutant B h e) hradical
  exact semisimple_simple_or_two_atoms_of_no_three
    (all_rank_orthogonal_no_three_isotropy_atoms B h heff hproper e hradical)

end Orthogonal

section Symplectic

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

set_option maxHeartbeats 1000000 in
/-- The original symplectic hypotheses exclude three actual pairwise
disjoint atomic isotropy ideals, using the constructed quaternionic form. -/
theorem all_rank_symplectic_no_three_isotropy_atoms
    (Q : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra Q))
    (h : LieSubalgebra ℝ (symplecticAlgebra Q))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (I J T : LieIdeal ℂ (ℂ ⊗[ℝ] h))
    (hI : IsAtom I) (hJ : IsAtom J) (hT : IsAtom T)
    (hIJ : Disjoint I J) (hIT : Disjoint I T) (hJT : Disjoint J T) : False := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
  letI := complexified_defining_lieModule (symplecticDefiningRepresentation Q h)
  letI : LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) W :=
    symplectic_complexified_defining_faithful Q h
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) W :=
    all_rank_symplectic_complexified_defining_irreducible Q B h heff hproper e hradical
  letI : LieAlgebra.IsSimple ℂ I := LieAlgebra.IsSemisimple.isSimple_of_isAtom I hI
  letI : LieAlgebra.IsSimple ℂ J := LieAlgebra.IsSemisimple.isSimple_of_isAtom J hJ
  letI : LieAlgebra.IsSimple ℂ T := LieAlgebra.IsSemisimple.isSimple_of_isAtom T hT
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) ((I ⊗[ℂ] J) ⊗[ℂ] T) :=
    pairwise_disjoint_simple_ideal_triple_irreducible I J T hIJ hIT hJT
  let μ := idealTripleProductMap (W := W) I J T
  have hform : ∀ t, μ t ∈ skewAdjointLieSubalgebra (quaternionicForm Q) := by
    intro t
    exact ideal_triple_product_map_mem_skewAdjointLieSubalgebra
      (quaternionicForm Q) (quaternionic_form_complexified_invariant Q h)
      I J T hIJ hIT hJT t
  let f := liftSymplecticEquivariant Q h μ hform
  have habs := compact_self_dual_irreducible_ambient_range_le B h hproper e
    (atomic_ideal_triple_self_dual I J T hI hJ hT) f
  apply semisimple_ideal_triple_product_range_not_le_action_range
    (W := W) I J T hI.1 hJ.1 hT.1 hIJ hIT hJT
  exact lift_symplectic_range_le_action_range Q h μ hform habs

/-- The actual complexified symplectic isotropy is simple, or is the sum
of exactly two disjoint atomic ideals, directly from the original hypotheses. -/
theorem all_rank_symplectic_isotropy_simple_or_two_atoms
    (Q : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra Q))
    (h : LieSubalgebra ℝ (symplecticAlgebra Q))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h) ∨
      ∃ I J : LieIdeal ℂ (ℂ ⊗[ℝ] h),
        IsAtom I ∧ IsAtom J ∧ Disjoint I J ∧ I ⊔ J = ⊤ := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  letI := complexified_isotropy_nontrivial h (hermitianHalfOfCommutant B h e) hradical
  exact semisimple_simple_or_two_atoms_of_no_three
    (all_rank_symplectic_no_three_isotropy_atoms Q B h heff hproper e hradical)

end Symplectic

end CubicAnomaly.Classification.ClassicalIsotropyFactors
