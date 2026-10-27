import CubicAnomaly.Classification.UnitaryModuleBridge
import CubicAnomaly.Classification.SimpleIdealStructure
import CubicAnomaly.Classification.ExternalTensor
import CubicAnomaly.Classification.IdealTensorDuality
import CubicAnomaly.Classification.IdealProductRepresentation
import CubicAnomaly.Classification.AnomalyComplexification

/-!
# Simple isotropy in the actual special-unitary branch

Two distinct simple isotropy ideals give a nonzero equivariant product of
their defining action operators. Its source is an actual irreducible
self-dual tensor module and its values are traceless. Absorption therefore
places it in the original isotropy image. Perfectness forces every such
tensor-to-adjoint map to vanish, contradicting the nonzero product.

All tensor irreducibility, self-duality, trace and action identifications
are derived. No tensor factorization or highest-weight classification of
the defining representation is supplied.
-/

namespace CubicAnomaly.Classification.UnitarySimplicity

open LieAlgebra LieModule
open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.AnomalyComplexification
open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.UnitaryDefining
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.UnitaryModuleBridge
open CubicAnomaly.Classification.SimpleIdealStructure
open CubicAnomaly.Classification.ExternalTensor
open CubicAnomaly.Classification.IdealTensorDuality
open CubicAnomaly.Classification.IdealProductRepresentation
open CubicAnomaly.Classification.CubicIdealDecomposition
open CubicAnomaly.Classification.SelfDualAbsorption

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

set_option maxHeartbeats 800000 in
/-- In the concrete special-unitary branch, the original hypotheses force
the actual complexified isotropy algebra to be simple in every dimension. -/
theorem all_rank_special_unitary_complexified_isotropy_simple
    (B : CompactForm (specialUnitaryAlgebra W))
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h) := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  have hradC := (hermitian_complex_radical_ne_bot_iff (hermitianHalfOfCommutant B h e)).mpr
    hradical
  have hnon : ¬Subsingleton (ℂ ⊗[ℝ] h) := by
    intro hs
    letI := hs
    exact hradC (Subsingleton.elim _ _)
  letI : Nontrivial (ℂ ⊗[ℝ] h) := not_subsingleton_iff_nontrivial.mp hnon
  letI := complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)
  letI := complexified_defining_lieModule (specialUnitaryDefiningRepresentation h)
  letI : LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) W :=
    special_unitary_complexified_defining_faithful h
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) W :=
    all_rank_special_unitary_complexified_defining_irreducible B h heff hproper e hradical
  rcases semisimple_simple_or_disjoint_atoms (R := ℂ) (L := ℂ ⊗[ℝ] h) with
    hsimple | ⟨I, J, hI, hJ, hIJ⟩
  · exact hsimple
  · letI : LieAlgebra.IsSimple ℂ I := LieAlgebra.IsSemisimple.isSimple_of_isAtom I hI
    letI : LieAlgebra.IsSimple ℂ J := LieAlgebra.IsSemisimple.isSimple_of_isAtom J hJ
    letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) (I ⊗[ℂ] J) :=
      disjoint_simple_ideal_tensor_irreducible I J hIJ
    let μ := idealProductMap (W := W) I J
    have htrace : ∀ t, LinearMap.trace ℂ W (μ t) = 0 :=
      ideal_product_map_trace_zero I J (semisimple_ideal_perfect I) hIJ
    let f := liftTraceZeroEquivariant h μ htrace
    have habs := compact_self_dual_irreducible_ambient_range_le B h hproper e
      (atomic_ideal_tensor_self_dual I J hI hJ) f
    exfalso
    apply semisimple_ideal_product_range_not_le_action_range (W := W) I J hI.1 hJ.1 hIJ
    exact lift_trace_zero_range_le_action_range h μ htrace habs

/-- Simplicity descends to the original real isotropy algebra in the
special-unitary branch, directly from the original compact-pair hypotheses. -/
theorem all_rank_special_unitary_isotropy_simple
    (B : CompactForm (specialUnitaryAlgebra W))
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieAlgebra.IsSimple ℝ h := by
  letI := all_rank_special_unitary_complexified_isotropy_simple B h heff hproper e hradical
  exact simple_of_complexification_simple

/-- The nonzero full anomaly radical is the whole actual isotropy in the
special-unitary branch. This strengthens a selected factor's vanishing to
vanishing in every mixed first-slot direction. -/
theorem all_rank_special_unitary_cubic_radical_eq_top
    (B : CompactForm (specialUnitaryAlgebra W))
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊤ := by
  letI := all_rank_special_unitary_isotropy_simple B h heff hproper e hradical
  exact (LieAlgebra.IsSimple.eq_bot_or_eq_top _).resolve_left hradical

/-- Every mixed entry of the actual Hermitian half's cubic trace is zero
under the original special-unitary hypotheses. -/
theorem all_rank_special_unitary_cubic_trace_zero
    (B : CompactForm (specialUnitaryAlgebra W))
    (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (x y z : h) :
    CubicAnomaly.Classification.CubicRadical.matrixTraceCubic
      ((hermitianHalfOfCommutant B h e).generators x)
      ((hermitianHalfOfCommutant B h e).generators y)
      ((hermitianHalfOfCommutant B h e).generators z) = 0 := by
  have hx : x ∈ (hermitianHalfOfCommutant B h e).cubicRadical := by
    rw [all_rank_special_unitary_cubic_radical_eq_top B h heff hproper e hradical]
    trivial
  exact (CubicAnomaly.Classification.AllRank.hermitian_half_cubic_radical_membership _ x).mp
    hx y z

end CubicAnomaly.Classification.UnitarySimplicity
