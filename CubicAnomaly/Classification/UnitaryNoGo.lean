import CubicAnomaly.Classification.UnitaryEndDecomposition
import CubicAnomaly.Classification.ScalarModule
import CubicAnomaly.Classification.UnitarySkewLine
import CubicAnomaly.Classification.UnitaryTraceSkewObstruction
import CubicAnomaly.Classification.UnitarySimplicity

/-!
# All-rank special-unitary exclusion by tensor interchange

The original hypotheses would give an actual scalar block, a simple
adjoint block, and one inequivalent irreducible dual pair inside the
actual defining endomorphisms. The trace-skew equivariant endomorphisms
therefore form one nonzero complex line. Canonical trace reshuffling
transports this to a flip-odd line in the actual tensor-square commutant.
That commutant is adjoint-closed, which makes such a line impossible.

Consequently the original special-unitary compact-pair hypotheses force
the full cubic radical to vanish in every dimension. No highest-weight
constituent theorem, root classification, or rank comparison is used.
-/

namespace CubicAnomaly.Classification.UnitaryNoGo

open Module LieModule LieAlgebra
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.ComplexDuality
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.UnitaryDefining
open CubicAnomaly.Classification.UnitarySimplicity
open CubicAnomaly.Classification.UnitaryEndDecomposition
open CubicAnomaly.Classification.ScalarModule
open CubicAnomaly.Classification.UnitarySkewLine
open CubicAnomaly.Classification.UnitaryTraceSkewObstruction
open CubicAnomaly.Classification.SelfDualAbsorption
open CubicAnomaly.Classification.AdjointTraceForms
open scoped TensorProduct

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

variable (h : LieSubalgebra ℝ (specialUnitaryAlgebra W))

local instance : LieRingModule (ℂ ⊗[ℝ] h) W :=
  complexifiedDefiningAction (specialUnitaryDefiningRepresentation h)

local instance : LieModule ℂ (ℂ ⊗[ℝ] h) W :=
  complexified_defining_lieModule (specialUnitaryDefiningRepresentation h)

/-- The scalar, isotropy, and complement decomposition is constructed
from the original special-unitary pair and literal normalized trace. -/
def actualEndBlocks [Nontrivial W] (B : CompactForm (specialUnitaryAlgebra W)) :
    ThreeBlockDecomposition ℂ (ℂ ⊗[ℝ] h) (Module.End ℂ W)
      (TrivialLieModule ℂ (ℂ ⊗[ℝ] h) ℂ) (ℂ ⊗[ℝ] h)
      (ℂ ⊗[ℝ] orthogonalComplement B h) where
  iU := scalarInsertion h
  pU := scalarProjection h
  iV := isotropyInsertion h
  pV := isotropyProjection h B
  iQ := complementInsertion h B
  pQ := complementProjection h B
  u_retraction := scalar_projection_insertion h
  v_retraction := isotropy_projection_insertion h B
  q_retraction := complement_projection_insertion h B
  sum_apply := scalar_isotropy_complement_sum h B

set_option maxHeartbeats 1200000 in
/-- The original hypotheses construct precisely one nonzero line of
trace-skew equivariant operators on the actual defining endomorphisms.
Every summand and all required module properties are derived. -/
theorem all_rank_special_unitary_end_trace_skew_line
    (B : CompactForm (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    ∃ D₀ : Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W, D₀ ≠ 0 ∧
      (∀ A C : Module.End ℂ W,
        LinearMap.trace ℂ W (D₀ A * C) = -LinearMap.trace ℂ W (A * D₀ C)) ∧
      ∀ D : Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.End ℂ W,
        (∀ A C : Module.End ℂ W,
          LinearMap.trace ℂ W (D A * C) = -LinearMap.trace ℂ W (A * D C)) →
        ∃ c : ℂ, D = c • D₀ := by
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) W :=
    all_rank_special_unitary_complexified_defining_irreducible B h heff hproper e hradical
  letI : Nontrivial W := LieModule.nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) W
  letI : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h) :=
    all_rank_special_unitary_complexified_isotropy_simple B h heff hproper e hradical
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  let U := TrivialLieModule ℂ (ℂ ⊗[ℝ] h) ℂ
  letI : FiniteDimensional ℂ U :=
    (TrivialLieModule.equiv ℂ (ℂ ⊗[ℝ] h) ℂ).symm.finiteDimensional
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) U := scalar_module_irreducible
  have hsH : Nonempty ((ℂ ⊗[ℝ] h) ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ (ℂ ⊗[ℝ] h)) :=
    invariant_nondegenerate_form_self_dual (killingForm ℂ (ℂ ⊗[ℝ] h))
      (LieModule.traceForm_lieInvariant ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] h))
      (LieAlgebra.IsKilling.killingForm_nondegenerate ℂ (ℂ ⊗[ℝ] h))
  let P := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let Q := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I)
  obtain ⟨hc, hP, hQ, ⟨d⟩, hne⟩ := compact_complement_complex_type_decomposition B h hproper e
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) P := hP
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) Q := hQ
  exact three_block_trace_skew_line (actualEndBlocks h B)
    (scalar_module_self_dual (K := ℂ) (L := ℂ ⊗[ℝ] h)) hsH
    (scalar_module_not_adjoint (K := ℂ) (L := ℂ ⊗[ℝ] h)) P Q hc d hne
    (endTraceForm (K := ℂ) (W := W)) end_trace_form_invariant
    end_trace_form_symmetric end_trace_form_nondegenerate

set_option maxHeartbeats 1200000 in
/-- A nonzero full cubic radical is impossible for the original
special-unitary compact pair, in every dimension. Tensor interchange
and the actual Hermitian adjoint supply the contradiction. -/
theorem all_rank_special_unitary_nonzero_cubic_radical_impossible
    (B : CompactForm (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) : False := by
  obtain ⟨D₀, hD₀, hsk, hline⟩ :=
    all_rank_special_unitary_end_trace_skew_line h B heff hproper e hradical
  exact complexified_defining_trace_skew_not_line (specialUnitaryDefiningRepresentation h)
    (fun x => x.val.property.1) D₀ hD₀ hsk hline

/-- The full mixed cubic radical of the actual canonical Hermitian half
vanishes for every original special-unitary compact pair of complex type. -/
theorem all_rank_special_unitary_cubic_radical_eq_bot
    (B : CompactForm (specialUnitaryAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊥ := by
  by_contra hradical
  exact all_rank_special_unitary_nonzero_cubic_radical_impossible h B heff hproper e hradical

end

end CubicAnomaly.Classification.UnitaryNoGo
