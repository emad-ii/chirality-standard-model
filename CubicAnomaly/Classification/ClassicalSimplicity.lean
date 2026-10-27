import CubicAnomaly.Classification.ClassicalTwoFactorReduction
import CubicAnomaly.Classification.ClassicalTensorPackageExclusion

/-!
# All-rank orthogonal and symplectic isotropy simplicity

The original compact-pair hypotheses construct the actual two-factor
representation and form package whenever isotropy is not already simple.
The tensor quotient and symmetric-pair derivation argument excludes that
package. Consequently isotropy is simple over both the reals and its
actual complexification, in every dimension. The nonzero full cubic
radical is therefore the whole isotropy and every mixed cubic trace
vanishes.

No highest-weight constituent theorem, low-dimensional classification,
or real-to-complex maximality implication is assumed.
-/

namespace CubicAnomaly.Classification.ClassicalSimplicity

open LieAlgebra LieModule
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.ComplexDefining
open CubicAnomaly.Classification.OrthogonalDefining
open CubicAnomaly.Classification.SymplecticGeometry
open CubicAnomaly.Classification.SymplecticDefining
open CubicAnomaly.Classification.ClassicalTwoFactorReduction
open CubicAnomaly.Classification.ClassicalTensorPackageExclusion
open CubicAnomaly.Classification.CompactOperatorModel
open CubicAnomaly.Classification.SimpleIdealStructure
open scoped TensorProduct

section Orthogonal

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

set_option maxHeartbeats 1000000 in
/-- The original orthogonal hypotheses force actual complexified
isotropy simplicity in every dimension. -/
theorem all_rank_orthogonal_complexified_isotropy_simple
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h) := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  rcases all_rank_orthogonal_isotropy_simple_or_actual_tensor_forms B h heff hproper e hradical
      with hsimple | ⟨I, J, hIJ, htop, hI, hJ, U, _, hForms⟩
  · exact hsimple
  · exact (actual_two_ideal_tensor_forms_impossible B hproper e (orthogonalModel h)
      I J hI hJ hIJ htop U hForms).elim

/-- Actual complexified orthogonal isotropy simplicity descends to the
original real isotropy algebra. -/
theorem all_rank_orthogonal_isotropy_simple
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieAlgebra.IsSimple ℝ h := by
  letI := all_rank_orthogonal_complexified_isotropy_simple B h heff hproper e hradical
  exact simple_of_complexification_simple

/-- The nonzero full cubic radical is all of the actual orthogonal
isotropy, with every mixed first-slot direction included. -/
theorem all_rank_orthogonal_cubic_radical_eq_top
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊤ := by
  letI := all_rank_orthogonal_isotropy_simple B h heff hproper e hradical
  exact (LieAlgebra.IsSimple.eq_bot_or_eq_top _).resolve_left hradical

/-- Every mixed cubic trace of the canonical Hermitian half vanishes
under the original orthogonal compact-pair hypotheses. -/
theorem all_rank_orthogonal_cubic_trace_zero
    (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (x y z : h) :
    CubicAnomaly.Classification.CubicRadical.matrixTraceCubic
      ((hermitianHalfOfCommutant B h e).generators x)
      ((hermitianHalfOfCommutant B h e).generators y)
      ((hermitianHalfOfCommutant B h e).generators z) = 0 := by
  have hx : x ∈ (hermitianHalfOfCommutant B h e).cubicRadical := by
    rw [all_rank_orthogonal_cubic_radical_eq_top B h heff hproper e hradical]
    trivial
  exact (CubicAnomaly.Classification.AllRank.hermitian_half_cubic_radical_membership _ x).mp
    hx y z

end Orthogonal

section Symplectic

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

set_option maxHeartbeats 1000000 in
/-- The original quaternionic symplectic hypotheses force actual
complexified isotropy simplicity in every dimension. -/
theorem all_rank_symplectic_complexified_isotropy_simple
    (Q : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra Q))
    (h : LieSubalgebra ℝ (symplecticAlgebra Q))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h) := by
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation Q h)
  letI := complexified_defining_lieModule (symplecticDefiningRepresentation Q h)
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  rcases all_rank_symplectic_isotropy_simple_or_actual_tensor_forms Q B h heff hproper e hradical
      with hsimple | ⟨I, J, hIJ, htop, hI, hJ, U, _, hForms⟩
  · exact hsimple
  · exact (actual_two_ideal_tensor_forms_impossible B hproper e (symplecticModel Q h)
      I J hI hJ hIJ htop U hForms).elim

/-- Simplicity of actual complexified symplectic isotropy descends to
the original real isotropy algebra. -/
theorem all_rank_symplectic_isotropy_simple
    (Q : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra Q))
    (h : LieSubalgebra ℝ (symplecticAlgebra Q))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieAlgebra.IsSimple ℝ h := by
  letI := all_rank_symplectic_complexified_isotropy_simple Q B h heff hproper e hradical
  exact simple_of_complexification_simple

/-- The nonzero full cubic radical is the entire actual symplectic
isotropy algebra. -/
theorem all_rank_symplectic_cubic_radical_eq_top
    (Q : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra Q))
    (h : LieSubalgebra ℝ (symplecticAlgebra Q))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊤ := by
  letI := all_rank_symplectic_isotropy_simple Q B h heff hproper e hradical
  exact (LieAlgebra.IsSimple.eq_bot_or_eq_top _).resolve_left hradical

/-- Every mixed cubic trace of the canonical Hermitian half vanishes
under the original symplectic compact-pair hypotheses. -/
theorem all_rank_symplectic_cubic_trace_zero
    (Q : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra Q))
    (h : LieSubalgebra ℝ (symplecticAlgebra Q))
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (x y z : h) :
    CubicAnomaly.Classification.CubicRadical.matrixTraceCubic
      ((hermitianHalfOfCommutant B h e).generators x)
      ((hermitianHalfOfCommutant B h e).generators y)
      ((hermitianHalfOfCommutant B h e).generators z) = 0 := by
  have hx : x ∈ (hermitianHalfOfCommutant B h e).cubicRadical := by
    rw [all_rank_symplectic_cubic_radical_eq_top Q B h heff hproper e hradical]
    trivial
  exact (CubicAnomaly.Classification.AllRank.hermitian_half_cubic_radical_membership _ x).mp
    hx y z

end Symplectic

end CubicAnomaly.Classification.ClassicalSimplicity
