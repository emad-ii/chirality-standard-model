import CubicAnomaly.Fixed.MatrixCompactForm
import CubicAnomaly.Fixed.E8Adjoints

/-!
# An actual compact real form of the fixed exceptional matrix algebra

The proved positive Hermitian matrix equips the actual defining coordinates
with an inner product. The literal raising/lowering and Cartan identities
then prove adjoint closure of the entire generated Lie algebra. Its real
skew part has an actual positive invariant trace form, and its actual tensor
complexification is Lie-isomorphic to the original Geck matrix algebra.

No Lie dimension, classification, compactness, or decomposition witness is
assumed. Integration to a compact Lie group is not asserted here.
-/

namespace CubicAnomaly.Fixed.E8Compact

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Fixed.E8RootPairing
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8Metric
open CubicAnomaly.Fixed.E8Adjoints
open RootPairing.GeckConstruction
open scoped TensorProduct ComplexOrder

noncomputable section

/-- The actual defining coordinate space with the proved positive metric. -/
abbrev DefiningSpace := MatrixCompactForm.MetricSpace gramMatrix gramMatrix_posDef

/-- Actual matrices and their actual operators in the positively metrized space. -/
def operatorEquiv : Matrix Index Index ℂ ≃ₐ[ℂ] Module.End ℂ DefiningSpace :=
  MatrixCompactForm.matrixOperatorEquiv gramMatrix gramMatrix_posDef

/-- The image of the original generated matrix algebra under the actual action. -/
def operatorAlgebra : LieSubalgebra ℂ (Module.End ℂ DefiningSpace) :=
  E8Geck.lieAlgebra.map operatorEquiv.toLieEquiv.toLieHom

private theorem operator_mem (A : Matrix Index Index ℂ) (hA : A ∈ E8Geck.lieAlgebra) :
    operatorEquiv A ∈ operatorAlgebra := ⟨A, hA, rfl⟩

private theorem raising_adjoint (i : base.support) :
    (operatorEquiv (e i)).adjoint = operatorEquiv (f i) :=
  MatrixCompactForm.metric_matrix_adjoint _ _ _ _ (geck_raising_weighted_adjoint i)

private theorem lowering_adjoint (i : base.support) :
    (operatorEquiv (f i)).adjoint = operatorEquiv (e i) :=
  MatrixCompactForm.metric_matrix_adjoint _ _ _ _ (geck_lowering_weighted_adjoint i)

private theorem cartan_adjoint (i : base.support) :
    (operatorEquiv (h i)).adjoint = operatorEquiv (h i) :=
  MatrixCompactForm.metric_matrix_adjoint _ _ _ _ (geck_cartan_weighted_adjoint i)

/-- Every actual operator in the generated exceptional algebra has its
Hermitian adjoint in the same algebra. -/
theorem e8_operator_adjoint_closed (A : Module.End ℂ DefiningSpace)
    (hA : A ∈ operatorAlgebra) : A.adjoint ∈ operatorAlgebra := by
  obtain ⟨X, hX, rfl⟩ := hA
  change (operatorEquiv X).adjoint ∈ operatorAlgebra
  change X ∈ RootPairing.GeckConstruction.lieAlgebra base at hX
  induction hX using LieSubalgebra.lieSpan_induction with
  | mem u hu =>
    obtain (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩) :
        (∃ j, h j = u) ∨ (∃ j, e j = u) ∨ (∃ j, f j = u) := by
      simpa only [Set.mem_union, Set.mem_range, or_assoc] using hu
    · rw [cartan_adjoint]
      exact operator_mem _ (cartan_generator_mem i)
    · rw [raising_adjoint]
      exact operator_mem _ (lowering_generator_mem i)
    · rw [lowering_adjoint]
      exact operator_mem _ (raising_generator_mem i)
  | zero => simp
  | add u v _ _ hu hv => simpa only [map_add] using operatorAlgebra.add_mem hu hv
  | smul t u _ hu =>
    simpa only [map_smul, map_smulₛₗ] using operatorAlgebra.smul_mem (starRingEnd ℂ t) hu
  | lie u v _ _ hu hv =>
    have hh : (operatorEquiv ⁅u, v⁆).adjoint =
        -⁅(operatorEquiv u).adjoint, (operatorEquiv v).adjoint⁆ := by
      rw [show operatorEquiv ⁅u, v⁆ = ⁅operatorEquiv u, operatorEquiv v⁆
        from operatorEquiv.toLieEquiv.map_lie u v]
      change ((operatorEquiv u).comp (operatorEquiv v) -
        (operatorEquiv v).comp (operatorEquiv u)).adjoint =
        -((operatorEquiv u).adjoint.comp (operatorEquiv v).adjoint -
          (operatorEquiv v).adjoint.comp (operatorEquiv u).adjoint)
      rw [map_sub, LinearMap.adjoint_comp, LinearMap.adjoint_comp]
      abel
    rw [hh]
    exact operatorAlgebra.neg_mem (operatorAlgebra.lie_mem hu hv)

/-- The actual real compact algebra, as the skew-adjoint part of the
constructed exceptional operator algebra. -/
def compactRealAlgebra := MatrixCompactForm.realForm operatorAlgebra

instance : LieRing compactRealAlgebra := inferInstanceAs (LieRing (MatrixCompactForm.realForm operatorAlgebra))
instance : LieAlgebra ℝ compactRealAlgebra := inferInstanceAs (LieAlgebra ℝ (MatrixCompactForm.realForm operatorAlgebra))

/-- A positive symmetric ad-invariant real form on the actual compact algebra. -/
def compactForm : CompactForm compactRealAlgebra :=
  MatrixCompactForm.compactForm operatorAlgebra

theorem e8_compact_real_finiteDimensional : FiniteDimensional ℝ compactRealAlgebra :=
  inferInstanceAs (FiniteDimensional ℝ (MatrixCompactForm.realForm operatorAlgebra))

/-- The exact operator identification retains the original matrix Lie algebra. -/
def operatorAlgebraEquiv : E8Geck.lieAlgebra ≃ₗ⁅ℂ⁆ operatorAlgebra :=
  operatorEquiv.toLieEquiv.ofSubalgebras _ _ rfl

/-- The actual tensor complexification of the constructed compact real algebra
is the original fixed exceptional matrix Lie algebra. -/
def complexificationEquiv :
    (ℂ ⊗[ℝ] compactRealAlgebra) ≃ₗ⁅ℂ⁆ E8Geck.lieAlgebra :=
  (MatrixCompactForm.complexificationEquiv operatorAlgebra e8_operator_adjoint_closed).trans
    operatorAlgebraEquiv.symm

theorem e8_compact_form_trace (x y : compactRealAlgebra) :
    compactForm.form x y = -(LinearMap.trace ℂ DefiningSpace (x.val * y.val)).re := rfl

theorem e8_compact_complexification_tmul (a : ℂ) (x : compactRealAlgebra) :
    (complexificationEquiv (a ⊗ₜ[ℝ] x)).val = operatorEquiv.symm (a • x.val) := rfl

end

end CubicAnomaly.Fixed.E8Compact
