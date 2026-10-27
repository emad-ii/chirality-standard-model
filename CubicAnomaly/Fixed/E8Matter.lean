import CubicAnomaly.Fixed.E8MatterMatching
import CubicAnomaly.Fixed.MatterNonSelfDual

/-!
# The actual exceptional matter representation and its anomaly

The degree-one subspace of the actual exceptional adjoint algebra is
restricted along the proved Standard Model and family embedding. Its
explicit signed coordinates identify that inherited action with the
previously constructed coupled matter representation. The full cubic and
its radical therefore apply to this actual exceptional subspace. After
restriction to the Standard Model algebra, the same explicit equivalence
transfers the three-family splitting and the obstruction to self-duality.
-/

namespace CubicAnomaly.Fixed.E8Matter

open Matrix
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8ClassicalEmbedding
open CubicAnomaly.Fixed.E8MatterMatching
open CubicAnomaly.Fixed.MatterSpectrum
open CubicAnomaly.Fixed.MatterLieAlgebra
open CubicAnomaly.Fixed.MatterChirality
open CubicAnomaly.Fixed.MatterNonSelfDual
open CubicAnomaly.Fixed.MatterFamilyAnomaly
open CubicAnomaly.Fixed.FamilyAnomaly
open CubicAnomaly.Fixed.TensorAnomaly

noncomputable section

/-- The actual Standard Model inclusion in the degree-zero exceptional algebra. -/
def actualGaugeZeroEmbedding : StandardModelAlgebra →ₗ⁅ℂ⁆ zeroSubalgebra :=
  E8A4.sl5ZeroEmbedding.comp gaugeSl5Embedding

instance actualMatterSMLieRingModule : LieRingModule StandardModelAlgebra ActualMatter :=
  LieRingModule.compLieHom ActualMatter actualGaugeZeroEmbedding

instance actualMatterSMLieModule : LieModule ℂ StandardModelAlgebra ActualMatter :=
  LieModule.compLieHom ActualMatter actualGaugeZeroEmbedding

theorem e8_actual_matter_sm_action (x : StandardModelAlgebra) (w : ActualMatter) :
    ⁅x, w⁆ = ⁅actualGaugeZeroEmbedding x, w⁆ := rfl

/-- The signed matter matching is equivariant for the actual Standard Model action. -/
def actualMatterSMEquiv : Matter81 ≃ₗ⁅ℂ,StandardModelAlgebra⁆ ActualMatter where
  __ := actualMatterEquiv
  map_lie' := by
    intro x v
    apply Subtype.ext
    exact (e8_matter_gauge_action x v).symm

/-- The actual exceptional matter half splits equivariantly into its families and extras. -/
def actualMatterSMSplit :
    ActualMatter ≃ₗ⁅ℂ,StandardModelAlgebra⁆ (Fin 3 → Family) × (Fin 3 → Extras) :=
  actualMatterSMEquiv.symm.trans matter81SMSplit

/-- The self-dual thirty-six-dimensional remainder is asserted after Standard Model restriction. -/
theorem e8_actual_matter_sm_three_families_self_dual_remainder :
    Nonempty (ActualMatter ≃ₗ⁅ℂ,StandardModelAlgebra⁆
      (Fin 3 → Family) × (Fin 3 → Extras)) ∧
      Nonempty ((Fin 3 → Extras) ≃ₗ⁅ℂ,StandardModelAlgebra⁆
        Module.Dual ℂ (Fin 3 → Extras)) ∧
      Module.finrank ℂ (Fin 3 → Family) = 45 ∧
      Module.finrank ℂ (Fin 3 → Extras) = 36 :=
  ⟨⟨actualMatterSMSplit⟩, ⟨extraCopiesSMSelfDual⟩,
    three_families_finrank, extra_copies_finrank⟩

private def actualMatterSMDualEquiv :
    Module.Dual ℂ ActualMatter ≃ₗ⁅ℂ,StandardModelAlgebra⁆ Module.Dual ℂ Matter81 where
  __ := actualMatterSMEquiv.toLinearEquiv.dualMap
  map_lie' := by
    intro x f
    apply LinearMap.ext
    intro v
    change -f ⁅x, actualMatterSMEquiv v⁆ = -f (actualMatterSMEquiv ⁅x, v⁆)
    have h : actualMatterSMEquiv ⁅x, v⁆ = ⁅x, actualMatterSMEquiv v⁆ :=
      actualMatterSMEquiv.map_lie x v
    exact (congrArg (fun w : ActualMatter => -f w) h).symm

/-- The actual exceptional half has no Standard Model equivariant self-duality. -/
theorem e8_actual_matter_not_self_dual :
    ¬ Nonempty (ActualMatter ≃ₗ⁅ℂ,StandardModelAlgebra⁆ Module.Dual ℂ ActualMatter) := by
  rintro ⟨e⟩
  exact matter81_not_self_dual
    ⟨actualMatterSMEquiv.trans (e.trans actualMatterSMDualEquiv)⟩

/-- The actual homogeneous adjoint space inherits the embedded gauge/family action. -/
instance actualMatterLieRingModule : LieRingModule GaugeFamilyAlgebra ActualMatter :=
  LieRingModule.compLieHom ActualMatter gaugeFamilyZeroEmbedding

instance actualMatterLieModule : LieModule ℂ GaugeFamilyAlgebra ActualMatter :=
  LieModule.compLieHom ActualMatter gaugeFamilyZeroEmbedding

theorem e8_actual_matter_action (x : GaugeFamilyAlgebra) (w : ActualMatter) :
    ⁅x, w⁆ = ⁅gaugeFamilyZeroEmbedding x, w⁆ := rfl

/-- The actual 81-dimensional adjoint component has explicit coupled-matter coordinates. -/
def actualCoordinates : ActualMatter ≃ₗ[ℂ] ((Fin 27 × Fin 3) → ℂ) :=
  actualMatterEquiv.symm.trans coupledMatterCoordinates

/-- The inherited adjoint action, pulled back through the proved embedding. -/
def actualRepresentation : GaugeFamilyAlgebra →ₗ⁅ℂ⁆ Module.End ℂ ActualMatter :=
  (LieModule.toEnd ℂ zeroSubalgebra ActualMatter).comp gaugeFamilyZeroEmbedding

/-- The matrix representation is built from the actual adjoint action and actual coordinates. -/
def actualMatrixRepresentation :
    GaugeFamilyAlgebra →ₗ⁅ℂ⁆ Matrix (Fin 27 × Fin 3) (Fin 27 × Fin 3) ℂ :=
  lieEquivMatrix'.toLieHom.comp
    (actualCoordinates.lieConj.toLieHom.comp actualRepresentation)

theorem e8_actual_matter_finrank : Module.finrank ℂ ActualMatter = 81 :=
  e8_complementary_module_dimensions.1

theorem e8_actual_coordinates_action (x : GaugeFamilyAlgebra) (w : ActualMatter) :
    actualCoordinates (actualRepresentation x w) =
      coupledMatter81Representation x *ᵥ actualCoordinates w :=
  e8_actual_matter_coordinates_action x w

private theorem actual_matrix_operator (x : GaugeFamilyAlgebra) :
    (actualMatrixRepresentation x).toLin' =
      actualCoordinates.conj (actualRepresentation x) := by
  simp [actualMatrixRepresentation, LinearEquiv.lieConj_apply]

/-- Exact representation equality matches the exceptional construction to the anomaly module. -/
theorem e8_actual_matrix_representation_eq :
    actualMatrixRepresentation = coupledMatter81Representation := by
  apply DFunLike.ext
  intro x
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [actual_matrix_operator]
  change actualCoordinates (actualRepresentation x (actualCoordinates.symm v)) =
    coupledMatter81Representation x *ᵥ v
  rw [e8_actual_coordinates_action, actualCoordinates.apply_symm_apply]

/-- The full cubic radical of the actual matter action restricted to the embedded
gauge-plus-family algebra is the Standard Model ideal. -/
theorem e8_actual_matter_radical_eq_gauge_ideal :
    complexTraceRadical actualMatrixRepresentation =
      (secondProjection : GaugeFamilyAlgebra →ₗ⁅ℂ⁆ FamilyLie).ker := by
  rw [e8_actual_matrix_representation_eq]
  exact coupled_matter81_radical_eq_gauge_ideal

theorem e8_actual_matter_linear_trace (x : GaugeFamilyAlgebra) :
    Matrix.trace (actualMatrixRepresentation x) = 0 := by
  rw [e8_actual_matrix_representation_eq]
  exact coupled_matter81_linear_trace x

/-- Every mixed term is included in this exact full symmetric cubic identity. -/
theorem e8_actual_matter_full_cubic (x y z : GaugeFamilyAlgebra) :
    matrixTraceCubic (actualMatrixRepresentation x)
      (actualMatrixRepresentation y) (actualMatrixRepresentation z) =
      27 * matrixTraceCubic (familyRepresentation x.2)
        (familyRepresentation y.2) (familyRepresentation z.2) := by
  rw [e8_actual_matrix_representation_eq]
  exact coupled_matter81_full_cubic x y z

theorem e8_actual_matter_gauge_insertion_zero
    (x : StandardModelAlgebra) (y z : GaugeFamilyAlgebra) :
    matrixTraceCubic (actualMatrixRepresentation (x, 0))
      (actualMatrixRepresentation y) (actualMatrixRepresentation z) = 0 := by
  rw [e8_actual_matrix_representation_eq]
  exact coupled_matter81_gauge_insertion_zero x y z

/-- The family anomaly is nonzero on a displayed element of the actual embedded family algebra. -/
theorem e8_actual_matter_family_cubic_witness :
    matrixTraceCubic (actualMatrixRepresentation (0, familyWitness))
      (actualMatrixRepresentation (0, familyWitness))
      (actualMatrixRepresentation (0, familyWitness)) = -162 := by
  rw [e8_actual_matrix_representation_eq]
  exact coupled_matter81_family_cubic_witness

theorem e8_actual_matter_radical_ne_bot :
    complexTraceRadical actualMatrixRepresentation ≠ ⊥ := by
  rw [e8_actual_matrix_representation_eq]
  exact coupled_matter81_radical_ne_bot

end

end CubicAnomaly.Fixed.E8Matter
