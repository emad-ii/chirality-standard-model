import CubicAnomaly.Fixed.MatterAnomaly

/-!
# A complete actual Standard Model and family anomaly endpoint

The already constructed twenty-seven-dimensional Standard Model module is
tensored with the actual defining `sl(3,ℂ)` family representation. Its full
cubic radical is exactly the Standard Model ideal; every mixed term with a
gauge insertion vanishes, while the family cubic has coefficient 27.

This theorem is downstream of the exceptional embedding. No assertion that
the constructed module is the restriction of an actual `E8` complement is
made or assumed here.
-/

namespace CubicAnomaly.Fixed.MatterFamilyAnomaly

open Matrix
open scoped Kronecker
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Fixed.TensorAnomaly
open CubicAnomaly.Fixed.FamilyAnomaly
open CubicAnomaly.Fixed.MatterBranching
open CubicAnomaly.Fixed.MatterSpectrum
open CubicAnomaly.Fixed.MatterLieAlgebra
open CubicAnomaly.Fixed.MatterAnomaly

noncomputable section

/-- The actual gauge and family Lie algebra acting on the constructed module. -/
abbrev GaugeFamilyAlgebra := ProductLie StandardModelAlgebra FamilyLie

/-- A genuine Lie representation on an eighty-one-dimensional space. -/
def coupledMatter81Representation :
    GaugeFamilyAlgebra →ₗ⁅ℂ⁆ Matrix (Fin 27 × Fin 3) (Fin 27 × Fin 3) ℂ :=
  familyTensorRepresentation matter27MatrixRepresentation

/-- The defining space of the constructed coupled representation has dimension 81. -/
theorem coupled_matter81_dimension :
    Module.finrank ℂ ((Fin 27 × Fin 3) → ℂ) = 81 := by
  simp

/-- The full cubic radical of the actual coupled module is precisely
the actual Standard Model ideal, with no anomaly assumptions left over. -/
theorem coupled_matter81_radical_eq_gauge_ideal :
    complexTraceRadical coupledMatter81Representation =
      (secondProjection : GaugeFamilyAlgebra →ₗ⁅ℂ⁆ FamilyLie).ker :=
  family_tensor_radical_eq_left_ideal matter27MatrixRepresentation
    matter27_matrix_trace matter27_standard_model_full_cubic

/-- Every linear trace vanishes on the actual coupled module. -/
theorem coupled_matter81_linear_trace (x : GaugeFamilyAlgebra) :
    trace (coupledMatter81Representation x) = 0 := by
  change trace (tensorAction (matter27MatrixRepresentation x.1)
    (familyRepresentation x.2)) = 0
  rw [tensor_action_trace, matter27_matrix_trace, family_representation_trace]
  ring

/-- All mixed cubic coefficients vanish and the sole surviving component
is the actual family cubic with coefficient exactly 27. -/
theorem coupled_matter81_full_cubic (x y z : GaugeFamilyAlgebra) :
    matrixTraceCubic (coupledMatter81Representation x)
      (coupledMatter81Representation y) (coupledMatter81Representation z) =
      27 * matrixTraceCubic (familyRepresentation x.2)
        (familyRepresentation y.2) (familyRepresentation z.2) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    family_tensor_full_cubic matter27MatrixRepresentation matter27_matrix_trace
      matter27_standard_model_full_cubic x y z

/-- An arbitrary gauge insertion kills the cubic, including mixed family
background insertions in either of the remaining two slots. -/
theorem coupled_matter81_gauge_insertion_zero
    (x : StandardModelAlgebra) (y z : GaugeFamilyAlgebra) :
    matrixTraceCubic (coupledMatter81Representation (x, 0))
      (coupledMatter81Representation y) (coupledMatter81Representation z) = 0 := by
  rw [coupled_matter81_full_cubic]
  simp [matrixTraceCubic]

/-- A concrete nonzero family anomaly remains in the complete constructed module. -/
theorem coupled_matter81_family_cubic_witness :
    matrixTraceCubic (coupledMatter81Representation (0, familyWitness))
      (coupledMatter81Representation (0, familyWitness))
      (coupledMatter81Representation (0, familyWitness)) = -162 :=
  family_tensor_27_cubic_witness matter27MatrixRepresentation

/-- The primitive hypercharge element is an actual nonzero gauge generator. -/
def gaugeHypercharge : StandardModelAlgebra :=
  standardModelGeneratorElement 0 0 1 (by simp) (by simp)

/-- Hypercharge is nonzero in the actual block matrix Lie subalgebra. -/
theorem gauge_hypercharge_ne_zero : gaugeHypercharge ≠ 0 := by
  intro h
  have hc := congrArg (fun x : StandardModelAlgebra => x.val (Sum.inl 0) (Sum.inl 0)) h
  norm_num [gaugeHypercharge, standardModelGeneratorElement, standardModelGenerator] at hc

/-- The radical just computed is nonzero, witnessed by actual hypercharge. -/
theorem coupled_matter81_radical_ne_bot :
    complexTraceRadical coupledMatter81Representation ≠ ⊥ := by
  intro h
  have hx : (gaugeHypercharge, (0 : FamilyLie)) ∈
      complexTraceRadical coupledMatter81Representation := by
    rw [coupled_matter81_radical_eq_gauge_ideal]
    rfl
  rw [h] at hx
  change ((gaugeHypercharge, (0 : FamilyLie)) : GaugeFamilyAlgebra) = 0 at hx
  exact gauge_hypercharge_ne_zero (congrArg (fun x : GaugeFamilyAlgebra => x.1) hx)

/-- Actual coordinates identify the original three copies of the constructed
twenty-seven with the defining space of the coupled representation. -/
def coupledMatterCoordinates : Matter81 ≃ₗ[ℂ] ((Fin 27 × Fin 3) → ℂ) where
  toFun v p := matter27Coordinates (v p.2) p.1
  invFun w j := matter27Coordinates.symm (fun i => w (i, j))
  left_inv v := by
    funext j
    exact matter27Coordinates.symm_apply_apply (v j)
  right_inv w := by
    funext p
    exact congrFun (matter27Coordinates.apply_symm_apply (fun i => w (i, p.2))) p.1
  map_add' v w := by ext p; simp
  map_smul' c v := by ext p; simp

/-- Restriction of the actual coupled action to the gauge ideal is exactly
the already constructed action on three identical copies of Matter27. -/
theorem coupled_matter81_gauge_action (x : StandardModelAlgebra) (v : Matter81) :
    coupledMatterCoordinates ⁅x, v⁆ =
      coupledMatter81Representation (x, 0) *ᵥ coupledMatterCoordinates v := by
  have ha (j : Fin 3) : matter27Coordinates ⁅x, v j⁆ =
      matter27MatrixRepresentation x *ᵥ matter27Coordinates (v j) := by
    have hh := congrArg (fun f : Module.End ℂ (Fin 27 → ℂ) =>
      f (matter27Coordinates (v j))) (matter27_matrix_operator x)
    simpa [LinearEquiv.conj_apply] using hh.symm
  ext p
  rcases p with ⟨i, j⟩
  change matter27Coordinates ⁅x, v j⁆ i = _
  rw [ha]
  change (matter27MatrixRepresentation x *ᵥ matter27Coordinates (v j)) i =
    (tensorAction (matter27MatrixRepresentation x) (familyRepresentation 0) *ᵥ
      coupledMatterCoordinates v) (i, j)
  simp [tensorAction, coupledMatterCoordinates, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap, Matrix.one_apply, Fintype.sum_prod_type]

end

end CubicAnomaly.Fixed.MatterFamilyAnomaly
