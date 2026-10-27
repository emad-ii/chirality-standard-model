import CubicAnomaly.Fixed.StandardModelGroup
import CubicAnomaly.Fixed.MatterSpectrum

/-!
# Actual group actions on the constructed matter spaces

The determinant-one unitary block group acts on the same defining five,
alternating ten, dual five, and product/copy spaces used by the Lie-module
construction. The alternating action is literally `X ↦ g X gᵀ`; the dual
action is precomposition with the inverse defining action. These are
homomorphisms into linear automorphism groups, so the covering kernel acts
trivially on the actual eighty-one-dimensional space.

This module does not assert a differentiation theorem or identify the
constructed matter spaces with an exceptional adjoint complement.
-/

namespace CubicAnomaly.Fixed.MatterGroupAction

open Matrix
open CubicAnomaly.Fixed.MatterAlternating
open CubicAnomaly.Fixed.MatterBranching
open CubicAnomaly.Fixed.MatterDual
open CubicAnomaly.Fixed.MatterSpectrum

noncomputable section

section UnitaryActions

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Congruence by an arbitrary matrix preserves alternating tensors. -/
def alternatingCongruence (A : Matrix n n ℂ) :
    AlternatingTensor n →ₗ[ℂ] AlternatingTensor n where
  toFun X := ⟨A * X.val * Aᵀ, by
    change (A * X.val * Aᵀ)ᵀ = -(A * X.val * Aᵀ)
    have hX : X.valᵀ = -X.val := X.property
    rw [transpose_mul, transpose_mul, transpose_transpose, hX]
    simp [mul_assoc]⟩
  map_add' X Y := by
    apply Subtype.ext
    simp [mul_add, add_mul]
  map_smul' c X := by
    apply Subtype.ext
    simp

private theorem alternating_congruence_one (X : AlternatingTensor n) :
    alternatingCongruence n 1 X = X := by
  apply Subtype.ext
  simp [alternatingCongruence]

private theorem alternating_congruence_mul (A B : Matrix n n ℂ)
    (X : AlternatingTensor n) :
    alternatingCongruence n (A * B) X =
      alternatingCongruence n A (alternatingCongruence n B X) := by
  apply Subtype.ext
  simp [alternatingCongruence, transpose_mul, mul_assoc]

/-- The actual alternating representation of the unitary matrix group. -/
def alternatingUnitaryEquiv (A : Matrix.unitaryGroup n ℂ) :
    AlternatingTensor n ≃ₗ[ℂ] AlternatingTensor n :=
  { alternatingCongruence n A.val with
    invFun := alternatingCongruence n (A⁻¹).val
    left_inv := by
      intro X
      change alternatingCongruence n (A⁻¹).val (alternatingCongruence n A.val X) = X
      rw [← alternating_congruence_mul]
      have h : (A⁻¹).val * A.val = 1 := A.prop.1
      rw [h, alternating_congruence_one]
    right_inv := by
      intro X
      change alternatingCongruence n A.val (alternatingCongruence n (A⁻¹).val X) = X
      rw [← alternating_congruence_mul]
      have h : A.val * (A⁻¹).val = 1 := A.prop.2
      rw [h, alternating_congruence_one] }

/-- The alternating group action is literal matrix congruence. -/
theorem alternating_unitary_group_action_val (A : Matrix.unitaryGroup n ℂ)
    (X : AlternatingTensor n) :
    (alternatingUnitaryEquiv n A X).val = A.val * X.val * A.valᵀ := rfl

/-- Multiplication in the matrix group gives composition of tensor actions. -/
def alternatingUnitaryRepresentation : Matrix.unitaryGroup n ℂ →*
    (AlternatingTensor n ≃ₗ[ℂ] AlternatingTensor n) where
  toFun := alternatingUnitaryEquiv n
  map_one' := by
    apply LinearEquiv.ext
    intro X
    exact alternating_congruence_one n X
  map_mul' A B := by
    apply LinearEquiv.ext
    intro X
    exact alternating_congruence_mul n A.val B.val X

/-- The actual defining representation of the unitary matrix group. -/
def definingUnitaryRepresentation : Matrix.unitaryGroup n ℂ →*
    ((n → ℂ) ≃ₗ[ℂ] (n → ℂ)) where
  toFun := Matrix.UnitaryGroup.toLinearEquiv
  map_one' := by ext v i; simp [Matrix.UnitaryGroup.toLinearEquiv]
  map_mul' A B := by
    ext v i
    change ((A.val * B.val) *ᵥ v) i = (A.val *ᵥ (B.val *ᵥ v)) i
    rw [Matrix.mulVec_mulVec]

end UnitaryActions

section RepresentationOperations

variable {G M N : Type*} [Group G] [AddCommGroup M] [Module ℂ M]
  [AddCommGroup N] [Module ℂ N]

/-- Contragredient action, constructed by inverse precomposition. -/
def dualGroupRepresentation (ρ : G →* (M ≃ₗ[ℂ] M)) :
    G →* (Module.Dual ℂ M ≃ₗ[ℂ] Module.Dual ℂ M) where
  toFun g := (ρ g⁻¹).dualMap
  map_one' := by
    ext f v
    simp [LinearEquiv.dualMap_apply]
  map_mul' g h := by
    ext f v
    simp [LinearEquiv.dualMap_apply, _root_.mul_inv_rev]

/-- Actual direct-sum action, represented on a product of vector spaces. -/
def productGroupRepresentation (ρ : G →* (M ≃ₗ[ℂ] M))
    (σ : G →* (N ≃ₗ[ℂ] N)) : G →* ((M × N) ≃ₗ[ℂ] (M × N)) where
  toFun g := LinearEquiv.prodCongr (ρ g) (σ g)
  map_one' := by ext v <;> simp
  map_mul' g h := by ext v <;> simp

/-- A group acts separately on every copy of an actual module. -/
def copiesGroupRepresentation (ι : Type*) (ρ : G →* (M ≃ₗ[ℂ] M)) :
    G →* ((ι → M) ≃ₗ[ℂ] (ι → M)) where
  toFun g := LinearEquiv.piCongrRight fun _ : ι => ρ g
  map_one' := by ext v i; simp
  map_mul' g h := by ext v i; simp

end RepresentationOperations

/-- The proved special-unitary block embedding, with determinant forgotten. -/
def gaugeUnitary : StandardModelGroup.GaugeGroup →*
    Matrix.unitaryGroup MatterBranching.FiveIndex ℂ where
  toFun g := ⟨(StandardModelGroup.blockEmbedding g).val, (StandardModelGroup.blockEmbedding g).prop.1⟩
  map_one' := by
    apply Subtype.ext
    change (StandardModelGroup.blockEmbedding 1).val = 1
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    change (StandardModelGroup.blockEmbedding (g * h)).val =
      (StandardModelGroup.blockEmbedding g).val * (StandardModelGroup.blockEmbedding h).val
    rw [map_mul]
    rfl

/-- The actual group action on the same defining five as the Lie module. -/
def fiveGroupRepresentation : StandardModelGroup.GaugeGroup →* (Five ≃ₗ[ℂ] Five) :=
  (definingUnitaryRepresentation MatterBranching.FiveIndex).comp gaugeUnitary

/-- The actual group action on the same alternating ten as the Lie module. -/
def tenGroupRepresentation : StandardModelGroup.GaugeGroup →* (Ten ≃ₗ[ℂ] Ten) :=
  (alternatingUnitaryRepresentation MatterBranching.FiveIndex).comp gaugeUnitary

/-- The actual dual group action on the same antifundamental five. -/
def antiFiveGroupRepresentation : StandardModelGroup.GaugeGroup →* (AntiFive ≃ₗ[ℂ] AntiFive) :=
  dualGroupRepresentation fiveGroupRepresentation

/-- The actual fifteen-dimensional group representation. -/
def familyGroupRepresentation : StandardModelGroup.GaugeGroup →* (Family ≃ₗ[ℂ] Family) :=
  productGroupRepresentation tenGroupRepresentation antiFiveGroupRepresentation

/-- The actual defining/dual group representation. -/
def vectorlikeGroupRepresentation :
    StandardModelGroup.GaugeGroup →* (VectorlikePair ≃ₗ[ℂ] VectorlikePair) :=
  productGroupRepresentation fiveGroupRepresentation antiFiveGroupRepresentation

/-- The actual two-dimensional trivial group representation. -/
def singletsGroupRepresentation : StandardModelGroup.GaugeGroup →* (TwoSinglets ≃ₗ[ℂ] TwoSinglets) := 1

/-- An actual group representation on the constructed twenty-seven. -/
def matter27GroupRepresentation : StandardModelGroup.GaugeGroup →* (Matter27 ≃ₗ[ℂ] Matter27) :=
  productGroupRepresentation familyGroupRepresentation
    (productGroupRepresentation vectorlikeGroupRepresentation singletsGroupRepresentation)

/-- An actual group representation on the constructed eighty-one. -/
def matter81GroupRepresentation : StandardModelGroup.GaugeGroup →* (Matter81 ≃ₗ[ℂ] Matter81) :=
  copiesGroupRepresentation (Fin 3) matter27GroupRepresentation

/-- The defining action uses the actual faithful block embedding. -/
theorem five_gauge_group_action (g : StandardModelGroup.GaugeGroup) (v : Five) :
    fiveGroupRepresentation g v = (StandardModelGroup.blockEmbedding g).val *ᵥ v := rfl

/-- The alternating action uses the same actual faithful block embedding. -/
theorem ten_gauge_group_action (g : StandardModelGroup.GaugeGroup) (X : Ten) :
    (tenGroupRepresentation g X).val =
      (StandardModelGroup.blockEmbedding g).val * X.val * (StandardModelGroup.blockEmbedding g).valᵀ := rfl

/-- The dual group action is inverse precomposition on actual functionals. -/
theorem antifive_gauge_group_action (g : StandardModelGroup.GaugeGroup) (f : AntiFive) (v : Five) :
    antiFiveGroupRepresentation g f v = f ((StandardModelGroup.blockEmbedding g⁻¹).val *ᵥ v) := rfl

/-- The twenty-seven group action has precisely the constructed matter summands. -/
theorem matter27_gauge_group_action (g : StandardModelGroup.GaugeGroup) (v : Matter27) :
    matter27GroupRepresentation g v =
      ((tenGroupRepresentation g v.1.1, antiFiveGroupRepresentation g v.1.2),
        (fiveGroupRepresentation g v.2.1.1, antiFiveGroupRepresentation g v.2.1.2),
        v.2.2) := rfl

/-- The eighty-one group action preserves the three constructed copies. -/
theorem matter81_gauge_group_action (g : StandardModelGroup.GaugeGroup) (v : Matter81) (i : Fin 3) :
    matter81GroupRepresentation g v i = matter27GroupRepresentation g (v i) := rfl

/-- The primitive circle has integer charges `-2` and `3` on the defining blocks. -/
def fundamentalCircleCharge : MatterBranching.FiveIndex → ℤ :=
  Sum.elim (fun _ => -2) (fun _ => 3)

private theorem circle_gauge_diagonal (z : StandardModelGroup.Phase) :
    (StandardModelGroup.blockEmbedding (StandardModelGroup.centralCircle z)).val =
      Matrix.diagonal (fun i => ((z ^ fundamentalCircleCharge i :
        StandardModelGroup.Phase) : ℂ)) := by
  change (StandardModelGroup.blockEmbedding (StandardModelGroup.cover ((1, 1), z))).val = _
  rw [StandardModelGroup.standard_model_circle_blocks]
  ext (i | i) (j | j) <;>
    simp [fundamentalCircleCharge, Matrix.diagonal, Matrix.one_apply]

/-- The actual circle action on the defining five has the proved integer powers. -/
theorem five_circle_group_action (z : StandardModelGroup.Phase) (v : Five)
    (i : MatterBranching.FiveIndex) :
    fiveGroupRepresentation (StandardModelGroup.centralCircle z) v i =
      ((z ^ fundamentalCircleCharge i : StandardModelGroup.Phase) : ℂ) * v i := by
  rw [five_gauge_group_action, circle_gauge_diagonal]
  exact Matrix.mulVec_diagonal _ _ _

/-- Alternating tensor entries carry the sum of their two defining charges.
These are `-4`, `1`, and `6` on the colour-colour, mixed, and weak-weak blocks. -/
theorem ten_circle_group_action (z : StandardModelGroup.Phase) (X : Ten)
    (i j : MatterBranching.FiveIndex) :
    (tenGroupRepresentation (StandardModelGroup.centralCircle z) X).val i j =
      ((z ^ (fundamentalCircleCharge i + fundamentalCircleCharge j) :
        StandardModelGroup.Phase) : ℂ) * X.val i j := by
  rw [ten_gauge_group_action, circle_gauge_diagonal]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hp : ((z ^ fundamentalCircleCharge i : StandardModelGroup.Phase) : ℂ) *
      ((z ^ fundamentalCircleCharge j : StandardModelGroup.Phase) : ℂ) =
      ((z ^ (fundamentalCircleCharge i + fundamentalCircleCharge j) :
        StandardModelGroup.Phase) : ℂ) :=
    congrArg Subtype.val (zpow_add z _ _).symm
  rw [← hp]
  ring

/-- Actual dual coordinates carry the opposite circle powers `2` and `-3`. -/
theorem antifive_circle_group_action (z : StandardModelGroup.Phase) (f : AntiFive)
    (i : MatterBranching.FiveIndex) :
    dualCoordinates MatterBranching.FiveIndex
      (antiFiveGroupRepresentation (StandardModelGroup.centralCircle z) f) i =
      ((z ^ (-fundamentalCircleCharge i) : StandardModelGroup.Phase) : ℂ) *
        dualCoordinates MatterBranching.FiveIndex f i := by
  rw [dual_coordinates_apply, antifive_gauge_group_action,
    ← map_inv, circle_gauge_diagonal]
  have hv : (Matrix.diagonal fun j =>
      ((z⁻¹ ^ fundamentalCircleCharge j : StandardModelGroup.Phase) : ℂ)) *ᵥ
        (Pi.single i 1 : Five) =
      ((z⁻¹ ^ fundamentalCircleCharge i : StandardModelGroup.Phase) : ℂ) •
        (Pi.single i 1 : Five) := by
    ext j
    rw [Matrix.mulVec_diagonal]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with h <;> simp_all
  rw [hv, map_smul, dual_coordinates_apply]
  simp only [smul_eq_mul, inv_zpow, zpow_neg]

/-- The literal action of the covering product group on the eighty-one. -/
def matter81CoverRepresentation : StandardModelGroup.Cover →* (Matter81 ≃ₗ[ℂ] Matter81) :=
  matter81GroupRepresentation.comp StandardModelGroup.cover

/-- Every element of the computed six-element kernel acts trivially on matter. -/
theorem matter81_cover_kernel_trivial (k : StandardModelGroup.cover.ker) (v : Matter81) :
    matter81CoverRepresentation k.val v = v := by
  change matter81GroupRepresentation (StandardModelGroup.cover k.val) v = v
  rw [show StandardModelGroup.cover k.val = 1 from k.prop, map_one]
  rfl

/-- The constructed matter action really descends through the central quotient. -/
theorem matter81_cover_group_descent :
    ∃ ρ : StandardModelGroup.GaugeGroup →* (Matter81 ≃ₗ[ℂ] Matter81),
      ρ.comp StandardModelGroup.cover = matter81CoverRepresentation :=
  ⟨matter81GroupRepresentation, rfl⟩

end

end CubicAnomaly.Fixed.MatterGroupAction
