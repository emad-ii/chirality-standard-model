import CubicAnomaly.Fixed.MatterDual
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Concrete fifteen-, twenty-seven-, and eighty-one-dimensional matter modules

These are actual complex representations of the matrix Lie algebra and
its traceless subalgebra. The fifteen is the alternating ten plus the
dual defining five. Adding a defining/dual pair and two trivial lines
constructs the twenty-seven; three copies construct the eighty-one.

The definitions do not assert that this twenty-seven is the restriction
of an `E6` representation, nor that the three copies are the half of an
`E8` adjoint complement. Those exceptional identifications remain separate.
-/

namespace CubicAnomaly.Fixed.MatterSpectrum

open Matrix
open CubicAnomaly.Fixed.MatterAlternating
open CubicAnomaly.Fixed.MatterBranching
open CubicAnomaly.Fixed.MatterDual

section Products

variable {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [LieRingModule L M] [LieRingModule L N] [LieModule R L M] [LieModule R L N]

instance (priority := 100) productLieRingModule : LieRingModule L (M × N) where
  bracket x m := (⁅x, m.1⁆, ⁅x, m.2⁆)
  add_lie x y m := Prod.ext (add_lie x y m.1) (add_lie x y m.2)
  lie_add x m n := Prod.ext (lie_add x m.1 n.1) (lie_add x m.2 n.2)
  leibniz_lie x y m := Prod.ext (leibniz_lie x y m.1) (leibniz_lie x y m.2)

instance (priority := 100) productLieModule : LieModule R L (M × N) where
  smul_lie c x m := Prod.ext (smul_lie c x m.1) (smul_lie c x m.2)
  lie_smul c x m := Prod.ext (lie_smul c x m.1) (lie_smul c x m.2)

/-- The product action is literal componentwise action. -/
@[simp] theorem product_lie (x : L) (m : M) (n : N) :
    ⁅x, (m, n)⁆ = (⁅x, m⁆, ⁅x, n⁆) := rfl

end Products

section Copies

variable {R L M ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

instance (priority := 100) copiesLieRingModule : LieRingModule L (ι → M) where
  bracket x f i := ⁅x, f i⁆
  add_lie x y f := funext fun i => add_lie x y (f i)
  lie_add x f g := funext fun i => lie_add x (f i) (g i)
  leibniz_lie x y f := funext fun i => leibniz_lie x y (f i)

instance (priority := 100) copiesLieModule : LieModule R L (ι → M) where
  smul_lie c x f := funext fun i => smul_lie c x (f i)
  lie_smul c x f := funext fun i => lie_smul c x (f i)

/-- The repeated representation acts separately on every actual copy. -/
@[simp] theorem copies_lie_apply (x : L) (f : ι → M) (i : ι) : ⁅x, f⁆ i = ⁅x, f i⁆ := rfl

end Copies

noncomputable section

/-- The ambient matrix algebra used to construct the classical matter action. -/
abbrev MatrixFive := Matrix FiveIndex FiveIndex ℂ

/-- Its traceless complex Lie subalgebra. -/
abbrev SpecialLinearFive := LieAlgebra.SpecialLinear.sl FiveIndex ℂ

/-- The actual five-dimensional defining module. -/
abbrev Five := FiveIndex → ℂ

/-- One actual minimal family: the alternating ten and the dual defining five. -/
abbrev Family := Ten × AntiFive

/-- An actual defining/dual pair. -/
abbrev VectorlikePair := Five × AntiFive

/-- Two actual trivial representation lines. -/
abbrev TwoSinglets := TrivialLieModule ℂ MatrixFive (Fin 2 → ℂ)

instance : FiniteDimensional ℂ TwoSinglets := by
  change FiniteDimensional ℂ (Fin 2 → ℂ)
  infer_instance

/-- The explicitly constructed classical restriction of the proposed twenty-seven. -/
abbrev Matter27 := Family × (VectorlikePair × TwoSinglets)

/-- Three actual copies of the constructed twenty-seven. -/
abbrev Matter81 := Fin 3 → Matter27

instance : FiniteDimensional ℂ Ten :=
  tenCoordinates.symm.finiteDimensional

instance : FiniteDimensional ℂ Matter27 := by
  change FiniteDimensional ℂ (Family × (VectorlikePair × TwoSinglets))
  infer_instance

/-- The dimension of one actual chiral-family module is fifteen. -/
theorem family_finrank : Module.finrank ℂ Family = 15 := by
  simp [Family, Module.finrank_prod, ten_finrank, AntiFive, FiveIndex]

/-- The defining/dual pair has dimension ten. -/
theorem vectorlike_pair_finrank : Module.finrank ℂ VectorlikePair = 10 := by
  simp [VectorlikePair, Five, AntiFive, FiveIndex, Module.finrank_prod]

/-- The two trivial lines have dimension two. -/
theorem two_singlets_finrank : Module.finrank ℂ TwoSinglets = 2 := by
  change Module.finrank ℂ (Fin 2 → ℂ) = 2
  simp

/-- The constructed twenty-seven has its actual module dimension. -/
theorem matter27_finrank : Module.finrank ℂ Matter27 = 27 := by
  change Module.finrank ℂ (Family × (VectorlikePair × TwoSinglets)) = 27
  rw [Module.finrank_prod, family_finrank, Module.finrank_prod,
    vectorlike_pair_finrank, two_singlets_finrank]

/-- The constructed three-copy module has dimension eighty-one. -/
theorem matter81_finrank : Module.finrank ℂ Matter81 = 81 := by
  change Module.finrank ℂ (Fin 3 → Matter27) = 81
  rw [Module.finrank_pi_fintype]
  simp only [matter27_finrank]
  decide

/-- Coordinates of all five actual Standard Model family multiplets. -/
def familyCoordinates : Family ≃ₗ[ℂ]
    ((Fin 3 → ℂ) × (Matrix (Fin 3) (Fin 2) ℂ × ℂ)) ×
      ((Fin 3 → ℂ) × (Fin 2 → ℂ)) :=
  LinearEquiv.prodCongr tenCoordinates antiFiveSMCoordinates

/-- The constructed family has the exact dual-colour, colour-weak,
singlet, dual-colour and weak actions with integer charges `-4,1,6,2,-3`. -/
theorem family_standard_model_action (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ)
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) (v : Family) :
    familyCoordinates ⁅standardModelGenerator A B q, v⁆ =
      ((-Aᵀ *ᵥ (familyCoordinates v).1.1 + (-4 * q) • (familyCoordinates v).1.1,
        A * (familyCoordinates v).1.2.1 + (familyCoordinates v).1.2.1 * Bᵀ +
          q • (familyCoordinates v).1.2.1,
        (6 * q) * (familyCoordinates v).1.2.2),
       (-Aᵀ *ᵥ (familyCoordinates v).2.1 + (2 * q) • (familyCoordinates v).2.1,
        B *ᵥ (familyCoordinates v).2.2 + (-3 * q) • (familyCoordinates v).2.2)) := by
  exact Prod.ext (ten_standard_model_action A B q hA hB v.1)
    (anti_five_sm_action A B q hB v.2)

/-- Every actual copy contains the same constructed family action. -/
theorem matter81_family_action (A : MatrixFive) (v : Matter81) (i : Fin 3) :
    (⁅A, v⁆ i).1 = ⁅A, (v i).1⁆ := rfl

/-- Literal colour and weak coordinates of the actual defining five. -/
def fiveCoordinates : Five ≃ₗ[ℂ] (Fin 3 → ℂ) × (Fin 2 → ℂ) :=
  LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 2) ℂ ℂ

/-- The defining five has colour and weak charges `-2` and `3`. -/
theorem five_standard_model_action (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) (v : Five) :
    fiveCoordinates ⁅standardModelGenerator A B q, v⁆ =
      (A *ᵥ (fiveCoordinates v).1 + (-2 * q) • (fiveCoordinates v).1,
        B *ᵥ (fiveCoordinates v).2 + (3 * q) • (fiveCoordinates v).2) := by
  apply Prod.ext
  · ext i
    simp [fiveCoordinates, standardModelGenerator, Matrix.lie_apply,
      LinearEquiv.sumArrowLequivProdArrow, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
      mul_ite]
  · ext i
    simp [fiveCoordinates, standardModelGenerator, Matrix.lie_apply,
      LinearEquiv.sumArrowLequivProdArrow, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
      mul_ite]

/-- Literal coordinates of both members of the additional vectorlike pair. -/
def vectorlikeCoordinates : VectorlikePair ≃ₗ[ℂ]
    ((Fin 3 → ℂ) × (Fin 2 → ℂ)) × ((Fin 3 → ℂ) × (Fin 2 → ℂ)) :=
  LinearEquiv.prodCongr fiveCoordinates antiFiveSMCoordinates

/-- The additional pair has charges `-2,3` and the opposite charges `2,-3`. -/
theorem vectorlike_hypercharge_action (v : VectorlikePair) :
    vectorlikeCoordinates ⁅standardModelGenerator 0 0 1, v⁆ =
      (((-2 : ℂ) • (vectorlikeCoordinates v).1.1,
          (3 : ℂ) • (vectorlikeCoordinates v).1.2),
        ((2 : ℂ) • (vectorlikeCoordinates v).2.1,
          (-3 : ℂ) • (vectorlikeCoordinates v).2.2)) := by
  apply Prod.ext
  · simpa using five_standard_model_action 0 0 1 v.1
  · simpa using anti_five_sm_action 0 0 1 (by simp) v.2

/-- Both additional singlet lines have zero action for every gauge generator. -/
theorem two_singlets_action_zero (A : MatrixFive) (v : TwoSinglets) : ⁅A, v⁆ = 0 := rfl

/-- The full actual eighty-one has three copies of the displayed family
charges, three vectorlike pairs, and six neutral singlet lines. -/
theorem matter81_full_hypercharge_action (v : Matter81) (i : Fin 3) :
    familyCoordinates (⁅standardModelGenerator 0 0 1, v⁆ i).1 =
      (((-4 : ℂ) • (familyCoordinates (v i).1).1.1,
          (familyCoordinates (v i).1).1.2.1,
          (6 : ℂ) * (familyCoordinates (v i).1).1.2.2),
        ((2 : ℂ) • (familyCoordinates (v i).1).2.1,
          (-3 : ℂ) • (familyCoordinates (v i).1).2.2)) ∧
    vectorlikeCoordinates (⁅standardModelGenerator 0 0 1, v⁆ i).2.1 =
      (((-2 : ℂ) • (vectorlikeCoordinates (v i).2.1).1.1,
          (3 : ℂ) • (vectorlikeCoordinates (v i).2.1).1.2),
        ((2 : ℂ) • (vectorlikeCoordinates (v i).2.1).2.1,
          (-3 : ℂ) • (vectorlikeCoordinates (v i).2.1).2.2)) ∧
    (⁅standardModelGenerator 0 0 1, v⁆ i).2.2 = 0 := by
  refine ⟨?_, vectorlike_hypercharge_action (v i).2.1, rfl⟩
  simpa using family_standard_model_action 0 0 1 (by simp) (by simp) (v i).1

end

end CubicAnomaly.Fixed.MatterSpectrum
