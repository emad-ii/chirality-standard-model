import CubicAnomaly.Fixed.MatterLieAlgebra
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Actual chiral content of the constructed eighty-one

The three-copy module is explicitly split into three family modules and
an actual self-dual remainder. The defining/dual pair and the trivial
lines are equipped with constructed equivariant duality isomorphisms.
Thus the cancellation is a statement about actual modules, rather than
only a table of signed multiplicities.
-/

namespace CubicAnomaly.Fixed.MatterChirality

open Matrix
open CubicAnomaly.Fixed.MatterBranching
open CubicAnomaly.Fixed.MatterDual
open CubicAnomaly.Fixed.MatterSpectrum
open CubicAnomaly.Fixed.MatterLieAlgebra

noncomputable section

private def vectorlikeDualLinearEquiv :
    VectorlikePair ≃ₗ[ℂ] Module.Dual ℂ VectorlikePair :=
  ((LinearEquiv.prodComm ℂ Five AntiFive).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℂ AntiFive) (Module.evalEquiv ℂ Five))).trans
      (Module.dualProdDualEquivDual ℂ Five AntiFive)

/-- The actual defining/dual pair has an explicit equivariant self-duality. -/
def vectorlikeSelfDual :
    VectorlikePair ≃ₗ⁅ℂ,MatrixFive⁆ Module.Dual ℂ VectorlikePair where
  __ := vectorlikeDualLinearEquiv
  map_lie' := by
    intro A v
    apply LinearMap.ext
    intro w
    change -v.2 ⁅A, w.1⁆ + w.2 ⁅A, v.1⁆ =
      -(v.2 ⁅A, w.1⁆ + -w.2 ⁅A, v.1⁆)
    ring

/-- The duality pairing is the canonical evaluation pairing in both orders. -/
@[simp] theorem vectorlike_self_dual_apply (v w : VectorlikePair) :
    vectorlikeSelfDual v w = v.2 w.1 + w.2 v.1 := rfl

private def singletsDualLinearEquiv : TwoSinglets ≃ₗ[ℂ] Module.Dual ℂ TwoSinglets :=
  (dualCoordinates (Fin 2)).symm

/-- The two actual trivial lines are equivariantly self-dual. -/
def singletsSelfDual : TwoSinglets ≃ₗ⁅ℂ,MatrixFive⁆ Module.Dual ℂ TwoSinglets where
  __ := singletsDualLinearEquiv
  map_lie' := by
    intro A v
    apply LinearMap.ext
    intro w
    change singletsDualLinearEquiv 0 w = -(singletsDualLinearEquiv v) 0
    simp

/-- All additional matter in one constructed twenty-seven. -/
abbrev Extras := VectorlikePair × TwoSinglets

private def extrasDualLinearEquiv : Extras ≃ₗ[ℂ] Module.Dual ℂ Extras :=
  (LinearEquiv.prodCongr vectorlikeSelfDual.toLinearEquiv
    singletsSelfDual.toLinearEquiv).trans
      (Module.dualProdDualEquivDual ℂ VectorlikePair TwoSinglets)

/-- The entire additional module is actually self-dual. -/
def extrasSelfDual : Extras ≃ₗ⁅ℂ,MatrixFive⁆ Module.Dual ℂ Extras where
  __ := extrasDualLinearEquiv
  map_lie' := by
    intro A v
    apply LinearMap.ext
    intro w
    change vectorlikeSelfDual ⁅A, v.1⁆ w.1 + singletsSelfDual ⁅A, v.2⁆ w.2 =
      -(vectorlikeSelfDual v.1 ⁅A, w.1⁆ + singletsSelfDual v.2 ⁅A, w.2⁆)
    have hv : vectorlikeSelfDual ⁅A, v.1⁆ = ⁅A, vectorlikeSelfDual v.1⁆ :=
      vectorlikeSelfDual.map_lie A v.1
    have hs : singletsSelfDual ⁅A, v.2⁆ = ⁅A, singletsSelfDual v.2⁆ :=
      singletsSelfDual.map_lie A v.2
    rw [hv, hs]
    simp only [Module.Dual.lie_apply]
    ring

private def copiesDualMap :
    (Fin 3 → Extras) →ₗ[ℂ] Module.Dual ℂ (Fin 3 → Extras) where
  toFun v :=
    { toFun := fun w => ∑ i, extrasSelfDual (v i) (w i)
      map_add' := by intros; simp [map_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [map_smul, Finset.mul_sum] }
  map_add' := by
    intro v w
    apply LinearMap.ext
    intro z
    simp [map_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    apply LinearMap.ext
    intro z
    simp [map_smul, Finset.mul_sum]

private theorem copiesDualMap_injective : Function.Injective copiesDualMap := by
  intro v w h
  funext i
  apply extrasSelfDual.injective
  apply LinearMap.ext
  intro z
  have hz := congrArg (fun f : Module.Dual ℂ (Fin 3 → Extras) => f (Pi.single i z)) h
  simpa [copiesDualMap, Pi.single_apply, apply_ite, map_zero] using hz

/-- The entire thirty-six-dimensional repeated remainder is actually self-dual. -/
def extraCopiesSelfDual :
    (Fin 3 → Extras) ≃ₗ⁅ℂ,MatrixFive⁆ Module.Dual ℂ (Fin 3 → Extras) where
  __ := copiesDualMap.linearEquivOfInjective copiesDualMap_injective
    Subspace.dual_finrank_eq.symm
  toFun := copiesDualMap
  map_lie' := by
    intro A v
    apply LinearMap.ext
    intro w
    change (∑ i, extrasSelfDual ⁅A, v i⁆ (w i)) =
      -(∑ i, extrasSelfDual (v i) ⁅A, w i⁆)
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f : Module.Dual ℂ Extras => f (w i))
      (show extrasSelfDual ⁅A, v i⁆ = ⁅A, extrasSelfDual (v i)⁆ from
        extrasSelfDual.map_lie A (v i))

/-- Literal equivariant splitting into three families and the repeated remainder. -/
def matter81Split :
    Matter81 ≃ₗ⁅ℂ,MatrixFive⁆ (Fin 3 → Family) × (Fin 3 → Extras) where
  toFun v := (fun i => (v i).1, fun i => (v i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv v := rfl
  right_inv p := rfl
  map_add' v w := rfl
  map_smul' c v := rfl
  map_lie' := by intros; rfl

/-- The actual retained family part has dimension forty-five. -/
theorem three_families_finrank : Module.finrank ℂ (Fin 3 → Family) = 45 := by
  rw [Module.finrank_pi_fintype]
  simp only [family_finrank]
  decide

/-- All additional states have dimension thirty-six. -/
theorem extra_copies_finrank : Module.finrank ℂ (Fin 3 → Extras) = 36 := by
  rw [Module.finrank_pi_fintype]
  have he : Module.finrank ℂ Extras = 12 := by
    change Module.finrank ℂ (VectorlikePair × TwoSinglets) = 12
    rw [Module.finrank_prod, vectorlike_pair_finrank, two_singlets_finrank]
  simp only [he]
  decide

/-- The actual eighty-one has three family modules and an actual self-dual
remainder. This is the representation-theoretic input to net chiral cancellation. -/
theorem matter81_three_families_self_dual_remainder :
    Nonempty (Matter81 ≃ₗ⁅ℂ,MatrixFive⁆ (Fin 3 → Family) × (Fin 3 → Extras)) ∧
      Nonempty ((Fin 3 → Extras) ≃ₗ⁅ℂ,MatrixFive⁆ Module.Dual ℂ (Fin 3 → Extras)) ∧
      Module.finrank ℂ (Fin 3 → Family) = 45 ∧
      Module.finrank ℂ (Fin 3 → Extras) = 36 :=
  ⟨⟨matter81Split⟩, ⟨extraCopiesSelfDual⟩, three_families_finrank, extra_copies_finrank⟩

/-- The same explicit split is equivariant for the actual Standard Model subalgebra. -/
def matter81SMSplit :
    Matter81 ≃ₗ⁅ℂ,StandardModelAlgebra⁆ (Fin 3 → Family) × (Fin 3 → Extras) where
  __ := matter81Split.toLinearEquiv
  map_lie' := by
    intro x v
    exact matter81Split.map_lie x.val v

/-- Restriction preserves the constructed duality of all extra states. -/
def extraCopiesSMSelfDual :
    (Fin 3 → Extras) ≃ₗ⁅ℂ,StandardModelAlgebra⁆ Module.Dual ℂ (Fin 3 → Extras) where
  __ := extraCopiesSelfDual.toLinearEquiv
  map_lie' := by
    intro x v
    exact extraCopiesSelfDual.map_lie x.val v

/-- Actual Standard Model representation decomposition into three family
modules and a thirty-six-dimensional self-dual remainder. -/
theorem matter81_sm_three_families_self_dual_remainder :
    Nonempty (Matter81 ≃ₗ⁅ℂ,StandardModelAlgebra⁆
      (Fin 3 → Family) × (Fin 3 → Extras)) ∧
      Nonempty ((Fin 3 → Extras) ≃ₗ⁅ℂ,StandardModelAlgebra⁆
        Module.Dual ℂ (Fin 3 → Extras)) ∧
      Module.finrank ℂ (Fin 3 → Family) = 45 ∧
      Module.finrank ℂ (Fin 3 → Extras) = 36 :=
  ⟨⟨matter81SMSplit⟩, ⟨extraCopiesSMSelfDual⟩, three_families_finrank, extra_copies_finrank⟩

end

end CubicAnomaly.Fixed.MatterChirality
