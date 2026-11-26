import CubicAnomaly.Classification.ExceptionalSieveNormalization
import CubicAnomaly.Classification.TensorEvaluation

/-!
# The actual factor index in an irreducible isotropy module

Restricting an irreducible module to one simple direct ideal gives copies
of an actual irreducible constituent. The evaluation map realizes these
copies with their multiplicity space. Trace on the tensor product supplies
the dimension of the entire module in the index numerator.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveFactorIndex

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open CubicAnomaly.Classification.TensorEvaluation
open CubicAnomaly.Classification.RootClassificationExceptional
open CubicAnomaly.Classification.ExceptionalSieveCatalog
open CubicAnomaly.Classification.ExceptionalSieveNormalization
open CubicAnomaly.Classification.ExceptionalSieveWeights
open scoped TensorProduct

variable {L W U : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [LieRingModule L W] [LieModule ℂ L W]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] [LieRingModule L U] [LieModule ℂ L U]

/-- Evaluation identifies the quadratic trace on the original module with
the constituent trace times the dimension of its actual multiplicity space. -/
theorem evaluation_trace_multiplicity
    (hb : Function.Bijective (lieHomEvaluation (K := ℂ) (L := L) (U := U) (W := W)))
    (x y : L) :
    traceForm ℂ L W x y =
      traceForm ℂ L U x y * finrank ℂ (U →ₗ⁅ℂ,L⁆ W) := by
  let D := U →ₗ⁅ℂ,L⁆ W
  letI : FiniteDimensional ℂ D := lieHom_space_finite
  let E := LinearEquiv.ofBijective lieHomEvaluation hb
  have hact (z : L) : toEnd ℂ L W z = E.conj ((toEnd ℂ L U z).rTensor D) := by
    apply LinearMap.ext
    intro w
    obtain ⟨p, rfl⟩ := E.surjective w
    have h := LinearMap.congr_fun (lieHomEvaluation_comp_left_action (U := U) (W := W) z) p
    simpa [LinearEquiv.conj_apply_apply, E] using h.symm
  rw [traceForm_apply_apply, hact x, hact y, ← LinearEquiv.conj_comp, LinearMap.trace_conj',
    ← LinearMap.rTensor_comp]
  change LinearMap.trace ℂ _ (TensorProduct.map _ (LinearMap.id : Module.End ℂ D)) = _
  rw [LinearMap.trace_tensorProduct', LinearMap.trace_id]
  rfl

variable [FiniteDimensional ℂ L] [IsIrreducible ℂ L W]

/-- For every identified simple ideal factor the original irreducible module
supplies a dominant factor label and a simple coroot giving the exact
ambient-restriction index numerator, including the full module dimension. -/
theorem simple_factor_index_numerator
    (I J : LieIdeal ℂ L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤)
    [LieAlgebra.IsKilling ℂ I] [LieAlgebra.IsSimple ℂ I]
    (H : LieSubalgebra ℂ I) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    (t : Factor) (s : Index t.datum ≃ b.support)
    (hmat : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j) :
    ∃ (S : LieSubmodule ℂ I W) (a : t.Label) (χ : Weight ℂ H S) (v : S),
      IsAtom S ∧ IsIrreducible ℂ I S ∧ v ≠ 0 ∧ (∀ z : H, ⁅z, v⁆ = χ z • v) ∧
      (∀ α : H.root, b.IsPos α → ∀ z ∈ rootSpace H α.val, ⁅z, v⁆ = 0) ∧
      (∀ i, χ (coroot (s i).val.val) = (a (nodes t i) : ℂ)) ∧
      ∃ i : Index t.datum, let x : I := coroot (s i).val.val
        killingForm ℂ L (x : L) x + 2 * traceForm ℂ L W (x : L) x =
          4 * t.dualCoxeter + 4 * (finrank ℂ W : ℂ) * (t.casimir a : ℂ) / t.algebraDim := by
  obtain ⟨S, hS, hIr, hb⟩ := exists_atomic_evaluation_factorization (W := W) I J hIJ htop
  letI := hIr
  letI := nontrivial_of_isIrreducible ℂ I S
  obtain ⟨χ, v, c, hv, hev, hkill, hc⟩ := exists_bounded_dominant_highest_weight (M := S) H b
  let a : t.Label := fun j => (c (s ((nodes t).symm j)) : ℕ)
  have ha (i : Index t.datum) : χ (coroot (s i).val.val) = (a (nodes t i) : ℂ) := by
    simpa [a] using hc (s i)
  obtain ⟨i, hk, hn⟩ := actual_long_coroot_trace H b t s hmat χ a ha hv hev hkill
  refine ⟨S, a, χ, v, hS, hIr, hv, hev, hkill, ha, i, ?_⟩
  let x : I := coroot (s i).val.val
  let D := S →ₗ⁅ℂ,I⁆ W
  letI : FiniteDimensional ℂ D := lieHom_space_finite
  have hdim : finrank ℂ W = finrank ℂ S * finrank ℂ D := by
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_tensorProduct]
  have hκ : killingForm ℂ L (x : L) x = killingForm ℂ I x x :=
    (LinearMap.congr_fun (LinearMap.congr_fun (I.killingForm_eq) x) x).symm
  change killingForm ℂ L (x : L) x + 2 * traceForm ℂ I W x x = _
  rw [hκ, evaluation_trace_multiplicity hb, hdim, Nat.cast_mul]
  change killingForm ℂ I x x = _ at hk
  change killingForm ℂ I x x + 2 * traceForm ℂ I S x x = _ at hn
  rw [hk] at hn ⊢
  linear_combination (finrank ℂ D : ℂ) * hn

end CubicAnomaly.Classification.ExceptionalSieveFactorIndex
