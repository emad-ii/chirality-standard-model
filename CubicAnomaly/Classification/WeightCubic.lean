import Mathlib.Algebra.Lie.TraceForm
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Tactic.Ring

/-!
# Actual weight sums for trace cubics

For an abelian Lie algebra, the trace of any product of action operators is
the sum of the corresponding products of weights, counted with generalized
weight-space multiplicities.  The proof works with Mathlib's actual generalized
weight decomposition: nilpotent parts disappear from the trace of commuting
products.  No simultaneous diagonal basis or highest-weight classification is
assumed.

The cubic specialization is the finite weight formula used for Cartan anomaly
calculations.  A final theorem treats the symmetrized trace cubic directly.
-/

namespace CubicAnomaly.Classification.WeightCubic

open LieModule Module

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [IsLieAbelian L]

private theorem action_commute (M : Type*) [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M] (x y : L) :
    Commute (toEnd K L M x) (toEnd K L M y) := by
  rw [commute_iff_lie_eq, ← LieHom.map_lie, trivial_lie_zero, map_zero]

omit [IsLieAbelian L] in
private theorem coe_prod_action (N : LieSubmodule K L M) (xs : List L) (m : N) :
    (((xs.map fun x => toEnd K L N x).prod) m : M) =
      ((xs.map fun x => toEnd K L M x).prod) (m : M) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change ⁅x, (((xs.map fun x => toEnd K L N x).prod) m : M)⁆ =
        ⁅x, ((xs.map fun x => toEnd K L M x).prod) (m : M)⁆
      rw [ih]

variable [FiniteDimensional K M]

/-- On an actual generalized weight space, every product of commuting action
operators has the expected scalar trace; nilpotent parts contribute zero. -/
theorem trace_prod_toEnd_genWeightSpace (χ : L → K) (xs : List L) :
    LinearMap.trace K (genWeightSpace M χ)
        (xs.map fun x => toEnd K L (genWeightSpace M χ) x).prod =
      finrank K (genWeightSpace M χ) • (xs.map χ).prod := by
  induction xs with
  | nil => simp [LinearMap.trace_one]
  | cons x xs ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [LinearMap.trace_mul_comm]
      have hcomm : Commute ((xs.map fun y => toEnd K L (genWeightSpace M χ) y).prod)
          (toEnd K L (genWeightSpace M χ) x) := by
        apply Commute.list_prod_left
        intro f hf
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hf
        exact action_commute (genWeightSpace M χ) y x
      have htrace := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent
        (χ x) hcomm (isNilpotent_toEnd_sub_algebraMap M χ x)
      rw [show ((xs.map fun y => toEnd K L (genWeightSpace M χ) y).prod) *
          toEnd K L (genWeightSpace M χ) x =
          ((xs.map fun y => toEnd K L (genWeightSpace M χ) y).prod) ∘ₗ
            toEnd K L (genWeightSpace M χ) x from rfl,
        htrace, ih]
      simp only [nsmul_eq_mul, Nat.cast_comm]
      ring

variable [IsTriangularizable K L M]

/-- The trace of an arbitrary product of Cartan action operators is its actual
weight sum, with generalized weight multiplicities. -/
theorem trace_prod_eq_sum_weights (xs : List L) :
    LinearMap.trace K M (xs.map fun x => toEnd K L M x).prod =
      ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • (xs.map χ).prod := by
  classical
  have hstable : ∀ χ : Weight K L M,
      Set.MapsTo ((xs.map fun x => toEnd K L M x).prod)
        (genWeightSpace M χ) (genWeightSpace M χ) := by
    intro χ
    induction xs with
    | nil => intro m hm; exact hm
    | cons x xs ih =>
        intro m hm
        change ⁅x, ((xs.map fun x => toEnd K L M x).prod) m⁆ ∈ genWeightSpace M χ
        exact (genWeightSpace M χ).lie_mem (ih hm)
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' K L M))
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' K L M))
  rw [LinearMap.trace_eq_sum_trace_restrict hds hstable]
  apply Finset.sum_congr rfl
  intro χ _
  have hrestrict : ((xs.map fun x => toEnd K L M x).prod).restrict (hstable χ) =
      (xs.map fun x => toEnd K L (genWeightSpace M χ) x).prod := by
    ext m
    exact (coe_prod_action (genWeightSpace M χ) xs m).symm
  rw [hrestrict]
  exact trace_prod_toEnd_genWeightSpace χ xs

/-- The cubic trace on an abelian Cartan is the sum of the three weight
coordinates multiplied together, with their actual multiplicities. -/
theorem trace_cubic_eq_sum_weights (x y z : L) :
    LinearMap.trace K M (toEnd K L M x * toEnd K L M y * toEnd K L M z) =
      ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • (χ x * χ y * χ z) := by
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    using trace_prod_eq_sum_weights (K := K) (M := M) [x, y, z]

/-- All higher moments follow from the same generalized-weight argument. -/
theorem trace_power_eq_sum_weights (x : L) (n : ℕ) :
    LinearMap.trace K M (toEnd K L M x ^ n) =
      ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • χ x ^ n := by
  simpa only [List.map_replicate, List.prod_replicate]
    using trace_prod_eq_sum_weights (K := K) (M := M) (List.replicate n x)

/-- The symmetrized trace cubic has exactly the same Cartan weight formula.
This is the expression whose coefficients are evaluated in the finite census. -/
theorem symmetrized_trace_cubic_eq_sum_weights [CharZero K] (x y z : L) :
    (1 / 2 : K) * LinearMap.trace K M
        (toEnd K L M x * (toEnd K L M y * toEnd K L M z +
          toEnd K L M z * toEnd K L M y)) =
      ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • (χ x * χ y * χ z) := by
  calc
    (1 / 2 : K) * LinearMap.trace K M
        (toEnd K L M x * (toEnd K L M y * toEnd K L M z +
          toEnd K L M z * toEnd K L M y)) =
        LinearMap.trace K M (toEnd K L M x * toEnd K L M y * toEnd K L M z) := by
      rw [(action_commute M z y).eq, mul_add, map_add]
      simp only [← mul_assoc]
      ring
    _ = _ := trace_cubic_eq_sum_weights (K := K) (M := M) x y z

end CubicAnomaly.Classification.WeightCubic
