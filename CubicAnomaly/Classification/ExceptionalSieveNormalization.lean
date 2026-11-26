import CubicAnomaly.Classification.ExceptionalSieveCatalog
import CubicAnomaly.Classification.ExceptionalSieveCasimir

/-!
# Normalized Dynkin index of an actual highest-weight representation

The restricted Killing form is the sum of the actual root squares. Transport
this identity and the sum of positive roots through the certified root list.
In the simple coroot basis the resulting Gram matrix is inverse, up to the
factor twice the dual Coxeter number, to the catalog's fundamental-weight
Gram matrix.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveNormalization

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.RootClassificationExceptional
open CubicAnomaly.Classification.ExceptionalSieveCatalog
open CubicAnomaly.Classification.ExceptionalSieveWeights
open CubicAnomaly.Classification.ExceptionalSieveCasimir

private theorem datum_rank : ∀ t : Factor, t.datum.cartan.size = t.rank := by native_decide

/-- Relabel the authored simple-coordinate positions by the factor's Dynkin nodes. -/
def nodes (t : Factor) : Index t.datum ≃ t.Node := finCongr (datum_rank t)

private def rootValue (t : Factor) (v : ↥(table t.datum)) (i : Index t.datum) : ℤ :=
  ∑ j, v.val[j] * matrix t.datum j i

private def killingEntry (t : Factor) (i j : Index t.datum) : ℤ :=
  ∑ v : ↥(table t.datum), rootValue t v i * rootValue t v j

private theorem normalized_entries : ∀ (t : Factor) (i j : Index t.datum),
    (∑ k, (killingEntry t i k : ℚ) * t.gram (nodes t k) (nodes t j)) =
      (if i = j then 2 * (t.dualCoxeter : ℚ) else 0) := by
  native_decide

private theorem positive_labels : ∀ (t : Factor) (i : Index t.datum),
    (∑ v : ↥(table t.datum), if 0 < ∑ k : Index t.datum, v.val[k] then rootValue t v i else 0) = 2 := by
  native_decide

private theorem table_dimensions : ∀ (t : Factor),
    t.datum.cartan.size + (table t.datum).card = t.algebraDim ∧
    ∃ i, killingEntry t i i = 4 * (t.dualCoxeter : ℤ) := by native_decide

noncomputable section

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] [AddCommGroup M] [Module ℂ M]
  [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  (t : Factor) (s : Index t.datum ≃ b.support)

private def corootBasis : Basis (Index t.datum) ℂ H := b.toCoweightBasis.reindex s.symm

private theorem root_data
    (hmat : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j) :
    ∃ E : ↥(table t.datum) ≃ H.root, (∀ v i,
      (E v).val (corootBasis H b t s i) = (rootValue t v i : ℂ)) ∧
      ∀ v, b.height (E v) = ∑ i : Index t.datum, v.val[i] := by
  classical
  obtain ⟨E, hE⟩ := exists_census_root_equiv b s (Factor.cartan_geometry t).1 hmat
  refine ⟨E, ?_, ?_⟩
  · intro v i
    change (rootSystem H).root (E v) _ = _
    rw [hE]
    have hc (j : Index t.datum) :
        (rootSystem H).root (s j) (corootBasis H b t s i) = (matrix t.datum j i : ℂ) := by
      rw [← hmat]
      simpa only [corootBasis, Basis.reindex_apply, Equiv.symm_symm, RootPairing.Base.toCoweightBasis_apply]
        using (b.algebraMap_cartanMatrixIn_apply ℤ (s j) (s i)).symm
    change ∀ j, (s j).val.val (corootBasis H b t s i) = _ at hc
    simp [realize, LinearMap.sum_apply, hc, rootValue, zsmul_eq_mul]
  · intro v
    obtain ⟨H₀, hp⟩ := exists_height_element H b
    have hone (i : Index t.datum) : (rootSystem H).root (s i) H₀ = 1 := by
      change (s i).val.val H₀ = _
      rw [hp, b.height_one_of_mem_support (s i).property, Int.cast_one]
    apply Int.cast_injective (α := ℂ)
    rw [← hp]
    change (rootSystem H).root (E v) H₀ = _
    rw [hE]
    change ∀ i, (s i).val.val H₀ = 1 at hone
    simp [realize, LinearMap.sum_apply, hone, zsmul_eq_mul]

private def twoRho : Module.Dual ℂ H := by
  classical
  exact ∑ α : H.root, if b.IsPos α then (rootSystem H).root α else 0

private theorem actual_entries
    (hmat : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j) :
    (∀ i j, traceForm ℂ H L (corootBasis H b t s i) (corootBasis H b t s j) =
      (killingEntry t i j : ℂ)) ∧ ∀ i, twoRho H b (corootBasis H b t s i) = 2 := by
  classical
  obtain ⟨E, hE, hp⟩ := root_data H b t s hmat
  constructor
  · intro i j
    let B := corootBasis H b t s
    have h := LinearMap.congr_fun (LinearMap.congr_fun
      (corootForm_rootSystem_eq_killing (H := H)) (B i)) (B j)
    change _ = traceForm ℂ H L (B i) (B j) at h
    rw [← h]
    rw [RootPairing.corootForm_apply_apply]
    change (∑ α : H.root, α.val (B i) * α.val (B j)) = _
    rw [← E.sum_comp (fun α : H.root => α.val (B i) * α.val (B j))]
    simp [B, hE, killingEntry]
  · intro i
    rw [twoRho, LinearMap.sum_apply, ← E.sum_comp]
    have hp' (v : ↥(table t.datum)) : b.IsPos (E v) ↔ 0 < ∑ k : Index t.datum, v.val[k] := by
      rw [RootPairing.Base.isPos_iff, hp]
    have h := congrArg (fun n : ℤ => (n : ℂ)) (positive_labels t i)
    have hh : (∑ v : ↥(table t.datum), if 0 < ∑ k : Index t.datum, v.val[k]
        then (rootValue t v i : ℂ) else 0) = 2 := by
      simpa only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Int.cast_ofNat] using h
    rw [← hh]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hpos : b.IsPos (E v)
    · rw [if_pos hpos, if_pos ((hp' v).mp hpos)]
      exact hE v i
    · rw [if_neg hpos, if_neg (mt (hp' v).mpr hpos)]
      rfl

private theorem inverse_killing
    (hmat : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j)
    (ψ : Module.Dual ℂ H) :
    (2 * (t.dualCoxeter : ℂ)) • (cartanEquivDual H).symm ψ =
      ∑ j, ψ (corootBasis H b t s j) • ∑ k, (t.gram (nodes t k) (nodes t j) : ℂ) •
        corootBasis H b t s k := by
  classical
  let B := corootBasis H b t s
  have hk := (actual_entries H b t s hmat).1
  apply (cartanEquivDual H).injective
  apply B.ext
  intro i
  simp only [map_smul, LinearEquiv.apply_symm_apply, LinearMap.smul_apply, smul_eq_mul,
    map_sum, LinearMap.sum_apply, cartanEquivDual_apply_apply]
  have hentry (j : Index t.datum) :
      ∑ k, (t.gram (nodes t k) (nodes t j) : ℂ) * traceForm ℂ H L (B k) (B i) =
      (if i = j then 2 * (t.dualCoxeter : ℂ) else 0) := by
    have h : (∑ k, (killingEntry t i k : ℂ) * (t.gram (nodes t k) (nodes t j) : ℂ)) =
        (if i = j then 2 * (t.dualCoxeter : ℂ) else 0) := by
      by_cases hij : i = j
      all_goals simpa only [hij, if_true, if_false, Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat,
        Rat.cast_natCast, Rat.cast_intCast, Rat.cast_zero] using
        congrArg (fun r : ℚ => (r : ℂ)) (normalized_entries t i j)
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => by
      have hsym : traceForm ℂ H L (B k) (B i) = traceForm ℂ H L (B i) (B k) :=
        (traceForm_isSymm ℂ H L).eq ..
      rw [hsym, hk i k, mul_comm]
  change _ = ∑ j, ψ (B j) * ∑ k, (t.gram (nodes t k) (nodes t j) : ℂ) * traceForm ℂ H L (B k) (B i)
  simp_rw [hentry]
  simp [mul_comm]

/-- The actual Killing-normalized Casimir, multiplied by twice the dual
Coxeter number, equals the catalog's rational fundamental-weight expression. -/
theorem normalized_highest_casimir
    (hmat : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j)
    (χ : Module.Dual ℂ H) (a : t.Label)
    (ha : ∀ i, χ (coroot (s i).val.val) = (a (nodes t i) : ℂ)) :
    (2 * (t.dualCoxeter : ℂ)) * highestCasimirValue H b χ = (t.casimir a : ℂ) := by
  classical
  let B := corootBasis H b t s
  let ψ := χ + twoRho H b
  have heb (i : Index t.datum) : χ (B i) = (a (nodes t i) : ℂ) := by
    simpa [B, corootBasis] using ha i
  have hψ (i : Index t.datum) : ψ (B i) = (a (nodes t i) : ℂ) + 2 := by
    change χ (B i) + twoRho H b (B i) = _
    rw [heb, (actual_entries H b t s hmat).2 i]
  have hcas : highestCasimirValue H b χ = χ ((cartanEquivDual H).symm ψ) := by
    simp [highestCasimirValue, ψ, twoRho, map_sum, apply_ite]
  have hv := congrArg χ (inverse_killing H b t s hmat ψ)
  rw [hcas]
  simp only [map_sum, map_smul, smul_eq_mul] at hv
  rw [hv]
  change (∑ j, ψ (B j) * ∑ k, (t.gram (nodes t k) (nodes t j) : ℂ) * χ (B k)) = _
  simp_rw [hψ, heb, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Factor.casimir, Rat.cast_sum, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_ofNat]
  rw [← (nodes t).sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (nodes t).sum_comp]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The trace index used by the finite search is the trace of the actual
irreducible highest-weight module, for any identified simple Cartan type. -/
theorem normalized_highest_weight_trace_index [LieAlgebra.IsSimple ℂ L] [IsIrreducible ℂ L M]
    (hmat : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j)
    (χ : Module.Dual ℂ H) (a : t.Label)
    (ha : ∀ i, χ (coroot (s i).val.val) = (a (nodes t i) : ℂ)) {v : M} (hv : v ≠ 0)
    (hev : ∀ x : H, ⁅x, v⁆ = χ x • v)
    (hkill : ∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, v⁆ = 0) :
    ∃ m : ℂ, traceForm ℂ L M = m • killingForm ℂ L ∧
      (t.casimir a : ℂ) * finrank ℂ M = 2 * (t.dualCoxeter : ℂ) * m * finrank ℂ L := by
  obtain ⟨m, hm, hc⟩ := highest_weight_trace_index H b χ hv hev hkill
  refine ⟨m, hm, ?_⟩
  rw [← normalized_highest_casimir H b t s hmat χ a ha]
  linear_combination (2 * (t.dualCoxeter : ℂ)) * hc

/-- In every catalog type there is an actual simple coroot on which the
combined isotropy-adjoint and doubled module trace equals the numerator
of the exceptional index quotient. -/
theorem actual_long_coroot_trace [LieAlgebra.IsSimple ℂ L] [IsIrreducible ℂ L M]
    (hmat : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j)
    (χ : Module.Dual ℂ H) (a : t.Label)
    (ha : ∀ i, χ (coroot (s i).val.val) = (a (nodes t i) : ℂ)) {v : M} (hv : v ≠ 0)
    (hev : ∀ x : H, ⁅x, v⁆ = χ x • v)
    (hkill : ∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, v⁆ = 0) :
    ∃ i : Index t.datum, let x : L := coroot (s i).val.val
      killingForm ℂ L x x = 4 * t.dualCoxeter ∧
      killingForm ℂ L x x + 2 * traceForm ℂ L M x x =
        4 * t.dualCoxeter + 4 * (finrank ℂ M : ℂ) * (t.casimir a : ℂ) / t.algebraDim := by
  classical
  obtain ⟨m, hm, hmul⟩ := normalized_highest_weight_trace_index H b t s hmat χ a ha hv hev hkill
  obtain ⟨i, hi⟩ := (table_dimensions t).2
  refine ⟨i, ?_⟩
  let x : L := coroot (s i).val.val
  have hκ : killingForm ℂ L x x = 4 * (t.dualCoxeter : ℂ) := by
    have hk := (actual_entries H b t s hmat).1 i i
    rw [hi] at hk
    simpa [x, corootBasis] using hk
  refine ⟨hκ, ?_⟩
  obtain ⟨E, -, -⟩ := root_data H b t s hmat
  have hdim : finrank ℂ L = t.algebraDim := by
    rw [KillingDimension.killing_finrank_eq_cartan_add_roots H,
      KillingDimension.actual_root_count_eq_card H, ← Fintype.card_congr E,
      finrank_eq_card_basis (corootBasis H b t s)]
    simpa using (table_dimensions t).1
  have hd : (t.algebraDim : ℂ) ≠ 0 := by
    rw [← hdim]
    letI : Nontrivial L := nontrivial_of_isIrreducible ℂ L L
    exact_mod_cast (finrank_pos (R := ℂ) (M := L)).ne'
  rw [hdim] at hmul
  change killingForm ℂ L x x + 2 * traceForm ℂ L M x x = _
  rw [hm]
  change killingForm ℂ L x x + 2 * (m * killingForm ℂ L x x) = _
  rw [hκ]
  congr 1
  apply (eq_div_iff hd).mpr
  linear_combination -4 * hmul

end
end CubicAnomaly.Classification.ExceptionalSieveNormalization
