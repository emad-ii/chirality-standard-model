import CubicAnomaly.Classification.SymplecticMatrixGenerators

/-! Signed-coordinate realization of an actual Cartan with simple matrix Cₙ. -/
namespace CubicAnomaly.Classification.TypeCCartanCoordinates

open LieAlgebra LieAlgebra.IsKilling LieModule Module SymplecticMatrixGenerators

variable {n : ℕ}

private def weightMap : (Fin (n+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ) where
  toFun d i := weight i d
  map_add' d e := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [weight, mul_add]
    | cast j => simp [weight]; ring
  map_smul' c d := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [weight]; ring
    | cast j => simp [weight, mul_sub]

private noncomputable def weightEquiv : (Fin (n+1) → ℂ) ≃ₗ[ℂ] (Fin (n+1) → ℂ) := by
  have hinj : Function.Injective (weightMap (n := n)) := by
    intro d e he
    have hv (i : Fin (n+1)) : weight i d = weight i e := congrFun he i
    ext i
    induction i using Fin.reverseInduction with
    | last => simpa [weight] using hv (Fin.last n)
    | cast j ih =>
      have hj := hv j.castSucc
      simp [weight, ih] at hj
      exact hj
  exact LinearEquiv.ofBijective weightMap ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  (s : b.support ≃ Fin (n+1)) (hm : b.cartanMatrix.reindex s s = CartanMatrix.C (n+1))

/-- The coordinates in which the simple roots evaluate as successive
differences and the doubled last coordinate. -/
noncomputable def coordinates : H ≃ₗ[ℂ] (Fin (n+1) → ℂ) :=
  ((evalEquiv ℂ H).trans (b.toWeightBasis.reindex s).dualBasis.equivFun).trans weightEquiv.symm

theorem weight_coordinates (h : H) (i : Fin (n+1)) :
    weight i (coordinates H b s h) = (s.symm i).val.val h := by
  change weightEquiv (weightEquiv.symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  change (b.toWeightBasis.reindex s).dualBasis.equivFun ((evalEquiv ℂ H) h) i = _
  rw [Basis.dualBasis_equivFun,
    Basis.reindex_apply, RootPairing.Base.toWeightBasis_apply]
  rfl

include hm in
theorem coordinates_coroot (i : Fin (n+1)) :
    coordinates H b s (coroot (s.symm i).val.val) = corootVector i := by
  apply weightEquiv.injective
  ext j
  change weight j (coordinates H b s _) = weight j (corootVector i)
  rw [weight_coordinates, weight_coroot]
  have hr := b.algebraMap_cartanMatrixIn_apply ℤ (s.symm j) (s.symm i)
  have hc := congrFun (congrFun hm j) i
  exact hr.symm.trans (congrArg (algebraMap ℤ ℂ) hc)

/-- The standard coordinate weights, as actual Cartan linear functionals. -/
noncomputable def epsilon (i : Fin (n+1)) : Dual ℂ H :=
  (LinearMap.proj i).comp (coordinates H b s).toLinearMap

theorem epsilon_apply (i : Fin (n+1)) (h : H) : epsilon H b s i h = coordinates H b s h i := rfl

theorem epsilon_simple (i : Fin n) :
    (rootSystem H).root (s.symm i.castSucc) = epsilon H b s i.castSucc - epsilon H b s i.succ := by
  ext h
  simpa only [weight, Fin.lastCases_castSucc] using (weight_coordinates H b s h i.castSucc).symm

theorem epsilon_last : (rootSystem H).root (s.symm (Fin.last n)) = 2 • epsilon H b s (Fin.last n) := by
  ext h
  simpa only [weight, Fin.lastCases_last, two_smul, two_mul] using (weight_coordinates H b s h (Fin.last n)).symm

end CubicAnomaly.Classification.TypeCCartanCoordinates
