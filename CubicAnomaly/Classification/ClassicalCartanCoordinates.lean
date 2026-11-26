import CubicAnomaly.Classification.ChevalleyCartanMatching

/-! Transport a standard coordinate Cartan chart to the actual Cartan by
its ordered basis of simple roots. -/
namespace CubicAnomaly.Classification.ClassicalCartanCoordinates

open LieAlgebra LieAlgebra.IsKilling LieModule Module

variable {r : ℕ} {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  (s : b.support ≃ Fin r) (W : (Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))

/-- Match the coordinates of a Cartan element by evaluating every simple root. -/
noncomputable def coordinates : H ≃ₗ[ℂ] (Fin r → ℂ) :=
  ((evalEquiv ℂ H).trans (b.toWeightBasis.reindex s).dualBasis.equivFun).trans W.symm

theorem value_coordinates (h : H) (i : Fin r) :
    W (coordinates H b s W h) i = (s.symm i).val.val h := by
  change W (W.symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  change (b.toWeightBasis.reindex s).dualBasis.equivFun ((evalEquiv ℂ H) h) i = _
  rw [Basis.dualBasis_equivFun, Basis.reindex_apply, RootPairing.Base.toWeightBasis_apply]
  rfl

theorem classical_coordinates_coroot (C : Matrix (Fin r) (Fin r) ℤ) (hm : b.cartanMatrix.reindex s s = C)
    (v : Fin r → Fin r → ℂ) (hv : ∀ i j, W (v j) i = (C i j : ℂ)) (i : Fin r) :
    coordinates H b s W (coroot (s.symm i).val.val) = v i := by
  apply W.injective
  ext j
  rw [value_coordinates, hv]
  exact (b.algebraMap_cartanMatrixIn_apply ℤ (s.symm j) (s.symm i)).symm.trans
    (congrArg (algebraMap ℤ ℂ) (congrFun (congrFun hm j) i))

end CubicAnomaly.Classification.ClassicalCartanCoordinates
