import CubicAnomaly.Classification.ChevalleyRootGeneration
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-! A reindexing of simple roots with identical Cartan matrices determines
a linear isomorphism of Cartans matching every simple coroot and pairing. -/

namespace CubicAnomaly.Classification.ChevalleyCartanMatching

open LieAlgebra LieModule Module LieAlgebra.IsKilling

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L] (H : LieSubalgebra K L)
  [H.IsCartanSubalgebra] [IsTriangularizable K H L] (b : (rootSystem H).Base)
  [LieRing M] [LieAlgebra K M] [FiniteDimensional K M] [LieAlgebra.IsKilling K M]
  (J : LieSubalgebra K M) [J.IsCartanSubalgebra] [IsTriangularizable K J M]
  (d : (rootSystem J).Base) (s : b.support ≃ d.support)

/-- The Cartan equivalence matching the indicated ordered simple coroots. -/
noncomputable def cartanEquiv : H ≃ₗ[K] J := b.toCoweightBasis.equiv d.toCoweightBasis s

theorem matched_simple_coroot (i : b.support) :
    cartanEquiv H b J d s (coroot i.val.val) = coroot (s i).val.val := by
  change b.toCoweightBasis.equiv d.toCoweightBasis s ((rootSystem H).coroot i) =
    (rootSystem J).coroot (s i)
  rw [← b.toCoweightBasis_apply, ← d.toCoweightBasis_apply, Basis.equiv_apply]

/-- Matching simple coroots also matches every simple root functional, on
every Cartan element. -/
theorem matched_simple_root_value
    (hm : ∀ i j, b.cartanMatrix i j = d.cartanMatrix (s i) (s j))
    (i : b.support) (h : H) :
    (s i).val.val (cartanEquiv H b J d s h) = i.val.val h := by
  let E := cartanEquiv H b J d s
  suffices hlin : ((rootSystem J).root (s i)).comp E.toLinearMap = (rootSystem H).root i from
    LinearMap.congr_fun hlin h
  apply b.toCoweightBasis.ext
  intro j
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, RootPairing.Base.toCoweightBasis_apply,
    rootSystem_coroot_apply, E, matched_simple_coroot]
  have h₁ := b.algebraMap_cartanMatrixIn_apply ℤ i j
  have h₂ := d.algebraMap_cartanMatrixIn_apply ℤ (s i) (s j)
  exact h₂.symm.trans ((congrArg (algebraMap ℤ K) (hm i j).symm).trans h₁)

end CubicAnomaly.Classification.ChevalleyCartanMatching
