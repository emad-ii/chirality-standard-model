import CubicAnomaly.Classification.RootCharacterCoordinates
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Cartan coordinates dual to the actual integer root lattice

The constructed integer root-lattice basis spans the Cartan dual over the
ground field and has exactly its dimension.  It therefore gives a basis of
the dual, without a supplied independence or classification witness.  The
dual Cartan basis makes every actual root evaluate to its intrinsic integer
coordinates, interpreted in the ground field.
-/

namespace CubicAnomaly.Classification.IntrinsicCartanBasis

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.RootLatticeBasis
open CubicAnomaly.Classification.RootCharacterCoordinates

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The actual function-valued root lattice embeds as linear forms on the
Cartan, through its established identification with the integer root span. -/
noncomputable def rootLatticeToDual : rootLattice H →ₗ[ℤ] Dual K H :=
  ((rootSystem H).rootSpan ℤ).subtype.comp (rootSpanEquivRootLattice H).symm.toLinearMap

/-- The linear form associated with a root-lattice element is its original
function on the Cartan. -/
@[simp] theorem root_lattice_to_dual_apply (x : rootLattice H) (h : H) :
    rootLatticeToDual H x h = x.val h := by
  have hx := congrArg (fun y : rootLattice H => y.val h)
    ((rootSpanEquivRootLattice H).apply_symm_apply x)
  exact hx

/-- An actual root is sent to its actual linear root form. -/
@[simp] theorem root_lattice_to_dual_root (α : H.root) :
    rootLatticeToDual H (rootLatticeElement H α) = (rootSystem H).root α := by
  ext h
  exact root_lattice_to_dual_apply H (rootLatticeElement H α) h

private theorem root_lattice_to_dual_eq_sum (x : rootLattice H) :
    rootLatticeToDual H x = ∑ i : Fin (finrank K H),
      ((intrinsicRootBasis H).repr x i : K) •
        rootLatticeToDual H (intrinsicRootBasis H i) := by
  have hx := congrArg (rootLatticeToDual H) ((intrinsicRootBasis H).sum_repr x)
  simpa only [map_sum, map_smul, ← Int.cast_smul_eq_zsmul K] using hx.symm

private theorem intrinsic_root_forms_span_eq_top :
    Submodule.span K (Set.range fun i : Fin (finrank K H) =>
      rootLatticeToDual H (intrinsicRootBasis H i)) = ⊤ := by
  apply top_unique
  rw [← RootPairing.IsRootSystem.span_root_eq_top (P := rootSystem H)]
  apply Submodule.span_le.mpr
  rintro _ ⟨α, rfl⟩
  rw [← root_lattice_to_dual_root H α, root_lattice_to_dual_eq_sum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The actual integer root-lattice basis, regarded as a basis of the
Cartan dual over the ground field. -/
noncomputable def intrinsicRootFormBasis :
    Basis (Fin (finrank K H)) K (Dual K H) :=
  basisOfTopLeSpanOfCardEqFinrank
    (fun i => rootLatticeToDual H (intrinsicRootBasis H i))
    (intrinsic_root_forms_span_eq_top H).ge
    (by simp only [Fintype.card_fin, Subspace.dual_finrank_eq])

@[simp] theorem intrinsic_root_form_basis_apply (i : Fin (finrank K H)) :
    intrinsicRootFormBasis H i = rootLatticeToDual H (intrinsicRootBasis H i) := by
  simp only [intrinsicRootFormBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

/-- Scalar extension of the actual lattice basis preserves its integer
coordinates, interpreted in the ground field. -/
theorem intrinsic_root_form_basis_repr_lattice (x : rootLattice H)
    (i : Fin (finrank K H)) :
    (intrinsicRootFormBasis H).repr (rootLatticeToDual H x) i =
      ((intrinsicRootBasis H).repr x i : K) := by
  have hx : (∑ j : Fin (finrank K H),
      ((intrinsicRootBasis H).repr x j : K) • intrinsicRootFormBasis H j) =
      rootLatticeToDual H x := by
    simpa only [intrinsic_root_form_basis_apply] using
      (root_lattice_to_dual_eq_sum H x).symm
  rw [← hx]
  exact congrFun ((intrinsicRootFormBasis H).repr_sum_self
    (fun j => ((intrinsicRootBasis H).repr x j : K))) i

/-- The Cartan basis dual to the constructed actual integer root basis. -/
noncomputable def intrinsicCartanBasis : Basis (Fin (finrank K H)) K H :=
  (intrinsicRootFormBasis H).dualBasis.map (Module.evalEquiv K H).symm

/-- Evaluation on the intrinsic Cartan basis extracts the coefficients in
the intrinsic root-form basis. -/
theorem linear_form_apply_intrinsic_cartan_basis (φ : Dual K H)
    (i : Fin (finrank K H)) :
    φ (intrinsicCartanBasis H i) = (intrinsicRootFormBasis H).repr φ i := by
  simp only [intrinsicCartanBasis, Basis.map_apply, Module.apply_evalEquiv_symm_apply,
    Basis.dualBasis_apply]

/-- In the dual intrinsic Cartan basis, the evaluation vector of every
actual root is literally its intrinsic integer coordinate vector. -/
theorem root_apply_intrinsic_cartan_basis (α : H.root) (i : Fin (finrank K H)) :
    α.val (intrinsicCartanBasis H i) = (intrinsicRootCoordinates H α i : K) := by
  change (rootSystem H).root α (intrinsicCartanBasis H i) = _
  rw [linear_form_apply_intrinsic_cartan_basis, ← root_lattice_to_dual_root H α]
  exact intrinsic_root_form_basis_repr_lattice H (rootLatticeElement H α) i

end CubicAnomaly.Classification.IntrinsicCartanBasis
