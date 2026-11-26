import CubicAnomaly.Classification.AdjointTraceForms
import CubicAnomaly.Classification.TensorEndomorphisms
import CubicAnomaly.Classification.ExternalTensor
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.RingTheory.Flat.Basic

/-!
# Actual tensor blocks of opposite adjoint parity

An actual ideal action in one tensor factor and a trace-zero self-adjoint
operator in the other give an equivariant block of operators preserving
the actual tensor bilinear form. A faithful ideal action makes this block
injective. Atomic ideals in a Killing Lie algebra make its source
self-dual through the derived Killing and trace forms.

Both factor orders are constructed. No decomposition of a defining
representation or factorization of a form is supplied to these maps.
-/

namespace CubicAnomaly.Classification.TensorParityBlocks

open Module LieModule
open CubicAnomaly.Classification.AdjointTraceForms
open CubicAnomaly.Classification.TensorEndomorphisms
open CubicAnomaly.Classification.IdealTensorDuality
open CubicAnomaly.Classification.ExternalTensor
open scoped TensorProduct

noncomputable section

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- Restriction of the actual defining action to an actual ideal is
equivariant for the ambient adjoint and endomorphism actions. -/
def idealActionModuleHom (I : LieIdeal K L) : I →ₗ⁅K,L⁆ Module.End K M where
  __ := (toEnd K L M).toLinearMap.comp I.incl.toLinearMap
  map_lie' := by
    intro x y
    change toEnd K L M ⁅x, (y : L)⁆ = ⁅x, toEnd K L M (y : L)⁆
    rw [LieHom.map_lie]
    rfl

@[simp] theorem ideal_action_module_hom_apply (I : LieIdeal K L) (x : I) :
    idealActionModuleHom (M := M) I x = toEnd K L M (x : L) := rfl

variable [FiniteDimensional K M] [FiniteDimensional K N]

/-- The actual left ideal/trace-zero self-adjoint block in the tensor
endomorphism representation. -/
def leftParityBlock (I : LieIdeal K L) (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L) :
    I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hγ →ₗ⁅K,L⁆ Module.End K (M ⊗[K] N) :=
  (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).toLieModuleHom.comp
    (TensorProduct.LieModule.map (idealActionModuleHom (M := M) I)
      (traceZeroSelfAdjointLieSubmodule γ hγ).incl)

/-- The actual right trace-zero self-adjoint/ideal block. -/
def rightParityBlock (I : LieIdeal K L) (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L) :
    traceZeroSelfAdjointLieSubmodule β hβ ⊗[K] I →ₗ⁅K,L⁆ Module.End K (M ⊗[K] N) :=
  (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).toLieModuleHom.comp
    (TensorProduct.LieModule.map (traceZeroSelfAdjointLieSubmodule β hβ).incl
      (idealActionModuleHom (M := N) I))

/-- The left block has its literal expected pure-tensor operator. -/
@[simp] theorem left_parity_block_tmul (I : LieIdeal K L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L)
    (x : I) (p : traceZeroSelfAdjointLieSubmodule γ hγ) :
    leftParityBlock (M := M) I γ hγ (x ⊗ₜ[K] p) =
      TensorProduct.map (toEnd K L M (x : L)) (p : Module.End K N) := by
  change tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)
    (toEnd K L M (x : L) ⊗ₜ[K] (p : Module.End K N)) = _
  exact tensor_endomorphism_equiv_tmul _ _

/-- The right block has its literal expected pure-tensor operator. -/
@[simp] theorem right_parity_block_tmul (I : LieIdeal K L)
    (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L)
    (p : traceZeroSelfAdjointLieSubmodule β hβ) (x : I) :
    rightParityBlock (N := N) I β hβ (p ⊗ₜ[K] x) =
      TensorProduct.map (p : Module.End K M) (toEnd K L N (x : L)) := by
  change tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)
    ((p : Module.End K M) ⊗ₜ[K] toEnd K L N (x : L)) = _
  exact tensor_endomorphism_equiv_tmul _ _

/-- The actual left block loses no tensor when the ideal acts faithfully
on the left defining factor. -/
theorem left_parity_block_injective (I : LieIdeal K L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L)
    (hI : Function.Injective (fun x : I => toEnd K L M (x : L))) :
    Function.Injective (leftParityBlock (M := M) I γ hγ) := by
  exact (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).injective.comp
    (TensorProduct.map_injective_of_flat_flat
      (idealActionModuleHom (M := M) I).toLinearMap
      (traceZeroSelfAdjointLieSubmodule γ hγ).incl.toLinearMap hI
      (LieSubmodule.injective_incl _))

/-- The actual right block is injective when its ideal acts faithfully
on the right defining factor. -/
theorem right_parity_block_injective (I : LieIdeal K L)
    (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L)
    (hI : Function.Injective (fun x : I => toEnd K L N (x : L))) :
    Function.Injective (rightParityBlock (N := N) I β hβ) := by
  exact (tensorEndomorphismEquiv (K := K) (L := L) (M := M) (N := N)).injective.comp
    (TensorProduct.map_injective_of_flat_flat
      (traceZeroSelfAdjointLieSubmodule β hβ).incl.toLinearMap
      (idealActionModuleHom (M := N) I).toLinearMap
      (LieSubmodule.injective_incl _) hI)

/-- Every actual left block operator preserves the actual tensor form. -/
theorem left_parity_block_mem_skewAdjointLieSubalgebra
    (I : LieIdeal K L) (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L)
    (t : I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hγ) :
    leftParityBlock (M := M) I γ hγ t ∈ skewAdjointLieSubalgebra (β.tmul γ) := by
  change leftParityBlock (M := M) I γ hγ t ∈ (β.tmul γ).skewAdjointSubmodule
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (β.tmul γ).skewAdjointSubmodule.zero_mem
  | tmul x p =>
    rw [left_parity_block_tmul]
    apply (LinearMap.mem_skewAdjointSubmodule _).mpr
    intro u v
    change (β.tmul γ) (TensorProduct.map (toEnd K L M (x : L)) (p : Module.End K N) u) v =
      (β.tmul γ) u (-(TensorProduct.map (toEnd K L M (x : L)) (p : Module.End K N) v))
    rw [map_neg]
    exact tensor_skew_self_adjoint_operator β γ _ _ (hβ (x : L))
      ((LinearMap.mem_selfAdjointSubmodule _).mp p.property.1) u v
  | add s t hs ht => simpa only [map_add] using (β.tmul γ).skewAdjointSubmodule.add_mem hs ht

/-- Every actual right block operator preserves the actual tensor form. -/
theorem right_parity_block_mem_skewAdjointLieSubalgebra
    (I : LieIdeal K L) (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L)
    (t : traceZeroSelfAdjointLieSubmodule β hβ ⊗[K] I) :
    rightParityBlock (N := N) I β hβ t ∈ skewAdjointLieSubalgebra (β.tmul γ) := by
  change rightParityBlock (N := N) I β hβ t ∈ (β.tmul γ).skewAdjointSubmodule
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (β.tmul γ).skewAdjointSubmodule.zero_mem
  | tmul p x =>
    rw [right_parity_block_tmul]
    apply (LinearMap.mem_skewAdjointSubmodule _).mpr
    intro u v
    change (β.tmul γ) (TensorProduct.map (p : Module.End K M) (toEnd K L N (x : L)) u) v =
      (β.tmul γ) u (-(TensorProduct.map (p : Module.End K M) (toEnd K L N (x : L)) v))
    rw [map_neg]
    exact tensor_self_adjoint_skew_operator β γ _ _
      ((LinearMap.mem_selfAdjointSubmodule _).mp p.property.1) (hγ (x : L)) u v
  | add s t hs ht => simpa only [map_add] using (β.tmul γ).skewAdjointSubmodule.add_mem hs ht

/-- A nonzero ideal and nonzero trace-zero self-adjoint factor give a
nonzero actual left block under faithful ideal action. -/
theorem left_parity_block_ne_zero (I : LieIdeal K L)
    (γ : LinearMap.BilinForm K N) (hγ : γ.lieInvariant L)
    (hI : Function.Injective (fun x : I => toEnd K L M (x : L))) (hI0 : I ≠ ⊥)
    (hP : traceZeroSelfAdjointLieSubmodule γ hγ ≠ ⊥) :
    leftParityBlock (M := M) I γ hγ ≠ 0 := by
  letI : Nontrivial I := (LieSubmodule.nontrivial_iff_ne_bot K L L).mpr hI0
  letI : Nontrivial (traceZeroSelfAdjointLieSubmodule γ hγ) :=
    (LieSubmodule.nontrivial_iff_ne_bot K L (Module.End K N)).mpr hP
  letI : Nontrivial (I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hγ) := tensor_product_nontrivial
  obtain ⟨t, ht⟩ := exists_ne (0 : I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hγ)
  intro hzero
  apply ht
  apply left_parity_block_injective I γ hγ hI
  rw [hzero]
  rfl

/-- The corresponding nonvanishing statement for the actual right block. -/
theorem right_parity_block_ne_zero (I : LieIdeal K L)
    (β : LinearMap.BilinForm K M) (hβ : β.lieInvariant L)
    (hI : Function.Injective (fun x : I => toEnd K L N (x : L))) (hI0 : I ≠ ⊥)
    (hP : traceZeroSelfAdjointLieSubmodule β hβ ≠ ⊥) :
    rightParityBlock (N := N) I β hβ ≠ 0 := by
  letI : Nontrivial I := (LieSubmodule.nontrivial_iff_ne_bot K L L).mpr hI0
  letI : Nontrivial (traceZeroSelfAdjointLieSubmodule β hβ) :=
    (LieSubmodule.nontrivial_iff_ne_bot K L (Module.End K M)).mpr hP
  letI : Nontrivial (traceZeroSelfAdjointLieSubmodule β hβ ⊗[K] I) := tensor_product_nontrivial
  obtain ⟨t, ht⟩ := exists_ne (0 : traceZeroSelfAdjointLieSubmodule β hβ ⊗[K] I)
  intro hzero
  apply ht
  apply right_parity_block_injective I β hβ hI
  rw [hzero]
  rfl

variable [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

/-- The actual left block source is equivariantly self-dual for an atomic
ideal and an actual nondegenerate reflexive invariant right-factor form.
The required ideal Killing and self-adjoint trace forms are derived. -/
theorem atomic_left_parity_source_self_dual (I : LieIdeal K L) (hI : IsAtom I)
    (γ : LinearMap.BilinForm K N) (hγ : γ.Nondegenerate)
    (hr : LinearMap.IsRefl γ) (hi : γ.lieInvariant L) :
    Nonempty ((I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hi) ≃ₗ⁅K,L⁆
      Module.Dual K (I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hi)) := by
  obtain ⟨eI⟩ := atomic_ideal_self_dual I hI
  obtain ⟨eP⟩ := trace_zero_self_adjoint_self_dual γ hγ hr hi
  exact ⟨tensorSelfDualEquiv eI eP⟩

/-- The actual right block source has the corresponding derived
equivariant self-duality. -/
theorem atomic_right_parity_source_self_dual (I : LieIdeal K L) (hI : IsAtom I)
    (β : LinearMap.BilinForm K M) (hβ : β.Nondegenerate)
    (hr : LinearMap.IsRefl β) (hi : β.lieInvariant L) :
    Nonempty ((traceZeroSelfAdjointLieSubmodule β hi ⊗[K] I) ≃ₗ⁅K,L⁆
      Module.Dual K (traceZeroSelfAdjointLieSubmodule β hi ⊗[K] I)) := by
  obtain ⟨eP⟩ := trace_zero_self_adjoint_self_dual β hβ hr hi
  obtain ⟨eI⟩ := atomic_ideal_self_dual I hI
  exact ⟨tensorSelfDualEquiv eP eI⟩

end

end CubicAnomaly.Classification.TensorParityBlocks
