import CubicAnomaly.Classification.ExternalTensor
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Tensoring with a simple ideal acting trivially on the other factor

If a simple ideal acts trivially on an irreducible ambient module, density
isolates its action on the right tensor factor. Subtracting that right
action from the ambient diagonal action isolates the left factor as well.
Thus the tensor product is irreducible.

In particular, three pairwise disjoint simple ideals have an irreducible
actual tensor product. This supplies the constituent used by odd products
of classical defining actions, without factoring the defining module.
-/

namespace CubicAnomaly.Classification.IdealTensorExtensions

open LieModule Module
open scoped TensorProduct
open CubicAnomaly.Classification.LieDensity
open CubicAnomaly.Classification.ExternalTensor

noncomputable section

private def endStabilizer {K P : Type*} [Field K] [AddCommGroup P] [Module K P]
    (U : Submodule K P) : Subalgebra K (Module.End K P) where
  carrier := {f | ∀ z ∈ U, f z ∈ U}
  zero_mem' := by intro z hz; simp
  one_mem' := by intro z hz; exact hz
  add_mem' := by intro f g hf hg z hz; exact U.add_mem (hf z hz) (hg z hz)
  mul_mem' := by intro f g hf hg z hz; exact hf _ (hg z hz)
  algebraMap_mem' := by intro c z hz; exact U.smul_mem c hz

section Asymmetric

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

private theorem right_ideal_action_of_left_trivial (J : LieIdeal K L)
    (htriv : ∀ x : J, ∀ m : M, ⁅(x : L), m⁆ = 0) (x : J) :
    (toEnd K J J x).lTensor M = toEnd K L (M ⊗[K] J) (x : L) := by
  ext m y
  change m ⊗ₜ[K] ⁅x, y⁆ =
    ⁅(x : L), m⁆ ⊗ₜ[K] y + m ⊗ₜ[K] ⁅(x : L), y⁆
  rw [htriv x m, TensorProduct.zero_tmul, zero_add]
  rfl

/-- Tensoring an irreducible ambient module with a simple ideal acting
trivially on it preserves irreducibility. Both tensor-factor actions are
derived from the actual diagonal action by density and subtraction. -/
theorem tensor_simple_ideal_irreducible_of_trivial_action
    [IsAlgClosed K] [Module.Finite K L] [Module.Finite K M]
    [LieModule.IsIrreducible K L M]
    (J : LieIdeal K L) [LieAlgebra.IsSimple K J]
    (htriv : ∀ x : J, ∀ m : M, ⁅(x : L), m⁆ = 0) :
    LieModule.IsIrreducible K L (M ⊗[K] J) := by
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
  letI : Nontrivial J := LieModule.nontrivial_of_isIrreducible K J J
  letI : Nontrivial (M ⊗[K] J) := tensor_product_nontrivial (K := K) (M := M) (N := J)
  apply LieModule.IsIrreducible.mk
  intro U hU
  let A := (endStabilizer U.toSubmodule).comap (Module.End.lTensorAlgHom K J M)
  have hA : A = ⊤ := by
    apply subalgebra_eq_top_of_lie_action_mem (K := K) (L := J) (M := J)
    intro x
    change ∀ z ∈ U, (toEnd K J J x).lTensor M z ∈ U
    intro z hz
    rw [right_ideal_action_of_left_trivial J htriv]
    exact U.lie_mem hz
  have hright (f : Module.End K J) : ∀ z ∈ U, f.lTensor M z ∈ U := by
    have hf : f ∈ A := by rw [hA]; trivial
    exact hf
  let B := (endStabilizer U.toSubmodule).comap (Module.End.rTensorAlgHom K M J)
  have hB : B = ⊤ := by
    apply subalgebra_eq_top_of_lie_action_mem (K := K) (L := L) (M := M)
    intro x
    change ∀ z ∈ U, (toEnd K L M x).rTensor J z ∈ U
    intro z hz
    have he : (toEnd K L M x).rTensor J z =
        ⁅x, z⁆ - (toEnd K L J x).lTensor M z := by
      change _ = ((toEnd K L M x).rTensor J z +
        (toEnd K L J x).lTensor M z) - (toEnd K L J x).lTensor M z
      exact (add_sub_cancel_right _ _).symm
    rw [he]
    exact U.sub_mem (U.lie_mem hz) (hright (toEnd K L J x) z hz)
  have hleft (f : Module.End K M) : ∀ z ∈ U, f.rTensor J z ∈ U := by
    have hf : f ∈ B := by rw [hB]; trivial
    exact hf
  rcases tensor_submodule_eq_bot_or_top_of_end_stable U.toSubmodule hleft hright with hbot | htop
  · exact (hU (LieSubmodule.toSubmodule_injective hbot)).elim
  · exact LieSubmodule.toSubmodule_injective htop

end Asymmetric

section Triple

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- An ideal disjoint from both tensor factors acts trivially on their
actual tensor product through the ambient diagonal action. -/
theorem disjoint_third_ideal_tensor_action_eq_zero
    (I J T : LieIdeal K L) (hTI : Disjoint T I) (hTJ : Disjoint T J)
    (x : T) (z : I ⊗[K] J) : ⁅(x : L), z⁆ = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact lie_zero _
  | tmul u v =>
    have hu : ⁅(x : L), u⁆ = (0 : I) := by
      apply Subtype.ext
      exact disjoint_ideal_bracket_eq_zero T I hTI x u
    have hv : ⁅(x : L), v⁆ = (0 : J) := by
      apply Subtype.ext
      exact disjoint_ideal_bracket_eq_zero T J hTJ x v
    simp only [TensorProduct.LieModule.lie_tmul_right, hu, hv,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  | add u v hu hv => simp only [lie_add, hu, hv, add_zero]

/-- Three pairwise disjoint simple ideals have an irreducible actual
tensor product for the ambient diagonal action. -/
theorem pairwise_disjoint_simple_ideal_triple_irreducible
    [IsAlgClosed K] [Module.Finite K L]
    (I J T : LieIdeal K L)
    [LieAlgebra.IsSimple K I] [LieAlgebra.IsSimple K J] [LieAlgebra.IsSimple K T]
    (hIJ : Disjoint I J) (hIT : Disjoint I T) (hJT : Disjoint J T) :
    LieModule.IsIrreducible K L ((I ⊗[K] J) ⊗[K] T) := by
  letI := disjoint_simple_ideal_tensor_irreducible I J hIJ
  exact tensor_simple_ideal_irreducible_of_trivial_action T
    (disjoint_third_ideal_tensor_action_eq_zero I J T hIT.symm hJT.symm)

end Triple

end

end CubicAnomaly.Classification.IdealTensorExtensions
