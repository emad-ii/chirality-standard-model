import CubicAnomaly.Classification.LieDensity
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Irreducibility for independent ideal actions

Distinct disjoint simple ideals act on their tensor product through its two
separate factors. Lie density turns stability under each ideal into stability
under every endomorphism of that factor. Rank-one endomorphisms then extract
any nonzero tensor coefficient and generate the whole tensor product.

No tensor factorization of another representation, highest weight, or
classification of simple Lie algebras is supplied.
-/

namespace CubicAnomaly.Classification.ExternalTensor

open LieModule Module
open scoped TensorProduct
open CubicAnomaly.Classification.LieDensity

noncomputable section

section Linear

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

private def leftTensorStabilizer (U : Submodule K (M ⊗[K] N)) :
    Subalgebra K (Module.End K M) where
  carrier := {f | ∀ z ∈ U, f.rTensor N z ∈ U}
  zero_mem' := by intro z hz; simp
  one_mem' := by
    intro z hz
    change (LinearMap.id : Module.End K M).rTensor N z ∈ U
    simpa using hz
  add_mem' := by
    intro f g hf hg z hz
    simpa only [LinearMap.rTensor_add, LinearMap.add_apply] using U.add_mem (hf z hz) (hg z hz)
  mul_mem' := by
    intro f g hf hg z hz
    simpa only [LinearMap.rTensor_mul, Module.End.mul_apply] using hf _ (hg z hz)
  algebraMap_mem' := by
    intro c z hz
    change (c • (LinearMap.id : Module.End K M)).rTensor N z ∈ U
    simpa only [LinearMap.rTensor_smul, LinearMap.rTensor_id, LinearMap.smul_apply,
      LinearMap.id_apply] using U.smul_mem c hz

private def rightTensorStabilizer (U : Submodule K (M ⊗[K] N)) :
    Subalgebra K (Module.End K N) where
  carrier := {f | ∀ z ∈ U, f.lTensor M z ∈ U}
  zero_mem' := by intro z hz; simp
  one_mem' := by
    intro z hz
    change (LinearMap.id : Module.End K N).lTensor M z ∈ U
    simpa using hz
  add_mem' := by
    intro f g hf hg z hz
    simpa only [LinearMap.lTensor_add, LinearMap.add_apply] using U.add_mem (hf z hz) (hg z hz)
  mul_mem' := by
    intro f g hf hg z hz
    simpa only [LinearMap.lTensor_mul, Module.End.mul_apply] using hf _ (hg z hz)
  algebraMap_mem' := by
    intro c z hz
    change (c • (LinearMap.id : Module.End K N)).lTensor M z ∈ U
    simpa only [LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.smul_apply,
      LinearMap.id_apply] using U.smul_mem c hz

/-- Separate stability under every factor endomorphism leaves only the
zero and whole tensor-product subspaces. No finite-dimensional hypothesis
is needed for this coefficient-extraction argument. -/
theorem tensor_submodule_eq_bot_or_top_of_end_stable
    (U : Submodule K (M ⊗[K] N))
    (hleft : ∀ f : Module.End K M, ∀ z ∈ U, f.rTensor N z ∈ U)
    (hright : ∀ f : Module.End K N, ∀ z ∈ U, f.lTensor M z ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  let b := Module.Free.chooseBasis K M
  let c := Module.Free.chooseBasis K N
  let d := b.tensorProduct c
  obtain ⟨ij, hij⟩ : ∃ ij, d.repr z ij ≠ 0 := by
    by_contra! h
    apply hz0
    apply d.repr.injective
    ext ij
    simpa using h ij
  have hpure (m : M) (n : N) : m ⊗ₜ[K] n ∈ U := by
    let A : Module.End K M := (b.coord ij.1).smulRight m
    let B : Module.End K N := (c.coord ij.2).smulRight n
    have hmap : TensorProduct.map A B = (d.coord ij).smulRight (m ⊗ₜ[K] n) := by
      rcases ij with ⟨i, j⟩
      ext x y
      simp [A, B, d, Module.Basis.coord_apply, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul, smul_smul, mul_comm]
    have hm : TensorProduct.map A B z ∈ U := by
      rw [← LinearMap.lTensor_comp_rTensor]
      exact hright B _ (hleft A z hz)
    rw [hmap] at hm
    exact (U.smul_mem_iff hij).mp hm
  apply Submodule.eq_top_iff'.mpr
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact U.zero_mem
  | tmul m n => exact hpure m n
  | add x y hx hy => exact U.add_mem hx hy

/-- Tensor products of nonzero vector spaces are nonzero, witnessed by
actual pure tensors and actual dual coordinate functionals. -/
theorem tensor_product_nontrivial [Nontrivial M] [Nontrivial N] :
    Nontrivial (M ⊗[K] N) := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨n, hn⟩ := exists_ne (0 : N)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hm
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one K hn
  refine ⟨⟨m ⊗ₜ[K] n, 0, ?_⟩⟩
  intro hzero
  have h := congrArg (TensorProduct.dualDistrib K M N (f ⊗ₜ[K] g)) hzero
  exact one_ne_zero (by
    simpa only [TensorProduct.dualDistrib_apply, hf, hg, one_mul, map_zero] using h)

end Linear

section Ideals

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- Disjoint ideals commute inside their actual ambient Lie algebra. -/
theorem disjoint_ideal_bracket_eq_zero (I J : LieIdeal K L) (hIJ : Disjoint I J)
    (x : I) (y : J) : ⁅(x : L), (y : L)⁆ = 0 := by
  have hm : ⁅(x : L), (y : L)⁆ ∈ I ⊓ J :=
    ⟨lie_mem_left K L I x y x.property, J.lie_mem y.property⟩
  simpa only [hIJ.eq_bot, LieSubmodule.mem_bot] using hm

private theorem left_ideal_tensor_action (I J : LieIdeal K L) (hIJ : Disjoint I J)
    (x : I) :
    (toEnd K I I x).rTensor J = toEnd K L (I ⊗[K] J) (x : L) := by
  ext u v
  have hz : ⁅(x : L), v⁆ = (0 : J) := by
    apply Subtype.ext
    exact disjoint_ideal_bracket_eq_zero I J hIJ x v
  change ⁅x, u⁆ ⊗ₜ[K] v = ⁅(x : L), u⁆ ⊗ₜ[K] v + u ⊗ₜ[K] ⁅(x : L), v⁆
  rw [hz, TensorProduct.tmul_zero, add_zero]
  rfl

private theorem right_ideal_tensor_action (I J : LieIdeal K L) (hIJ : Disjoint I J)
    (y : J) :
    (toEnd K J J y).lTensor I = toEnd K L (I ⊗[K] J) (y : L) := by
  ext u v
  have hz : ⁅(y : L), u⁆ = (0 : I) := by
    apply Subtype.ext
    exact disjoint_ideal_bracket_eq_zero J I hIJ.symm y u
  change u ⊗ₜ[K] ⁅y, v⁆ = ⁅(y : L), u⁆ ⊗ₜ[K] v + u ⊗ₜ[K] ⁅(y : L), v⁆
  rw [hz, TensorProduct.zero_tmul, zero_add]
  rfl

/-- The tensor product of two disjoint simple ideals is irreducible for
the actual diagonal action of the ambient Lie algebra. Only the ideals'
adjoint simplicity and finite-dimensional Lie density are used. -/
theorem disjoint_simple_ideal_tensor_irreducible
    [IsAlgClosed K] [Module.Finite K L]
    (I J : LieIdeal K L) [LieAlgebra.IsSimple K I] [LieAlgebra.IsSimple K J]
    (hIJ : Disjoint I J) : LieModule.IsIrreducible K L (I ⊗[K] J) := by
  letI : Nontrivial I := LieModule.nontrivial_of_isIrreducible K I I
  letI : Nontrivial J := LieModule.nontrivial_of_isIrreducible K J J
  letI : Nontrivial (I ⊗[K] J) := tensor_product_nontrivial (K := K) (M := I) (N := J)
  apply LieModule.IsIrreducible.mk
  intro U hU
  have hleft : leftTensorStabilizer U.toSubmodule = ⊤ := by
    apply subalgebra_eq_top_of_lie_action_mem (K := K) (L := I) (M := I)
    intro x z hz
    rw [left_ideal_tensor_action I J hIJ]
    exact U.lie_mem hz
  have hright : rightTensorStabilizer U.toSubmodule = ⊤ := by
    apply subalgebra_eq_top_of_lie_action_mem (K := K) (L := J) (M := J)
    intro y z hz
    rw [right_ideal_tensor_action I J hIJ]
    exact U.lie_mem hz
  rcases tensor_submodule_eq_bot_or_top_of_end_stable U.toSubmodule
      (fun f => show f ∈ leftTensorStabilizer U.toSubmodule from by rw [hleft]; trivial)
      (fun f => show f ∈ rightTensorStabilizer U.toSubmodule from by rw [hright]; trivial)
    with hbot | htop
  · exact (hU (LieSubmodule.toSubmodule_injective hbot)).elim
  · exact LieSubmodule.toSubmodule_injective htop

end Ideals

end

end CubicAnomaly.Classification.ExternalTensor
