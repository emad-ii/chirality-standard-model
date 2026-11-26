import CubicAnomaly.Classification.ComplexDefining
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Algebra.Lie.TensorProduct

/-!
# Actual adjoints in complexified tensor commutants

The actual equivariant operators form a complex subalgebra. If the real
generators of a complexified action are skew-Hermitian, this subalgebra
is closed under the actual Hermitian adjoint. The same property holds
on the actual tensor square. Its canonical tensor flip is equivariant,
self-adjoint and involutive.
-/

namespace CubicAnomaly.Classification.TensorUnitary

open Module LieModule
open scoped TensorProduct

noncomputable section

section Commutant

variable {K L U : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup U] [Module K U] [LieRingModule L U] [LieModule K L U]

/-- The actual equivariant endomorphisms, as an associative subalgebra. -/
def equivariantOperatorAlgebra : Subalgebra K (Module.End K U) where
  carrier := {T | ∀ (x : L) (u : U), T ⁅x, u⁆ = ⁅x, T u⁆}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro T S hT hS x u
    simp only [LinearMap.add_apply, lie_add]
    rw [hT x u, hS x u]
  mul_mem' := by
    intro T S hT hS x u
    simp only [Module.End.mul_apply]
    rw [hS x u, hT x (S u)]
  algebraMap_mem' := by intro c x u; simp

/-- A member of the actual commutant is an actual equivariant map. -/
def equivariantOperatorHom (T : Module.End K U)
    (hT : T ∈ equivariantOperatorAlgebra (K := K) (L := L) (U := U)) : U →ₗ⁅K,L⁆ U :=
  { T with map_lie' := by intro x u; exact hT x u }

/-- Every actual equivariant endomorphism belongs to the actual commutant. -/
theorem equivariant_hom_mem (T : U →ₗ⁅K,L⁆ U) :
    T.toLinearMap ∈ equivariantOperatorAlgebra (K := K) (L := L) (U := U) := T.map_lie

/-- Membership in the actual commutant is exactly commutation with each
actual action operator. -/
theorem equivariant_operator_mem_iff_commute (T : Module.End K U) :
    T ∈ equivariantOperatorAlgebra (K := K) (L := L) (U := U) ↔
      ∀ x : L, Commute T (toEnd K L U x) := by
  constructor
  · intro hT x
    apply LinearMap.ext
    intro u
    exact hT x u
  · intro hT x u
    exact LinearMap.congr_fun (hT x).eq u

end Commutant

section Adjoint

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [FiniteDimensional ℂ U]

/-- The adjoint of an operator commuting with a skew-Hermitian operator
commutes with that same actual operator. -/
theorem adjoint_commutes_of_skew_adjoint
    (A : Module.End ℂ U) (hA : A.adjoint = -A)
    (T : Module.End ℂ U) (hT : Commute T A) : Commute T.adjoint A := by
  have h := congrArg star hT.eq
  simp only [star_mul, LinearMap.star_eq_adjoint] at h
  rw [hA, neg_mul, mul_neg, neg_inj] at h
  exact h.symm

variable {l : Type*} [LieRing l] [LieAlgebra ℝ l]
  [LieRingModule (ℂ ⊗[ℝ] l) U] [LieModule ℂ (ℂ ⊗[ℝ] l) U]

/-- Skew-Hermitian real generators make the actual complexified
commutant closed under the actual Hermitian adjoint. -/
theorem complexified_equivariant_adjoint_mem
    (hskew : ∀ x : l, (toEnd ℂ (ℂ ⊗[ℝ] l) U (1 ⊗ₜ[ℝ] x)).adjoint =
      -toEnd ℂ (ℂ ⊗[ℝ] l) U (1 ⊗ₜ[ℝ] x))
    (T : Module.End ℂ U)
    (hT : T ∈ equivariantOperatorAlgebra (K := ℂ) (L := ℂ ⊗[ℝ] l) (U := U)) :
    T.adjoint ∈ equivariantOperatorAlgebra (K := ℂ) (L := ℂ ⊗[ℝ] l) (U := U) := by
  apply (equivariant_operator_mem_iff_commute _).mpr
  have hcomm := (equivariant_operator_mem_iff_commute T).mp hT
  intro z
  change T.adjoint * toEnd ℂ (ℂ ⊗[ℝ] l) U z = toEnd ℂ (ℂ ⊗[ℝ] l) U z * T.adjoint
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    have he : c ⊗ₜ[ℝ] x = c • ((1 : ℂ) ⊗ₜ[ℝ] x) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he, map_smul, mul_smul_comm, smul_mul_assoc]
    exact congrArg (fun A : Module.End ℂ U => c • A)
      (adjoint_commutes_of_skew_adjoint _ (hskew x) T (hcomm _)).eq
  | add z w hz hw => simp only [map_add, mul_add, add_mul, hz, hw]

end Adjoint

section TensorSquare

variable {L W : Type*} [LieRing L] [LieAlgebra ℂ L]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [LieRingModule L W] [LieModule ℂ L W]

/-- The actual diagonal tensor action preserves skew-Hermitian adjoints. -/
theorem tensor_action_adjoint_of_skew (x : L)
    (hx : (toEnd ℂ L W x).adjoint = -toEnd ℂ L W x) :
    (toEnd ℂ L (W ⊗[ℂ] W) x).adjoint = -toEnd ℂ L (W ⊗[ℂ] W) x := by
  have he : toEnd ℂ L (W ⊗[ℂ] W) x =
      (toEnd ℂ L W x).rTensor W + (toEnd ℂ L W x).lTensor W := by
    apply TensorProduct.ext'
    intro u v
    rfl
  rw [he, map_add, LinearMap.adjoint_rTensor, LinearMap.adjoint_lTensor, hx,
    LinearMap.rTensor_neg, LinearMap.lTensor_neg, neg_add]

omit [FiniteDimensional ℂ W] in
/-- The canonical tensor flip is an actual equivariant operator. -/
theorem tensor_flip_mem :
    (TensorProduct.comm ℂ W W).toLinearMap ∈
      equivariantOperatorAlgebra (K := ℂ) (L := L) (U := W ⊗[ℂ] W) := by
  intro x t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp [TensorProduct.LieModule.lie_tmul_right, add_comm]
  | add t s ht hs => simp only [map_add, lie_add, ht, hs]

omit [LieRing L] [LieAlgebra ℂ L] [LieRingModule L W] [LieModule ℂ L W] in
/-- The actual tensor flip is self-adjoint for the canonical tensor
inner product. -/
theorem tensor_flip_adjoint :
    (TensorProduct.comm ℂ W W).toLinearMap.adjoint = (TensorProduct.comm ℂ W W).toLinearMap := by
  apply LinearMap.IsSymmetric.adjoint_eq
  intro z w
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul u' v' => simp only [LinearEquiv.coe_coe, TensorProduct.comm_tmul,
        TensorProduct.inner_tmul, mul_comm]
    | add w t hw ht => simp only [map_add, inner_add_right, hw, ht]
  | add z t hz ht => simp only [map_add, inner_add_left, hz, ht]

omit [FiniteDimensional ℂ W]
    [LieRing L] [LieAlgebra ℂ L] [LieRingModule L W] [LieModule ℂ L W] in
/-- The actual tensor flip squares to the identity operator. -/
theorem tensor_flip_sq :
    (TensorProduct.comm ℂ W W).toLinearMap * (TensorProduct.comm ℂ W W).toLinearMap =
      (1 : Module.End ℂ (W ⊗[ℂ] W)) := by
  apply TensorProduct.ext'
  intro u v
  rfl

end TensorSquare

section ComplexifiedTensor

variable {l W : Type*} [LieRing l] [LieAlgebra ℝ l]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [LieRingModule (ℂ ⊗[ℝ] l) W] [LieModule ℂ (ℂ ⊗[ℝ] l) W]

/-- The actual tensor-square commutant is adjoint-closed when the
original real generators are skew-Hermitian. -/
theorem complexified_tensor_equivariant_adjoint_mem
    (hskew : ∀ x : l, (toEnd ℂ (ℂ ⊗[ℝ] l) W (1 ⊗ₜ[ℝ] x)).adjoint =
      -toEnd ℂ (ℂ ⊗[ℝ] l) W (1 ⊗ₜ[ℝ] x))
    (T : Module.End ℂ (W ⊗[ℂ] W))
    (hT : T ∈ equivariantOperatorAlgebra (K := ℂ) (L := ℂ ⊗[ℝ] l) (U := W ⊗[ℂ] W)) :
    T.adjoint ∈ equivariantOperatorAlgebra (K := ℂ) (L := ℂ ⊗[ℝ] l) (U := W ⊗[ℂ] W) :=
  complexified_equivariant_adjoint_mem (fun x => tensor_action_adjoint_of_skew _ (hskew x)) T hT

end ComplexifiedTensor

section DefiningRepresentation

variable {l W : Type*} [LieRing l] [LieAlgebra ℝ l]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- For the actual scalar-extended defining action, real generators
retain their original skew-Hermitian adjoints. -/
theorem complexified_defining_real_action_skew
    (ρ : l →ₗ⁅ℝ⁆ Module.End ℂ W) (hρ : ∀ x : l, (ρ x).adjoint = -ρ x) (x : l) :
    letI := ComplexDefining.complexifiedDefiningAction ρ
    letI := ComplexDefining.complexified_defining_lieModule ρ
    (toEnd ℂ (ℂ ⊗[ℝ] l) W (1 ⊗ₜ[ℝ] x)).adjoint =
      -toEnd ℂ (ℂ ⊗[ℝ] l) W (1 ⊗ₜ[ℝ] x) := by
  letI := ComplexDefining.complexifiedDefiningAction ρ
  letI := ComplexDefining.complexified_defining_lieModule ρ
  have he : toEnd ℂ (ℂ ⊗[ℝ] l) W (1 ⊗ₜ[ℝ] x) = ρ x := by
    apply LinearMap.ext
    intro w
    change (1 : ℂ) • ρ x w = ρ x w
    exact one_smul _ _
  rw [he]
  exact hρ x

/-- The commutant of the actual tensor-square scalar-extended defining
action is closed under the actual Hermitian adjoint. -/
theorem complexified_defining_tensor_equivariant_adjoint_mem
    (ρ : l →ₗ⁅ℝ⁆ Module.End ℂ W) (hρ : ∀ x : l, (ρ x).adjoint = -ρ x) :
    letI := ComplexDefining.complexifiedDefiningAction ρ
    letI := ComplexDefining.complexified_defining_lieModule ρ
    ∀ T : Module.End ℂ (W ⊗[ℂ] W),
      T ∈ equivariantOperatorAlgebra (K := ℂ) (L := ℂ ⊗[ℝ] l) (U := W ⊗[ℂ] W) →
      T.adjoint ∈ equivariantOperatorAlgebra (K := ℂ) (L := ℂ ⊗[ℝ] l) (U := W ⊗[ℂ] W) := by
  letI := ComplexDefining.complexifiedDefiningAction ρ
  letI := ComplexDefining.complexified_defining_lieModule ρ
  exact complexified_tensor_equivariant_adjoint_mem (complexified_defining_real_action_skew ρ hρ)

end DefiningRepresentation

end

end CubicAnomaly.Classification.TensorUnitary
