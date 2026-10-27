import CubicAnomaly.Classification.ExternalTensor
import CubicAnomaly.Classification.AdjointTraceForms
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Fixed vectors in the surviving tensor block

If an ideal has no fixed vectors in one factor and acts trivially in the
other, their tensor product has no fixed vectors. Dual coordinate
contraction proves this without finite-dimensionality or complete
reducibility. An injective surjective equivariant image inherits the
same obstruction, so commuting operators have zero image in such a
quotient.
-/

namespace CubicAnomaly.Classification.TensorFixedVectors

open Module LieModule
open CubicAnomaly.Classification.AdjointTraceForms
open scoped TensorProduct

noncomputable section

variable {K L M N Q : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [AddCommGroup Q] [Module K Q] [LieRingModule L Q] [LieModule K L Q]

private def rightCoefficient (φ : Module.Dual K N) : M ⊗[K] N →ₗ[K] M :=
  (TensorProduct.rid K M).toLinearMap.comp (φ.lTensor M)

private theorem rightCoefficient_tmul (φ : Module.Dual K N) (m : M) (n : N) :
    rightCoefficient φ (m ⊗ₜ[K] n) = φ n • m := by
  simp [rightCoefficient]

private theorem tensor_eq_zero_of_right_coefficients
    (z : M ⊗[K] N) (hz : ∀ φ : Module.Dual K N, rightCoefficient φ z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis K M
  let c := Module.Free.chooseBasis K N
  let d := b.tensorProduct c
  apply d.repr.injective
  ext ij
  have he : ∀ t : M ⊗[K] N,
      b.coord ij.1 (rightCoefficient (c.coord ij.2) t) = d.repr t ij := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      rcases ij with ⟨i, j⟩
      simp [rightCoefficient_tmul, d, Module.Basis.coord_apply]
    | add t u ht hu => simp only [map_add, Finsupp.add_apply, ht, hu]
  rw [← he, hz]
  simp

/-- Tensoring a module with no fixed vectors by an ideal-trivial factor
introduces no fixed vectors. This uses the actual ambient tensor action
and needs no finite-dimensionality assumption. -/
theorem tensor_fixed_eq_zero
    (I : LieIdeal K L)
    (hM : ∀ m : M, (∀ x : I, ⁅(x : L), m⁆ = 0) → m = 0)
    (hN : ∀ (x : I) (n : N), ⁅(x : L), n⁆ = 0)
    (z : M ⊗[K] N) (hz : ∀ x : I, ⁅(x : L), z⁆ = 0) : z = 0 := by
  apply tensor_eq_zero_of_right_coefficients
  intro φ
  apply hM
  intro x
  have he (t : M ⊗[K] N) :
      rightCoefficient φ ⁅(x : L), t⁆ = ⁅(x : L), rightCoefficient φ t⁆ := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      simp only [TensorProduct.LieModule.lie_tmul_right, map_add,
        rightCoefficient_tmul, hN, map_zero, zero_smul, add_zero, lie_smul]
    | add t u ht hu => simp only [lie_add, map_add, ht, hu]
  rw [← he, hz, map_zero]

/-- The same fixed-vector obstruction with the two tensor factors in
the opposite order. -/
theorem tensor_fixed_eq_zero_right
    (I : LieIdeal K L)
    (hM : ∀ (x : I) (m : M), ⁅(x : L), m⁆ = 0)
    (hN : ∀ n : N, (∀ x : I, ⁅(x : L), n⁆ = 0) → n = 0)
    (z : M ⊗[K] N) (hz : ∀ x : I, ⁅(x : L), z⁆ = 0) : z = 0 := by
  apply (TensorProduct.comm K M N).injective
  rw [map_zero]
  apply tensor_fixed_eq_zero I hN hM
  intro x
  have he (t : M ⊗[K] N) :
      (TensorProduct.comm K M N) ⁅(x : L), t⁆ =
        ⁅(x : L), (TensorProduct.comm K M N) t⁆ := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [TensorProduct.LieModule.lie_tmul_right, add_comm]
    | add t u ht hu => simp only [lie_add, map_add, ht, hu]
  rw [← he, hz, map_zero]

/-- The actual adjoint module of a centerless ideal has no fixed vectors
under that ideal. -/
theorem ideal_adjoint_fixed_eq_zero (I : LieIdeal K L)
    (hI : LieAlgebra.center K I = ⊥)
    (y : I) (hy : ∀ x : I, ⁅(x : L), y⁆ = 0) : y = 0 := by
  have hm : y ∈ LieAlgebra.center K I := by
    rw [LieModule.mem_maxTrivSubmodule]
    intro x
    exact hy x
  simpa only [hI, LieSubmodule.mem_bot] using hm

/-- An ideal's centerless adjoint module tensored with an ideal-trivial
module has no fixed vectors for that ideal. -/
theorem ideal_tensor_fixed_eq_zero (I : LieIdeal K L)
    (hI : LieAlgebra.center K I = ⊥)
    (hN : ∀ (x : I) (n : N), ⁅(x : L), n⁆ = 0)
    (z : I ⊗[K] N) (hz : ∀ x : I, ⁅(x : L), z⁆ = 0) : z = 0 :=
  tensor_fixed_eq_zero I (ideal_adjoint_fixed_eq_zero I hI) hN z hz

/-- Triviality on a defining factor gives triviality on its actual
trace-zero self-adjoint endomorphism module. -/
theorem trace_zero_self_adjoint_ideal_action_eq_zero
    (I : LieIdeal K L) (γ : LinearMap.BilinForm K N) (hiγ : γ.lieInvariant L)
    (hN : ∀ (x : I) (n : N), ⁅(x : L), n⁆ = 0)
    (x : I) (p : traceZeroSelfAdjointLieSubmodule γ hiγ) : ⁅(x : L), p⁆ = 0 := by
  apply Subtype.ext
  ext n
  change ⁅(x : L), (p : Module.End K N) n⁆ - (p : Module.End K N) ⁅(x : L), n⁆ = 0
  rw [hN, hN, map_zero, sub_self]

/-- The surviving ideal/trace-zero-self-adjoint block has no ideal-fixed
vectors. All actions are the actual inherited and diagonal actions. -/
theorem left_parity_source_fixed_eq_zero
    (I : LieIdeal K L) (hI : LieAlgebra.center K I = ⊥)
    (γ : LinearMap.BilinForm K N) (hiγ : γ.lieInvariant L)
    (hN : ∀ (x : I) (n : N), ⁅(x : L), n⁆ = 0)
    (z : I ⊗[K] traceZeroSelfAdjointLieSubmodule γ hiγ)
    (hz : ∀ x : I, ⁅(x : L), z⁆ = 0) : z = 0 :=
  ideal_tensor_fixed_eq_zero I hI
    (trace_zero_self_adjoint_ideal_action_eq_zero I γ hiγ hN) z hz

/-- The right parity block source has the corresponding absence of
fixed vectors for its centerless ideal. -/
theorem right_parity_source_fixed_eq_zero
    (J : LieIdeal K L) (hJ : LieAlgebra.center K J = ⊥)
    (β : LinearMap.BilinForm K M) (hiβ : β.lieInvariant L)
    (hM : ∀ (x : J) (m : M), ⁅(x : L), m⁆ = 0)
    (z : traceZeroSelfAdjointLieSubmodule β hiβ ⊗[K] J)
    (hz : ∀ x : J, ⁅(x : L), z⁆ = 0) : z = 0 :=
  tensor_fixed_eq_zero_right J
    (trace_zero_self_adjoint_ideal_action_eq_zero J β hiβ hM)
    (ideal_adjoint_fixed_eq_zero J hJ) z hz

omit [LieModule K L M] [LieModule K L Q] in
/-- A bijective equivariant map transports the absence of ideal-fixed
vectors. This applies directly to a surviving block's quotient map. -/
theorem fixed_eq_zero_of_bijective
    (I : LieIdeal K L) (f : M →ₗ⁅K,L⁆ Q) (hf : Function.Bijective f)
    (hM : ∀ m : M, (∀ x : I, ⁅(x : L), m⁆ = 0) → m = 0)
    (q : Q) (hq : ∀ x : I, ⁅(x : L), q⁆ = 0) : q = 0 := by
  obtain ⟨m, rfl⟩ := hf.2 q
  have hm : m = 0 := by
    apply hM
    intro x
    apply hf.1
    rw [f.map_lie, hq, map_zero]
  rw [hm, map_zero]

omit [LieModule K L M] [LieModule K L Q] in
/-- An equivariant map from an ideal-trivial module to a module with no
ideal-fixed vectors is zero. This absorbs additional commuting factor
operators once the surviving block fills the quotient. -/
theorem hom_eq_zero_of_trivial_to_no_fixed
    (I : LieIdeal K L)
    (hM : ∀ (x : I) (m : M), ⁅(x : L), m⁆ = 0)
    (hQ : ∀ q : Q, (∀ x : I, ⁅(x : L), q⁆ = 0) → q = 0)
    (f : M →ₗ⁅K,L⁆ Q) : f = 0 := by
  ext m
  apply hQ
  intro x
  rw [← f.map_lie, hM, map_zero]

end

end CubicAnomaly.Classification.TensorFixedVectors
