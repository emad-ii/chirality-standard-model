import CubicAnomaly.Classification.TraceReshuffle
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Highest vectors in the defining module's tensor square

For the classical constituent lemma, work in the flip eigenspaces of the
ordinary tensor square over a field of characteristic zero. Starting with a
highest vector and its simple-root string, construct the vectors at weights
`2λ`, `2λ-αᵢ`, and `2λ-3αᵢ`. All three are nonzero. Their weights are tested
on arbitrary Cartan elements, and their highest-vector equations are tested
both on the raising element of the string and on other raising elements
commuting with its lowering element.
-/

namespace CubicAnomaly.Classification.ClassicalConstituents

open LieModule
open scoped TensorProduct

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

private theorem square_ne_zero {v : M} (hv : v ≠ 0) : v ⊗ₜ[K] v ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv
  intro hz
  have he := congrArg (fun t : M ⊗[K] M => (TensorProduct.lid K M) ((φ.rTensor M) t)) hz
  exact hv (by simpa [hφ] using he)

/-- The symmetric Cartan square vector used for the symplectic defining module. -/
theorem symmetric_square_highest_vector (v : M) (hv : v ≠ 0) :
    v ⊗ₜ[K] v ≠ 0 ∧ TensorProduct.comm K M M (v ⊗ₜ[K] v) = v ⊗ₜ[K] v ∧
    (∀ x : L, ∀ μ : K, ⁅x, v⁆ = μ • v → ⁅x, v ⊗ₜ[K] v⁆ = (2 * μ) • (v ⊗ₜ[K] v)) ∧
    (∀ x : L, ⁅x, v⁆ = 0 → ⁅x, v ⊗ₜ[K] v⁆ = 0) := by
  refine ⟨square_ne_zero hv, rfl, ?_, ?_⟩
  · intro x μ hx
    rw [TensorProduct.LieModule.lie_tmul_right, hx, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, ← add_smul, two_mul]
  · intro x hx
    simp [hx]

/-- Antisymmetrization of a pure tensor. -/
def alternatingTensor (K : Type*) [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    (v w : M) : M ⊗[K] M := v ⊗ₜ[K] w - w ⊗ₜ[K] v

private theorem flip_alt (v w : M) :
    TensorProduct.comm K M M (alternatingTensor K v w) = -alternatingTensor K v w := by
  simp [alternatingTensor]

private theorem act_alt (x : L) (v w : M) :
    ⁅x, alternatingTensor K v w⁆ =
      alternatingTensor K ⁅x, v⁆ w + alternatingTensor K v ⁅x, w⁆ := by
  simp only [alternatingTensor, lie_sub, TensorProduct.LieModule.lie_tmul_right]
  abel

private theorem alt_weight (x : L) {v w : M} {a b : K}
    (hv : ⁅x, v⁆ = a • v) (hw : ⁅x, w⁆ = b • w) :
    ⁅x, alternatingTensor K v w⁆ = (a + b) • alternatingTensor K v w := by
  rw [act_alt, hv, hw]
  simp only [alternatingTensor, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_sub,
    add_smul]
  abel

private theorem lower_weight (x f : L) {v : M} {μ α : K}
    (hv : ⁅x, v⁆ = μ • v) (hf : ⁅x, f⁆ = -(α • f)) (n : ℕ) :
    ⁅x, (toEnd K L M f ^ n) v⁆ = (μ - n * α) • ((toEnd K L M f ^ n) v) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, leibniz_lie, hf, neg_lie, smul_lie,
      ih, lie_smul, ← neg_smul, ← add_smul]
    congr 1
    push_cast
    ring

private theorem lower_annihilated (x f : L) {v : M} (hv : ⁅x, v⁆ = 0) (hf : ⁅x, f⁆ = 0)
    (n : ℕ) : ⁅x, (toEnd K L M f ^ n) v⁆ = 0 := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, leibniz_lie, hf, zero_lie, ih,
      lie_zero, add_zero]

section Strings

variable [CharZero K] {h e f : L} {v : M} {m : ℕ} {t : IsSl2Triple h e f}
local notation "F" n => ((toEnd K L M f) ^ n) v

/-- The vector at the first lowering step is an alternating highest vector.
The Cartan and commuting-raising-element formulas give all the other
Chevalley-generator equations. -/
theorem alternating_square_first_highest_vector (P : t.HasPrimitiveVectorWith v (m : K))
    (hm : 1 ≤ m) :
    let z := alternatingTensor K v (F 1)
    z ≠ 0 ∧ TensorProduct.comm K M M z = -z ∧ ⁅e, z⁆ = 0 ∧
    (∀ x : L, ∀ μ α : K, ⁅x, v⁆ = μ • v → ⁅x, f⁆ = -(α • f) →
      ⁅x, z⁆ = (2 * μ - α) • z) ∧
    (∀ x : L, ⁅x, v⁆ = 0 → ⁅x, f⁆ = 0 → ⁅x, z⁆ = 0) := by
  dsimp only
  have he₁ : ⁅e, F 1⁆ = (m : K) • v := by simpa using P.lie_e_pow_succ_toEnd_f 0
  refine ⟨?_, flip_alt _ _, ?_, ?_, ?_⟩
  · intro hz
    have he := congrArg (LinearMap.rTensor M (toEnd K L M e)) hz
    have hm' : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp [-pow_one, alternatingTensor, P.lie_e, he₁, ← TensorProduct.smul_tmul',
      hm', square_ne_zero (K := K) P.ne_zero] at he
  · simp [-pow_one, alternatingTensor, P.lie_e, he₁, ← TensorProduct.smul_tmul']
  · intro x μ α hx hf
    rw [alt_weight x hx (lower_weight x f hx hf 1)]
    congr 1
    push_cast
    ring
  · intro x hx hf
    simp [-pow_one, alternatingTensor, hx, lower_annihilated x f hx hf 1]

/-- The paper's level-three vector inside the ordinary tensor square. -/
def thirdAlternatingVector (K : Type*) [Field K] {L M : Type*} [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] (f : L) (v : M)
    (m : ℕ) : M ⊗[K] M :=
  (m : K) • alternatingTensor K v ((toEnd K L M f ^ 3) v) -
    (3 * ((m : K) - 2)) • alternatingTensor K ((toEnd K L M f ^ 1) v) ((toEnd K L M f ^ 2) v)

/-- The third step of a string of length at least three gives a second
nonzero alternating highest vector. -/
theorem alternating_square_third_highest_vector (P : t.HasPrimitiveVectorWith v (m : K))
    (hm : 3 ≤ m) :
    let z := thirdAlternatingVector K f v m
    z ≠ 0 ∧ TensorProduct.comm K M M z = -z ∧ ⁅e, z⁆ = 0 ∧
    (∀ x : L, ∀ μ α : K, ⁅x, v⁆ = μ • v → ⁅x, f⁆ = -(α • f) →
      ⁅x, z⁆ = (2 * μ - 3 * α) • z) ∧
    (∀ x : L, ⁅x, v⁆ = 0 → ⁅x, f⁆ = 0 → ⁅x, z⁆ = 0) := by
  dsimp only
  have he₁ : ⁅e, F 1⁆ = (m : K) • v := by simpa using P.lie_e_pow_succ_toEnd_f 0
  have he₂ : ⁅e, F 2⁆ = (2 * ((m : K) - 1)) • (F 1) := by
    convert P.lie_e_pow_succ_toEnd_f 1 using 1
    norm_num
  have he₃ : ⁅e, F 3⁆ = (3 * ((m : K) - 2)) • (F 2) := by
    convert P.lie_e_pow_succ_toEnd_f 2 using 1
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    let E := (toEnd K L M e).rTensor M
    have he := congrArg (fun z : M ⊗[K] M => E (E (E z))) hz
    have hm₀ : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm₁ : (m : K) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show m ≠ 1 by omega))
    have hm₂ : (m : K) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show m ≠ 2 by omega))
    simp [-pow_one, E, thirdAlternatingVector, alternatingTensor, P.lie_e, he₁, he₂, he₃,
      ← TensorProduct.smul_tmul', hm₀, hm₁, hm₂, square_ne_zero (K := K) P.ne_zero] at he
  · simp only [thirdAlternatingVector, map_sub, map_smul, flip_alt, smul_neg]
    abel
  · simp only [thirdAlternatingVector, lie_sub, lie_smul, TensorProduct.LieModule.lie_tmul_right, P.lie_e, he₁, he₂, he₃,
      alternatingTensor, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    module
  · intro x μ α hx hf
    rw [thirdAlternatingVector, lie_sub, lie_smul, lie_smul,
      alt_weight x hx (lower_weight x f hx hf 3),
      alt_weight x (lower_weight x f hx hf 1) (lower_weight x f hx hf 2)]
    push_cast
    module
  · intro x hx hf
    simp [-pow_one, thirdAlternatingVector, alternatingTensor, hx, lower_annihilated x f hx hf]

/-- Lower in two mutually orthogonal root directions. A label of two at
the second node gives a symmetric level-two vector. Lowering antisymmetrically
at the first node produces a new highest vector in the alternating square. -/
theorem alternating_square_two_node_vector {h' e' p : L} {t' : IsSl2Triple h' e' p}
    (P : t.HasPrimitiveVectorWith v (2 : K)) (P' : t'.HasPrimitiveVectorWith v (2 : K))
    (hcross : ⁅e, p⁆ = 0) (hcross' : ⁅e', f⁆ = 0) (horth : ⁅h', f⁆ = 0) :
    ∃ z : M ⊗[K] M, z ≠ 0 ∧ TensorProduct.comm K M M z = -z ∧
      ⁅e, z⁆ = 0 ∧ ⁅e', z⁆ = 0 ∧
      (∀ x : L, ∀ μ α β : K, ⁅x, v⁆ = μ • v → ⁅x, f⁆ = -(α • f) →
        ⁅x, p⁆ = -(β • p) → ⁅x, z⁆ = (2 * μ - 2 * α - β) • z) ∧
      ∀ x : L, ⁅x, v⁆ = 0 → ⁅x, f⁆ = 0 → ⁅x, p⁆ = 0 → ⁅x, z⁆ = 0 := by
  let u := ⁅f, v⁆
  let w := ⁅f, u⁆
  let z := alternatingTensor K ⁅p, v⁆ w + alternatingTensor K ⁅p, w⁆ v -
    alternatingTensor K ⁅p, u⁆ u
  have eu : ⁅e, u⁆ = (2 : K) • v := by simpa [u] using P.lie_e_pow_succ_toEnd_f 0
  have ew : ⁅e, w⁆ = (2 : K) • u := by
    convert P.lie_e_pow_succ_toEnd_f 1 using 1
    norm_num [u, w, pow_succ', Module.End.mul_apply]
  have ku : ⁅e', u⁆ = 0 := by simp [u, leibniz_lie, hcross', P'.lie_e]
  have kw : ⁅e', w⁆ = 0 := by simp [w, leibniz_lie, hcross', ku]
  have hu : ⁅h', u⁆ = (2 : K) • u := by simp [u, leibniz_lie, horth, P'.lie_h]
  have hw : ⁅h', w⁆ = (2 : K) • w := by simp [w, leibniz_lie, horth, hu]
  have kp {y : M} (hy : ⁅e', y⁆ = 0) (hh : ⁅h', y⁆ = (2 : K) • y) :
      ⁅e', ⁅p, y⁆⁆ = (2 : K) • y := by rw [leibniz_lie, t'.lie_e_f, hh, hy, lie_zero, add_zero]
  have ep (y : M) : ⁅e, ⁅p, y⁆⁆ = ⁅p, ⁅e, y⁆⁆ := by rw [leibniz_lie, hcross, zero_lie, zero_add]
  refine ⟨z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    let E := (toEnd K L M e).rTensor M
    let E' := (toEnd K L M e').rTensor M
    have hh := congrArg (fun s => E (E (E' s))) hz
    simp [z, E, E', alternatingTensor, kp P'.lie_e P'.lie_h, kp ku hu, kp kw hw, ku, kw,
      P'.lie_e, P.lie_e, eu, ew, ← TensorProduct.smul_tmul', square_ne_zero (K := K) P.ne_zero] at hh
  · simp only [z, map_sub, map_add, flip_alt]
    abel
  · simp only [z, lie_add, lie_sub, TensorProduct.LieModule.lie_tmul_right, ep, ew, eu, P.lie_e, lie_zero, lie_smul,
      alternatingTensor, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    module
  · simp only [z, lie_add, lie_sub, TensorProduct.LieModule.lie_tmul_right, kp P'.lie_e P'.lie_h, kp ku hu, kp kw hw,
      P'.lie_e, ku, kw, alternatingTensor, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    module
  · intro x μ α β hv hf hp
    have lower (l : L) (γ : K) (hl : ⁅x, l⁆ = -(γ • l)) {y : M} {ν : K}
        (hy : ⁅x, y⁆ = ν • y) : ⁅x, ⁅l, y⁆⁆ = (ν - γ) • ⁅l, y⁆ := by
      rw [leibniz_lie, hl, neg_lie, smul_lie, hy, lie_smul]
      module
    have huv := lower f α hf hv
    have hwv := lower f α hf huv
    change ⁅x, u⁆ = _ at huv
    change ⁅x, w⁆ = _ at hwv
    simp only [z, lie_sub, lie_add, alt_weight x (lower p β hp hv) hwv,
      alt_weight x (lower p β hp hwv) hv, alt_weight x (lower p β hp huv) huv]
    module
  · intro x hv hf hp
    have kill {y : M} (hy : ⁅x, y⁆ = 0) (l : L) (hl : ⁅x, l⁆ = 0) :
        ⁅x, ⁅l, y⁆⁆ = 0 := by rw [leibniz_lie, hl, zero_lie, hy, lie_zero, add_zero]
    have huv := kill hv f hf
    have hwv := kill huv f hf
    change ⁅x, u⁆ = _ at huv
    change ⁅x, w⁆ = _ at hwv
    simp [z, alternatingTensor, hv, huv, hwv, kill hv p hp, kill huv p hp, kill hwv p hp]

end Strings

section FormOperators

variable [FiniteDimensional K M]

/-- Use the actual invariant form to identify the tensor square with
endomorphisms, with the diagonal and commutator actions, respectively. -/
noncomputable def formTensorEndEquiv (β : LinearMap.BilinForm K M)
    (hβ : β.Nondegenerate) (hInv : β.lieInvariant L) :
    (M ⊗[K] M) ≃ₗ⁅K,L⁆ Module.End K M :=
  let D : M ≃ₗ⁅K,L⁆ Module.Dual K M := {
    β.toDual hβ with
    map_lie' := by intro x v; exact LinearMap.ext (hInv x v) }
  (IdealTensorDuality.tensorLieEquiv D (LieModuleEquiv.refl (R := K) (L := L) (M := M))).trans
    TraceReshuffle.dualTensorEndLieEquiv

/-- A pure tensor acts by the corresponding rank-one endomorphism. -/
@[simp] theorem form_tensor_end_equiv_tmul (β : LinearMap.BilinForm K M)
    (hβ : β.Nondegenerate) (hInv : β.lieInvariant L) (a b u : M) :
    formTensorEndEquiv β hβ hInv (a ⊗ₜ[K] b) u = β a u • b := rfl

private theorem form_tensor_flip_pair (β : LinearMap.BilinForm K M)
    (hβ : β.Nondegenerate) (hInv : β.lieInvariant L) (ε : K)
    (hε : ∀ a b, β a b = ε * β b a) (z : M ⊗[K] M) (u w : M) :
    β (formTensorEndEquiv β hβ hInv (TensorProduct.comm K M M z) u) w =
      ε * β u (formTensorEndEquiv β hβ hInv z w) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb, mul_add]
  | tmul a b =>
    simp only [TensorProduct.comm_tmul, form_tensor_end_equiv_tmul,
      map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hε b u]
    ring

/-- The orthogonal form (sign `+1`) selects the alternating tensor square,
and the symplectic form (sign `-1`) selects the symmetric tensor square.
This equivalence tests membership in the actual form-preserving algebra. -/
theorem form_tensor_mem_skew_adjoint_iff (β : LinearMap.BilinForm K M)
    (hβ : β.Nondegenerate) (hInv : β.lieInvariant L) (ε : K) (h₀ : ε ≠ 0)
    (hε : ∀ a b, β a b = ε * β b a) (z : M ⊗[K] M) :
    formTensorEndEquiv β hβ hInv z ∈ skewAdjointLieSubalgebra β ↔
      TensorProduct.comm K M M z = (-ε) • z := by
  rw [show (formTensorEndEquiv β hβ hInv z ∈ skewAdjointLieSubalgebra β) ↔ _ from
    LinearMap.mem_skewAdjointSubmodule (B := β) _]
  change (∀ u w, β (formTensorEndEquiv β hβ hInv z u) w =
    β u (-(formTensorEndEquiv β hβ hInv z w))) ↔ _
  constructor
  · intro hz
    apply (formTensorEndEquiv β hβ hInv).injective
    ext u
    apply sub_eq_zero.mp
    apply hβ.1
    intro w
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      form_tensor_flip_pair β hβ hInv ε hε, hz u w, map_neg]
    ring
  · intro hz u w
    have h := form_tensor_flip_pair β hβ hInv ε hε z u w
    rw [hz] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, neg_mul] at h
    rw [map_neg]
    apply mul_left_cancel₀ h₀
    rw [mul_neg, ← h, neg_neg]

end FormOperators

end CubicAnomaly.Classification.ClassicalConstituents
