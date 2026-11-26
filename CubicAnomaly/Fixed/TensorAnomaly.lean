import CubicAnomaly.Classification.CartanTrace
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The full cubic of an actual external tensor representation

The action `(x,y) ↦ ρ(x) ⊗ 1 + 1 ⊗ σ(y)` is constructed as a Lie
homomorphism. When both factor actions are traceless, its full symmetric
trace cubic is the dimension-weighted sum of the two factor cubics.
Consequently its radical is determined by the two actual factor radicals,
including every mixed insertion. No classification of either factor is used.
-/

namespace CubicAnomaly.Fixed.TensorAnomaly

open Matrix
open scoped Kronecker
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanTrace

noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The sum of the two factor actions on the actual tensor product basis. -/
def tensorAction (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B

/-- Trace factorization eliminates every mixed cubic term when each
factor generator is traceless. This is the full trilinear identity. -/
theorem tensor_action_trace_cubic
    (A₁ A₂ A₃ : Matrix m m ℂ) (B₁ B₂ B₃ : Matrix n n ℂ)
    (hA₁ : trace A₁ = 0) (hA₂ : trace A₂ = 0) (hA₃ : trace A₃ = 0)
    (hB₁ : trace B₁ = 0) (hB₂ : trace B₂ = 0) (hB₃ : trace B₃ = 0) :
    matrixTraceCubic (tensorAction A₁ B₁) (tensorAction A₂ B₂)
        (tensorAction A₃ B₃) =
      (Fintype.card n : ℂ) * matrixTraceCubic A₁ A₂ A₃ +
        (Fintype.card m : ℂ) * matrixTraceCubic B₁ B₂ B₃ := by
  simp only [matrixTraceCubic, tensorAction, Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_kronecker,
    one_mul, mul_one, Matrix.trace_one, hA₁, hA₂, hA₃, hB₁, hB₂, hB₃,
    mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- The trace of the tensor action is the dimension-weighted sum of traces. -/
theorem tensor_action_trace (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    trace (tensorAction A B) =
      (Fintype.card n : ℂ) * trace A + (Fintype.card m : ℂ) * trace B := by
  simp [tensorAction, Matrix.trace_kronecker, mul_comm]

/-- A separate type for the direct product Lie algebra, with its literal
componentwise bracket. -/
def ProductLie (L K : Type*) := L × K

instance {L K : Type*} [AddCommGroup L] [AddCommGroup K] :
    AddCommGroup (ProductLie L K) := inferInstanceAs (AddCommGroup (L × K))

instance {R L K : Type*} [CommRing R] [AddCommGroup L] [AddCommGroup K]
    [Module R L] [Module R K] : Module R (ProductLie L K) :=
  inferInstanceAs (Module R (L × K))

instance {L K : Type*} [LieRing L] [LieRing K] : LieRing (ProductLie L K) where
  bracket x y := (⁅x.1, y.1⁆, ⁅x.2, y.2⁆)
  add_lie x y z := by apply Prod.ext <;> exact add_lie _ _ _
  lie_add x y z := by apply Prod.ext <;> exact lie_add _ _ _
  lie_self x := by apply Prod.ext <;> exact lie_self _
  leibniz_lie x y z := by apply Prod.ext <;> exact leibniz_lie _ _ _

instance {R L K : Type*} [CommRing R] [LieRing L] [LieRing K]
    [LieAlgebra R L] [LieAlgebra R K] : LieAlgebra R (ProductLie L K) where
  lie_smul t x y := by apply Prod.ext <;> exact lie_smul _ _ _

variable {L K : Type*} [LieRing L] [LieRing K] [LieAlgebra ℂ L] [LieAlgebra ℂ K]

/-- Projection to the second ideal of the actual product Lie algebra. -/
def secondProjection : ProductLie L K →ₗ⁅ℂ⁆ K where
  toFun x := x.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := by intros; rfl

/-- The actual external tensor representation, in tensor-product coordinates. -/
def tensorRepresentation (ρ : L →ₗ⁅ℂ⁆ Matrix m m ℂ)
    (σ : K →ₗ⁅ℂ⁆ Matrix n n ℂ) :
    ProductLie L K →ₗ⁅ℂ⁆ Matrix (m × n) (m × n) ℂ where
  toFun x := tensorAction (ρ x.1) (σ x.2)
  map_add' x y := by
    change tensorAction (ρ (x.1 + y.1)) (σ (x.2 + y.2)) = _
    simp only [tensorAction, map_add, Matrix.add_kronecker, Matrix.kronecker_add]
    abel
  map_smul' t x := by
    change tensorAction (ρ (t • x.1)) (σ (t • x.2)) =
      t • tensorAction (ρ x.1) (σ x.2)
    simp only [tensorAction, map_smul, Matrix.smul_kronecker,
      Matrix.kronecker_smul, smul_add]
  map_lie' := by
    intro x y
    change tensorAction (ρ ⁅x.1, y.1⁆) (σ ⁅x.2, y.2⁆) =
      ⁅tensorAction (ρ x.1) (σ x.2), tensorAction (ρ y.1) (σ y.2)⁆
    simp only [tensorAction, LieHom.map_lie, Ring.lie_def, sub_eq_add_neg,
      Matrix.add_kronecker, Matrix.kronecker_add, Matrix.mul_add, Matrix.add_mul,
      ← Matrix.mul_kronecker_mul, one_mul, mul_one]
    ext i j
    simp only [Matrix.kroneckerMap, Matrix.of_apply, Matrix.add_apply, Matrix.neg_apply]
    ring

/-- The constructed tensor action has the dimension-weighted full cubic. -/
theorem tensor_representation_cubic
    (ρ : L →ₗ⁅ℂ⁆ Matrix m m ℂ) (σ : K →ₗ⁅ℂ⁆ Matrix n n ℂ)
    (hρ : ∀ x, trace (ρ x) = 0) (hσ : ∀ y, trace (σ y) = 0)
    (x y z : ProductLie L K) :
    matrixTraceCubic (tensorRepresentation ρ σ x)
        (tensorRepresentation ρ σ y) (tensorRepresentation ρ σ z) =
      (Fintype.card n : ℂ) * matrixTraceCubic (ρ x.1) (ρ y.1) (ρ z.1) +
        (Fintype.card m : ℂ) * matrixTraceCubic (σ x.2) (σ y.2) (σ z.2) :=
  tensor_action_trace_cubic _ _ _ _ _ _ (hρ _) (hρ _) (hρ _) (hσ _) (hσ _) (hσ _)

/-- The full radical of the actual tensor representation is the product
of the two factor radicals, provided both factor spaces are nonzero. -/
theorem mem_tensor_representation_radical_iff [Nonempty m] [Nonempty n]
    (ρ : L →ₗ⁅ℂ⁆ Matrix m m ℂ) (σ : K →ₗ⁅ℂ⁆ Matrix n n ℂ)
    (hρ : ∀ x, trace (ρ x) = 0) (hσ : ∀ y, trace (σ y) = 0)
    (x : ProductLie L K) :
    x ∈ complexTraceRadical (tensorRepresentation ρ σ) ↔
      x.1 ∈ complexTraceRadical ρ ∧ x.2 ∈ complexTraceRadical σ := by
  simp only [complexTraceRadical, mem_radical_iff]
  change (∀ y z : ProductLie L K,
    matrixTraceCubic (tensorRepresentation ρ σ x)
      (tensorRepresentation ρ σ y) (tensorRepresentation ρ σ z) = 0) ↔
    (∀ y z : L, matrixTraceCubic (ρ x.1) (ρ y) (ρ z) = 0) ∧
      (∀ y z : K, matrixTraceCubic (σ x.2) (σ y) (σ z) = 0)
  have hm : (Fintype.card m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hn : (Fintype.card n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h0m (A : Matrix m m ℂ) : matrixTraceCubic A 0 0 = 0 := by
    simp [matrixTraceCubic]
  have h0n (A : Matrix n n ℂ) : matrixTraceCubic A 0 0 = 0 := by
    simp [matrixTraceCubic]
  constructor
  · intro hx
    constructor
    · intro y z
      have h := hx (y, 0) (z, 0)
      rw [tensor_representation_cubic ρ σ hρ hσ] at h
      change (Fintype.card n : ℂ) * matrixTraceCubic (ρ x.1) (ρ y) (ρ z) +
        (Fintype.card m : ℂ) * matrixTraceCubic (σ x.2) (σ 0) (σ 0) = 0 at h
      simp only [map_zero, h0n, mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hn
    · intro y z
      have h := hx (0, y) (0, z)
      rw [tensor_representation_cubic ρ σ hρ hσ] at h
      change (Fintype.card n : ℂ) * matrixTraceCubic (ρ x.1) (ρ 0) (ρ 0) +
        (Fintype.card m : ℂ) * matrixTraceCubic (σ x.2) (σ y) (σ z) = 0 at h
      simp only [map_zero, h0m, mul_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hm
  · rintro ⟨hleft, hright⟩ y z
    rw [tensor_representation_cubic ρ σ hρ hσ, hleft, hright]
    simp

/-- An anomaly-free left factor and a nondegenerate right cubic make the
full tensor radical exactly the actual left ideal. -/
theorem tensor_radical_eq_first_ideal [Nonempty m] [Nonempty n]
    (ρ : L →ₗ⁅ℂ⁆ Matrix m m ℂ) (σ : K →ₗ⁅ℂ⁆ Matrix n n ℂ)
    (hρ : ∀ x, trace (ρ x) = 0) (hσ : ∀ y, trace (σ y) = 0)
    (hleft : ∀ x y z, matrixTraceCubic (ρ x) (ρ y) (ρ z) = 0)
    (hright : complexTraceRadical σ = ⊥) :
    complexTraceRadical (tensorRepresentation ρ σ) =
      (secondProjection : ProductLie L K →ₗ⁅ℂ⁆ K).ker := by
  ext x
  rw [mem_tensor_representation_radical_iff ρ σ hρ hσ]
  have hxleft : x.1 ∈ complexTraceRadical ρ := by
    exact (mem_radical_iff _ _ _).mpr (hleft x.1)
  simp only [hxleft, true_and, hright, LieSubmodule.mem_bot, LieHom.mem_ker]
  rfl

/-- In a `27 ⊠ 3` action the surviving cubic has coefficient exactly 27.
The vanishing of the first factor's cubic is an explicit hypothesis here;
it is not a substitute for constructing the exceptional representation. -/
theorem tensor_27_by_3_family_cubic
    (ρ : L →ₗ⁅ℂ⁆ Matrix (Fin 27) (Fin 27) ℂ)
    (σ : K →ₗ⁅ℂ⁆ Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ∀ x, trace (ρ x) = 0) (hσ : ∀ y, trace (σ y) = 0)
    (hleft : ∀ x y z, matrixTraceCubic (ρ x) (ρ y) (ρ z) = 0)
    (x y z : ProductLie L K) :
    matrixTraceCubic (tensorRepresentation ρ σ x)
        (tensorRepresentation ρ σ y) (tensorRepresentation ρ σ z) =
      27 * matrixTraceCubic (σ x.2) (σ y.2) (σ z.2) := by
  rw [tensor_representation_cubic ρ σ hρ hσ, hleft]
  simp

end

end CubicAnomaly.Fixed.TensorAnomaly
