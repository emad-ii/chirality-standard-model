import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Recognizing an adjoint module from generator equivariance

A linear candidate map from an irreducible module into an ambient Lie
algebra need only intertwine a generating set. One nonzero image in the
generated algebra forces every image into it; irreducibility also gives
injectivity. If the generators occur in the image, the map identifies the
module with the entire generated algebra and its actual adjoint action.

No bracket or Jacobi identity is imposed on the original module.
-/

namespace CubicAnomaly.Fixed.AdjointRecognition

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

noncomputable section

/-- Elements for which a given linear map intertwines the module and
adjoint actions form an actual Lie subalgebra. -/
def equivarianceSubalgebra (B : M →ₗ[K] L) : LieSubalgebra K L where
  carrier := {x | ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro x y hx hy v
    change ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆ at hx
    change ∀ v, B ⁅y, v⁆ = ⁅y, B v⁆ at hy
    simp only [add_lie, map_add, hx, hy]
  smul_mem' := by
    intro c x hx v
    change ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆ at hx
    simp only [smul_lie, map_smul, hx]
  lie_mem' := by
    intro x y hx hy v
    change ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆ at hx
    change ∀ v, B ⁅y, v⁆ = ⁅y, B v⁆ at hy
    simp only [lie_lie, map_sub, hx, hy]

/-- Equivariance on the generators extends to the actual generated algebra. -/
theorem generated_intertwiner_equivariance
    (S : Set L) (B : M →ₗ[K] L)
    (hgen : ∀ x ∈ S, ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆)
    (x : LieSubalgebra.lieSpan K L S) (v : M) :
    B ⁅x, v⁆ = ⁅x, B v⁆ := by
  have hg : LieSubalgebra.lieSpan K L S ≤ equivarianceSubalgebra B :=
    LieSubalgebra.lieSpan_le.mpr hgen
  exact hg x.property v

/-- The actual intertwiner into the ambient adjoint module. -/
def generatedIntertwiner (S : Set L) (B : M →ₗ[K] L)
    (hgen : ∀ x ∈ S, ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆) :
    M →ₗ⁅K, LieSubalgebra.lieSpan K L S⁆ L where
  __ := B
  map_lie' := by
    intro x v
    exact generated_intertwiner_equivariance S B hgen x v

/-- One nonzero image lying in the generated algebra forces all images
there, because its preimage is a nonzero invariant submodule. -/
theorem irreducible_generated_intertwiner_mem
    (S : Set L) (B : M →ₗ[K] L)
    (hgen : ∀ x ∈ S, ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆)
    [LieModule.IsIrreducible K (LieSubalgebra.lieSpan K L S) M]
    (v₀ : M) (hv₀ : B v₀ ≠ 0) (hmem : B v₀ ∈ LieSubalgebra.lieSpan K L S)
    (v : M) : B v ∈ LieSubalgebra.lieSpan K L S := by
  let f := generatedIntertwiner S B hgen
  let U := (LieSubalgebra.lieSpan K L S).toLieSubmodule.comap f
  have hv : v₀ ∈ U := hmem
  have hU : U ≠ ⊥ := by
    intro h
    have hz : v₀ = 0 := by simpa [h] using hv
    exact hv₀ (by simp [hz])
  have htop : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU
  have : v ∈ U := by rw [htop]; trivial
  exact this

/-- A nonzero equivariant candidate is injective on the irreducible module. -/
theorem irreducible_generated_intertwiner_injective
    (S : Set L) (B : M →ₗ[K] L)
    (hgen : ∀ x ∈ S, ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆)
    [LieModule.IsIrreducible K (LieSubalgebra.lieSpan K L S) M]
    (v₀ : M) (hv₀ : B v₀ ≠ 0) : Function.Injective B := by
  let f := generatedIntertwiner S B hgen
  have hk : f.ker ≠ ⊤ := by
    intro h
    have : v₀ ∈ f.ker := by rw [h]; trivial
    exact hv₀ this
  exact (LieModuleHom.ker_eq_bot f).mp
    ((IsSimpleOrder.eq_bot_or_eq_top f.ker).resolve_right hk)

private def imageSubalgebra (S : Set L) (B : M →ₗ[K] L)
    (hgen : ∀ x ∈ S, ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆)
    (hmem : ∀ v, B v ∈ LieSubalgebra.lieSpan K L S) : LieSubalgebra K L where
  __ := B.range
  lie_mem' := by
    rintro x y ⟨v, rfl⟩ ⟨w, rfl⟩
    refine ⟨⁅(⟨B v, hmem v⟩ : LieSubalgebra.lieSpan K L S), w⁆, ?_⟩
    exact generated_intertwiner_equivariance S B hgen _ w

/-- Generator equivariance and one nonzero image prove an exact adjoint
recognition theorem. Jacobi and the generated algebra's dimension are not
assumptions. -/
theorem generated_adjoint_recognition
    (S : Set L) (B : M →ₗ[K] L)
    (hgen : ∀ x ∈ S, ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆)
    [LieModule.IsIrreducible K (LieSubalgebra.lieSpan K L S) M]
    (v₀ : M) (hv₀ : B v₀ ≠ 0) (hmem : B v₀ ∈ LieSubalgebra.lieSpan K L S)
    (hcover : S ⊆ Set.range B) :
    Function.Injective B ∧ B.range = (LieSubalgebra.lieSpan K L S).toSubmodule := by
  refine ⟨irreducible_generated_intertwiner_injective S B hgen v₀ hv₀, ?_⟩
  have hall := irreducible_generated_intertwiner_mem S B hgen v₀ hv₀ hmem
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact hall v
  · have hle : LieSubalgebra.lieSpan K L S ≤ imageSubalgebra S B hgen hall :=
      LieSubalgebra.lieSpan_le.mpr hcover
    exact hle

/-- The actual adjoint-module equivalence supplied by recognition. -/
def generatedAdjointEquiv
    (S : Set L) (B : M →ₗ[K] L)
    (hgen : ∀ x ∈ S, ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆)
    [LieModule.IsIrreducible K (LieSubalgebra.lieSpan K L S) M]
    (v₀ : M) (hv₀ : B v₀ ≠ 0) (hmem : B v₀ ∈ LieSubalgebra.lieSpan K L S)
    (hcover : S ⊆ Set.range B) :
    M ≃ₗ⁅K, LieSubalgebra.lieSpan K L S⁆ LieSubalgebra.lieSpan K L S := by
  let hall := irreducible_generated_intertwiner_mem S B hgen v₀ hv₀ hmem
  let f : M →ₗ[K] LieSubalgebra.lieSpan K L S := B.codRestrict _ hall
  have hrec := generated_adjoint_recognition S B hgen v₀ hv₀ hmem hcover
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      exact hrec.1 (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ B.range := by rw [hrec.2]; exact x.property
      obtain ⟨v, hv⟩ := hx
      exact ⟨v, Subtype.ext hv⟩
  exact
    { LinearEquiv.ofBijective f hf with
      map_lie' := by
        intro x v
        apply Subtype.ext
        exact generated_intertwiner_equivariance S B hgen x v }

/-- Recognition preserves the literal candidate matrix map. -/
theorem generated_adjoint_equiv_val
    (S : Set L) (B : M →ₗ[K] L)
    (hgen : ∀ x ∈ S, ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆)
    [LieModule.IsIrreducible K (LieSubalgebra.lieSpan K L S) M]
    (v₀ : M) (hv₀ : B v₀ ≠ 0) (hmem : B v₀ ∈ LieSubalgebra.lieSpan K L S)
    (hcover : S ⊆ Set.range B) (v : M) :
    (generatedAdjointEquiv S B hgen v₀ hv₀ hmem hcover v : L) = B v := rfl

/-- The actual generated algebra has the module's dimension. -/
theorem generated_adjoint_finrank
    (S : Set L) (B : M →ₗ[K] L)
    (hgen : ∀ x ∈ S, ∀ v, B ⁅x, v⁆ = ⁅x, B v⁆)
    [LieModule.IsIrreducible K (LieSubalgebra.lieSpan K L S) M]
    (v₀ : M) (hv₀ : B v₀ ≠ 0) (hmem : B v₀ ∈ LieSubalgebra.lieSpan K L S)
    (hcover : S ⊆ Set.range B) :
    Module.finrank K (LieSubalgebra.lieSpan K L S) = Module.finrank K M :=
  (generatedAdjointEquiv S B hgen v₀ hv₀ hmem hcover).toLinearEquiv.finrank_eq.symm

end

end CubicAnomaly.Fixed.AdjointRecognition
