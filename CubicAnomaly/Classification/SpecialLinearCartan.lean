import CubicAnomaly.Classification.SpecialLinearGenerators
import CubicAnomaly.Classification.ChevalleySimpleTriples
import Mathlib.Data.Matrix.Cartan
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-! The adjacent diagonal differences realize the type-A simple coroots and
their Cartan weights on both sets of adjacent matrix units. -/

namespace CubicAnomaly.Classification.SpecialLinearCartan

open LieAlgebra LieAlgebra.SpecialLinear LieAlgebra.IsKilling LieModule Module
open SpecialLinearGenerators

variable {n : ℕ}

private def entry (j : Fin n) (a : Fin (n+1)) : ℂ :=
  (if j.castSucc = a then 1 else 0) - (if j.succ = a then 1 else 0)

private theorem diagonal_coe (j : Fin n) :
    (diagonal j).val = Matrix.diagonal (entry j) := by
  rw [show entry j = Pi.single j.castSucc 1 - Pi.single j.succ 1 by
    funext k; simp [entry, Pi.single_apply, eq_comm]]
  change Matrix.single j.castSucc j.castSucc (1 : ℂ) - Matrix.single j.succ j.succ 1 = _
  rw [← Matrix.diagonal_single, ← Matrix.diagonal_single, Matrix.diagonal_sub]
  rfl

private theorem difference (j i : Fin n) : entry j i.castSucc - entry j i.succ =
    (CartanMatrix.A n i j : ℂ) := by
  simp only [entry, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> norm_num <;> omega

theorem bracket_diagonal_single {m : Type*} [Fintype m] [DecidableEq m]
    (d : m → ℂ) (i j : m) :
    ⁅Matrix.diagonal d, Matrix.single i j (1 : ℂ)⁆ = (d i - d j) • Matrix.single i j 1 := by
  ext k l
  simp only [Ring.lie_def, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply]
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl,rfl⟩ := h; simp
  · simp [h]

theorem diagonal_raising (j i : Fin n) :
    ⁅diagonal j, raising i⁆ = (CartanMatrix.A n i j : ℂ) • raising i := by
  apply Subtype.ext
  change ⁅(diagonal j).val, Matrix.single i.castSucc i.succ (1 : ℂ)⁆ = _ • _
  rw [diagonal_coe, bracket_diagonal_single, difference]
  rfl

theorem diagonal_lowering (j i : Fin n) :
    ⁅diagonal j, lowering i⁆ = -(CartanMatrix.A n i j : ℂ) • lowering i := by
  apply Subtype.ext
  change ⁅(diagonal j).val, Matrix.single i.succ i.castSucc (1 : ℂ)⁆ = _ • _
  rw [diagonal_coe, bracket_diagonal_single, ← neg_sub, difference]
  rfl

theorem diagonal_commute (i j : Fin n) : ⁅diagonal i, diagonal j⁆ = 0 := by
  apply Subtype.ext
  change ⁅(diagonal i).val, (diagonal j).val⁆ = 0
  simp [diagonal_coe, Ring.lie_def, Matrix.diagonal_mul_diagonal, mul_comm]

theorem mixed_same (i : Fin n) : ⁅raising i, lowering i⁆ = diagonal i := by
  apply Subtype.ext
  simp [raising, lowering, diagonal, Ring.lie_def]

theorem mixed_distinct (i j : Fin n) (hij : i ≠ j) : ⁅raising i, lowering j⁆ = 0 := by
  apply Subtype.ext
  have h₁ : i.succ ≠ j.succ := fun he => hij (Fin.succ_injective _ he)
  have h₂ : j.castSucc ≠ i.castSucc := fun he => hij (Fin.castSucc_inj.mp he.symm)
  change Matrix.single i.castSucc i.succ (1 : ℂ) * Matrix.single j.succ j.castSucc 1 -
    Matrix.single j.succ j.castSucc 1 * Matrix.single i.castSucc i.succ 1 = 0
  simp [h₁,h₂,Matrix.single_mul_single_of_ne]

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    (s : b.support ≃ Fin n) (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n)

noncomputable def diagonalMap : H →ₗ[ℂ] sl (Fin (n+1)) ℂ := b.toCoweightBasis.constr ℂ (diagonal ∘ s)

theorem diagonalMap_basis (j : b.support) : diagonalMap H b s (b.toCoweightBasis j) = diagonal (s j) :=
  b.toCoweightBasis.constr_basis ℂ _ j

include hm in
private theorem root_value (i j : b.support) :
    i.val.val (b.toCoweightBasis j) = (CartanMatrix.A n (s i) (s j) : ℂ) := by
  have h := b.algebraMap_cartanMatrixIn_apply ℤ i j
  change ((b.cartanMatrix i j : ℤ) : ℂ) = i.val.val (coroot j.val.val) at h
  have he := congrFun (congrFun hm (s i)) (s j)
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, s.symm_apply_apply] at he
  rw [b.toCoweightBasis_apply, rootSystem_coroot_apply, ← h, he]

include hm in
theorem diagonalMap_raising (x : H) (i : b.support) :
    ⁅diagonalMap H b s x, raising (s i)⁆ = i.val.val x • raising (s i) := by
  let F := (-(ad ℂ _ (raising (s i)))).comp (diagonalMap H b s)
  have he : F = ((rootSystem H).root i).smulRight (raising (s i)) := by
    apply b.toCoweightBasis.ext
    intro j
    change -⁅raising (s i), diagonalMap H b s (b.toCoweightBasis j)⁆ =
      i.val.val (b.toCoweightBasis j) • raising (s i)
    rw [lie_skew, diagonalMap_basis, diagonal_raising, root_value H b s hm]
  exact (lie_skew _ _).symm.trans (LinearMap.congr_fun he x)

include hm in
theorem diagonalMap_lowering (x : H) (i : b.support) :
    ⁅diagonalMap H b s x, lowering (s i)⁆ = -i.val.val x • lowering (s i) := by
  let F := (-(ad ℂ _ (lowering (s i)))).comp (diagonalMap H b s)
  have he : F = (- (rootSystem H).root i).smulRight (lowering (s i)) := by
    apply b.toCoweightBasis.ext
    intro j
    change -⁅lowering (s i), diagonalMap H b s (b.toCoweightBasis j)⁆ =
      -i.val.val (b.toCoweightBasis j) • lowering (s i)
    rw [lie_skew, diagonalMap_basis, diagonal_lowering, root_value H b s hm]
  exact (lie_skew _ _).symm.trans (LinearMap.congr_fun he x)

noncomputable def diagonalHom : H →ₗ⁅ℂ⁆ sl (Fin (n+1)) ℂ where
  __ := diagonalMap H b s
  map_lie' {x y} := by
    rw [trivial_lie_zero]
    change diagonalMap H b s 0 = ⁅diagonalMap H b s x, diagonalMap H b s y⁆
    rw [map_zero, ← b.toCoweightBasis.sum_repr x, ← b.toCoweightBasis.sum_repr y]
    simp only [map_sum, map_smul, diagonalMap_basis, sum_lie, lie_sum, smul_lie, lie_smul,
      diagonal_commute, smul_zero, Finset.sum_const_zero]

include hm in
theorem diagonalHom_injective : Function.Injective (diagonalHom H b s) := by
  apply (LinearMap.ker_eq_bot.mp · : _ → Function.Injective (diagonalHom H b s).toLinearMap)
  apply eq_bot_iff.mpr
  intro t ht
  have ht' : diagonalMap H b s t = 0 := ht
  have hz (i : b.support) : i.val.val t = 0 := by
    have hh := (diagonalMap_raising H b s hm t i).symm
    rw [ht', zero_lie] at hh
    refine (smul_eq_zero.mp hh).resolve_right ?_
    intro hr
    have he := congrArg (fun x : sl (Fin (n+1)) ℂ => x.val (s i).castSucc (s i).succ) hr
    simp [raising] at he
  change t = 0
  apply (evalEquiv ℂ H).injective
  rw [map_zero]
  apply b.toWeightBasis.ext
  intro i
  simpa only [RootPairing.Base.toWeightBasis_apply, LinearMap.zero_apply] using hz i

end CubicAnomaly.Classification.SpecialLinearCartan
