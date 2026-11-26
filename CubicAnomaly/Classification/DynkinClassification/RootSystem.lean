/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Jonathan Reich

Adapted to the repository's Lean 4.28 and mathlib pin. See NOTICE.md.
-/
import CubicAnomaly.Classification.DynkinClassification.Basic
import CubicAnomaly.Classification.DynkinClassification.Indecomposable
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite Cartan matrices from actual reduced root systems

The integral positive form on the root span gives a positive diagonal
symmetrizer. Applying the argument to coroots gives the left diagonal
required by the finite Cartan classification.
-/

namespace CubicAnomaly.Classification.DynkinClassification

open Matrix RootPairing Module
open scoped Matrix

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)

omit [CharZero K] [P.IsCrystallographic] in
private theorem root_span_eq :
    Submodule.span ℤ (Set.range b.toWeightBasis) = P.rootSpan ℤ := by
  rw [RootPairing.rootSpan, ← b.span_int_root_support, Set.image_eq_range]
  exact congrArg (fun f : b.support → M => Submodule.span ℤ (Set.range f))
    (funext b.toWeightBasis_apply)

private noncomputable def intBasis : Basis b.support ℤ (P.rootSpan ℤ) :=
  (b.toWeightBasis.restrictScalars ℤ).map (LinearEquiv.ofEq _ _ (root_span_eq b))

omit [P.IsCrystallographic] in
private theorem intBasis_apply (i : b.support) : intBasis b i = P.rootSpanMem ℤ i := by
  apply Subtype.ext
  change (↑((b.toWeightBasis.restrictScalars ℤ) i) : M) = P.root i
  rw [Basis.restrictScalars_apply, b.toWeightBasis_apply]

variable [Fintype ι] [DecidableEq ι]

private theorem root_gram_posDef :
    ((P.RootFormIn ℤ).toMatrix (intBasis b)).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
  · ext i j
    change star ((P.RootFormIn ℤ) _ _) = (P.RootFormIn ℤ) _ _
    rw [star_trivial]
    apply FaithfulSMul.algebraMap_injective ℤ K
    simpa only [algebraMap_rootFormIn] using P.rootForm_symmetric.eq _ _
  · intro x hx
    rw [star_trivial, LinearMap.BilinForm.dotProduct_toMatrix_mulVec]
    apply P.posRootForm_rootFormIn_posDef ℤ
    exact fun he => hx ((intBasis b).equivFun.symm.injective (he.trans (map_zero _).symm))

private theorem exists_right_symmetrizer :
    ∃ d : b.support → ℤ, (∀ i, 0 < d i) ∧ (b.cartanMatrix * diagonal d).PosDef := by
  let d (i : b.support) := P.RootFormIn ℤ (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ i)
  have hmat : b.cartanMatrix * diagonal d =
      (2 : ℤ) • (P.RootFormIn ℤ).toMatrix (intBasis b) := by
    ext i j
    apply FaithfulSMul.algebraMap_injective ℤ K
    simp only [mul_diagonal, d, map_mul, algebraMap_rootFormIn, Matrix.smul_apply,
      LinearMap.BilinForm.toMatrix_apply, intBasis_apply, Int.zsmul_eq_mul]
    simpa [← P.algebraMap_pairingIn ℤ i j] using
      congrFun (congrFun (b.cartanMatrixIn_mul_diagonal_eq ℤ P.toInvariantForm) i) j
  refine ⟨d, fun i => ?_, ?_⟩
  · exact P.posRootForm_rootFormIn_posDef ℤ (P.rootSpanMem ℤ i)
      (fun h => P.ne_zero i (congrArg Subtype.val h))
  · rw [hmat, two_smul]
    exact (root_gram_posDef b).add (root_gram_posDef b)

private theorem exists_left_symmetrizer :
    ∃ d : b.support → ℤ, (∀ i, 0 < d i) ∧ (diagonal d * b.cartanMatrix).PosDef := by
  obtain ⟨d, hd, hpos⟩ := exists_right_symmetrizer b.flip
  refine ⟨d, hd, ?_⟩
  have hf : b.flip.cartanMatrixᵀ = b.cartanMatrix := by
    ext i j
    apply FaithfulSMul.algebraMap_injective ℤ K
    exact (P.flip.algebraMap_pairingIn ℤ j i).trans (P.algebraMap_pairingIn ℤ i j).symm
  simpa only [transpose_mul, diagonal_transpose, hf] using hpos.transpose

omit [P.IsRootSystem] [DecidableEq ι] in
/-- The nonzero entries of the actual simple Cartan matrix connect every
pair of simple roots in an irreducible reduced root system. -/
theorem actual_cartan_connected [P.IsIrreducible] [P.IsReduced] (i j : b.support) :
    Relation.ReflTransGen (fun u v => b.cartanMatrix u v ≠ 0) i j := by
  refine b.induction_on_cartanMatrix _ (Relation.ReflTransGen.refl (a := i)) (fun u v hu hv => ?_)
  exact hu.tail (fun hz => hv (b.cartanMatrix_apply_eq_zero_iff_symm.mp hz))

/-- The actual simple-root Cartan matrix of an irreducible reduced root
system satisfies both hypotheses of the finite Dynkin classification. -/
theorem actual_finite_indecomposable_cartan [P.IsIrreducible] [P.IsReduced] :
    b.cartanMatrix.IsFiniteCartan ∧ b.cartanMatrix.IsIndecomposable :=
  ⟨Matrix.IsFiniteCartan.mk_of_exists_posDef b.cartanMatrix_apply_same
     b.cartanMatrix_le_zero_of_ne (exists_left_symmetrizer b),
   actual_cartan_connected b⟩

end CubicAnomaly.Classification.DynkinClassification
