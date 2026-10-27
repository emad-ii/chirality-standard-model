import CubicAnomaly.Classification.AllRank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-!
# Hermitian realization of the complex complement

The complex commutant defines complex scalar multiplication on the real
complement.  If `J` is multiplication by `I`, symmetrizing the given positive
real form gives `S(x,y) = B(x,y) + B(Jx,Jy)`.  The Hermitian form is
`S(x,y) + I * S(Jx,y)`, using Mathlib's conjugate-linear first-slot convention.

An orthonormal complex basis gives matrix generators `T = -I * ρ`.  The
invariance of the constructed Hermitian form proves that these generators are
Hermitian.  Thus `HermitianHalf` is constructed, not assumed, and the final
structural-reduction theorem has no separate realization-witness input.

This closes the realization step of the structural lemma.  It does not prove
the subsequent classification bridge from simple/maximal/semisimple pairs to
the finite exceptional census.
-/

namespace CubicAnomaly.Classification.HermitianRealization

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.AllRank
open Matrix
open scoped InnerProductSpace

section RealModule

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]

private noncomputable def complexScalarAction
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) :
    ℂ →ₐ[ℝ] Module.End ℝ M :=
  (lieCommutant (L := L) (M := M)).val.comp e.symm.toAlgHom

private noncomputable def complexModule
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) : Module ℂ M :=
  Module.compHom M (complexScalarAction e).toRingHom

private theorem complex_scalar_tower
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) :
    letI := complexModule e
    IsScalarTower ℝ ℂ M := by
  letI := complexModule e
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change complexScalarAction e (algebraMap ℝ ℂ r) x = r • x
  rw [(complexScalarAction e).commutes]
  rfl

private theorem complex_smul_formula
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) :
    letI := complexModule e
    ∀ (z : ℂ) (x : M), z • x = z.re • x + z.im • commutantComplexStructure e x := by
  letI := complexModule e
  intro z x
  change complexScalarAction e z x = _
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simp [Complex.real_smul]
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, map_one]
  rfl

private theorem complex_action_linear
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) :
    letI := complexModule e
    ∀ (x : L) (z : ℂ) (m : M), ⁅x, z • m⁆ = z • ⁅x, m⁆ := by
  letI := complexModule e
  intro x z m
  exact ((e.symm z).property x m).symm

private def symmetrizedRealForm (Φ : LinearMap.BilinForm ℝ M)
    (J : M →ₗ⁅ℝ,L⁆ M) (x y : M) : ℝ :=
  Φ x y + Φ (J x) (J y)

private noncomputable def hermitianCore
    (Φ : LinearMap.BilinForm ℝ M)
    (hsym : ∀ x y, Φ x y = Φ y x)
    (hpos : ∀ x, x ≠ 0 → 0 < Φ x x)
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) :
    letI := complexModule e
    InnerProductSpace.Core ℂ M := by
  letI := complexModule e
  let J := commutantComplexStructure e
  have hJ : ∀ x, J (J x) = -x := commutant_complex_structure_square e
  let S := symmetrizedRealForm Φ J
  have hSsym : ∀ x y, S x y = S y x := by
    intro x y
    dsimp [S, symmetrizedRealForm]
    rw [hsym x y, hsym (J x) (J y)]
  have hSJ : ∀ x y, S (J x) y = -S x (J y) := by
    intro x y
    dsimp [S, symmetrizedRealForm]
    rw [hJ, hJ, map_neg, LinearMap.neg_apply, map_neg]
    ring
  have hSadd : ∀ x y z, S (x + y) z = S x z + S y z := by
    intro x y z
    simp [S, symmetrizedRealForm, map_add]
    ring
  have hSsmul : ∀ (r : ℝ) x y, S (r • x) y = r * S x y := by
    intro r x y
    simp [S, symmetrizedRealForm, map_smul]
    ring
  have hnonneg (x : M) : 0 ≤ Φ x x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  have hSpos (x : M) (hx : x ≠ 0) : 0 < S x x := by
    exact add_pos_of_pos_of_nonneg (hpos x hx) (hnonneg (J x))
  let H (x y : M) : ℂ := (S x y : ℂ) + Complex.I * (S (J x) y : ℂ)
  refine {
    inner := H
    conj_inner_symm := ?_
    re_inner_nonneg := ?_
    add_left := ?_
    smul_left := ?_
    definite := ?_ }
  · intro x y
    apply Complex.ext
    · simp [H, hSsym]
    · simp [H]
      rw [hSsym (J y) x, ← hSJ]
  · intro x
    have hSnonneg : 0 ≤ S x x := add_nonneg (hnonneg x) (hnonneg (J x))
    simpa [H] using hSnonneg
  · intro x y z
    change H (x + y) z = H x z + H y z
    simp [H, hSadd, map_add]
    ring
  · intro x y z
    change H (z • x) y = star z * H x y
    rw [complex_smul_formula e]
    change H (z.re • x + z.im • J x) y = star z * H x y
    simp only [H, map_add, map_smul, hSadd, hSsmul, hJ]
    have hSJ' : S (-x) y = -S x y := by
      simpa only [neg_one_smul, neg_one_mul] using hSsmul (-1) x y
    rw [hSJ']
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · intro x hx
    have hre := congrArg Complex.re hx
    have hzero : S x x = 0 := by simpa [H] using hre
    by_contra hne
    have := hSpos x hne
    linarith

private theorem hermitianCore_lie_invariant
    (Φ : LinearMap.BilinForm ℝ M)
    (hsym : ∀ x y, Φ x y = Φ y x)
    (hpos : ∀ x, x ≠ 0 → 0 < Φ x x)
    (hinv : Φ.lieInvariant L)
    (e : lieCommutant (L := L) (M := M) ≃ₐ[ℝ] ℂ) :
    letI := complexModule e
    ∀ (a : L) (x y : M),
      (hermitianCore Φ hsym hpos e).inner ⁅a, x⁆ y =
        -(hermitianCore Φ hsym hpos e).inner x ⁅a, y⁆ := by
  letI := complexModule e
  let J := commutantComplexStructure e
  let S := symmetrizedRealForm Φ J
  have hSinv (a : L) (x y : M) : S ⁅a, x⁆ y = -S x ⁅a, y⁆ := by
    dsimp [S, symmetrizedRealForm]
    simp only [J.map_lie]
    rw [hinv a x y, hinv a (J x) (J y)]
    ring
  intro a x y
  change (S ⁅a, x⁆ y : ℂ) + Complex.I * (S (J ⁅a, x⁆) y : ℂ) =
    -((S x ⁅a, y⁆ : ℂ) + Complex.I * (S (J x) ⁅a, y⁆ : ℂ))
  rw [J.map_lie, hSinv, hSinv]
  push_cast
  ring

end RealModule

section CompactPair

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

private noncomputable def hermitianHalfFromCompactForm
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (q : LieSubmodule ℝ h g)
    (e : lieCommutant (L := h) (M := q) ≃ₐ[ℝ] ℂ) : HermitianHalf h q := by
  classical
  letI originalRealModule : Module ℝ q := inferInstance
  let Φ : LinearMap.BilinForm ℝ q := B.form.restrict q.toSubmodule
  have hsym : ∀ x y : q, Φ x y = Φ y x := by
    intro x y
    exact B.symmetric x y
  have hpos : ∀ x : q, x ≠ 0 → 0 < Φ x x := by
    intro x hx
    exact B.positive x (fun hz => hx (Subtype.ext hz))
  have hinv : Φ.lieInvariant h := by
    intro x y z
    exact B.invariant x.val y.val z.val
  letI : Module ℂ q := complexModule e
  letI : IsScalarTower ℝ ℂ q := complex_scalar_tower e
  let C := hermitianCore Φ hsym hpos e
  letI : InnerProductSpace.Core ℂ q := C
  letI : NormedAddCommGroup q := @InnerProductSpace.Core.toNormedAddCommGroup ℂ q _ _ _ C
  letI : InnerProductSpace ℂ q := InnerProductSpace.ofCore C.toCore
  letI : Module.Finite ℂ q := Module.Finite.of_restrictScalars_finite ℝ ℂ q
  have hskew (x : h) (m n : q) :
      ⟪⁅x, m⁆, n⟫_ℂ = -⟪m, ⁅x, n⁆⟫_ℂ :=
    hermitianCore_lie_invariant Φ hsym hpos hinv e x m n
  let n := Module.finrank ℂ q
  let b : OrthonormalBasis (Fin n) ℂ q := stdOrthonormalBasis ℂ q
  let v : q ≃ₗ[ℝ] (Fin n → ℂ) := b.toBasis.equivFun.restrictScalars ℝ
  let ρ : h →ₗ[ℝ] (q →ₗ[ℂ] q) := {
    toFun x := {
      toFun := fun m => ⁅x, m⁆
      map_add' := by intro m k; exact lie_add x m k
      map_smul' := by intro z m; exact complex_action_linear e x z m }
    map_add' := by intro x y; apply LinearMap.ext; intro m; exact add_lie x y m
    map_smul' := by intro r x; apply LinearMap.ext; intro m; exact smul_lie r x m }
  let R : h →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ((LinearMap.toMatrix b.toBasis b.toBasis).toLinearMap.restrictScalars ℝ).comp ρ
  let T : h →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := (-Complex.I) • R
  have hRaction (x : h) (m : q) : R x *ᵥ v m = v ⁅x, m⁆ :=
    (ρ x).toMatrix_mulVec_repr b.toBasis b.toBasis m
  have hRentry (x : h) (i j : Fin n) : R x i j = ⟪b i, ⁅x, b j⁆⟫_ℂ := by
    change LinearMap.toMatrix b.toBasis b.toBasis (ρ x) i j = _
    rw [LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply]
    rfl
  refine {
    dimension := n
    coordinates := v
    generators := T
    action := ?_
    hermitian := ?_ }
  · intro x m
    change v ⁅x, m⁆ = Complex.I • (((-Complex.I) • R x) *ᵥ v m)
    rw [Matrix.smul_mulVec, smul_smul]
    simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    exact (hRaction x m).symm
  · intro x
    apply Matrix.IsHermitian.ext_iff.mpr
    intro i j
    change star ((-Complex.I) * R x j i) = (-Complex.I) * R x i j
    rw [hRentry, hRentry]
    simp only [map_mul, map_neg, Complex.star_def, Complex.conj_I, neg_neg]
    rw [inner_conj_symm, hskew]
    ring

/-- A Hermitian matrix realization of the complete adjoint complement,
constructed from the compact form and complex commutant.  It carries no
additional representation-existence hypothesis. -/
noncomputable def hermitianHalfOfCommutant
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    HermitianHalf h (orthogonalComplement B h) :=
  hermitianHalfFromCompactForm B h (orthogonalComplement B h) e

/-- The complex-commutant hypothesis supplies the Hermitian half used by the
structural reduction; no separate witness needs to be assumed. -/
theorem hermitian_half_exists_of_commutant
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    Nonempty (HermitianHalf h (orthogonalComplement B h)) :=
  ⟨hermitianHalfOfCommutant B h e⟩

/-- All five structural conclusions from compactness, effectivity, properness,
the complex commutant, and the nonzero full cubic radical of its constructed
complex half.  This version has no Hermitian-realization witness input. -/
theorem all_rank_structural_reduction_of_commutant
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    LieModule.IsIrreducible ℝ h (orthogonalComplement B h) ∧
      LieModule.IsFaithful ℝ h (orthogonalComplement B h) ∧
      LieAlgebra.IsSimple ℝ g ∧ LieAlgebra.IsSemisimple ℝ h ∧ IsCoatom h :=
  all_rank_structural_reduction B h heff hproper e (hermitianHalfOfCommutant B h e) hradical

end CompactPair

end CubicAnomaly.Classification.HermitianRealization
