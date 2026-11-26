import CubicAnomaly.Fixed.E8CompactFactors
import CubicAnomaly.Fixed.E8FamilyComplexStructure
import CubicAnomaly.Classification.UnitaryComplexification
import Mathlib.Analysis.Matrix.Hermitian

/-!
# The compact family ideal is the real Lie algebra su(3)

A nonzero local matter vector gives a three-dimensional family subspace
inside the canonical Hermitian half. Its inherited positive Hermitian metric
makes the compact family action skew-adjoint. In orthonormal coordinates
the action therefore gives an injection into su(3), and the two real
dimensions agree by complexification.
-/

namespace CubicAnomaly.Fixed.E8LocalCompactFamily

open E8CompactFactors E8CompactPair E8CanonicalPair E8MatterMatching E8FamilyComplexStructure
open MatterSpectrum MatterFamilyCoordinates
open CubicAnomaly.Classification.UnitaryGeometry
open CubicAnomaly.Classification.UnitaryComplexification
open scoped TensorProduct Matrix

noncomputable section

attribute [local irreducible] canonicalHalf
attribute [local instance] E8Compact.e8_compact_real_finiteDimensional
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

private abbrev Three := Fin 3 → ℂ
private abbrev Hilbert3 := EuclideanSpace ℂ (Fin 3)
private abbrev Ambient := EuclideanSpace ℂ (Fin canonicalHalf.dimension)

private def familyMatrix (x : compactFamily) : E8A2.sl3 :=
  compactFamilyComplexEquiv (1 ⊗ₜ[ℝ] x)

private def familyEndComplex :
    (ℂ ⊗[ℝ] compactFamily) →ₗ⁅ℂ⁆ Module.End ℂ Three :=
  lieEquivMatrix'.symm.toLieHom.comp
    (E8A2.sl3.incl.comp compactFamilyComplexEquiv.toLieHom)

private def realRestriction {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup M] [Module ℂ M] (f : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ M) :
    L →ₗ⁅ℝ⁆ Module.End ℂ M where
  __ := (f.toLinearMap.restrictScalars ℝ).comp (TensorProduct.mk ℝ ℂ L 1)
  map_lie' {x y} := by
    change f (1 ⊗ₜ[ℝ] ⁅x, y⁆) = ⁅f (1 ⊗ₜ[ℝ] x), f (1 ⊗ₜ[ℝ] y)⁆
    refine Eq.trans (congrArg f ?_) (f.map_lie _ _)
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]

private def familyEnd : compactFamily →ₗ⁅ℝ⁆ Module.End ℂ Three :=
  realRestriction familyEndComplex

private theorem familyEnd_injective : Function.Injective familyEnd := by
  intro x y h
  have hmat : (familyMatrix x).val = (familyMatrix y).val := Matrix.toLin'.injective h
  have hh := congrArg E8A2.sl3ZeroEmbedding (Subtype.ext hmat)
  exact Subtype.ext (e8_compactZeroToComplex_injective
    ((e8_compact_family_embedding x).symm.trans (hh.trans (e8_compact_family_embedding y))))

private def copiesOf (m : Matter27) : Three →ₗ[ℂ] Matter81 where
  toFun a i := a i • m
  map_add' a b := funext fun i => add_smul (a i) (b i) m
  map_smul' c a := funext fun i => mul_smul c (a i) m

private def triplet (m : Matter27) : Three →ₗ[ℂ] Ambient :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    ((actualMatterEquiv.trans canonicalMatterCoordinates).toLinearMap.comp (copiesOf m))

private theorem triplet_injective (m : Matter27) (hm : m ≠ 0) :
    Function.Injective (triplet m) := by
  apply (WithLp.linearEquiv 2 ℂ _).symm.injective.comp
  apply (actualMatterEquiv.trans canonicalMatterCoordinates).injective.comp
  intro a b h
  funext i
  have hi : a i • m = b i • m := congrFun h i
  exact (smul_left_injective ℂ hm) hi

private theorem triplet_action (m : Matter27) (x : compactFamily) (a : Three) :
    triplet m (familyEnd x a) =
      Complex.I • (canonicalHalf.generators x.val).toEuclideanLin (triplet m a) := by
  have hh : familyCopyAction (familyMatrix x).val (copiesOf m a) =
      copiesOf m (familyEnd x a) := by
    funext i
    change (∑ j, (familyMatrix x).val i j • (a j • m)) =
      (∑ j, (familyMatrix x).val i j * a j) • m
    simp only [Finset.sum_smul, smul_smul]
  have ha := e8_familyOperator_matching (familyMatrix x) (copiesOf m a)
  have hx : ⁅x.val, actualMatterEquiv (copiesOf m a)⁆ =
      actualMatterEquiv (copiesOf m (familyEnd x a)) :=
    ((congrArg (fun y : E8Grading.zeroSubalgebra => ⁅y, actualMatterEquiv (copiesOf m a)⁆)
      (e8_compact_family_embedding x).symm).trans ha).trans (congrArg actualMatterEquiv hh)
  exact congrArg (WithLp.toLp 2)
    ((congrArg canonicalMatterCoordinates hx.symm).trans
      (e8_canonical_matter_action x.val (actualMatterEquiv (copiesOf m a))))

private def orthogonalCoordinates {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [FiniteDimensional ℂ A] (j : Three →ₗ[ℂ] A) (hj : Function.Injective j) :
    j.range ≃ₗᵢ[ℂ] Hilbert3 :=
  ((stdOrthonormalBasis ℂ j.range).reindex (finCongr (by
    rw [LinearMap.finrank_range_of_inj hj, Module.finrank_fin_fun]))).repr

private def basisChange {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [FiniteDimensional ℂ A] (j : Three →ₗ[ℂ] A) (hj : Function.Injective j) :
    Three ≃ₗ[ℂ] Hilbert3 :=
  (LinearEquiv.ofInjective j hj).trans (orthogonalCoordinates j hj).toLinearEquiv

private theorem basis_inner {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [FiniteDimensional ℂ A] (j : Three →ₗ[ℂ] A) (hj : Function.Injective j) (a b : Three) :
    inner ℂ (basisChange j hj a) (basisChange j hj b) = inner ℂ (j a) (j b) :=
  (orthogonalCoordinates j hj).inner_map_map
    (LinearEquiv.ofInjective j hj a) (LinearEquiv.ofInjective j hj b)

private def threeCoordinates (m : Matter27) (hm : m ≠ 0) : Three ≃ₗ[ℂ] Hilbert3 :=
  basisChange (triplet m) (triplet_injective m hm)

private def conjugate {L P Q : Type*} [LieRing L] [LieAlgebra ℝ L] [AddCommGroup P]
    [AddCommGroup Q] [Module ℂ P] [Module ℂ Q] (e : P ≃ₗ[ℂ] Q)
    (f : L →ₗ⁅ℝ⁆ Module.End ℂ P) : L →ₗ⁅ℝ⁆ Module.End ℂ Q where
  __ := (e.lieConj.toLinearEquiv.restrictScalars ℝ).toLinearMap.comp f.toLinearMap
  map_lie' {x y} := (congrArg e.lieConj (f.map_lie x y)).trans (e.lieConj.map_lie _ _)

private def unitaryAction (m : Matter27) (hm : m ≠ 0) :
    compactFamily →ₗ⁅ℝ⁆ Module.End ℂ Hilbert3 :=
  conjugate (threeCoordinates m hm) familyEnd

private theorem transported_skew {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 3))
    (j : V →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (hinner : ∀ a b, inner ℂ (e a) (e b) = inner ℂ (j a) (j b))
    (T : Module.End ℂ V) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hT : ∀ a, j (T a) = Complex.I • A.toEuclideanLin (j a)) :
    (e.conj T).adjoint = -(e.conj T) := by
  apply (unitary_mem_iff _).mpr
  intro a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  change inner ℂ (e (T (e.symm (e a)))) (e b) =
    -inner ℂ (e a) (e (T (e.symm (e b))))
  rw [e.symm_apply_apply, e.symm_apply_apply, hinner, hinner, hT, hT,
    inner_smul_left, inner_smul_right, Matrix.isHermitian_iff_isSymmetric.mp hA]
  simp

private theorem action_mem (m : Matter27) (hm : m ≠ 0) (x : compactFamily) :
    unitaryAction m hm x ∈ specialUnitaryAlgebra Hilbert3 := by
  constructor
  · exact transported_skew (threeCoordinates m hm) (triplet m) (basis_inner (triplet m) (triplet_injective m hm))
      (familyEnd x) (canonicalHalf.generators x.val) (canonicalHalf.hermitian x.val)
      (triplet_action m x)
  · change LinearMap.trace ℂ Hilbert3 ((threeCoordinates m hm).conj (familyEnd x)) = 0
    rw [LinearMap.trace_conj']
    change LinearMap.trace ℂ Three (familyMatrix x).val.toLin' = 0
    rw [Matrix.trace_toLin'_eq]
    exact (familyMatrix x).property

private def familyToSu (m : Matter27) (hm : m ≠ 0) :
    compactFamily →ₗ⁅ℝ⁆ specialUnitaryAlgebra Hilbert3 :=
  { (unitaryAction m hm).toLinearMap.codRestrict (specialUnitaryAlgebra Hilbert3).toSubmodule
      (action_mem m hm) with
    map_lie' := fun {x y} => Subtype.ext ((unitaryAction m hm).map_lie x y) }

private theorem real_dimension {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (e : (ℂ ⊗[ℝ] L) ≃ₗ⁅ℂ⁆ E8A2.sl3) :
    Module.finrank ℝ L = Module.finrank ℝ (specialUnitaryAlgebra Hilbert3) := by
  have hc := (e.trans (specialUnitaryMatrixEquiv
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).symm).toLinearEquiv.finrank_eq
  simpa only [Module.finrank_baseChange] using hc

private theorem familyToSu_bijective (m : Matter27) (hm : m ≠ 0) :
    Function.Bijective (familyToSu m hm) := by
  have hi : Function.Injective (familyToSu m hm) := by
    intro x y h
    apply familyEnd_injective
    apply (threeCoordinates m hm).lieConj.injective
    exact congrArg Subtype.val h
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (familyToSu m hm).toLinearMap) ?_).mp hi
  exact real_dimension compactFamilyComplexEquiv

/-- The orthogonal family ideal of the actual compact isotropy is isomorphic
over the reals to the traceless skew-Hermitian algebra on standard complex three-space. -/
def compactFamilySu3Equiv :
    compactFamily ≃ₗ⁅ℝ⁆ specialUnitaryAlgebra (EuclideanSpace ℂ (Fin 3)) := by
  haveI : Nontrivial Matter27 := Module.nontrivial_of_finrank_pos (R := ℂ)
    (by rw [matter27_finrank]; decide)
  let m := Classical.choose (exists_ne (0 : Matter27))
  let hm : m ≠ 0 := Classical.choose_spec (exists_ne (0 : Matter27))
  exact LieEquiv.ofBijective (familyToSu m hm) (familyToSu_bijective m hm)

end

end CubicAnomaly.Fixed.E8LocalCompactFamily
