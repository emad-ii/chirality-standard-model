import CubicAnomaly.Classification.InvolutionObstruction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The actual compact symplectic algebra

A quaternionic structure is a conjugate-linear map whose square is minus
the identity and which reverses the complex inner product. The compact
symplectic algebra consists of the skew-Hermitian complex endomorphisms
commuting with that structure. These are actual endomorphisms, rather than
type labels or a supplied classification of subalgebras.
-/

namespace CubicAnomaly.Classification.SymplecticGeometry

open scoped ComplexConjugate

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- An antiunitary quaternionic structure on an actual complex inner-product space. -/
structure QuaternionicStructure (W : Type*) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] where
  toConjLinearMap : W →ₗ⋆[ℂ] W
  square : ∀ w, toConjLinearMap (toConjLinearMap w) = -w
  inner_map : ∀ u v, inner ℂ (toConjLinearMap u) (toConjLinearMap v) =
    conj (inner ℂ u v)

instance : CoeFun (QuaternionicStructure W) (fun _ => W → W) :=
  ⟨fun J => J.toConjLinearMap⟩

namespace QuaternionicStructure

variable (J : QuaternionicStructure W)

@[simp] theorem apply_add (u v : W) : J (u + v) = J u + J v :=
  J.toConjLinearMap.map_add u v

@[simp] theorem apply_neg (u : W) : J (-u) = -J u :=
  J.toConjLinearMap.map_neg u

@[simp] theorem apply_sub (u v : W) : J (u - v) = J u - J v :=
  J.toConjLinearMap.map_sub u v

@[simp] theorem apply_smul (c : ℂ) (u : W) : J (c • u) = conj c • J u :=
  J.toConjLinearMap.map_smulₛₗ c u

@[simp] theorem apply_zero : J (0 : W) = 0 := J.toConjLinearMap.map_zero

theorem injective : Function.Injective J := by
  intro u v huv
  have h := congrArg J huv
  simpa only [J.square, neg_inj] using h

theorem surjective : Function.Surjective J := fun w =>
  ⟨-J w, by rw [J.apply_neg, J.square, neg_neg]⟩

/-- Moving the quaternionic structure between inner-product inputs. -/
theorem inner_left (u v : W) :
    inner ℂ (J u) v = -conj (inner ℂ u (J v)) := by
  have h := J.inner_map u (-J v)
  simpa only [J.apply_neg, J.square, neg_neg, inner_neg_right, map_neg] using h

theorem inner_right (u v : W) :
    inner ℂ u (J v) = -conj (inner ℂ (J u) v) := by
  have h := J.inner_map (-J u) v
  simpa only [J.apply_neg, J.square, neg_neg, inner_neg_left, map_neg] using h

/-- A vector and its quaternionic image are orthogonal. -/
theorem inner_self_image (u : W) : inner ℂ u (J u) = 0 := by
  have h := J.inner_right u u
  rw [inner_conj_symm] at h
  linear_combination (1 / 2 : ℂ) * h

/-- Conjugation by the quaternionic structure is complex-linear on vectors. -/
def conjugateEnd (A : Module.End ℂ W) : Module.End ℂ W :=
  (-J.toConjLinearMap).comp (A.comp J.toConjLinearMap)

@[simp] theorem conjugateEnd_apply (A : Module.End ℂ W) (w : W) :
    J.conjugateEnd A w = -J (A (J w)) := rfl

theorem conjugateEnd_apply_image (A : Module.End ℂ W) (w : W) :
    J.conjugateEnd A (J w) = J (A w) := by
  simp only [conjugateEnd_apply, J.square, map_neg, J.apply_neg, neg_neg]

theorem image_conjugateEnd_apply (A : Module.End ℂ W) (w : W) :
    J (J.conjugateEnd A w) = A (J w) := by
  rw [conjugateEnd_apply, J.apply_neg, J.square, neg_neg]

theorem inner_conjugateEnd_left (A : Module.End ℂ W) (u v : W) :
    inner ℂ (J.conjugateEnd A u) v = conj (inner ℂ (A (J u)) (J v)) := by
  rw [conjugateEnd_apply, inner_neg_left, J.inner_left, neg_neg]

theorem inner_conjugateEnd_right (A : Module.End ℂ W) (u v : W) :
    inner ℂ u (J.conjugateEnd A v) = conj (inner ℂ (J u) (A (J v))) := by
  rw [conjugateEnd_apply, inner_neg_right, J.inner_right, neg_neg]

end QuaternionicStructure

/-- The actual compact symplectic algebra on a quaternionic inner-product space. -/
def symplecticAlgebra (J : QuaternionicStructure W) : LieSubalgebra ℝ (Module.End ℂ W) where
  carrier := {A | (∀ u v, inner ℂ (A u) v = -inner ℂ u (A v)) ∧
    ∀ w, A (J w) = J (A w)}
  zero_mem' := by simp
  add_mem' := by
    rintro A C ⟨hA, hAJ⟩ ⟨hC, hCJ⟩
    constructor
    · intro u v
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hA, hC]
      ring
    · intro w
      simp only [LinearMap.add_apply, J.apply_add, hAJ, hCJ]
  smul_mem' := by
    intro t A hA
    constructor
    · intro u v
      change inner ℂ ((t : ℂ) • A u) v = -inner ℂ u ((t : ℂ) • A v)
      rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, hA.1]
      ring
    · intro w
      change (t : ℂ) • A (J w) = J ((t : ℂ) • A w)
      simp only [J.apply_smul, Complex.conj_ofReal, hA.2]
  lie_mem' := by
    rintro A C ⟨hA, hAJ⟩ ⟨hC, hCJ⟩
    constructor
    · intro u v
      change inner ℂ (A (C u) - C (A u)) v = -inner ℂ u (A (C v) - C (A v))
      simp only [inner_sub_left, inner_sub_right, hA, hC]
      ring
    · intro w
      change A (C (J w)) - C (A (J w)) = J (A (C w) - C (A w))
      rw [J.apply_sub, hAJ, hCJ, hAJ, hCJ]

theorem symplectic_skew_action (J : QuaternionicStructure W)
    (A : symplecticAlgebra J) (u v : W) :
    inner ℂ (A.val u) v = -inner ℂ u (A.val v) := A.property.1 u v

theorem symplectic_commutes (J : QuaternionicStructure W)
    (A : symplecticAlgebra J) (w : W) : A.val (J w) = J (A.val w) :=
  A.property.2 w

instance [FiniteDimensional ℂ W] (J : QuaternionicStructure W) :
    Module.Finite ℝ (symplecticAlgebra J) := by
  letI : Module.Finite ℝ (Module.End ℂ W) := Module.Finite.trans ℂ (Module.End ℂ W)
  infer_instance

private def realEndConjugation (r : W ≃ₗ[ℂ] W) :
    Module.End ℂ W ≃ₗ⁅ℝ⁆ Module.End ℂ W where
  __ := r.lieConj.toLinearEquiv.restrictScalars ℝ
  map_lie' := by intro A C; exact r.lieConj.map_lie A C

theorem isometry_inverse_commutes (J : QuaternionicStructure W)
    (r : W ≃ₗᵢ[ℂ] W) (hr : ∀ w, r (J w) = J (r w)) (w : W) :
    r.symm (J w) = J (r.symm w) := by
  apply r.injective
  rw [r.apply_symm_apply, hr, r.apply_symm_apply]

private theorem isometry_conjugation_mem (J : QuaternionicStructure W)
    (r : W ≃ₗᵢ[ℂ] W) (hr : ∀ w, r (J w) = J (r w))
    (A : Module.End ℂ W) (hA : A ∈ symplecticAlgebra J) :
    realEndConjugation r.toLinearEquiv A ∈ symplecticAlgebra J := by
  constructor
  · intro u v
    obtain ⟨u, rfl⟩ := r.surjective u
    obtain ⟨v, rfl⟩ := r.surjective v
    change inner ℂ (r (A (r.symm (r u)))) (r v) =
      -inner ℂ (r u) (r (A (r.symm (r v))))
    rw [r.symm_apply_apply, r.symm_apply_apply, r.inner_map_map, r.inner_map_map]
    exact hA.1 u v
  · intro w
    change r (A (r.symm (J w))) = J (r (A (r.symm w)))
    rw [isometry_inverse_commutes J r hr, hA.2, hr]

/-- Quaternionic unitary changes of coordinates act on the actual compact
symplectic algebra by Lie automorphisms. -/
def symplecticConjugation (J : QuaternionicStructure W)
    (r : W ≃ₗᵢ[ℂ] W) (hr : ∀ w, r (J w) = J (r w)) :
    symplecticAlgebra J ≃ₗ⁅ℝ⁆ symplecticAlgebra J :=
  (realEndConjugation r.toLinearEquiv).ofSubalgebras _ _ (by
    ext A
    constructor
    · rintro ⟨C, hC, rfl⟩
      exact isometry_conjugation_mem J r hr C hC
    · intro hA
      refine ⟨realEndConjugation r.symm.toLinearEquiv A,
        isometry_conjugation_mem J r.symm (isometry_inverse_commutes J r hr) A hA, ?_⟩
      exact (realEndConjugation r.toLinearEquiv).apply_symm_apply A)

theorem symplecticConjugation_apply (J : QuaternionicStructure W)
    (r : W ≃ₗᵢ[ℂ] W) (hr : ∀ w, r (J w) = J (r w))
    (A : symplecticAlgebra J) (w : W) :
    (symplecticConjugation J r hr A).val w = r (A.val (r.symm w)) := rfl

/-- The skew-Hermitian cross operator of two defining vectors. -/
def complexCrossSkew (u v : W) : Module.End ℂ W :=
  (innerSL ℂ v).toLinearMap.smulRight u - (innerSL ℂ u).toLinearMap.smulRight v

theorem complexCrossSkew_skew (u v x y : W) :
    inner ℂ (complexCrossSkew u v x) y = -inner ℂ x (complexCrossSkew u v y) := by
  change inner ℂ ((inner ℂ v x) • u - (inner ℂ u x) • v) y =
    -inner ℂ x ((inner ℂ v y) • u - (inner ℂ u y) • v)
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_conj_symm]
  ring

/-- Averaging a skew-Hermitian cross operator with its quaternionic
conjugate gives an actual symplectic endomorphism. -/
def symplecticCrossSkew (J : QuaternionicStructure W) (u v : W) : symplecticAlgebra J :=
  ⟨complexCrossSkew u v + J.conjugateEnd (complexCrossSkew u v), by
    constructor
    · intro x y
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right,
        J.inner_conjugateEnd_left, J.inner_conjugateEnd_right, complexCrossSkew_skew,
        map_neg]
      ring
    · intro w
      simp only [LinearMap.add_apply, J.apply_add, J.conjugateEnd_apply_image,
        J.image_conjugateEnd_apply]
      exact add_comm _ _⟩

/-- A cross operator witnesses nontrivial conjugation across a quaternionic
orthogonal splitting. -/
theorem symplecticCrossSkew_apply_right (J : QuaternionicStructure W) (u v : W)
    (huv : inner ℂ u v = 0) (huJv : inner ℂ u (J v) = 0) :
    (symplecticCrossSkew J u v).val v = (inner ℂ v v) • u := by
  change complexCrossSkew u v v + J.conjugateEnd (complexCrossSkew u v) v = _
  rw [J.conjugateEnd_apply]
  change ((inner ℂ v v) • u - (inner ℂ u v) • v) +
    -J ((inner ℂ v (J v)) • u - (inner ℂ u (J v)) • v) = _
  simp only [huv, huJv, J.inner_self_image, zero_smul, sub_zero, sub_self,
    J.apply_zero, neg_zero, add_zero]

end

end CubicAnomaly.Classification.SymplecticGeometry
