import CubicAnomaly.Classification.Structural
import CubicAnomaly.Classification.TensorFormFactorization
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A complex structure recovered from one real Lie action

If multiplication by `i` is a real polynomial in one acting operator, every
real intertwiner is automatically complex linear. When the real acting
algebra complexly spans an irreducibly acting complex algebra, Schur's
lemma therefore identifies the actual real commutant with `ℂ`.

The particular cubic polynomial used here takes both `i` and `-2i` to `i`.
It applies to the defining family action with weights `1, 1, -2`.
-/

namespace CubicAnomaly.Fixed.PolynomialComplexStructure

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.TensorFormFactorization

noncomputable section

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [Module ℝ W]
  [IsScalarTower ℝ ℂ W]

omit [IsScalarTower ℝ ℂ W] in
/-- Commuting with one operator whose cubic polynomial is `i` forces
commutation with the actual complex structure. -/
theorem commutes_I_of_cubic_polynomial (T f : Module.End ℝ W)
    (hpoly : ∀ v, Complex.I • v = (3 / 2 : ℝ) • T v +
      (1 / 2 : ℝ) • T (T (T v)))
    (hf : ∀ v, f (T v) = T (f v)) :
    ∀ v, f (Complex.I • v) = Complex.I • f v := by
  intro v
  rw [hpoly v, map_add, map_smul, map_smul, hf, hf, hf, hf]
  exact (hpoly (f v)).symm

/-- A real linear map commuting with the actual complex structure is
complex linear on the same underlying vectors. -/
def complexLinearOfCommutesI (f : Module.End ℝ W)
    (hf : ∀ v, f (Complex.I • v) = Complex.I • f v) : Module.End ℂ W where
  toFun := f
  map_add' := f.map_add
  map_smul' := by
    intro z v
    change f (z • v) = z • f v
    have hs (r : ℝ) (w : W) : (r : ℂ) • w = r • w :=
      IsScalarTower.algebraMap_smul ℂ r w
    rw [← Complex.re_add_im z]
    simp only [add_smul, mul_smul, hs, map_add, map_smul, hf]

section LieAction

variable {H L : Type*} [LieRing H] [LieAlgebra ℝ H]
  [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℝ L]
  [LieRingModule H W] [LieModule ℝ H W]
  [LieRingModule L W] [LieModule ℂ L W]

variable (φ : H →ₗ⁅ℝ⁆ L)
  (haction : ∀ (x : H) (v : W), ⁅x, v⁆ = ⁅φ x, v⁆)

/-- Complex scalar multiplication is a real algebra homomorphism into
the actual real commutant. -/
def scalarCommutantHom : ℂ →ₐ[ℝ] lieCommutant (L := H) (M := W) where
  toFun c := ⟨((c • LinearMap.id : Module.End ℂ W).restrictScalars ℝ), by
    intro x v
    change c • ⁅x, v⁆ = ⁅x, c • v⁆
    rw [haction, haction, lie_smul]⟩
  map_zero' := by apply Subtype.ext; ext v; simp
  map_one' := by apply Subtype.ext; ext v; simp
  map_add' c d := by apply Subtype.ext; ext v; simp [add_smul]
  map_mul' c d := by apply Subtype.ext; ext v; simp [mul_smul]
  commutes' r := by
    apply Subtype.ext
    ext v
    change (r : ℂ) • v = r • v
    exact IsScalarTower.algebraMap_smul ℂ r v

theorem scalar_commutant_apply (c : ℂ) (v : W) :
    ((scalarCommutantHom φ haction c).val) v = c • v := rfl

variable (hspan : ∀ x : L, ∃ a b : H, x = φ a + Complex.I • φ b)
  (t : H)
  (hpoly : ∀ v : W, Complex.I • v = (3 / 2 : ℝ) • ⁅t, v⁆ +
    (1 / 2 : ℝ) • ⁅t, ⁅t, ⁅t, v⁆⁆⁆)

/-- The polynomial complex structure turns each real intertwiner into an
intertwiner for the complexly spanned algebra. -/
def complexIntertwiner (f : lieCommutant (L := H) (M := W)) : W →ₗ⁅ℂ,L⁆ W where
  __ := complexLinearOfCommutesI f.val
    (commutes_I_of_cubic_polynomial (LieModule.toEnd ℝ H W t) f.val hpoly
      (f.property t))
  map_lie' := by
    intro x v
    obtain ⟨a, b, rfl⟩ := hspan x
    change complexLinearOfCommutesI f.val _ ⁅φ a + Complex.I • φ b, v⁆ =
      ⁅φ a + Complex.I • φ b, complexLinearOfCommutesI f.val _ v⁆
    simp only [add_lie, smul_lie, map_add, map_smul]
    change f.val ⁅φ a, v⁆ + Complex.I • f.val ⁅φ b, v⁆ =
      ⁅φ a, f.val v⁆ + Complex.I • ⁅φ b, f.val v⁆
    rw [← haction a v, ← haction b v, f.property a v, f.property b v,
      haction a (f.val v), haction b (f.val v)]

include hspan t hpoly in
/-- One polynomial complex structure and complex irreducibility suffice
to determine every real equivariant endomorphism. -/
theorem real_intertwiner_is_complex_scalar [Module.Finite ℂ W]
    [LieModule.IsIrreducible ℂ L W]
    (f : lieCommutant (L := H) (M := W)) :
    ∃ c : ℂ, f = scalarCommutantHom φ haction c := by
  obtain ⟨c, hc⟩ := equivariant_end_eq_smul_id
    (complexIntertwiner φ haction hspan t hpoly f)
  refine ⟨c, ?_⟩
  apply Subtype.ext
  ext v
  exact congrArg (fun F : W →ₗ⁅ℂ,L⁆ W => F v) hc

/-- The actual real commutant is the field of complex scalars, as a real
algebra, with no assumption about a preclassified complex representation. -/
def realCommutantEquivComplex [Module.Finite ℂ W]
    [LieModule.IsIrreducible ℂ L W] :
    lieCommutant (L := H) (M := W) ≃ₐ[ℝ] ℂ := by
  letI : Nontrivial W := LieModule.nontrivial_of_isIrreducible ℂ L W
  exact (AlgEquiv.ofBijective (scalarCommutantHom φ haction)
    ⟨(scalarCommutantHom φ haction).injective, fun f => by
      obtain ⟨c, hc⟩ := real_intertwiner_is_complex_scalar φ haction hspan t hpoly f
      exact ⟨c, hc.symm⟩⟩).symm

/-- The chosen orientation sends the scalar `i` to the existing complex
structure, rather than to its negative. -/
theorem real_commutant_equiv_symm_apply [Module.Finite ℂ W]
    [LieModule.IsIrreducible ℂ L W] (c : ℂ) (v : W) :
    ((realCommutantEquivComplex φ haction hspan t hpoly).symm c).val v = c • v := rfl

end LieAction

section Transport

variable {H N : Type*} [LieRing H] [LieAlgebra ℝ H]
  [LieRingModule H W] [LieModule ℝ H W]
  [AddCommGroup N] [Module ℝ N] [LieRingModule H N] [LieModule ℝ H N]

/-- Equivariant real coordinates transport the actual endomorphism
commutant as a real algebra. -/
def commutantTransport (e : W ≃ₗ⁅ℝ,H⁆ N) :
    lieCommutant (L := H) (M := W) ≃ₐ[ℝ] lieCommutant (L := H) (M := N) where
  toFun f := ⟨e.toLinearEquiv.conj f.val, by
    intro x n
    change e (f.val (e.symm ⁅x, n⁆)) = ⁅x, e (f.val (e.symm n))⁆
    have hs : e.symm ⁅x, n⁆ = ⁅x, e.symm n⁆ := e.symm.map_lie x n
    have he : e ⁅x, f.val (e.symm n)⁆ = ⁅x, e (f.val (e.symm n))⁆ :=
      e.map_lie x (f.val (e.symm n))
    rw [hs, f.property, he]⟩
  invFun f := ⟨e.symm.toLinearEquiv.conj f.val, by
    intro x w
    change e.symm (f.val (e ⁅x, w⁆)) = ⁅x, e.symm (f.val (e w))⁆
    have he : e ⁅x, w⁆ = ⁅x, e w⁆ := e.map_lie x w
    have hs : e.symm ⁅x, f.val (e w)⁆ = ⁅x, e.symm (f.val (e w))⁆ :=
      e.symm.map_lie x (f.val (e w))
    rw [he, f.property, hs]⟩
  left_inv f := by
    apply Subtype.ext
    ext w
    change e.symm (e (f.val (e.symm (e w)))) = f.val w
    rw [e.symm_apply_apply, e.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    ext n
    change e (e.symm (f.val (e (e.symm n)))) = f.val n
    rw [e.apply_symm_apply, e.apply_symm_apply]
  map_add' f g := Subtype.ext (e.toLinearEquiv.conj.map_add f.val g.val)
  map_mul' f g := by
    apply Subtype.ext
    ext n
    change e (f.val (g.val (e.symm n))) = e (f.val (e.symm (e (g.val (e.symm n)))))
    rw [e.symm_apply_apply]
  commutes' r := by
    apply Subtype.ext
    ext n
    change e (r • e.symm n) = r • n
    rw [map_smul, e.apply_symm_apply]

omit [Module ℂ W] [IsScalarTower ℝ ℂ W] in
theorem commutant_transport_apply (e : W ≃ₗ⁅ℝ,H⁆ N)
    (f : lieCommutant (L := H) (M := W)) (n : N) :
    ((commutantTransport e) f).val n = e (f.val (e.symm n)) := rfl

omit [Module ℂ W] [IsScalarTower ℝ ℂ W] in
/-- Evaluating the transported intertwiner on an image needs no reduction
of the concrete inverse coordinate map. -/
theorem commutant_transport_apply_image (e : W ≃ₗ⁅ℝ,H⁆ N)
    (f : lieCommutant (L := H) (M := W)) (w : W) :
    ((commutantTransport e) f).val (e w) = e (f.val w) := by
  rw [commutant_transport_apply, e.symm_apply_apply]

end Transport

end

end CubicAnomaly.Fixed.PolynomialComplexStructure
