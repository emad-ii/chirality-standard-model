import CubicAnomaly.Classification.Structural
import Mathlib.Algebra.Lie.Killing
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The Killing form of a compact real Lie algebra

A positive invariant form makes every adjoint operator skew-adjoint.  In an
orthonormal basis its trace square is the negative sum of the squared norms
of its values on the basis.  Consequently the kernel of the compact Killing
form is exactly the centre.  In particular, a centreless compact algebra
has Mathlib's `LieAlgebra.IsKilling` structure without a classification or
Cartan-criterion assumption.
-/

namespace CubicAnomaly.Classification.CompactKilling

open CubicAnomaly.Classification.Structural
open scoped InnerProductSpace

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

private def compactInnerCore (B : CompactForm g) : InnerProductSpace.Core ℝ g where
  inner := fun x y => B.form x y
  conj_inner_symm x y := by simpa using B.symmetric y x
  re_inner_nonneg x := by
    change 0 ≤ B.form x x
    by_cases hx : x = 0
    · simp [hx]
    · exact (B.positive x hx).le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra hne
    have := B.positive x hne
    linarith

/-- A skew-adjoint real operator for a positive form has zero trace square
exactly when it is zero.  The proof uses an orthonormal basis, without any
assumption about its eigenvalues or diagonalizability. -/
theorem compact_skew_trace_square_zero_iff (B : CompactForm g) (A : Module.End ℝ g)
    (hskew : ∀ x y, B.form (A x) y = -B.form x (A y)) :
    LinearMap.trace ℝ g (A.comp A) = 0 ↔ A = 0 := by
  classical
  let C := compactInnerCore B
  letI : InnerProductSpace.Core ℝ g := C
  letI : NormedAddCommGroup g := @InnerProductSpace.Core.toNormedAddCommGroup ℝ g _ _ _ C
  letI : InnerProductSpace ℝ g := InnerProductSpace.ofCore C.toCore
  let b : OrthonormalBasis (Fin (Module.finrank ℝ g)) ℝ g := stdOrthonormalBasis ℝ g
  have htrace : LinearMap.trace ℝ g (A.comp A) =
      -(∑ i, B.form (A (b i)) (A (b i))) := by
    rw [LinearMap.trace_eq_sum_inner _ b, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change B.form (b i) (A (A (b i))) = -B.form (A (b i)) (A (b i))
    have h := hskew (b i) (A (b i))
    linarith
  constructor
  · intro hz
    have hnonneg : ∀ i, 0 ≤ B.form (A (b i)) (A (b i)) := by
      intro i
      by_cases hi : A (b i) = 0
      · simp [hi]
      · exact (B.positive _ hi).le
    have hsum : (∑ i, B.form (A (b i)) (A (b i))) = 0 := by linarith
    apply b.toBasis.ext
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).1 hsum i
      (Finset.mem_univ i)
    change A (b i) = 0
    by_contra hne
    have := B.positive _ hne
    linarith
  · intro hzero
    simp [hzero]

/-- On a compact real Lie algebra, the Killing square vanishes exactly on
the centre. -/
theorem compact_killing_self_zero_iff_center (B : CompactForm g) (x : g) :
    killingForm ℝ g x x = 0 ↔ x ∈ LieAlgebra.center ℝ g := by
  rw [killingForm_apply_apply]
  rw [compact_skew_trace_square_zero_iff B (LieAlgebra.ad ℝ g x) (B.invariant x)]
  constructor
  · intro had y
    have hxy : ⁅x, y⁆ = 0 := congrArg (fun f : Module.End ℝ g => f y) had
    rw [← lie_skew, hxy, neg_zero]
  · intro hcenter
    ext y
    change ⁅x, y⁆ = 0
    rw [← lie_skew, hcenter y, neg_zero]

/-- The radical of the Killing form is exactly the centre for a compact
real Lie algebra. -/
theorem compact_killing_complement_top_eq_center (B : CompactForm g) :
    LieIdeal.killingCompl ℝ g ⊤ = LieAlgebra.center ℝ g := by
  ext x
  constructor
  · intro hx
    exact (compact_killing_self_zero_iff_center B x).1
      (((LieIdeal.mem_killingCompl ℝ g ⊤).mp hx) x (by trivial))
  · intro hx
    apply (LieIdeal.mem_killingCompl ℝ g ⊤).mpr
    intro y _
    rw [killingForm_apply_apply]
    have had : LieAlgebra.ad ℝ g x = 0 := by
      ext z
      change ⁅x, z⁆ = 0
      rw [← lie_skew, hx z, neg_zero]
    simp [had]

/-- Centreless compact real Lie algebras have nondegenerate Killing form.
This supplies Mathlib's inner-derivation and root-system machinery directly. -/
theorem compact_centerless_isKilling (B : CompactForm g)
    (hc : LieAlgebra.center ℝ g = ⊥) : LieAlgebra.IsKilling ℝ g :=
  ⟨(compact_killing_complement_top_eq_center B).trans hc⟩

end CubicAnomaly.Classification.CompactKilling
