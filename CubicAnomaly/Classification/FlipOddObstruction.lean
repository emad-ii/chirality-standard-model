import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.NormNum

/-!
# A star-closed algebra has no nonzero one-dimensional odd space

Let `F` be a self-adjoint involution in a complex star algebra. In any
star-closed subalgebra containing `F`, the operators anticommuting with
`F` cannot form a nonzero complex line. Multiplication by `F` and the
adjoint give incompatible eigenvalues on such a line.

No semisimplicity, irreducible decomposition, or dimension calculation
is needed. The result applies to the actual equivariant operator algebra
on a tensor square after the canonical trace reshuffle.
-/

namespace CubicAnomaly.Classification.FlipOddObstruction

noncomputable section

section StarAlgebra

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- In a star-closed complex subalgebra, the odd operators for a
self-adjoint involution cannot form a nonzero scalar line. -/
theorem flip_odd_not_line
    (C : Subalgebra ℂ A) (hstar : ∀ S ∈ C, star S ∈ C)
    (F : A) (hF : F ∈ C) (hFstar : star F = F) (hFsq : F * F = 1)
    (T : A) (hT : T ∈ C) (hTne : T ≠ 0) (hodd : F * T = -(T * F))
    (hline : ∀ S ∈ C, F * S = -(S * F) → ∃ c : ℂ, S = c • T) : False := by
  have hFTodd : F * (F * T) = -((F * T) * F) := by
    simpa only [mul_neg, mul_assoc] using congrArg (fun S : A => F * S) hodd
  obtain ⟨c, hc⟩ := hline (F * T) (C.mul_mem hF hT) hFTodd
  have hTsq : T = (c * c) • T := by
    calc
      T = F * (F * T) := by rw [← mul_assoc, hFsq, one_mul]
      _ = F * (c • T) := by rw [hc]
      _ = c • (F * T) := mul_smul_comm _ _ _
      _ = (c * c) • T := by rw [hc, smul_smul]
  have hcsq : c * c = 1 := smul_left_injective ℂ hTne (by
    simpa only [one_smul] using hTsq.symm)
  have hTstarne : star T ≠ 0 := by
    intro hzero
    apply hTne
    simpa only [star_star, star_zero] using congrArg star hzero
  have hoddstar : F * star T = -(star T * F) := by
    have h := congrArg star hodd
    simp only [star_mul, star_neg, hFstar] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  obtain ⟨d, hd⟩ := hline (star T) (hstar T hT) hoddstar
  have hleft : F * star T = c • star T := by
    rw [hd, mul_smul_comm, hc, smul_smul, smul_smul, mul_comm d c]
  have hright : star T * F = star c • star T := by
    simpa only [star_mul, hFstar, star_smul] using congrArg star hc
  have hzero : (c + star c) • star T = 0 := by
    rw [add_smul, ← hleft, ← hright, hoddstar, neg_add_cancel]
  have hcstar : c + star c = 0 := (smul_eq_zero.mp hzero).resolve_right hTstarne
  rcases mul_self_eq_one_iff.mp hcsq with hc1 | hc1
  · norm_num [hc1] at hcstar
  · norm_num [hc1] at hcstar

end StarAlgebra

section Operators

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [FiniteDimensional ℂ U]

/-- The obstruction applies to the actual Hermitian adjoint of finite
complex inner-product-space operators. -/
theorem adjoint_closed_flip_odd_not_line
    (C : Subalgebra ℂ (Module.End ℂ U)) (hstar : ∀ S ∈ C, S.adjoint ∈ C)
    (F : Module.End ℂ U) (hF : F ∈ C) (hFstar : F.adjoint = F) (hFsq : F * F = 1)
    (T : Module.End ℂ U) (hT : T ∈ C) (hTne : T ≠ 0) (hodd : F * T = -(T * F))
    (hline : ∀ S ∈ C, F * S = -(S * F) → ∃ c : ℂ, S = c • T) : False :=
  flip_odd_not_line C hstar F hF hFstar hFsq T hT hTne hodd hline

end Operators

end

end CubicAnomaly.Classification.FlipOddObstruction
