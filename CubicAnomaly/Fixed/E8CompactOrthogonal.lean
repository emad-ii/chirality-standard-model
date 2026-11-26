import CubicAnomaly.Fixed.E8CompactPair

/-!
# The graded compact complement is the actual orthogonal complement

The trace of a matrix with nonzero degree shift vanishes. This identifies
the real homogeneous complement with the canonical orthogonal complement
for the actual compactness form, and proves properness and effectivity.
-/

namespace CubicAnomaly.Fixed.E8CompactPair

open Matrix
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8Compact
open CubicAnomaly.Fixed.E8CompactGrading
open CubicAnomaly.Fixed.E8Structure
open CubicAnomaly.Classification.Structural
open scoped BigOperators

noncomputable section

private theorem trace_of_nonzero_degree (a : ZMod 3) (ha : a ≠ 0)
    (A : Matrix Index Index ℂ) (hA : A ∈ matrixGrade a) : A.trace = 0 := by
  classical
  change (∑ i : Index, A i i) = 0
  apply Finset.sum_eq_zero
  intro i _
  apply hA i i
  intro hi
  apply ha
  exact (add_right_cancel (show 0 + indexGrade i = a + indexGrade i by
    simpa only [zero_add] using hi)).symm

/-- The original compactness form is the matrix trace in the actual adjoint coordinates. -/
theorem e8_compact_form_matrix (x y : compactRealAlgebra) :
    compactForm.form x y =
      -(Matrix.trace ((compactToComplex x).val * (compactToComplex y).val)).re := by
  rw [e8_compact_form_trace, ← e8_compactToComplex_operator x,
    ← e8_compactToComplex_operator y, ← map_mul]
  change -(LinearMap.trace ℂ (Index → ℂ) (Matrix.toLin' _)).re = _
  rw [Matrix.trace_toLin'_eq]

/-- Different total grades have zero trace pairing with the degree-zero algebra. -/
theorem e8_compact_zero_complement_orthogonal (x : compactZero) (y : compactComplement) :
    compactForm.form x.val y.val = 0 := by
  obtain ⟨u, hu, v, hv, he⟩ :=
    (Submodule.mem_sup (p := actualGrade 1) (p' := actualGrade 2)
      (x := compactToComplex y.val)).mp ((e8_mem_compactComplement y.val).mp y.property)
  have hx := (e8_actualGrade_iff_matrixGrade 0 _).mp
    ((e8_mem_compactZero x.val).mp x.property)
  have hu' : ((compactToComplex x.val).val * u.val).trace = 0 := by
    apply trace_of_nonzero_degree 1 (by decide)
    simpa only [zero_add] using matrix_grade_mul 0 1 _ _ hx
      ((e8_actualGrade_iff_matrixGrade 1 u).mp hu)
  have hv' : ((compactToComplex x.val).val * v.val).trace = 0 := by
    apply trace_of_nonzero_degree 2 (by decide)
    simpa only [zero_add] using matrix_grade_mul 0 2 _ _ hx
      ((e8_actualGrade_iff_matrixGrade 2 v).mp hv)
  have hy : (compactToComplex y.val).val = u.val + v.val :=
    (congrArg (fun z : E8Geck.lieAlgebra => z.val) he).symm
  rw [e8_compact_form_matrix, hy, Matrix.mul_add, Matrix.trace_add, hu', hv']
  simp

private theorem compactComplement_le_orthogonal :
    compactComplement.toSubmodule ≤
      (orthogonalComplement compactForm compactZero).toSubmodule := by
  intro y hy
  change ∀ x ∈ compactZero, compactForm.form x y = 0
  intro x hx
  exact e8_compact_zero_complement_orthogonal ⟨x, hx⟩ ⟨y, hy⟩

set_option maxHeartbeats 1600000 in
/-- The literal graded real complement equals the canonical orthogonal complement. -/
theorem e8_compactComplement_eq_orthogonal :
    compactComplement = orthogonalComplement compactForm compactZero := by
  have hdim := Submodule.finrank_add_eq_of_isCompl
    (compact_orthogonal_complement_isCompl compactForm compactZero)
  change Module.finrank ℝ compactZero +
    Module.finrank ℝ (orthogonalComplement compactForm compactZero) =
      Module.finrank ℝ compactRealAlgebra at hdim
  rw [e8_compactZero_finrank, e8_compact_finrank] at hdim
  have hq : Module.finrank ℝ (orthogonalComplement compactForm compactZero) = 162 :=
    Nat.add_left_cancel (show 86 + Module.finrank ℝ
      (orthogonalComplement compactForm compactZero) = 86 + 162 from hdim)
  apply LieSubmodule.toSubmodule_injective
  exact Submodule.eq_of_le_of_finrank_eq compactComplement_le_orthogonal
    (e8_compactComplement_finrank.trans hq.symm)

/-- The actual compact algebra splits into its zero algebra and the real nonzero grades. -/
theorem e8_compact_pair_isCompl :
    IsCompl compactZero.toSubmodule compactComplement.toSubmodule := by
  rw [e8_compactComplement_eq_orthogonal]
  exact compact_orthogonal_complement_isCompl compactForm compactZero

theorem e8_compactZero_ne_top : compactZero ≠ ⊤ := by
  intro ht
  have hd := e8_compactZero_finrank
  rw [ht] at hd
  have he := (LieSubalgebra.topEquiv :
    (⊤ : LieSubalgebra ℝ compactRealAlgebra) ≃ₗ⁅ℝ⁆ compactRealAlgebra).toLinearEquiv.finrank_eq
  rw [e8_compact_finrank] at he
  omega

/-- The compact pair is effective because the actual ambient algebra is simple. -/
theorem e8_compact_pair_effective : Effective compactZero := by
  letI := e8_compact_isSimple
  intro I hI
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top I with hbot | htop
  · exact hbot
  · exfalso
    apply e8_compactZero_ne_top
    apply LieSubalgebra.toSubmodule_injective
    apply top_unique
    simpa only [htop] using hI

/-- The actual action on the constructed real complement is faithful. -/
theorem e8_compact_complement_faithful :
    LieModule.IsFaithful ℝ compactZero compactComplement :=
  effective_invariant_complement_faithful compactZero compactComplement
    e8_compact_pair_effective e8_compact_pair_isCompl.sup_eq_top

end

end CubicAnomaly.Fixed.E8CompactPair
