import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

/-! Positive and negative words in root generators have strictly signed heights.
Only the specified Cartan generators can therefore contribute to height zero
in a triangular span. -/

namespace CubicAnomaly.Classification.ChevalleyHeightSeparation

open LieAlgebra Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

private noncomputable def heights (t : L) (c : K) (i : ℕ) :=
  (ad K L t).eigenspace (((i : K) + 1) * c)

omit [CharZero K] in
private theorem bracket_at_heights {t x y : L} {c : K} {i j : ℕ}
    (hx : x ∈ heights t c i) (hy : y ∈ heights t c j) :
    ⁅x, y⁆ ∈ heights t c (i + j + 1) := by
  rw [heights, Module.End.mem_eigenspace_iff] at hx hy ⊢
  change ⁅t, x⁆ = (((i : K) + 1) * c) • x at hx
  change ⁅t, y⁆ = (((j : K) + 1) * c) • y at hy
  change ⁅t, ⁅x, y⁆⁆ = _
  rw [leibniz_lie, hx, hy, smul_lie, lie_smul, ← add_smul]
  congr 1
  push_cast
  ring

private noncomputable def positiveSpan (t : L) (c : K) : LieSubalgebra K L where
  toSubmodule := ⨆ i, heights t c i
  lie_mem' {x y} hx hy := by
    let U := ⨆ i, heights t c i
    change ⁅x, y⁆ ∈ U
    refine Submodule.iSup_induction (motive := fun x => ⁅x, y⁆ ∈ U) _ hx
      (fun i x hx => ?_) (by simp only [zero_lie, Submodule.zero_mem])
      (fun a b ha hb => by simpa only [add_lie] using U.add_mem ha hb)
    refine Submodule.iSup_induction (motive := fun y => ⁅x, y⁆ ∈ U) _ hy
      (fun j y hy => ?_) (by simp only [lie_zero, Submodule.zero_mem])
      (fun a b ha hb => by simpa only [lie_add] using U.add_mem ha hb)
    exact (le_iSup (heights t c) (i + j + 1)) (bracket_at_heights hx hy)

private theorem lieSpan_le_offzero {ι : Type*} (t : L) (c : K) (hc : c ≠ 0) (e : ι → L)
    (he : ∀ i, ⁅t, e i⁆ = c • e i) :
    (LieSubalgebra.lieSpan K L (Set.range e)).toSubmodule ≤
      ⨆ (v : K) (_ : v ≠ 0), (ad K L t).eigenspace v := by
  have hp : LieSubalgebra.lieSpan K L (Set.range e) ≤ positiveSpan t c := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (le_iSup (heights t c) 0)
    rw [heights, Module.End.mem_eigenspace_iff]
    simpa using he i
  apply le_trans (show (LieSubalgebra.lieSpan K L (Set.range e)).toSubmodule ≤
    (positiveSpan t c).toSubmodule from hp)
  apply iSup_le
  intro n
  exact le_iSup_of_le _ (le_iSup_of_le (mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) hc) le_rfl)

/-- The height-zero intersection of a triangular span is contained in its
specified Cartan part. This applies in a product as well as in one algebra. -/
theorem triangular_height_zero_mem {ι : Type*} (t : L) (D : Submodule K L)
    (hD : ∀ x ∈ D, ⁅t, x⁆ = 0) (e f : ι → L)
    (he : ∀ i, ⁅t, e i⁆ = e i) (hf : ∀ i, ⁅t, f i⁆ = -f i)
    {x : L} (hx : ⁅t, x⁆ = 0)
    (htri : x ∈ (LieSubalgebra.lieSpan K L (Set.range f)).toSubmodule ⊔ D ⊔
      (LieSubalgebra.lieSpan K L (Set.range e)).toSubmodule) : x ∈ D := by
  let Q := ⨆ (v : K) (_ : v ≠ 0), (ad K L t).eigenspace v
  have hP := lieSpan_le_offzero t (1 : K) one_ne_zero e (by simpa using he)
  have hN := lieSpan_le_offzero t (-1 : K) (neg_ne_zero.mpr one_ne_zero) f (by simpa using hf)
  obtain ⟨nd, hnd, p, hp, rfl⟩ := Submodule.mem_sup.mp htri
  obtain ⟨n, hn, d, hd, rfl⟩ := Submodule.mem_sup.mp hnd
  have hnp : n + p ∈ Q := Q.add_mem (hN hn) (hP hp)
  have hzero : n + p ∈ (ad K L t).eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff]
    change ⁅t, n + p⁆ = (0 : K) • (n + p)
    simpa [lie_add, hD d hd] using hx
  have hdj := (ad K L t).eigenspaces_iSupIndep (0 : K)
  change Disjoint ((ad K L t).eigenspace 0) Q at hdj
  have hnp0 := (Submodule.disjoint_def.mp hdj) (n + p) hzero hnp
  rw [add_right_comm, hnp0, zero_add]
  exact hd

end CubicAnomaly.Classification.ChevalleyHeightSeparation
