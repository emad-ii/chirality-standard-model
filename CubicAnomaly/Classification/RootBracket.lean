import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Nonzero brackets of adjacent root spaces

The actual `sl₂` root string supplies a nonzero bracket whenever the sum of
two roots is a root.  This is the bridge from closure under the Lie bracket
to additive closure of an actual closed root subsystem.  No classification
of root systems, matrix presentation, or authored root table is assumed.
-/

namespace CubicAnomaly.Classification.RootBracket

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- Adjacent spaces in an actual root string have a nonzero raising bracket.
The second weight and its sum with the first are allowed to be zero. -/
theorem exists_nonzero_root_bracket (α β : Weight K H L) (hα : α.IsNonZero)
    (hsum : rootSpace H ((α : H → K) + β) ≠ ⊥) :
    ∃ x ∈ rootSpace H α, ∃ y ∈ rootSpace H β, ⁅x, y⁆ ≠ 0 := by
  have hp : 1 ≤ chainTopCoeff α β := by
    have := ((rootSpace_zsmul_add_ne_bot_iff α β hα 1).mp (by simpa using hsum)).1
    exact_mod_cast this
  obtain ⟨k, hk⟩ : ∃ k, chainTopCoeff α β = k + 1 :=
    Nat.exists_eq_add_one.mpr hp
  obtain ⟨x, hx, hxne⟩ := (chainTop α β).exists_ne_zero
  obtain ⟨s, e, f, hsl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := hsl2.h_eq_coroot hα he hf
  have prim : hsl2.HasPrimitiveVectorWith x (chainLength α β : K) :=
    have htop := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨hxne, (chainLength_smul α β hx).symm,
      by rwa [genWeightSpace_add_chainTop α β hα] at htop⟩
  have hlen : k + 1 ≤ chainLength α β := hk ▸ chainTopCoeff_le_chainLength α β
  let y := (toEnd K L L f ^ (k + 1)) x
  have hy : y ∈ rootSpace H β := by
    have hmem := toEnd_pow_apply_mem hf hx (k + 1)
    simpa only [coe_chainTop', hk, Weight.coe_neg, smul_neg,
      neg_add_cancel_left] using hmem
  refine ⟨e, he, y, hy, ?_⟩
  change ⁅e, (toEnd K L L f ^ (k + 1)) x⁆ ≠ 0
  rw [prim.lie_e_pow_succ_toEnd_f]
  apply smul_ne_zero
  · apply mul_ne_zero (Nat.cast_add_one_ne_zero k)
    apply sub_ne_zero.mpr
    exact_mod_cast (show chainLength α β ≠ k by omega)
  · exact prim.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega)

/-- Function-valued version of the nonzero root-bracket theorem, matching
the carrier used by the root-lattice saturation and grading constructions. -/
theorem exists_nonzero_root_bracket_of_functions {α β : H → K}
    (hα : α ≠ 0) (hαroot : rootSpace H α ≠ ⊥) (hβroot : rootSpace H β ≠ ⊥)
    (hsum : rootSpace H (α + β) ≠ ⊥) :
    ∃ x ∈ rootSpace H α, ∃ y ∈ rootSpace H β, ⁅x, y⁆ ≠ 0 := by
  exact exists_nonzero_root_bracket (Weight.mk α hαroot) (Weight.mk β hβroot) hα hsum

/-- Every pair of nonzero vectors in adjacent nonzero root spaces has a
nonzero bracket, since both root spaces are one-dimensional. -/
theorem lie_ne_zero_of_mem_rootSpace (α β : Weight K H L)
    (hα : α.IsNonZero) (hβ : β.IsNonZero)
    (hsum : rootSpace H ((α : H → K) + β) ≠ ⊥)
    {x y : L} (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β)
    (hxne : x ≠ 0) (hyne : y ≠ 0) : ⁅x, y⁆ ≠ 0 := by
  obtain ⟨e, he, f, hf, hef⟩ := exists_nonzero_root_bracket α β hα hsum
  obtain ⟨a, ha⟩ : ∃ a : K, a • x = e := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨x, hx⟩ (by simpa using hxne)).mp
      (finrank_rootSpace_eq_one α hα) ⟨e, he⟩
  obtain ⟨b, hb⟩ : ∃ b : K, b • y = f := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨y, hy⟩ (by simpa using hyne)).mp
      (finrank_rootSpace_eq_one β hβ) ⟨f, hf⟩
  intro hxy
  apply hef
  rw [← ha, ← hb, smul_lie, lie_smul, hxy, smul_zero, smul_zero]

end CubicAnomaly.Classification.RootBracket
