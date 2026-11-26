import CubicAnomaly.Classification.ClassicalConstituentWeyl

/-!
# Contragredient highest weights under Weyl opposition

Transport a highest functional to the opposite chamber. It has nonzero
evaluation on the given module's highest line since it vanishes on every
nonempty lowering word. Cartan evaluation gives the contragredient
highest weight as minus the transported original weight.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentOpposition

open LieAlgebra LieModule Module LieAlgebra.IsKilling Submodule
open ClassicalConstituentHighest ClassicalConstituentWeyl ClassicalConstituentComparison

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [FiniteDimensional ℂ M] [IsIrreducible ℂ L M]

omit [FiniteDimensional ℂ L] [IsKilling ℂ L] in
/-- The contragredient of a finite-dimensional irreducible module is irreducible. -/
theorem dual_irreducible : IsIrreducible ℂ L (Dual ℂ M) := by
  letI := nontrivial_of_isIrreducible ℂ L M
  apply IsIrreducible.mk
  intro N hN
  let A : LieSubmodule ℂ L M := { N.toSubmodule.dualCoannihilator with
    lie_mem := by
      intro x v hv
      apply (mem_dualCoannihilator _).mpr
      intro f hf
      exact neg_eq_zero.mp ((mem_dualCoannihilator _).mp hv ⁅x,f⁆ (N.lie_mem hf)) }
  have hdc := Subspace.dualCoannihilator_dualAnnihilator_eq (W := N.toSubmodule)
  change A.toSubmodule.dualAnnihilator = N.toSubmodule at hdc
  rcases IsSimpleOrder.eq_bot_or_eq_top A with ha | ha
  · apply (LieSubmodule.toSubmodule_eq_top N).mp
    simpa only [ha, LieSubmodule.bot_toSubmodule, dualAnnihilator_bot] using hdc.symm
  · apply (hN ?_).elim
    apply (LieSubmodule.toSubmodule_eq_bot N).mp
    simpa only [ha, LieSubmodule.top_toSubmodule, dualAnnihilator_top] using hdc.symm

private theorem inverse_rootSpace (w : List H.root) (σ : L ≃ₗ⁅ℂ⁆ L)
    (hs : ∀ z : H, σ (z : L) = (cartanWord H w z : H))
    (j : H.root) {x : L} (hx : x ∈ rootSpace H (rootWord H w j).val) :
    σ.symm x ∈ rootSpace H j.val := by
  apply weightSpace_le_genWeightSpace
  apply (mem_weightSpace _ _).mpr
  intro z
  apply σ.injective
  change σ ⁅(z : L),σ.symm x⁆ = _
  rw [σ.map_lie, σ.apply_symm_apply, hs, map_smul]
  change ⁅((cartanWord H w z : H) : L), x⁆ = j.val z • σ (σ.symm x)
  rw [σ.apply_symm_apply,
    show ⁅((cartanWord H w z : H) : L),x⁆ = _ from lie_eq_smul_of_mem_rootSpace hx (cartanWord H w z),
    word_root_eval]

/-- For any word taking the positive chamber to its negative, the actual
highest weights of an irreducible and its contragredient are opposite
after Cartan transport. -/
theorem dual_highest_weight_of_reversing_word (w : List H.root)
    (hw : ∀ i : H.root, b.IsPos i ↔ ¬ b.IsPos (rootWord H w i))
    {μ ν : H → ℂ} {v : M} {ψ : Dual ℂ M}
    (hv : IsHighestVector H b μ v) (hψ : IsHighestVector H b ν ψ) :
    ∀ z : H, ν z = -μ (cartanWord H w z) := by
  obtain ⟨σ, τ, hσ, hτ⟩ := exists_module_weyl_word (M := Dual ℂ M) H w
  let f := τ ψ
  have hf : f ≠ 0 := fun he => hψ.1 (τ.injective (he.trans (map_zero τ).symm))
  have heval := negative_annihilator_pairs_highest H b hv f hf (by
    intro i hni x hx m
    let j := (rootWord H w).symm i
    have hj : rootWord H w j = i := Equiv.apply_symm_apply _ _
    have hpre := inverse_rootSpace H w σ hσ j (x := x) (hj ▸ hx)
    have hpos : b.IsPos j := (hw j).mpr (hj ▸ hni)
    have he := (hτ (σ.symm x) ψ).symm.trans (by rw [hψ.2.2 j hpos _ hpre, map_zero])
    rw [σ.apply_symm_apply] at he
    exact neg_eq_zero.mp (LinearMap.congr_fun he m))
  intro z
  have he := (hτ (z : L) ψ).symm.trans (by rw [show ⁅(z:L), ψ⁆ = ν z • ψ from hψ.2.1 z, map_smul])
  rw [hσ] at he
  have he' := LinearMap.congr_fun he v
  change -f ⁅(cartanWord H w z : H), v⁆ = ν z * f v at he'
  rw [hv.2.1, map_smul, smul_eq_mul, ← neg_mul] at he'
  exact mul_right_cancel₀ heval he'.symm

private theorem neg_chamber_of_neg_cartan (w : List H.root) (hw : ∀ z : H, cartanWord H w z = -z) :
    ∀ i : H.root, b.IsPos i ↔ ¬ b.IsPos (rootWord H w i) := by
  letI := (rootSystem H).indexNeg
  intro i
  have hi : rootWord H w i = -i := by
    apply (rootSystem H).root.injective
    ext z
    have he := word_root_eval H w i z
    rw [hw] at he
    have he' : (-i : H.root).val z = -i.val z := LinearMap.congr_fun ((rootSystem H).root_eq_neg_iff.mpr rfl) z
    change (rootWord H w i).val z = (-i : H.root).val z
    change ((rootWord H w i).val : Dual ℂ H) (-z) = i.val z at he
    rw [map_neg] at he
    rw [he']
    exact neg_eq_iff_eq_neg.mp he
  rw [hi, RootPairing.Base.IsPos.neg_iff_not b, not_not]

include b in
/-- If negation on the whole Cartan is a Weyl word, every irreducible
finite-dimensional representation is equivariantly self-dual. -/
theorem irreducible_self_dual_of_neg_word (w : List H.root)
    (hw : ∀ z : H, cartanWord H w z = -z) : Nonempty (M ≃ₗ⁅ℂ,L⁆ Dual ℂ M) := by
  letI := nontrivial_of_isIrreducible ℂ L M
  letI := dual_irreducible (L := L) (M := M)
  obtain ⟨μ, v, _, hv, hc, hk, _⟩ := ExceptionalSieveWeights.exists_bounded_dominant_highest_weight (M := M) H b
  obtain ⟨ν, ψ, _, hψ, hd, hn, _⟩ := ExceptionalSieveWeights.exists_bounded_dominant_highest_weight
    (M := Dual ℂ M) H b
  have htop : IsHighestVector H b μ v := ⟨hv, hc, hk⟩
  have hdual : IsHighestVector H b ν ψ := ⟨hψ, hd, hn⟩
  have he := dual_highest_weight_of_reversing_word H b w (neg_chamber_of_neg_cartan H b w hw) htop hdual
  have hweights : (ν : H → ℂ) = μ := by
    funext z
    rw [he, hw]
    apply smul_left_injective ℂ hv
    change -μ (-z) • v = μ z • v
    rw [neg_smul, ← hc, ← hc]
    change - ⁅-(z : L), v⁆ = ⁅(z : L), v⁆
    rw [neg_lie, neg_neg]
  obtain ⟨E, _⟩ := irreducible_equiv_of_highest_weight H htop (hweights ▸ hdual)
  exact ⟨E⟩

end CubicAnomaly.Classification.ClassicalConstituentOpposition
