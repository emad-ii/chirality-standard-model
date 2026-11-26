import CubicAnomaly.Classification.ClassicalConstituents

/-!
# Generation by two paired symplectic rank-one operators

If an irreducible symplectic action contains the squares of two vectors
with nonzero pairing, it contains every symmetrized rank-one operator.
Bracketing with the two squares produces all mixed terms in the span of
their factors. Irreducibility forces that span to be the defining module.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentGeneration

open LieModule Module ClassicalConstituents
open scoped TensorProduct

variable {L W : Type*} [LieRing L] [LieAlgebra ℂ L] [AddCommGroup W] [Module ℂ W]
    [LieRingModule L W] [LieModule ℂ L W] [FiniteDimensional ℂ W]
    (β : LinearMap.BilinForm ℂ W) (hβ : β.Nondegenerate) (hi : β.lieInvariant L)

private noncomputable def mix (a b : W) : End ℂ W :=
  formTensorEndEquiv β hβ hi (a ⊗ₜ[ℂ] b + b ⊗ₜ[ℂ] a)

private theorem mix_comm (a b : W) : mix β hβ hi a b = mix β hβ hi b a := by simp [mix, add_comm]

private theorem mix_apply (a b w : W) : mix β hβ hi a b w = β a w • b + β b w • a := by
  simp [mix]

private theorem mix_add_left (a b w : W) :
    mix β hβ hi (a + b) w = mix β hβ hi a w + mix β hβ hi b w := by
  simp [mix, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

private theorem mix_smul_left (c : ℂ) (a w : W) :
    mix β hβ hi (c • a) w = c • mix β hβ hi a w := by
  simp [mix, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

private theorem lie_mix {X : End ℂ W} (hx : X ∈ (toEnd ℂ L W).range) (a b : W) :
    ⁅X, mix β hβ hi a b⁆ = mix β hβ hi (X a) b + mix β hβ hi (X b) a := by
  obtain ⟨x, rfl⟩ := hx
  let E := formTensorEndEquiv β hβ hi
  change ⁅x, E (a ⊗ₜ[ℂ] b + b ⊗ₜ[ℂ] a)⁆ = _
  rw [show ⁅x, E (a ⊗ₜ[ℂ] b + b ⊗ₜ[ℂ] a)⁆ = E ⁅x, a ⊗ₜ[ℂ] b + b ⊗ₜ[ℂ] a⁆ from (E.map_lie _ _).symm, lie_add, TensorProduct.LieModule.lie_tmul_right,
    TensorProduct.LieModule.lie_tmul_right]
  change E _ = mix β hβ hi ⁅x, a⁆ b + mix β hβ hi ⁅x, b⁆ a
  simp only [map_add, mix, E]
  abel

omit [FiniteDimensional ℂ W] in
private theorem isolate {R : Submodule ℂ (End ℂ W)} {c : ℂ} (hc : c ≠ 0)
    {A B : End ℂ W} (hs : c • A + B ∈ R) (hb : B ∈ R) : A ∈ R := by
  have h := R.smul_mem c⁻¹ (R.sub_mem hs hb)
  simpa only [add_sub_cancel_right, inv_smul_smul₀ hc] using h

/-- Every mixed symmetric operator belongs to an irreducible action
containing two rank-one squares whose defining vectors pair nontrivially. -/
theorem mixed_operators_mem_of_paired_squares [IsIrreducible ℂ L W] (u v : W)
    (hp : β u v ≠ 0)
    (huu : formTensorEndEquiv β hβ hi (u ⊗ₜ[ℂ] u) ∈ (toEnd ℂ L W).range)
    (hvv : formTensorEndEquiv β hβ hi (v ⊗ₜ[ℂ] v) ∈ (toEnd ℂ L W).range) :
    ∀ w z : W, formTensorEndEquiv β hβ hi (w ⊗ₜ[ℂ] z + z ⊗ₜ[ℂ] w) ∈ (toEnd ℂ L W).range := by
  let R := (toEnd ℂ L W).range
  let m := mix β hβ hi
  have hcomm (a b : W) : m a b = m b a := mix_comm β hβ hi a b
  have hadd (a b w : W) : m (a + b) w = m a w + m b w := mix_add_left β hβ hi a b w
  have hsm (c : ℂ) (a w : W) : m (c • a) w = c • m a w := mix_smul_left β hβ hi c a w
  have hbr {X : End ℂ W} (hx : X ∈ R) (a b : W) :
      ⁅X, m a b⁆ = m (X a) b + m (X b) a := lie_mix β hβ hi hx a b
  let U : Submodule ℂ W := {
    carrier := {w | m w v ∈ R}
    zero_mem' := by simpa only [Set.mem_setOf_eq, m, mix, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero, map_zero] using R.zero_mem
    add_mem' := fun ha hb => by rw [Set.mem_setOf_eq, hadd]; exact R.add_mem ha hb
    smul_mem' := fun c _ ha => by rw [Set.mem_setOf_eq, hsm]; exact R.smul_mem c ha }
  have hmvv : m v v ∈ R := by simpa only [m, mix, map_add] using R.add_mem hvv hvv
  have hmuu : m u u ∈ R := by simpa only [m, mix, map_add] using R.add_mem huu huu
  have action_v {X : End ℂ W} (hx : X ∈ R) : X v ∈ U := by
    have h := R.lie_mem hx hmvv
    rw [hbr hx, ← two_smul ℂ] at h
    exact isolate (R := R.toSubmodule) (c := 2) (by norm_num) (B := 0) (by rwa [add_zero]) R.zero_mem
  have huv : u ∈ U := by
    have h := action_v huu
    change (β u v • u) ∈ U at h
    simpa only [inv_smul_smul₀ hp] using U.smul_mem (β u v)⁻¹ h
  have cross {w : W} (hw : w ∈ U) : m u w ∈ R := by
    have h := R.lie_mem huu (show m v w ∈ R from hcomm w v ▸ hw)
    rw [hbr huu, form_tensor_end_equiv_tmul, form_tensor_end_equiv_tmul, hsm, hsm] at h
    exact isolate (R := R.toSubmodule) hp h (R.smul_mem _ huv)
  have allMix {w z : W} (hw : w ∈ U) (hz : z ∈ U) : m w z ∈ R := by
    have h := R.lie_mem (cross hw) (show m v z ∈ R from hcomm z v ▸ hz)
    rw [hbr (cross hw), show m u w v = _ from mix_apply β hβ hi u w v,
      show m u w z = _ from mix_apply β hβ hi u w z, hadd, hadd, hsm, hsm, hsm, hsm] at h
    apply isolate (R := R.toSubmodule) hp (B := (β w v) • m u z + ((β u z) • m w v + (β w z) • m u v))
    · simpa only [add_assoc] using h
    · exact R.add_mem (R.smul_mem _ (cross hz)) (R.add_mem (R.smul_mem _ hw) (R.smul_mem _ huv))
  let V : LieSubmodule ℂ L W := { U with
    lie_mem := by
      intro x w hw
      have hx : toEnd ℂ L W x ∈ R := ⟨x, rfl⟩
      have h := R.lie_mem hx (show m w v ∈ R from hw)
      rw [hbr hx] at h
      change m ((toEnd ℂ L W x) w) v ∈ R
      simpa only [add_sub_cancel_right] using R.sub_mem h (allMix (action_v hx) hw) }
  have hV : V = ⊤ := by
    apply (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
    intro hh
    have hmem : v ∈ V := hmvv
    have hv : v = 0 := by simpa [hh] using hmem
    exact hp (by simp [hv])
  intro w z
  exact allMix (show w ∈ V from hV ▸ LieSubmodule.mem_top _) (show z ∈ V from hV ▸ LieSubmodule.mem_top _)

/-- Two paired pure squares force the entire ambient symplectic algebra
to be the defining action image. -/
theorem skew_operators_mem_of_paired_squares [IsIrreducible ℂ L W] (ha : β.IsAlt) (u v : W)
    (hp : β u v ≠ 0)
    (huu : formTensorEndEquiv β hβ hi (u ⊗ₜ[ℂ] u) ∈ (toEnd ℂ L W).range)
    (hvv : formTensorEndEquiv β hβ hi (v ⊗ₜ[ℂ] v) ∈ (toEnd ℂ L W).range)
    (A : End ℂ W) (hA : A ∈ skewAdjointLieSubalgebra β) :
    A ∈ (toEnd ℂ L W).range := by
  let E := formTensorEndEquiv β hβ hi
  let R := (toEnd ℂ L W).range
  let C := TensorProduct.comm ℂ W W
  have hsum (t : W ⊗[ℂ] W) : E (t + C t) ∈ R := by
    induction t using TensorProduct.induction_on with
    | zero => simpa only [map_zero, add_zero] using R.zero_mem
    | tmul a b => exact mixed_operators_mem_of_paired_squares β hβ hi u v hp huu hvv a b
    | add t s ht hs =>
      rw [map_add C, add_add_add_comm, map_add E]
      exact R.add_mem ht hs
  obtain ⟨t, rfl⟩ := E.surjective A
  have he := (form_tensor_mem_skew_adjoint_iff β hβ hi (-1) (by norm_num)
    (fun a b => by simpa using (ha.neg_eq b a).symm) t).mp hA
  have hc : C t = t := by simpa only [neg_neg, one_smul] using he
  have h := hsum t
  rw [hc, map_add, ← two_smul ℂ] at h
  exact isolate (R := R.toSubmodule) (c := 2) (by norm_num) (B := 0) (by rwa [add_zero]) R.zero_mem

end CubicAnomaly.Classification.ClassicalConstituentGeneration
