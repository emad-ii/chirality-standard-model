import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.Algebra.Lie.Derivation.Basic

/-!
# Lie algebra automorphisms representing root reflections

For an actual root of a splitting Cartan subalgebra, exponentiating the
two nilpotent adjoint operators in its `sl₂` triple gives a Lie automorphism.
Its action on the Cartan subalgebra and on all root spaces is the Weyl reflection.
-/

namespace CubicAnomaly.Classification.RootReflectionAutomorphism

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- The inner derivation associated to a root operator. -/
def adDerivation (x : L) : LieDerivation K L L where
  toLinearMap := ad K L x
  leibniz' a b := by
    change ⁅x, ⁅a, b⁆⁆ = ⁅a, ⁅x, b⁆⁆ - ⁅b, ⁅x, a⁆⁆
    rw [leibniz_lie, ← lie_skew ⁅x, a⁆ b]
    abel

section Exp

variable [LieAlgebra ℚ L]

private theorem exp_two (D : LieDerivation K L L) (hn : IsNilpotent D.toLinearMap)
    (x : L) (h : D (D x) = 0) : D.exp hn x = x + D x := by
  rw [D.exp_map_apply]
  have eqn := IsNilpotent.exp_smul_eq_sum (a := D.toLinearMap) (m := x) (k := 2)
    (by simpa [pow_succ, Module.End.mul_apply] using h) hn
  simpa [Finset.sum_range_succ] using eqn

private theorem exp_three (D : LieDerivation K L L) (hn : IsNilpotent D.toLinearMap)
    (x : L) (h : D (D (D x)) = 0) :
    D.exp hn x = x + D x + (2 : ℚ)⁻¹ • D (D x) := by
  rw [D.exp_map_apply]
  have eqn := IsNilpotent.exp_smul_eq_sum (a := D.toLinearMap) (m := x) (k := 3)
    (by simpa [pow_succ, Module.End.mul_apply] using h) hn
  simpa [Finset.sum_range_succ, Nat.factorial, pow_succ, Module.End.mul_apply] using eqn

end Exp

variable [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- A property of Lie automorphisms that is preserved by composition and
holds on the exponentials of nilpotent root operators holds on a lift
of every root reflection. -/
theorem exists_coreflection_of_exp_stable [LieAlgebra ℚ L] (i : H.root)
    (p : (L ≃ₗ⁅K⁆ L) → Prop)
    (hexp : ∀ (x : L) (χ : H → K), χ ≠ 0 → x ∈ rootSpace H χ →
      ∀ hn : IsNilpotent ((adDerivation (K := K) x).toLinearMap),
        p ((adDerivation (K := K) x).exp hn))
    (htrans : ∀ a b, p a → p b → p (a.trans b)) :
    ∃ σ : L ≃ₗ⁅K⁆ L, p σ ∧ ∀ z : H, σ (z : L) = ((rootSystem H).coreflection i z : H) := by
  have hi : i.val.IsNonZero := (Finset.mem_filter.mp i.property).2
  obtain ⟨s, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hi
  obtain rfl := t.h_eq_coroot hi he hf
  let E := adDerivation (K := K) e
  let F := adDerivation (K := K) (-f)
  have hE : IsNilpotent E.toLinearMap := isNilpotent_ad_of_mem_rootSpace H hi he
  have hF : IsNilpotent F.toLinearMap :=
    isNilpotent_ad_of_mem_rootSpace H (neg_ne_zero.mpr hi) ((rootSpace H _).neg_mem hf)
  let h : L := coroot i.val
  have Ee : E e = 0 := lie_self e
  have Ff : F f = 0 := by change ⁅-f, f⁆ = 0; simp
  have Eh : E h = -(2 • e) := (lie_skew e h).symm.trans (congrArg Neg.neg t.lie_h_e_nsmul)
  have Fh : F h = -(2 • f) := by
    change ⁅-f, h⁆ = _
    rw [neg_lie, lie_skew h f, t.lie_h_f_nsmul]
  have Fe : F e = h := by
    change ⁅-f, e⁆ = _
    rw [neg_lie, lie_skew e f, t.lie_e_f]
  have Efix : E.exp hE e = e := by rw [exp_two, Ee, add_zero]; simp [Ee]
  have EonH : E.exp hE h = h - 2 • e := by
    rw [exp_two, Eh, sub_eq_add_neg]
    simp [Eh, Ee]
  have FonE : F.exp hF e = e + h - f := by
    rw [exp_three, Fe, Fh, ← Nat.cast_smul_eq_nsmul ℚ, smul_neg, smul_smul]
    · norm_num [sub_eq_add_neg]
    · simp [Fe, Fh, Ff]
  have hpE : p (E.exp hE) := hexp e _ hi he hE
  have hpF : p (F.exp hF) := hexp (-f) _ (neg_ne_zero.mpr hi) ((rootSpace H _).neg_mem hf) hF
  refine ⟨((E.exp hE).trans (F.exp hF)).trans (E.exp hE),
    htrans _ _ (htrans _ _ hpE hpF) hpE, fun z => ?_⟩
  let k := i.val z
  have Ez : E (z : L) = -(k • e) :=
    (lie_skew e (z : L)).symm.trans (congrArg Neg.neg (lie_eq_smul_of_mem_rootSpace he z))
  have Fz : F (z : L) = -(k • f) := by
    change ⁅-f, (z : L)⁆ = _
    rw [neg_lie, lie_skew (z : L) f]
    simpa [k] using lie_eq_smul_of_mem_rootSpace hf z
  have EonZ : E.exp hE (z : L) = z.val - k • e := by
    rw [exp_two, Ez, sub_eq_add_neg]
    simp [Ez, Ee]
  have FonZ : F.exp hF (z : L) = z.val - k • f := by
    rw [exp_two, Fz, sub_eq_add_neg]
    simp [Fz, Ff]
  change E.exp hE (F.exp hF (E.exp hE (z : L))) = z.val - k • h
  rw [EonZ, map_sub, map_smul, FonZ, FonE]
  have eqn : (z : L) - k • f - k • (e + h - f) = z.val - k • e - k • h := by module
  rw [eqn, map_sub, map_sub, map_smul, map_smul, EonZ, Efix, EonH]
  module

/-- Each Weyl generator on the Cartan subalgebra is realized by an ambient
Lie algebra automorphism. -/
theorem exists_automorphism_coreflection (i : H.root) :
    ∃ σ : L ≃ₗ⁅K⁆ L, ∀ z : H, σ (z : L) = ((rootSystem H).coreflection i z : H) := by
  letI : LieAlgebra ℚ L := {
    __ := Module.compHom L (algebraMap ℚ K)
    lie_smul := fun q x y => LieAlgebra.lie_smul ((algebraMap ℚ K) q) x y }
  obtain ⟨σ, _, hs⟩ := exists_coreflection_of_exp_stable H i (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
  exact ⟨σ, hs⟩

private theorem map_mem_reflected_rootSpace (i : H.root) (σ : L ≃ₗ⁅K⁆ L)
    (hs : ∀ z : H, σ (z : L) = ((rootSystem H).coreflection i z : H))
    (j : H.root) {x : L} (hx : x ∈ rootSpace H j.val) :
    σ x ∈ rootSpace H ((rootSystem H).reflectionPerm i j).val := by
  apply weightSpace_le_genWeightSpace
  apply (mem_weightSpace _ _).mpr
  intro z
  let z' := (rootSystem H).coreflection i z
  have he : σ (z' : L) = z := by simp [hs, z']
  have hj : ((rootSystem H).reflectionPerm i j).val z = j.val z' := by
    have eqn := LinearMap.congr_fun ((rootSystem H).root_reflectionPerm i j) z
    change _ = ((rootSystem H).reflection i ((rootSystem H).root j)) z at eqn
    refine eqn.trans ?_
    rw [RootPairing.reflection_apply_root]
    change _ - _ * _ = (j.val : Dual K H) (z - i.val z • coroot i.val)
    simp [mul_comm]
  change ⁅(z : L), σ x⁆ = _
  rw [← he, ← σ.map_lie, hj]
  rw [show ⁅(z' : L), x⁆ = j.val z' • x from lie_eq_smul_of_mem_rootSpace hx z', map_smul]

/-- One automorphism simultaneously lifts the Cartan coreflection and carries
every actual root space exactly onto its reflected root space. -/
theorem exists_automorphism_reflecting_rootSpaces (i : H.root) :
    ∃ σ : L ≃ₗ⁅K⁆ L,
      (∀ z : H, σ (z : L) = ((rootSystem H).coreflection i z : H)) ∧
      ∀ (j : H.root) (x : L), σ x ∈ rootSpace H ((rootSystem H).reflectionPerm i j).val ↔
        x ∈ rootSpace H j.val := by
  obtain ⟨σ, hs⟩ := exists_automorphism_coreflection H i
  refine ⟨σ, hs, fun j x => ⟨?_, map_mem_reflected_rootSpace H i σ hs j⟩⟩
  have hsinv (z : H) : σ.symm (z : L) = ((rootSystem H).coreflection i z : H) := by
    apply σ.injective
    simp [hs]
  intro hx
  simpa using map_mem_reflected_rootSpace H i σ.symm hsinv ((rootSystem H).reflectionPerm i j) hx

end CubicAnomaly.Classification.RootReflectionAutomorphism
