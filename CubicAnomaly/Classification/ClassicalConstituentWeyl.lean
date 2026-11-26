import CubicAnomaly.Classification.RootReflectionAutomorphism
import CubicAnomaly.Classification.ClassicalConstituentComparison

/-!
# Simultaneous Weyl action on a Cartan and its representations

A nilpotent root operator acts exponentially on both the Lie algebra
and the module. The action map from their tensor product intertwines
the two exponentials by the Leibniz rule. Composing the resulting
linear isomorphisms lifts each word of root reflections.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentWeyl

open LieAlgebra LieModule Module LieAlgebra.IsKilling IsNilpotent
open RootReflectionAutomorphism
open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [AddCommGroup M] [Module ℂ M]
    [LieRingModule L M] [LieModule ℂ L M]

private theorem exp_intertwines [LieAlgebra ℚ L] [Module ℚ M]
    (x : L) (hD : IsNilpotent (ad ℂ L x)) (hA : IsNilpotent (toEnd ℂ L M x))
    (y : L) (m : M) :
    exp (toEnd ℂ L M x) ⁅y,m⁆ = ⁅exp (ad ℂ L x) y, exp (toEnd ℂ L M x) m⁆ := by
  let D := ad ℂ L x
  let A := toEnd ℂ L M x
  let DA : End ℂ (L ⊗[ℂ] M) := D.rTensor M
  let MA : End ℂ (L ⊗[ℂ] M) := A.lTensor L
  have hD' : IsNilpotent DA := hD.map (End.rTensorAlgHom ℂ L M)
  have hA' : IsNilpotent MA := hA.map (End.lTensorAlgHom ℂ M L)
  have hc : Commute DA MA := by
    change (D.rTensor M).comp (A.lTensor L) = (A.lTensor L).comp (D.rTensor M)
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  let act : L ⊗[ℂ] M →ₗ[ℂ] M := TensorProduct.lift (toEnd ℂ L M).toLinearMap
  have hd : A.comp act = act.comp (DA + MA) := by
    ext l v
    change ⁅x, ⁅l,v⁆⁆ = act (DA (l ⊗ₜ[ℂ] v) + MA (l ⊗ₜ[ℂ] v))
    rw [map_add]
    exact leibniz_lie x l v
  have he := End.commute_exp_left_of_commute (hc.isNilpotent_add hD' hA') hA hd
  have he' : exp A ⁅y,m⁆ = act (exp (DA + MA) (y ⊗ₜ[ℂ] m)) :=
    LinearMap.congr_fun he (y ⊗ₜ[ℂ] m)
  have hDE : exp DA = (exp D).rTensor M := (hD.map_exp (End.rTensorAlgHom ℂ L M)).symm
  have hAE : exp MA = (exp A).lTensor L := (hA.map_exp (End.lTensorAlgHom ℂ M L)).symm
  rw [show exp (toEnd ℂ L M x) ⁅y,m⁆ = _ from he', exp_add_of_commute hc hD' hA', hDE, hAE]
  rfl

private noncomputable def expEquiv [Module ℚ M] (A : End ℂ M) (hn : IsNilpotent A) : M ≃ₗ[ℂ] M := {
  exp A with
  invFun := fun v => exp (-A) v
  left_inv v := congrArg (fun f : End ℂ M => f v) hn.exp_neg_mul_exp_self
  right_inv v := congrArg (fun f : End ℂ M => f v) hn.exp_mul_exp_neg_self }

variable [FiniteDimensional ℂ L] [IsKilling ℂ L] (H : LieSubalgebra ℂ L)
    [H.IsCartanSubalgebra]

/-- The composition of Cartan coreflections with the head of the word
applied first. -/
noncomputable def cartanWord : List H.root → H ≃ₗ[ℂ] H
  | [] => LinearEquiv.refl ℂ H
  | i :: w => ((rootSystem H).coreflection i).trans (cartanWord w)

/-- The same word acts on the indices of the actual roots. -/
noncomputable def rootWord : List H.root → Equiv.Perm H.root
  | [] => Equiv.refl _
  | i :: w => ((rootSystem H).reflectionPerm i).trans (rootWord w)

private theorem reflected_eval (i j : H.root) (z : H) :
    ((rootSystem H).reflectionPerm i j).val z = j.val ((rootSystem H).coreflection i z) := by
  have eqn := LinearMap.congr_fun ((rootSystem H).root_reflectionPerm i j) z
  change _ = ((rootSystem H).reflection i ((rootSystem H).root j)) z at eqn
  refine eqn.trans ?_
  rw [RootPairing.reflection_apply_root]
  change _ - _ * _ = (j.val : Dual ℂ H) (z - i.val z • coroot i.val)
  simp [mul_comm]

/-- Evaluation of a transformed root on a transformed Cartan element. -/
theorem word_root_eval (w : List H.root) (j : H.root) (z : H) :
    (rootWord H w j).val (cartanWord H w z) = j.val z := by
  induction w generalizing j z with
  | nil => rfl
  | cons i w ih =>
    change (rootWord H w _).val (cartanWord H w _) = _
    rw [ih, reflected_eval]
    simp

variable [FiniteDimensional ℂ M]

private theorem module_reflection (i : H.root) :
    ∃ (σ : L ≃ₗ⁅ℂ⁆ L) (τ : M ≃ₗ[ℂ] M),
      (∀ z : H, σ (z : L) = ((rootSystem H).coreflection i z : H)) ∧
      ∀ (x : L) (v : M), τ ⁅x,v⁆ = ⁅σ x, τ v⁆ := by
  letI : LieAlgebra ℚ L := {
    __ := Module.compHom L (algebraMap ℚ ℂ)
    lie_smul := fun q x y => LieAlgebra.lie_smul ((algebraMap ℚ ℂ) q) x y }
  letI : Module ℚ M := Module.compHom M (algebraMap ℚ ℂ)
  let p := fun σ : L ≃ₗ⁅ℂ⁆ L => ∃ τ : M ≃ₗ[ℂ] M, ∀ x v, τ ⁅x,v⁆ = ⁅σ x, τ v⁆
  obtain ⟨σ, ⟨τ, hh⟩, hσ⟩ := exists_coreflection_of_exp_stable H i p (by
    intro x χ hχ hx hd
    have hn := isNilpotent_toEnd_of_mem_rootSpace (M := M) H hχ hx
    exact ⟨expEquiv (toEnd ℂ L M x) hn, exp_intertwines x hd hn⟩) (by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s.trans t, fun x v => (congrArg t (hs x v)).trans (ht (a x) (s v))⟩)
  exact ⟨σ, τ, hσ, hh⟩

/-- Every Cartan Weyl word lifts simultaneously to the algebra and each
actual finite-dimensional representation. -/
theorem exists_module_weyl_word (w : List H.root) :
    ∃ (σ : L ≃ₗ⁅ℂ⁆ L) (τ : M ≃ₗ[ℂ] M),
      (∀ z : H, σ (z : L) = (cartanWord H w z : H)) ∧
      ∀ (x : L) (v : M), τ ⁅x,v⁆ = ⁅σ x, τ v⁆ := by
  induction w with
  | nil => exact ⟨LieEquiv.refl, LinearEquiv.refl ℂ M, fun _ => rfl, fun _ _ => rfl⟩
  | cons i w ih =>
    obtain ⟨σ, τ, hσ, hτ⟩ := module_reflection (M := M) H i
    obtain ⟨γ, δ, hγ, hδ⟩ := ih
    exact ⟨σ.trans γ, τ.trans δ, fun z => (congrArg γ (hσ z)).trans (hγ _),
      fun x v => (congrArg δ (hτ x v)).trans (hδ _ _)⟩

end CubicAnomaly.Classification.ClassicalConstituentWeyl
