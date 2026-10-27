import CubicAnomaly.Classification.ExternalTensor
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Evaluation on an irreducible Lie module

The canonical evaluation map from an irreducible module tensored with its
space of equivariant maps is injective over an algebraically closed field.
The proof uses density on the first tensor factor and extracts each
coefficient of a tensor. No complete reducibility of the target is assumed.
-/

namespace CubicAnomaly.Classification.TensorEvaluation

open LieModule Module
open scoped TensorProduct
open CubicAnomaly.Classification.LieDensity

noncomputable section

section Evaluation

variable {K L U W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup U] [Module K U] [LieRingModule L U] [LieModule K L U]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

/-- Evaluate an equivariant map on the first tensor factor. -/
def lieHomEvaluation : U ⊗[K] (U →ₗ⁅K,L⁆ W) →ₗ[K] W :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun f => f u
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := by intro u v; ext f; exact map_add f u v
      map_smul' := by intro c u; ext f; exact map_smul f c u }

omit [LieModule K L U] in
/-- The evaluation construction has its literal expected value on pure tensors. -/
@[simp] theorem lieHomEvaluation_tmul (u : U) (f : U →ₗ⁅K,L⁆ W) :
    lieHomEvaluation (u ⊗ₜ[K] f) = f u := rfl

/-- Evaluation with the equivariant maps restricted to a linear subspace. -/
def restrictedLieHomEvaluation (V : Submodule K (U →ₗ⁅K,L⁆ W)) :
    U ⊗[K] V →ₗ[K] W :=
  lieHomEvaluation.comp (V.subtype.lTensor U)

omit [LieModule K L U] in
/-- Restricted evaluation also has its literal value on pure tensors. -/
@[simp] theorem restrictedLieHomEvaluation_tmul
    (V : Submodule K (U →ₗ⁅K,L⁆ W)) (u : U) (f : V) :
    restrictedLieHomEvaluation V (u ⊗ₜ[K] f) = (f : U →ₗ⁅K,L⁆ W) u := rfl

/-- The left action intertwines evaluation with the given action on the target. -/
theorem lieHomEvaluation_comp_left_action (x : L) :
    (lieHomEvaluation (K := K) (L := L) (U := U) (W := W)).comp
        ((toEnd K L U x).rTensor (U →ₗ⁅K,L⁆ W)) =
      (toEnd K L W x).comp lieHomEvaluation := by
  ext u f
  exact f.map_lie x u

private def evaluationEndStabilizer {P : Type*} [AddCommGroup P] [Module K P]
    (S : Submodule K P) : Subalgebra K (Module.End K P) where
  carrier := {f | ∀ z ∈ S, f z ∈ S}
  zero_mem' := by intro z hz; simp
  one_mem' := by intro z hz; exact hz
  add_mem' := by intro f g hf hg z hz; exact S.add_mem (hf z hz) (hg z hz)
  mul_mem' := by intro f g hf hg z hz; exact hf _ (hg z hz)
  algebraMap_mem' := by intro c z hz; exact S.smul_mem c hz

private theorem rankOne_rTensor_eq_coefficient {V ι : Type*}
    [AddCommGroup V] [Module K V] [DecidableEq ι] (b : Basis ι K U) (i : ι) (u : U)
    (z : U ⊗[K] V) :
    ((b.coord i).smulRight u).rTensor V z =
      u ⊗ₜ[K] (TensorProduct.equivFinsuppOfBasisLeft b z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    simp only [LinearMap.rTensor_tmul, LinearMap.smulRight_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
      Basis.coord_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add z t hz ht =>
    simp only [map_add, Finsupp.add_apply, TensorProduct.tmul_add, hz, ht]

/-- Evaluation is injective when its first factor is an irreducible,
finite-dimensional Lie module over an algebraically closed field. The target
may be any Lie module, without a semisimplicity hypothesis. -/
theorem lieHomEvaluation_injective [IsAlgClosed K] [Module.Finite K U]
    [LieModule.IsIrreducible K L U] :
    Function.Injective (lieHomEvaluation (K := K) (L := L) (U := U) (W := W)) := by
  classical
  let E := lieHomEvaluation (K := K) (L := L) (U := U) (W := W)
  let A := (evaluationEndStabilizer E.ker).comap
    (Module.End.rTensorAlgHom K U (U →ₗ⁅K,L⁆ W))
  have hA : A = ⊤ := by
    apply subalgebra_eq_top_of_lie_action_mem (K := K) (L := L) (M := U)
    intro x
    change ∀ z ∈ E.ker, (toEnd K L U x).rTensor (U →ₗ⁅K,L⁆ W) z ∈ E.ker
    intro z hz
    change E ((toEnd K L U x).rTensor (U →ₗ⁅K,L⁆ W) z) = 0
    have he := LinearMap.congr_fun
      (lieHomEvaluation_comp_left_action (K := K) (U := U) (W := W) x) z
    change E ((toEnd K L U x).rTensor (U →ₗ⁅K,L⁆ W) z) = ⁅x, E z⁆ at he
    rw [he, LinearMap.mem_ker.mp hz, lie_zero]
  have hstable (f : Module.End K U) (z : U ⊗[K] (U →ₗ⁅K,L⁆ W))
      (hz : z ∈ E.ker) : f.rTensor (U →ₗ⁅K,L⁆ W) z ∈ E.ker := by
    have hf : f ∈ A := by rw [hA]; trivial
    exact hf z hz
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  change z = 0
  let b := Module.Free.chooseBasis K U
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  apply Finsupp.ext
  intro i
  simp only [map_zero, Finsupp.zero_apply]
  apply LieModuleHom.ext
  intro u
  have h := hstable ((b.coord i).smulRight u) z hz
  rw [rankOne_rTensor_eq_coefficient] at h
  exact LinearMap.mem_ker.mp h

private def forgetLieHom : (U →ₗ⁅K,L⁆ W) →ₗ[K] (U →ₗ[K] W) where
  toFun := LieModuleHom.toLinearMap
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

omit [LieModule K L U] in
/-- The actual equivariant-map multiplicity space is finite-dimensional when
both original modules are finite-dimensional. -/
theorem lieHom_space_finite [Module.Finite K U] [Module.Finite K W] :
    Module.Finite K (U →ₗ⁅K,L⁆ W) := by
  apply FiniteDimensional.of_injective (forgetLieHom (K := K) (L := L) (U := U) (W := W))
  intro f g h
  apply LieModuleHom.ext
  intro u
  exact LinearMap.congr_fun h u

/-- Surjective evaluation transfers faithfulness of the target action to its
irreducible tensor factor. -/
theorem lieHomEvaluation_left_faithful [LieModule.IsFaithful K L W]
    (hs : Function.Surjective (lieHomEvaluation (K := K) (L := L) (U := U) (W := W))) :
    LieModule.IsFaithful K L U := by
  apply (LieModule.isFaithful_iff' K L U).mpr
  intro x hx
  apply (LieModule.isFaithful_iff' K L W).mp inferInstance x
  intro w
  obtain ⟨z, rfl⟩ := hs w
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u f =>
    change ⁅x, f u⁆ = 0
    rw [← f.map_lie, hx, map_zero]
  | add z t hz ht => simp only [map_add, lie_add, hz, ht, add_zero]

end Evaluation

section CommutingIdeals

variable {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  (I J : LieIdeal K L) (hIJ : Disjoint I J)
  {U : Type*} [AddCommGroup U] [Module K U] [LieRingModule I U] [LieModule K I U]

/-- An element of a commuting ideal acts on equivariant maps by actual
postcomposition with its given action on the target. -/
def commutingIdealHomPostcompose (y : J) : Module.End K (U →ₗ⁅K,I⁆ W) where
  toFun f :=
    { toLinearMap := (toEnd K L W (y : L)).comp f.toLinearMap
      map_lie' := by
        intro x u
        change ⁅(y : L), f ⁅x, u⁆⁆ = ⁅(x : L), ⁅(y : L), f u⁆⁆
        rw [f.map_lie]
        change ⁅(y : L), ⁅(x : L), f u⁆⁆ = ⁅(x : L), ⁅(y : L), f u⁆⁆
        rw [leibniz_lie,
          CubicAnomaly.Classification.ExternalTensor.disjoint_ideal_bracket_eq_zero
            J I hIJ.symm y x, zero_lie, zero_add] }
  map_add' := by intro f g; ext u; exact lie_add _ _ _
  map_smul' := by intro c f; ext u; exact lie_smul _ _ _

omit [LieModule K I U] in
/-- The multiplicity-space action is literal postcomposition. -/
@[simp] theorem commutingIdealHomPostcompose_apply (y : J)
    (f : U →ₗ⁅K,I⁆ W) (u : U) :
    commutingIdealHomPostcompose I J hIJ y f u = ⁅(y : L), f u⁆ := rfl

/-- The actual postcomposition action satisfies the Lie module axioms. -/
def commutingIdealHomLieRingModule : LieRingModule J (U →ₗ⁅K,I⁆ W) where
  bracket y f := commutingIdealHomPostcompose I J hIJ y f
  add_lie := by intro x y f; ext u; exact add_lie (x : L) (y : L) (f u)
  lie_add := by intro x f g; ext u; exact lie_add (x : L) (f u) (g u)
  leibniz_lie := by intro x y f; ext u; exact leibniz_lie (x : L) (y : L) (f u)

omit [LieModule K I U] in
/-- The postcomposition action is linear over the ground field. -/
theorem commutingIdealHomLieModule :
    letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
    LieModule K J (U →ₗ⁅K,I⁆ W) := by
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  constructor
  · intro c x f; ext u; exact smul_lie c (x : L) (f u)
  · intro c x f; ext u; exact lie_smul c (x : L) (f u)

private def commutingIdealRestrictedEvaluationRange (htop : I ⊔ J = ⊤)
    (V : Submodule K (U →ₗ⁅K,I⁆ W))
    (hV : ∀ y : J, ∀ f ∈ V, commutingIdealHomPostcompose I J hIJ y f ∈ V) :
    LieSubmodule K L W where
  toSubmodule := (restrictedLieHomEvaluation V).range
  lie_mem := by
    intro x w hw
    obtain ⟨z, rfl⟩ := hw
    have hx : x ∈ I ⊔ J := by rw [htop]; trivial
    obtain ⟨i, hi, j, hj, rfl⟩ := (LieSubmodule.mem_sup I J x).mp hx
    rw [add_lie]
    apply (restrictedLieHomEvaluation V).range.add_mem
    · induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u f =>
        refine ⟨⁅(⟨i, hi⟩ : I), u⁆ ⊗ₜ[K] f, ?_⟩
        exact (f : U →ₗ⁅K,I⁆ W).map_lie ⟨i, hi⟩ u
      | add z t hz ht =>
        simp only [map_add, lie_add]
        exact (restrictedLieHomEvaluation V).range.add_mem hz ht
    · induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u f =>
        refine ⟨u ⊗ₜ[K] ⟨commutingIdealHomPostcompose I J hIJ ⟨j, hj⟩ f,
          hV ⟨j, hj⟩ f f.property⟩, rfl⟩
      | add z t hz ht =>
        simp only [map_add, lie_add]
        exact (restrictedLieHomEvaluation V).range.add_mem hz ht

omit [LieModule K I U] in
/-- A nonzero subspace of equivariant maps stable under the commuting ideal
already evaluates onto an irreducible ambient module. -/
theorem commutingIdeal_restrictedEvaluation_surjective
    [LieModule.IsIrreducible K L W] (htop : I ⊔ J = ⊤)
    (V : Submodule K (U →ₗ⁅K,I⁆ W))
    (hV : ∀ y : J, ∀ f ∈ V, commutingIdealHomPostcompose I J hIJ y f ∈ V)
    (hne : ∃ f ∈ V, f ≠ 0) :
    Function.Surjective (restrictedLieHomEvaluation V) := by
  let S := commutingIdealRestrictedEvaluationRange I J hIJ htop V hV
  have hS : S ≠ ⊥ := by
    intro he
    obtain ⟨f, hf, hf0⟩ := hne
    apply hf0
    apply LieModuleHom.ext
    intro u
    have hu : f u ∈ S := ⟨u ⊗ₜ[K] ⟨f, hf⟩, rfl⟩
    rw [he] at hu
    exact hu
  have htopS : S = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top S).resolve_left hS
  apply LinearMap.range_eq_top.mp
  exact congrArg LieSubmodule.toSubmodule htopS

omit [LieModule K I U] in
/-- Evaluation is onto when the ideals span the ambient algebra and at least
one nonzero equivariant map into the irreducible target exists. -/
theorem commutingIdeal_lieHomEvaluation_surjective
    (hIJ : Disjoint I J) [LieModule.IsIrreducible K L W] (htop : I ⊔ J = ⊤)
    (hne : ∃ f : U →ₗ⁅K,I⁆ W, f ≠ 0) :
    Function.Surjective (lieHomEvaluation (K := K) (L := I) (U := U) (W := W)) := by
  have hs := commutingIdeal_restrictedEvaluation_surjective I J hIJ htop
    (⊤ : Submodule K (U →ₗ⁅K,I⁆ W)) (fun _ _ _ => trivial)
    (by obtain ⟨f, hf⟩ := hne; exact ⟨f, trivial, hf⟩)
  intro w
  obtain ⟨z, hz⟩ := hs w
  exact ⟨(⊤ : Submodule K (U →ₗ⁅K,I⁆ W)).subtype.lTensor U z, hz⟩

omit [LieModule K I U] in
/-- The commuting ideal acts on the right tensor factor under evaluation. -/
theorem lieHomEvaluation_comp_right_action (y : J) :
    (lieHomEvaluation (K := K) (L := I) (U := U) (W := W)).comp
        ((commutingIdealHomPostcompose I J hIJ y).lTensor U) =
      (toEnd K L W (y : L)).comp lieHomEvaluation := by
  ext u f
  rfl

/-- The canonical tensor factorization obtained from actual equivariant maps. -/
def commutingIdealEvaluationEquiv [IsAlgClosed K] [Module.Finite K U]
    [LieModule.IsIrreducible K I U] [LieModule.IsIrreducible K L W]
    (htop : I ⊔ J = ⊤) (hne : ∃ f : U →ₗ⁅K,I⁆ W, f ≠ 0) :
    U ⊗[K] (U →ₗ⁅K,I⁆ W) ≃ₗ[K] W :=
  LinearEquiv.ofBijective lieHomEvaluation
    ⟨lieHomEvaluation_injective,
      commutingIdeal_lieHomEvaluation_surjective I J hIJ htop hne⟩

/-- The tensor factorization sends a pure tensor to actual evaluation. -/
@[simp] theorem commutingIdealEvaluationEquiv_tmul [IsAlgClosed K] [Module.Finite K U]
    [LieModule.IsIrreducible K I U] [LieModule.IsIrreducible K L W]
    (htop : I ⊔ J = ⊤) (hne : ∃ f : U →ₗ⁅K,I⁆ W, f ≠ 0)
    (u : U) (f : U →ₗ⁅K,I⁆ W) :
    commutingIdealEvaluationEquiv I J hIJ htop hne (u ⊗ₜ[K] f) = f u := rfl

/-- The actual multiplicity space is irreducible for the commuting ideal.
This is proved from the evaluation map, without a supplied decomposition. -/
theorem commutingIdealHom_irreducible [IsAlgClosed K] [Module.Finite K U]
    [LieModule.IsIrreducible K I U] [LieModule.IsIrreducible K L W]
    (htop : I ⊔ J = ⊤) (hne : ∃ f : U →ₗ⁅K,I⁆ W, f ≠ 0) :
    letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
    LieModule.IsIrreducible K J (U →ₗ⁅K,I⁆ W) := by
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  letI : Nontrivial (U →ₗ⁅K,I⁆ W) := by
    obtain ⟨f, hf⟩ := hne
    exact ⟨⟨f, 0, hf⟩⟩
  letI : Nontrivial U := LieModule.nontrivial_of_isIrreducible K I U
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  obtain ⟨c, hc⟩ := Module.Projective.exists_dual_eq_one K hu
  apply LieModule.IsIrreducible.mk
  intro N hN
  have hNV : ∀ y : J, ∀ f ∈ N.toSubmodule,
      commutingIdealHomPostcompose I J hIJ y f ∈ N.toSubmodule := by
    intro y f hf
    exact N.lie_mem hf
  have hNne : ∃ f ∈ N.toSubmodule, f ≠ 0 := by
    letI : Nontrivial N := (LieSubmodule.nontrivial_iff_ne_bot K J _).mpr hN
    obtain ⟨f, hf⟩ := exists_ne (0 : N)
    exact ⟨f, f.property, fun he => hf (Subtype.ext he)⟩
  have hs := commutingIdeal_restrictedEvaluation_surjective I J hIJ htop
    N.toSubmodule hNV hNne
  apply top_unique
  intro f _
  obtain ⟨z, hz⟩ := hs (lieHomEvaluation (u ⊗ₜ[K] f))
  have ht : N.toSubmodule.subtype.lTensor U z = u ⊗ₜ[K] f :=
    lieHomEvaluation_injective hz
  have hmem : TensorProduct.lid K (U →ₗ⁅K,I⁆ W)
      (c.rTensor (U →ₗ⁅K,I⁆ W) (N.toSubmodule.subtype.lTensor U z)) ∈ N := by
    clear hz ht
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v g =>
      change c v • (g : U →ₗ⁅K,I⁆ W) ∈ N
      exact N.smul_mem (c v) g.property
    | add z t hz ht =>
      simp only [map_add]
      exact N.add_mem hz ht
  simpa only [ht, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hc, one_smul] using hmem

omit [LieModule K I U] in
/-- The actual multiplicity action is faithful whenever the ambient action
is faithful and irreducible and the two commuting ideals span the algebra. -/
theorem commutingIdealHom_faithful [LieModule.IsFaithful K L W]
    [LieModule.IsIrreducible K L W]
    (htop : I ⊔ J = ⊤) (hne : ∃ f : U →ₗ⁅K,I⁆ W, f ≠ 0) :
    letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
    letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
    LieModule.IsFaithful K J (U →ₗ⁅K,I⁆ W) := by
  letI := commutingIdealHomLieRingModule (U := U) (W := W) I J hIJ
  letI := commutingIdealHomLieModule (U := U) (W := W) I J hIJ
  apply (LieModule.isFaithful_iff' K J (U →ₗ⁅K,I⁆ W)).mpr
  intro y hy
  apply Subtype.ext
  apply (LieModule.isFaithful_iff' K L W).mp inferInstance (y : L)
  intro w
  obtain ⟨z, rfl⟩ := commutingIdeal_lieHomEvaluation_surjective I J hIJ htop hne w
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u f => exact LieModuleHom.congr_fun (hy f) u
  | add z t hz ht => simp only [map_add, lie_add, hz, ht, add_zero]

end CommutingIdeals

section ActualFactor

variable {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

omit [LieAlgebra K L] [LieModule K L W] in
/-- An actual atomic Lie submodule is irreducible under its inherited action. -/
theorem atomic_lieSubmodule_irreducible (S : LieSubmodule K L W) (hS : IsAtom S) :
    LieModule.IsIrreducible K L S := by
  letI : Nontrivial S := (LieSubmodule.nontrivial_iff_ne_bot K L W).mpr hS.ne_bot
  apply LieModule.IsIrreducible.mk
  intro N hN
  have hinj := LieSubmodule.map_injective_of_injective (f := S.incl) Subtype.coe_injective
  apply hinj
  rw [S.map_incl_top]
  apply (hS.le_iff_eq ?_).mp LieSubmodule.map_incl_le
  intro he
  apply hN
  apply hinj
  simpa only [LieSubmodule.map_bot] using he

/-- A finite-dimensional module has an actual irreducible restricted submodule.
For complementary commuting ideals, this produces a canonical bijective
evaluation map and hence the two-factor tensor decomposition. -/
theorem exists_atomic_evaluation_factorization [IsAlgClosed K] [Module.Finite K W]
    [LieModule.IsIrreducible K L W]
    (I J : LieIdeal K L) (hIJ : Disjoint I J) (htop : I ⊔ J = ⊤) :
    ∃ S : LieSubmodule K I W, IsAtom S ∧ LieModule.IsIrreducible K I S ∧
      Function.Bijective (lieHomEvaluation (K := K) (L := I) (U := S) (W := W)) := by
  letI : Nontrivial W := LieModule.nontrivial_of_isIrreducible K L W
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (α := LieSubmodule K I W)
  letI := atomic_lieSubmodule_irreducible S hS
  refine ⟨S, hS, inferInstance, lieHomEvaluation_injective, ?_⟩
  apply commutingIdeal_lieHomEvaluation_surjective I J hIJ htop
  refine ⟨S.incl, ?_⟩
  intro he
  apply hS.ne_bot
  apply (LieSubmodule.eq_bot_iff S).mpr
  intro w hw
  exact LieModuleHom.congr_fun he ⟨w, hw⟩

end ActualFactor

end

end CubicAnomaly.Classification.TensorEvaluation
