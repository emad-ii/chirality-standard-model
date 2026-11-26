import CubicAnomaly.Fixed.E8RadicalFamily
import CubicAnomaly.Fixed.E8MatterIrreducible

/-!
# The local factor of the exceptional degree-one module

The full radical commutes with the family algebra. In the signed matter
coordinates, the traceless family matrices generate all coordinate transfers
up to scalars. Thus each radical element acts by the same operator on all
three copies of the existing `Matter27`. A local invariant subspace gives a
zero-grade invariant subspace by taking its three copies. Irreducibility of
the actual degree-one module then gives irreducibility of the local action.
-/

namespace CubicAnomaly.Fixed.E8LocalMatter

open Matrix
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8MatterMatching
open CubicAnomaly.Fixed.E8MatterIrreducible
open CubicAnomaly.Fixed.E8FullCubic
open CubicAnomaly.Fixed.E8RadicalFamily
open CubicAnomaly.Fixed.MatterSpectrum
open CubicAnomaly.Fixed.MatterFamilyCoordinates
open CubicAnomaly.Fixed.FamilyAnomaly

noncomputable section

private def copiesRep : zeroSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ Matter81 :=
  actualMatterEquiv.symm.lieConj.toLieHom.comp
    (LieModule.toEnd ℂ zeroSubalgebra ActualMatter)

private theorem copiesRep_apply (x : zeroSubalgebra) (v : Matter81) :
    copiesRep x v = actualMatterEquiv.symm ⁅x, actualMatterEquiv v⁆ := rfl

private theorem copiesRep_family (F : FamilyLie) (v : Matter81) :
    copiesRep (E8A2.sl3ZeroEmbedding F) v = familyCopyActionMap F.val v := by
  rw [copiesRep_apply, LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  exact e8_matter_family_action F v

private theorem familyCopyAction_one (v : Matter81) :
    familyCopyActionMap 1 v = v := by
  funext i
  simp [familyCopyAction, Matrix.one_apply, ite_smul]

private theorem familyCopyAction_single (p q : Fin 3) (v : Matter81) :
    familyCopyActionMap (Matrix.single p q (1 : ℂ)) v = Pi.single p (v q) := by
  funext i
  by_cases h : p = i
  · subst i
    simp [familyCopyAction, Matrix.single_apply, ite_smul]
  · simp [familyCopyAction, h, Ne.symm h]

private theorem coordinates_of_commuting (A : Module.End ℂ Matter81)
    (hc : ∀ (F : FamilyLie) (v : Matter81),
      A (familyCopyActionMap F.val v) = familyCopyActionMap F.val (A v))
    (v : Matter81) (i : Fin 3) :
    A (Pi.single 0 (v i)) 0 = A v i := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := Matrix.single 0 i 1
  let t := M.trace / 3
  let F : FamilyLie := ⟨M - t • 1, by
    change Matrix.trace (M - t • (1 : Matrix (Fin 3) (Fin 3) ℂ)) = 0
    simp [t, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]⟩
  have hh := hc F v
  change A (familyCopyActionMap (M - t • 1) v) =
    familyCopyActionMap (M - t • 1) (A v) at hh
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    familyCopyAction_one] at hh
  rw [A.map_sub, A.map_smul] at hh
  have hu := sub_left_inj.mp hh
  change A (familyCopyActionMap (Matrix.single 0 i 1) v) =
    familyCopyActionMap (Matrix.single 0 i 1) (A v) at hu
  rw [familyCopyAction_single, familyCopyAction_single] at hu
  simpa using congrFun hu 0

private def localOperator (x : fullRadical) : Module.End ℂ Matter27 :=
  (LinearMap.proj (0 : Fin 3)).comp
    ((copiesRep x.val).comp (LinearMap.single ℂ (fun _ : Fin 3 => Matter27) 0))

private theorem copiesRep_radical (x : fullRadical) (v : Matter81) (i : Fin 3) :
    copiesRep x.val v i = localOperator x (v i) := by
  symm
  refine coordinates_of_commuting (copiesRep x.val) ?_ v i
  intro F w
  have h : ⁅copiesRep x.val, copiesRep (E8A2.sl3ZeroEmbedding F)⁆ = 0 := by
    rw [← copiesRep.map_lie, e8_radical_family_commute, map_zero]
  have he := LinearMap.congr_fun h w
  change copiesRep x.val (copiesRep (E8A2.sl3ZeroEmbedding F) w) -
    copiesRep (E8A2.sl3ZeroEmbedding F) (copiesRep x.val w) = 0 at he
  simpa only [copiesRep_family] using sub_eq_zero.mp he

/-- The action of the actual 78-dimensional ideal on the local matter factor. -/
def localRepresentation : fullRadical →ₗ⁅ℂ⁆ Module.End ℂ Matter27 where
  toFun := localOperator
  map_add' x y := by
    apply LinearMap.ext
    intro u
    change copiesRep (x.val + y.val) (Pi.single 0 u) 0 = _
    rw [map_add]
    rfl
  map_smul' t x := by
    apply LinearMap.ext
    intro u
    change copiesRep (t • x.val) (Pi.single 0 u) 0 = _
    rw [map_smul]
    rfl
  map_lie' := by
    intro x y
    apply LinearMap.ext
    intro u
    change copiesRep ⁅x.val, y.val⁆ (Pi.single 0 u) 0 = _
    rw [copiesRep.map_lie]
    change copiesRep x.val (copiesRep y.val (Pi.single 0 u)) 0 -
      copiesRep y.val (copiesRep x.val (Pi.single 0 u)) 0 =
      localOperator x (localOperator y u) - localOperator y (localOperator x u)
    rw [copiesRep_radical x (copiesRep y.val _) 0, copiesRep_radical y (copiesRep x.val _) 0]
    rfl

instance : LieRingModule fullRadical Matter27 :=
  LieRingModule.compLieHom Matter27 localRepresentation

instance : LieModule ℂ fullRadical Matter27 :=
  LieModule.compLieHom Matter27 localRepresentation

/-- The existing signed bijection identifies three copies of the local radical
module with the actual degree-one adjoint module, equivariantly. -/
def localCopiesEquiv : Matter81 ≃ₗ⁅ℂ,fullRadical⁆ ActualMatter where
  __ := actualMatterEquiv
  map_lie' := by
    intro x v
    change actualMatterEquiv ⁅x, v⁆ = ⁅x.val, actualMatterEquiv v⁆
    apply actualMatterEquiv.symm.injective
    rw [actualMatterEquiv.symm_apply_apply]
    funext i
    exact (copiesRep_radical x v i).symm

/-- The two factors of the complete zero algebra act by the local radical
operator and the literal defining family matrix on the displayed copies. -/
theorem e8_local_family_action (x : fullRadical) (F : E8A2.sl3) (v : Matter81) (i : Fin 3) :
    actualMatterEquiv.symm ⁅radicalFamilyEquiv (x, F), actualMatterEquiv v⁆ i =
      localRepresentation x (v i) + ∑ j, F.val i j • v j := by
  change copiesRep (radicalFamilyEquiv (x, F)) v i = _
  rw [e8_radicalFamilyEquiv_apply, map_add]
  change copiesRep x.val v i + copiesRep (E8A2.sl3ZeroEmbedding F) v i = _
  exact congrArg₂ (· + ·) (copiesRep_radical x v i) (congrFun (copiesRep_family F v) i)

set_option maxHeartbeats 800000 in
private def invariantCopies (U : LieSubmodule ℂ fullRadical Matter27) :
    LieSubmodule ℂ zeroSubalgebra ActualMatter where
  carrier := {w | ∀ i, actualMatterEquiv.symm w i ∈ U}
  zero_mem' i := by simp
  add_mem' := by
    intro w z hw hz i
    exact (show actualMatterEquiv.symm (w + z) i ∈ U by
      rw [map_add]; exact U.add_mem (hw i) (hz i))
  smul_mem' := by
    intro t w hw i
    change actualMatterEquiv.symm (t • w) i ∈ U
    rw [map_smul]
    exact U.smul_mem t (hw i)
  lie_mem := by
    intro z w hw i
    obtain ⟨⟨x, F⟩, rfl⟩ := radicalFamilyEquiv.surjective z
    have h := e8_local_family_action x F (actualMatterEquiv.symm w) i
    rw [actualMatterEquiv.apply_symm_apply] at h
    change actualMatterEquiv.symm ⁅radicalFamilyEquiv (x, F), w⁆ i ∈ U
    rw [h]
    exact U.add_mem (U.lie_mem (x := x) (hw i))
      (U.toSubmodule.sum_mem fun j _ => U.smul_mem _ (hw j))

set_option maxHeartbeats 1000000 in
/-- On its 27-dimensional local factor, the radical acts irreducibly. -/
theorem e8_local_matter_irreducible :
    LieModule.IsIrreducible ℂ fullRadical Matter27 := by
  haveI : Nontrivial Matter27 := Module.nontrivial_of_finrank_pos
    (R := ℂ) (by rw [matter27_finrank]; decide)
  apply LieModule.IsIrreducible.mk
  intro U hU
  have hlift (u : Matter27) : actualMatterEquiv (fun _ => u) ∈ invariantCopies U ↔ u ∈ U := by
    change (∀ i : Fin 3, actualMatterEquiv.symm (actualMatterEquiv (fun _ => u)) i ∈ U) ↔ _
    simp
  have hne : invariantCopies U ≠ ⊥ := by
    intro hbot
    apply hU
    apply (LieSubmodule.eq_bot_iff U).mpr
    intro u hu
    have h := (hlift u).mpr hu
    rw [hbot, LieSubmodule.mem_bot] at h
    simpa using congrArg (fun w : ActualMatter => actualMatterEquiv.symm w 0) h
  have htop := e8_actualMatter_submodule_eq_top (invariantCopies U) hne
  apply top_unique
  intro u _
  apply (hlift u).mp
  rw [htop]
  trivial

end

end CubicAnomaly.Fixed.E8LocalMatter
