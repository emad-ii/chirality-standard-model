import CubicAnomaly.Classification.ExceptionalSieveFactorProduct
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

/-!
# Self-duality assembled from the actual simple-factor constituents

We act simultaneously on a module and its contragredient. For a self-dual
constituent the two actions of its ideal generate one matrix algebra in
this product. Their finite join is simple and has the dimension of either
endomorphism ring, so the two projections identify these endomorphism
rings by an algebra equivalence carrying each Lie generator to its dual.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveFactorDual

open LieAlgebra LieModule Module ExceptionalSieveFactorProduct TensorEvaluation IdealProductRepresentation

universe u v
variable {L : Type u} {W : Type v} [LieRing L] [LieAlgebra ℂ L] [AddCommGroup W]
  [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W] [FiniteDimensional ℂ W]

private abbrev paired (x : L) : End ℂ W × End ℂ (Dual ℂ W) :=
  (toEnd ℂ L W x, toEnd ℂ L (Dual ℂ W) x)

private def pairedAlgebra (I : LieIdeal ℂ L) :=
  Algebra.adjoin ℂ (Set.range (fun x : I => paired (W := W) (x : L)))

private theorem paired_matrix (I : LieIdeal ℂ L) (S : LieSubmodule ℂ I W)
    [IsIrreducible ℂ I S] [Nontrivial W]
    (hb : Function.Bijective (lieHomEvaluation (K := ℂ) (L := I) (U := S) (W := W)))
    (e : S ≃ₗ⁅ℂ,I⁆ Dual ℂ S) :
    Nonempty (Matrix (Fin (finrank ℂ S)) (Fin (finrank ℂ S)) ℂ ≃ₐ[ℂ]
      pairedAlgebra (W := W) I) := by
  classical
  obtain ⟨F,hF,hf⟩ := isotypic_operator_lift I S hb
  let c := e.toLinearEquiv.symm.conjAlgEquiv (R := ℂ)
  let tr {P : Type v} [AddCommGroup P] [Module ℂ P] : End ℂ P →ₗ[ℂ] End ℂ (Dual ℂ P) :=
    Module.Dual.transpose
  have trmul {P : Type v} [AddCommGroup P] [Module ℂ P] (x y : End ℂ P) :
      tr (P := P) (x*y) = tr (P := P) y * tr (P := P) x := rfl
  have trone {P : Type v} [AddCommGroup P] [Module ℂ P] :
      tr (1 : End ℂ P) = 1 := rfl
  let D : End ℂ S →ₐ[ℂ] End ℂ (Dual ℂ W) := AlgHom.ofLinearMap
    (tr.comp (F.toLinearMap.comp (c.toLinearMap.comp tr)))
    (by change tr (F (c (tr 1))) = 1; rw [trone, map_one, map_one, trone])
    (fun x y => by change tr (F (c (tr (x*y)))) = _; rw [trmul, map_mul, map_mul, trmul]; rfl)
  have hc (x : I) : c (tr (toEnd ℂ I S x)) = -toEnd ℂ I S x := by
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (e.symm ((e v).comp (toEnd ℂ I S x))) = e (-⁅x,v⁆)
    rw [e.apply_symm_apply, map_neg, show e ⁅x,v⁆ = ⁅x,e v⁆ from e.map_lie x v]
    ext w
    simp
  have hd (x : I) : D (toEnd ℂ I S x) = toEnd ℂ L (Dual ℂ W) (x : L) := by
    change tr (F (c (tr (toEnd ℂ I S x)))) = _
    rw [hc, map_neg, hf, map_neg]
    rfl
  let G := F.prod D
  have hg (x : I) : G (toEnd ℂ I S x) = paired (W := W) (x : L) := Prod.ext (hf x) (hd x)
  have hrange : G.range = pairedAlgebra (W := W) I := by
    rw [← Algebra.map_top, ← LieDensity.lie_action_adjoin_eq_top (L := I) (M := S),
      AlgHom.map_adjoin, ← Set.range_comp, pairedAlgebra]
    exact congrArg (Algebra.adjoin ℂ) (congrArg Set.range (funext hg))
  rw [← hrange]
  exact ⟨(LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ S)).symm.trans
    (AlgEquiv.ofInjective G (fun _ _ h => hF (congrArg Prod.fst h)))⟩

omit [FiniteDimensional ℂ W] in
private theorem paired_commute (I J : LieIdeal ℂ L) (hIJ : Disjoint I J)
    (x : pairedAlgebra (W := W) I) (y : pairedAlgebra (W := W) J) :
    Commute (x : End ℂ W × End ℂ (Dual ℂ W)) (y : End ℂ W × End ℂ (Dual ℂ W)) := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute y.property
  rintro _ ⟨u,rfl⟩
  apply Commute.symm
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute x.property
  rintro _ ⟨v,rfl⟩
  have h (P : Type v) [AddCommGroup P] [Module ℂ P] [LieRingModule L P] [LieModule ℂ L P] :
      Commute (toEnd ℂ L P (u : L)) (toEnd ℂ L P (v : L)) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie, disjoint_ideals_bracket_zero J I hIJ.symm u v, map_zero]
  exact Prod.ext (h W).eq (h (Dual ℂ W)).eq

variable [IsIrreducible ℂ L W] [LieAlgebra.IsSemisimple ℂ L] [FiniteDimensional ℂ L]

/-- An irreducible module whose actual constituents on every atomic ideal
are self-dual is itself self-dual. -/
theorem self_dual_of_atomic_constituents (S : ∀ i : Atom L, LieSubmodule ℂ i.val W)
    (ha : ∀ i, IsAtom (S i)) (he : ∀ i, Nonempty (S i ≃ₗ⁅ℂ,i.val⁆ Dual ℂ (S i))) :
    Nonempty (W ≃ₗ⁅ℂ,L⁆ Dual ℂ W) := by
  classical
  letI := atomFintype L
  letI := nontrivial_of_isIrreducible ℂ L W
  letI (i : Atom L) := atomic_lieSubmodule_irreducible (S i) (ha i)
  let A (i : Atom L) := pairedAlgebra (W := W) i.val
  let d (i : Atom L) := finrank ℂ (S i)
  have hd (i : Atom L) : 0 < d i := by
    letI := nontrivial_of_isIrreducible ℂ i.val (S i)
    exact finrank_pos
  have hm (i : Atom L) : Nonempty (Matrix (Fin (d i)) (Fin (d i)) ℂ ≃ₐ[ℂ] A i) := by
    apply paired_matrix i.val (S i) _ (he i).some
    refine ⟨lieHomEvaluation_injective, commutingIdeal_lieHomEvaluation_surjective i.val i.valᶜ
      disjoint_compl_right sup_compl_eq_top ⟨(S i).incl, ?_⟩⟩
    intro hz
    apply (ha i).ne_bot
    exact (LieSubmodule.eq_bot_iff _).mpr fun y hy => LieModuleHom.congr_fun hz ⟨y,hy⟩
  have hdis := ((sSupIndep_iff _).mp (IsSemisimple.sSupIndep_isAtom (R := ℂ) (L := L))).pairwiseDisjoint
  have hh := matrix_join_dimension A d hd hm (fun i j hij => paired_commute _ _ (hdis hij)) Finset.univ
  let B := Finset.univ.sup A
  letI : IsSimpleRing B := hh.1
  let p := (AlgHom.fst ℂ (End ℂ W) (End ℂ (Dual ℂ W))).comp B.val
  let q := (AlgHom.snd ℂ (End ℂ W) (End ℂ (Dual ℂ W))).comp B.val
  have hdim : finrank ℂ B = (finrank ℂ W)^2 := hh.2.trans
    (congrArg (·^2) (all_atomic_constituent_dimension_product S ha).symm)
  have hpi : Function.Injective p := @RingHom.injective B (End ℂ W) _ _ _ _ p.toRingHom
  have hqi : Function.Injective q := @RingHom.injective B (End ℂ (Dual ℂ W)) _ _ _ _ q.toRingHom
  have hp : Function.Bijective p := ⟨hpi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℂ) (V := B) (V₂ := End ℂ W) (f := p.toLinearMap)
      (by change finrank ℂ B = finrank ℂ (End ℂ W); rw [hdim, finrank_linearMap, sq])).mp hpi⟩
  have hq : Function.Bijective q := ⟨hqi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℂ) (V := B) (V₂ := End ℂ (Dual ℂ W)) (f := q.toLinearMap)
      (by change finrank ℂ B = finrank ℂ (End ℂ (Dual ℂ W)); rw [hdim, finrank_linearMap, Subspace.dual_finrank_eq, sq])).mp hqi⟩
  let P := AlgEquiv.ofBijective p hp
  let Q := AlgEquiv.ofBijective q hq
  let F := P.symm.trans Q
  have hx (x : L) : paired (W := W) x ∈ B := by
    have hm : x ∈ ⨆ i : Atom L, i.val := by rw [atom_span (L := L)]; exact LieSubmodule.mem_top _
    refine LieSubmodule.iSup_induction (fun i : Atom L => i.val)
      (motive := fun x => paired (W := W) x ∈ B) hm ?_ ?_ ?_
    · intro i y hy
      apply (Finset.le_sup (f := A) (Finset.mem_univ i))
      exact Algebra.subset_adjoin (Set.mem_range_self (⟨y,hy⟩ : i.val))
    · change ((toEnd ℂ L W) 0, (toEnd ℂ L (Dual ℂ W)) 0) ∈ B
      rw [map_zero, map_zero]
      exact B.zero_mem
    · intro x y hx hy
      simpa [paired] using B.add_mem hx hy
  obtain ⟨u,hu⟩ := AlgEquiv.eq_linearEquivConjAlgEquiv F
  refine ⟨{ u with map_lie' := fun {x} w => ?_ }⟩
  let z : B := ⟨_,hx x⟩
  have hgen : F (toEnd ℂ L W x) = toEnd ℂ L (Dual ℂ W) x := by
    change Q (P.symm (P z)) = Q z
    rw [P.symm_apply_apply]
  rw [hu] at hgen
  have hv := LinearMap.congr_fun hgen (u w)
  simpa using hv

end CubicAnomaly.Classification.ExceptionalSieveFactorDual
