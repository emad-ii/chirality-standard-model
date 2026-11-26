import CubicAnomaly.Classification.ClassicalConstituentHighest
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Minuscule weights from signed integral coordinates

Cartan coordinates in a finite set can be checked just on the simple roots.
Stability and the bound on all coroot values follow by reflection induction.
For a highest vector the values on positive coroots are nonnegative by the
primitive-vector theorem for its actual root triples.
-/

namespace CubicAnomaly.Classification.MinusculeIntegralWeights

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentHighest

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]

/-- A finite signed-weight model gives a Weyl-stable set of actual complex
linear weights. Its highest weight is minuscule on every positive coroot. -/
theorem minuscule_finset_of_integral_labels {n : ℕ} (s : Fin n ≃ b.support)
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : ∀ i j, b.cartanMatrix (s i) (s j) = C i j)
    {ι : Type*} [Fintype ι] (d : ι → Fin n → ℤ) (e : ι)
    (hstep : ∀ u i, ∃ v, ∀ j, d v j = d u j - C i j * d u i)
    (hbound : ∀ u i, -1 ≤ d u i ∧ d u i ≤ 1)
    (χ : Module.Dual ℂ H) (hχ : ∀ i, χ (coroot (s i).val.val) = (d e i : ℂ))
    {v : M} (hv : IsHighestVector H b χ v) :
    ∃ S : Finset (H → ℂ), (χ : H → ℂ) ∈ S ∧
      (∀ μ ∈ S, ∀ i : H.root, (fun z => μ ((rootSystem H).coreflection i z)) ∈ S) ∧
      (∀ i : H.root, b.IsPos i → χ (coroot i.val) = 0 ∨ χ (coroot i.val) = 1) ∧
      S.card ≤ Fintype.card ι := by
  classical
  let basis := b.toCoweightBasis.reindex s.symm
  let wt (u : ι) : Dual ℂ H := basis.constr ℂ (fun j => (d u j : ℂ))
  let S : Finset (H → ℂ) := Finset.univ.image fun u => (wt u : H → ℂ)
  let P := rootSystem H
  have hbas (i : Fin n) : basis i = coroot (s i).val.val := by
    simp [basis, b.toCoweightBasis_apply]
  have hwt (u i) : wt u (coroot (s i).val.val) = (d u i : ℂ) := by
    rw [← hbas]
    exact basis.constr_basis ..
  have heq : wt e = χ := basis.ext fun j => by rw [hbas, hwt, hχ]
  have he (u : ι) : (wt u : H → ℂ) ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ u)
  have hs (i : H.root) (hi : i ∈ b.support) (μ : H → ℂ) (hμ : μ ∈ S) :
      (fun z => μ (P.coreflection i z)) ∈ S := by
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hμ
    obtain ⟨k,hk⟩ := s.surjective ⟨i,hi⟩
    obtain ⟨v,hr⟩ := hstep u k
    have hw : (wt u).comp (P.coreflection i).toLinearMap = wt v := by
      apply basis.ext
      intro j
      rw [hbas, LinearMap.comp_apply]
      change wt u (P.coreflection i (P.coroot (s j))) = wt v (coroot (s j).val.val)
      rw [RootPairing.coreflection_apply_coroot, map_sub, map_smul, hwt, hr]
      have hmat := b.algebraMap_cartanMatrixIn_apply ℤ (s k) (s j)
      change ((b.cartanMatrix (s k) (s j) : ℤ) : ℂ) = P.pairing (s k) (s j) at hmat
      have hie : i = (s k).val := (congrArg Subtype.val hk).symm
      rw [hie, ← hmat, hC]
      change wt u (coroot (s j).val.val) - _ * wt u (coroot (s k).val.val) = _
      rw [hwt,hwt]
      push_cast
      rfl
    change ((wt u).comp (P.coreflection i).toLinearMap : H → ℂ) ∈ S
    rw [hw]
    exact he v
  let stable (i : H.root) := ∀ μ ∈ S, (fun z => μ (P.coreflection i z)) ∈ S
  have reflected (i j : H.root) (hi : stable i) (hj : stable j) : stable (P.reflectionPerm j i) := by
    intro μ hμ
    have hc : P.coreflection (P.reflectionPerm j i) =
        P.coreflection j * P.coreflection i * P.coreflection j := P.flip.reflection_reflectionPerm
    simp only [hc, LinearEquiv.mul_apply]
    exact hj _ (hi _ (hj _ hμ))
  have hall (i : H.root) : stable i :=
    b.induction_reflect i (fun j hj => reflected j j hj hj) hs
      (fun j k hj hk => reflected j k hj (hs k hk))
  have hval (i : H.root) : ∀ μ ∈ S,
      μ (P.coroot i) = -1 ∨ μ (P.coroot i) = 0 ∨ μ (P.coroot i) = 1 := by
    let p (i : H.root) := ∀ μ ∈ S,
      μ (P.coroot i) = -1 ∨ μ (P.coroot i) = 0 ∨ μ (P.coroot i) = 1
    have step (j k : H.root) (hj : p j) : p (P.reflectionPerm k j) := by
      intro μ hμ
      rw [P.coroot_reflectionPerm]
      exact hj _ (hall k μ hμ)
    apply b.induction_reflect (p := p) i (fun j h => step j j h) _ (fun j k h _ => step j k h)
    intro j hj μ hμ
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hμ
    obtain ⟨k,hk⟩ := s.surjective ⟨j,hj⟩
    change wt u (P.coroot j) = -1 ∨ wt u (P.coroot j) = 0 ∨ wt u (P.coroot j) = 1
    rw [← show (s k).val = j from congrArg Subtype.val hk]
    change wt u (coroot (s k).val.val) = -1 ∨ wt u (coroot (s k).val.val) = 0 ∨
      wt u (coroot (s k).val.val) = 1
    rw [hwt]
    have := hbound u k
    rcases (show d u k = -1 ∨ d u k = 0 ∨ d u k = 1 by omega) with hh | hh | hh <;> simp [hh]
  refine ⟨S, heq ▸ he e, fun μ hμ i => hall i μ hμ, ?_, Finset.card_image_le.trans (by simp)⟩
  intro i hi
  have hne : i.val.IsNonZero := (Finset.mem_filter.mp i.property).2
  obtain ⟨z,x,y,ht,hx,hy⟩ := exists_isSl2Triple_of_weight_isNonZero hne
  have hz := ht.h_eq_coroot hne hx hy
  subst z
  have hprim : ht.HasPrimitiveVectorWith v (χ (coroot i.val)) :=
    ⟨hv.1, hv.2.1 _, hv.2.2 _ hi x hx⟩
  obtain ⟨m,hm⟩ := hprim.exists_nat
  refine (hval i _ (heq ▸ he e)).resolve_left ?_
  intro hn
  have hn' : (m : ℂ) = -1 := hm.symm.trans hn
  have : (m : ℤ) = -1 := by exact_mod_cast hn'
  omega

end CubicAnomaly.Classification.MinusculeIntegralWeights
