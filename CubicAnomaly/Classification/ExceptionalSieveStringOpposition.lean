import CubicAnomaly.Classification.ExceptionalSieveStringCatalog
import CubicAnomaly.Classification.ClassicalConstituentChamber
import CubicAnomaly.Classification.ClassicalConstituentOpposition
import CubicAnomaly.Classification.WeylDualityObstruction

/-!
# Actual contragredients for the bounded Cartan types

Reflect a strictly dominant regular weight successively at positive simple
coroots. The resulting finite words realize the signed permutation encoded
by the contragredient labels. On actual irreducible modules this determines
the highest weight of the dual.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveStringOpposition

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ExceptionalSieveCatalog ExceptionalSieveProducts ExceptionalSieveStringCatalog
open ClassicalConstituentHighest ClassicalConstituentComparison ClassicalConstituentWeyl
open ClassicalConstituentOpposition ClassicalConstituentChamber

private def opposite (t : Factor) (i : t.Node) : t.Node :=
  ⟨(dualLabels (t, List.range t.rank))[i.val]! % t.rank,
    Nat.mod_lt _ (by cases t <;> simp [Factor.rank])⟩

private def descent {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) : ℕ → Vector ℤ n → List (Fin n)
  | 0, _ => []
  | k + 1, x =>
    match (List.finRange n).find? (fun i => (0 : ℤ) < x[i]) with
    | none => []
    | some i => i :: descent C k (Vector.ofFn fun j => x[j] - x[i] * C i j)

private def word (t : Factor) := descent (matrix t) 64 (Vector.replicate _ 1)

private theorem signed : ∀ t : Factor,
    WeylDualityObstruction.SignedCorootWord (matrix t) (word t) (opposite t) := by native_decide

set_option maxHeartbeats 3000000 in
private theorem labels_apply (t : Factor) (a : t.Label) (i : t.Node) :
    (dualLabels (t,List.ofFn a))[i.val]! = a (opposite t i) := by
  fin_cases t <;> fin_cases i <;> first | rfl | (simp +decide [dualLabels, opposite, Factor.rank]; rfl)

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

private theorem cartan_eq (w : List H.root) (z : H) :
    cartanWord H w z = WeylDualityObstruction.applyWord H w z := by
  induction w generalizing z with
  | nil => rfl
  | cons i w ih => exact ih _

/-- A word with the canonical opposite simple-node permutation on coroots
reverses the whole positive chamber. -/
theorem factor_opposition_word (t : Factor) (s : t.Node ≃ b.support)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t i j) (a : t.Label) :
    ∃ w : List H.root, (∀ i : H.root, b.IsPos i ↔ ¬ b.IsPos (rootWord H w i)) ∧
      ∀ i, ∃ j, cartanWord H w (coroot (s i).val.val) = -coroot (s j).val.val ∧
        a j = (dualLabels (t,List.ofFn a))[i.val]! := by
  classical
  let P := rootSystem H
  letI := P.indexNeg
  let w := (word t).map fun j => (s j).val
  have he (i : t.Node) : cartanWord H w (P.coroot (s i)) = -P.coroot (s (opposite t i)) :=
    (cartan_eq H ..).trans (by simpa only [w, b.toCoweightBasis_apply] using
      (WeylDualityObstruction.signed_word_indexed_coroots H b s _ _ hC (signed t) i))
  refine ⟨w, ?_, fun i => ⟨_, he i, (labels_apply t a i).symm⟩⟩
  obtain ⟨h, hh⟩ := ExceptionalSieveWeights.exists_height_element H b
  have hr (i : t.Node) : rootWord H w (s i) = -(s (opposite t i)).val := by
    apply P.coroot.injective
    rw [← coroot_word, he]
    exact (P.coroot_eq_neg_iff.mpr rfl).symm
  have hz : (cartanWord H w).symm h = -h := by
    apply b.toCoweightBasis.eval_injective
    apply b.toWeightBasis.ext
    intro j
    obtain ⟨i,rfl⟩ := s.surjective j
    have ht := word_root_eval H w (s i).val ((cartanWord H w).symm h)
    rw [LinearEquiv.apply_symm_apply, hr] at ht
    have hn := LinearMap.congr_fun (P.root_eq_neg_iff.mpr (rfl : -(s (opposite t i)).val =
      P.reflectionPerm (s (opposite t i)).val (s (opposite t i)).val)) h
    change (-(s (opposite t i)).val : H.root).val h = -(s (opposite t i)).val.val h at hn
    rw [b.toWeightBasis_apply]
    change (s i).val.val ((cartanWord H w).symm h) = (s i).val.val (-h)
    rw [← ht, hn, hh, b.height_one_of_mem_support (s (opposite t i)).property,
      map_neg, hh, b.height_one_of_mem_support (s i).property]
  intro i
  have ht := word_root_eval H w i ((cartanWord H w).symm h)
  rw [LinearEquiv.apply_symm_apply, hz, map_neg, hh, hh] at ht
  have hneg : b.height (rootWord H w i) = -b.height i := by exact_mod_cast ht
  have hne := b.height_ne_zero i
  simp only [RootPairing.Base.isPos_iff, hneg, not_lt]
  omega

variable [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
    [FiniteDimensional ℂ M] [IsIrreducible ℂ L M]

/-- An opposition-fixed highest label yields an equivariant linear
isomorphism with the finite-dimensional contragredient. -/
theorem factor_self_dual_of_fixed_label (t : Factor) (s : t.Node ≃ b.support)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t i j) (a : t.Label)
    (χ : Module.Dual ℂ H) (v : M) (hv : IsHighestVector H b χ v)
    (hl : ∀ i, χ (coroot (s i).val.val) = (a i : ℂ))
    (hf : dualLabels (t,List.ofFn a) = List.ofFn a) : Nonempty (M ≃ₗ⁅ℂ,L⁆ Dual ℂ M) := by
  letI := nontrivial_of_isIrreducible ℂ L M
  letI := dual_irreducible (L := L) (M := M)
  obtain ⟨w,hw,hcor⟩ := factor_opposition_word H b t s hC a
  obtain ⟨μ,f,_,hf₀,hm,hk,_⟩ :=
    ExceptionalSieveWeights.exists_bounded_dominant_highest_weight (M := Dual ℂ M) H b
  have hf' : IsHighestVector H b μ f := ⟨hf₀,hm,hk⟩
  have hh := dual_highest_weight_of_reversing_word H b w hw hv hf'
  have hs' : -(χ.comp (cartanWord H w).toLinearMap) = χ := by
    apply b.toCoweightBasis.ext
    intro j
    obtain ⟨i,rfl⟩ := s.surjective j
    obtain ⟨k,hk,he⟩ := hcor i
    rw [hf, getElem!_pos _ _ (by simp), List.getElem_ofFn] at he
    rw [b.toCoweightBasis_apply]
    change -χ (cartanWord H w (coroot (s i).val.val)) = χ (coroot (s i).val.val)
    rw [hk,map_neg,neg_neg,hl,hl,he]
  have hs : (μ : H → ℂ) = χ := funext fun z => (hh z).trans (LinearMap.congr_fun hs' z)
  obtain ⟨E,_⟩ := irreducible_equiv_of_highest_weight H hv (hs ▸ hf')
  exact ⟨E⟩

end CubicAnomaly.Classification.ExceptionalSieveStringOpposition
