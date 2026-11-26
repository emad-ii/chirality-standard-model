import CubicAnomaly.Classification.ClassicalConstituentWeyl
import Mathlib.Data.Set.Finite.Lemmas

/-!
# The opposite Weyl chamber

Minimize a functional that is one on every simple coroot over the finite
Weyl orbit of the height element. A positive simple-root value there
would be decreased by the corresponding reflection. Every positive root
therefore takes a negative value, so the minimizing word reverses all
root signs.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentChamber

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentWeyl

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

/-- The root permutation records the Cartan action on every coroot. -/
theorem coroot_word (w : List H.root) (i : H.root) :
    cartanWord H w ((rootSystem H).coroot i) = (rootSystem H).coroot (rootWord H w i) := by
  induction w generalizing i with
  | nil => rfl
  | cons j w ih =>
    change cartanWord H w ((rootSystem H).coreflection j _) = _
    rw [← RootPairing.coroot_reflectionPerm, ih]
    rfl

private theorem cartan_append (v w : List H.root) (z : H) :
    cartanWord H (v ++ w) z = cartanWord H w (cartanWord H v z) := by
  induction v generalizing z with
  | nil => rfl
  | cons i v ih => exact ih _

/-- Every base of the actual complex root system admits a Weyl word
which reverses the sign of every root. -/
theorem exists_reversing_word :
    ∃ w : List H.root, ∀ i : H.root, b.IsPos i ↔ ¬ b.IsPos (rootWord H w i) := by
  classical
  let P := rootSystem H
  letI := P.indexNeg
  obtain ⟨h, hh⟩ := ExceptionalSieveWeights.exists_height_element H b
  let F := b.toCoweightBasis.constr ℂ (fun _ => (1 : ℂ))
  let orbit := fun (σ : Equiv.Perm H.root) =>
    b.toCoweightBasis.constr ℂ (fun i : b.support => P.coroot (σ i))
  have heq (w : List H.root) : (cartanWord H w).toLinearMap = orbit (rootWord H w) := by
    apply b.toCoweightBasis.ext
    intro i
    change cartanWord H w (b.toCoweightBasis i) =
      b.toCoweightBasis.constr ℂ _ (b.toCoweightBasis i)
    rw [Basis.constr_basis, b.toCoweightBasis_apply, coroot_word]
  let score := fun σ : Equiv.Perm H.root => (F (orbit σ h)).re
  let S := Set.range (rootWord H)
  obtain ⟨_, ⟨w, rfl⟩, hmin⟩ := Set.exists_min_image S score S.toFinite ⟨_, ⟨[], rfl⟩⟩
  let z := cartanWord H w h
  have hsimple (i : H.root) (hi : i ∈ b.support) : (i.val z).re ≤ 0 := by
    have hm := hmin _ (show rootWord H (w ++ [i]) ∈ S from ⟨_, rfl⟩)
    change (F (orbit _ h)).re ≤ (F (orbit _ h)).re at hm
    rw [← heq, ← heq] at hm
    change (F (cartanWord H w h)).re ≤ (F (cartanWord H (w ++ [i]) h)).re at hm
    rw [cartan_append] at hm
    change (F z).re ≤ (F (z - i.val z • P.coroot i)).re at hm
    have hf : F (P.coroot i) = 1 := by
      change F (P.coroot (⟨i,hi⟩ : b.support)) = _
      rw [← b.toCoweightBasis_apply]
      exact b.toCoweightBasis.constr_basis ℂ _ _
    simp only [map_sub, map_smul, hf, smul_eq_mul, mul_one, Complex.sub_re] at hm
    linarith
  have hpos (i : H.root) (hi : b.IsPos i) : (i.val z).re ≤ 0 := by
    apply hi.induction_on_add (p := fun a => (a.val z).re ≤ 0) hsimple
    intro a j k he ha hj
    have h := LinearMap.congr_fun he z
    change k.val z = a.val z + j.val z at h
    rw [h, Complex.add_re]
    exact add_nonpos ha (hsimple _ hj)
  refine ⟨w, fun i => ⟨fun hi hj => ?_, fun hj => ?_⟩⟩
  · have hz := hpos _ hj
    change ((rootWord H w i).val (cartanWord H w h)).re ≤ 0 at hz
    rw [word_root_eval, hh, Complex.intCast_re] at hz
    have hp := (RootPairing.Base.isPos_iff b).mp hi
    exact (not_le_of_gt (show 0 < (b.height i : ℝ) by exact_mod_cast hp)) hz
  · have hneg := hpos _ ((RootPairing.Base.IsPos.neg_iff_not b _).mpr hj)
    have he := LinearMap.congr_fun ((rootSystem H).root_eq_neg_iff.mpr
      (rfl : -(rootWord H w i) = (rootSystem H).reflectionPerm (rootWord H w i) (rootWord H w i))) z
    change (-(rootWord H w i) : H.root).val z = -(rootWord H w i).val z at he
    rw [he, Complex.neg_re] at hneg
    change -((rootWord H w i).val (cartanWord H w h)).re ≤ 0 at hneg
    rw [word_root_eval, hh, Complex.intCast_re] at hneg
    apply (RootPairing.Base.isPos_iff' b).mpr
    exact_mod_cast (show (0 : ℝ) ≤ (b.height i : ℝ) by linarith)

private theorem support_of_height_one {i : H.root} (hi : b.IsPos i) :
    0 < b.height i ∧ (b.height i = 1 → i ∈ b.support) := by
  apply hi.induction_on_add (p := fun j => 0 < b.height j ∧ (b.height j = 1 → j ∈ b.support))
  · intro j hj
    exact ⟨RootPairing.Base.isPos_of_mem_support hj, fun _ => hj⟩
  · intro i j k hsum hi hj
    rw [b.height_add hsum, b.height_one_of_mem_support hj]
    constructor <;> omega

private theorem preserves_support (σ : Equiv.Perm H.root)
    (hpos : ∀ i, b.IsPos i ↔ b.IsPos (σ i))
    (hadd : ∀ i j k, (rootSystem H).root k = (rootSystem H).root i + (rootSystem H).root j ↔
      (rootSystem H).root (σ k) = (rootSystem H).root (σ i) + (rootSystem H).root (σ j)) :
    ∀ i, i ∈ b.support ↔ σ i ∈ b.support := by
  have increasing (f : H.root → H.root) (hp : ∀ i, b.IsPos i → b.IsPos (f i))
      (ha : ∀ i j k, (rootSystem H).root k = (rootSystem H).root i + (rootSystem H).root j →
        (rootSystem H).root (f k) = (rootSystem H).root (f i) + (rootSystem H).root (f j))
      (i : H.root) (hi : b.IsPos i) : b.height i ≤ b.height (f i) := by
    apply hi.induction_on_add (p := fun j => b.height j ≤ b.height (f j))
    · intro j hj
      rw [b.height_one_of_mem_support hj]
      have h := (RootPairing.Base.isPos_iff b).mp (hp j (RootPairing.Base.isPos_of_mem_support hj))
      omega
    · intro j k l hsum hle hk
      rw [b.height_add hsum, b.height_add (ha _ _ _ hsum), b.height_one_of_mem_support hk]
      have h := (RootPairing.Base.isPos_iff b).mp (hp k (RootPairing.Base.isPos_of_mem_support hk))
      omega
  have he (i : H.root) (hi : b.IsPos i) : b.height i = b.height (σ i) := by
    apply le_antisymm (increasing σ (fun j => (hpos j).mp) (fun j k l => (hadd j k l).mp) i hi)
    have h := increasing σ.symm (fun j hj => (hpos _).mpr (by simpa using hj))
      (fun j k l he => (hadd _ _ _).mpr (by simpa using he)) (σ i) ((hpos i).mp hi)
    simpa using h
  intro i
  constructor
  · intro hi
    have hp := RootPairing.Base.isPos_of_mem_support hi
    exact (support_of_height_one H b ((hpos i).mp hp)).2 ((he i hp).symm.trans (b.height_one_of_mem_support hi))
  · intro hi
    have hp := (hpos i).mpr (RootPairing.Base.isPos_of_mem_support hi)
    exact (support_of_height_one H b hp).2 ((he i hp).trans (b.height_one_of_mem_support hi))

set_option maxHeartbeats 1500000 in
/-- Opposition acts by an actual permutation of the simple nodes. Its
action on roots and coroots is specified on the chosen Cartan. -/
theorem exists_opposition_nodes (w : List H.root)
    (hw : ∀ i : H.root, b.IsPos i ↔ ¬ b.IsPos (rootWord H w i)) :
    ∃ δ : Equiv.Perm b.support, ∀ i : b.support,
      (∀ z : H, (δ i).val.val z = -i.val.val (cartanWord H w z)) ∧
      cartanWord H w (coroot (δ i).val.val) = -coroot i.val.val := by
  classical
  let P := rootSystem H
  letI := P.indexNeg
  let s := rootWord H w
  let D : Equiv.Perm H.root := s.symm.trans (Equiv.neg _)
  have hD (i : H.root) (z : H) : (D i).val z = -i.val (cartanWord H w z) := by
    have hd : P.root (D i) = -P.root (s.symm i) := P.root_eq_neg_iff.mpr rfl
    have hneg := LinearMap.congr_fun hd z
    have he := word_root_eval H w (s.symm i) z
    change (s (s.symm i)).val (cartanWord H w z) = _ at he
    rw [s.apply_symm_apply] at he
    exact hneg.trans (congrArg Neg.neg he.symm)
  have hp (i : H.root) : b.IsPos i ↔ b.IsPos (D i) := by
    change b.IsPos i ↔ b.IsPos (-(s.symm i))
    rw [RootPairing.Base.IsPos.neg_iff_not]
    have h := hw (s.symm i)
    change b.IsPos (s.symm i) ↔ ¬b.IsPos (s (s.symm i)) at h
    rw [s.apply_symm_apply] at h
    tauto
  have ha (i j k : H.root) : P.root k = P.root i + P.root j ↔ P.root (D k) = P.root (D i) + P.root (D j) := by
    constructor
    · intro he
      ext z
      have h := LinearMap.congr_fun he (cartanWord H w z)
      change (D k).val z = (D i).val z + (D j).val z
      simp only [hD]
      change k.val _ = i.val _ + j.val _ at h
      rw [h, neg_add]
    · intro he
      ext y
      obtain ⟨z, rfl⟩ := (cartanWord H w).surjective y
      have h := LinearMap.congr_fun he z
      change (D k).val z = (D i).val z + (D j).val z at h
      simp only [hD, ← neg_add, neg_inj] at h
      exact h
  have hs := preserves_support H b D hp ha
  let δ : Equiv.Perm b.support := D.subtypeEquiv (fun i => hs i)
  refine ⟨δ, fun i => ⟨hD i, ?_⟩⟩
  change cartanWord H w (P.coroot (D i)) = -P.coroot i
  rw [coroot_word]
  apply P.coroot_eq_neg_iff.mpr
  apply P.root.injective
  ext y
  obtain ⟨z, rfl⟩ := (cartanWord H w).surjective y
  have he := word_root_eval H w (D i) z
  rw [hD] at he
  exact he.trans (LinearMap.congr_fun (P.root_eq_neg_iff.mpr rfl) (cartanWord H w z)).symm

end CubicAnomaly.Classification.ClassicalConstituentChamber
