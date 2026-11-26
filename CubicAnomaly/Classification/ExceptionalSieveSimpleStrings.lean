import CubicAnomaly.Classification.ChevalleySimpleTriples
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Dimension lower bounds from successively unused simple roots

After lowering in a list of distinct simple directions, the raising operator
at each unused node still kills the resulting vector. Its entire simple-root
string therefore contributes vectors with explicit and distinct joint weights.
These give dimension lower bounds from just the Cartan matrix and highest label.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveSimpleStrings

open LieAlgebra LieModule Module LieAlgebra.IsKilling

def level {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (a p : Fin n → ℕ) (i : Fin n) : ℤ :=
  (a i : ℤ) - ∑ j, (p j : ℤ) * C j i

/-- Integer lowering profiles. The last list element acts first. -/
def profiles {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℕ) :
    List (Fin n) → Finset (Fin n → ℕ)
  | [] => {0}
  | i :: w => (profiles C a w).biUnion fun p =>
      (Finset.range ((level C a p i).toNat + 1)).image fun k => p + Pi.single i k

/-- List enumeration in a repeated-node-free string, used to evaluate bounds
without a quadratic search for duplicate profiles. -/
def profileList {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℕ) :
    List (Fin n) → List (Fin n → ℕ)
  | [] => [0]
  | i :: w => (profileList C a w).flatMap fun p =>
    (List.range ((level C a p i).toNat + 1)).map fun k => p + Pi.single i k

private theorem profileList_finset {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℕ)
    (w : List (Fin n)) : (profileList C a w).toFinset = profiles C a w := by
  induction w with
  | nil => simp [profileList, profiles]
  | cons i w ih =>
    ext p
    simp only [profileList, profiles, Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset,
      List.mem_flatMap, List.mem_map, Finset.mem_range, List.mem_range, ← ih]

private theorem profileList_off {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℕ)
    (w : List (Fin n)) {i : Fin n} (hi : i ∉ w) {p} (hp : p ∈ profileList C a w) :
    p i = 0 := by
  induction w generalizing p with
  | nil => simpa only [profileList, List.mem_singleton] using congrArg (· i) (List.mem_singleton.mp hp)
  | cons j w ih =>
    obtain ⟨q, hq, hmem⟩ := List.mem_flatMap.mp hp
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hmem
    have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self)
    simp [Pi.single_eq_of_ne hij, ih (fun h => hi (List.mem_cons_of_mem j h)) hq]

private theorem profileList_nodup {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℕ)
    (w : List (Fin n)) (hw : w.Nodup) : (profileList C a w).Nodup := by
  induction w with
  | nil => simp [profileList]
  | cons i w ih =>
    obtain ⟨hi, hw⟩ := List.nodup_cons.mp hw
    apply List.nodup_flatMap.mpr
    constructor
    · intro p _
      apply List.Nodup.map _ List.nodup_range
      intro k l eqn
      simpa using congrFun eqn i
    · apply (ih hw).imp_of_mem
      intro p q hp hq hpq u hu hv
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hu
      obtain ⟨l,_,he⟩ := List.mem_map.mp hv
      apply hpq
      funext j
      by_cases hji : j = i
      · subst j
        rw [profileList_off C a w hi hp, profileList_off C a w hi hq]
      · simpa [Pi.single_eq_of_ne hji] using (congrFun he j).symm

theorem profileList_length {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → ℕ)
    (w : List (Fin n)) (hw : w.Nodup) : (profileList C a w).length = (profiles C a w).card := by
  rw [← profileList_finset, List.toFinset_card_of_nodup (profileList_nodup C a w hw)]

private theorem profile_mono {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    {a b : Fin n → ℕ} (hab : a ≤ b) (w : List (Fin n)) :
    profiles C a w ⊆ profiles C b w := by
  induction w with
  | nil => exact fun _ hp => hp
  | cons i w ih =>
    intro u hu
    obtain ⟨p, hp, himage⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨k,hk,hval⟩ := Finset.mem_image.mp himage
    subst u
    refine Finset.mem_biUnion.mpr ⟨p, ih hp, Finset.mem_image.mpr ⟨k, ?_, rfl⟩⟩
    apply Finset.mem_range.mpr
    have hle : level C a p i ≤ level C b p i := by
      unfold level
      exact sub_le_sub_right (by exact_mod_cast hab i) _
    have hk' := Finset.mem_range.mp hk
    omega

theorem profiles_card_monotone {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (w : List (Fin n))
    {a b : Fin n → ℕ} (hab : a ≤ b) : (profiles C a w).card ≤ (profiles C b w).card :=
  Finset.card_le_card (profile_mono C hab w)

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]

private theorem commute_power {x y : L} (h : ⁅x,y⁆ = 0) (k : ℕ) (v : M) :
    ⁅x, (toEnd ℂ L M y ^ k) v⁆ = (toEnd ℂ L M y ^ k) ⁅x,v⁆ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply, leibniz_lie x, h, zero_lie,
      zero_add, ih]

private theorem power_weight {x y : L} {v : M} {lam μ : ℂ}
    (hxy : ⁅x,y⁆ = -lam • y) (hv : ⁅x,v⁆ = μ • v) (k : ℕ) :
    ⁅x, (toEnd ℂ L M y ^ k) v⁆ = (μ - k * lam) • (toEnd ℂ L M y ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply, leibniz_lie x,
      hxy, smul_lie, ih, lie_smul, Nat.cast_succ]
    module

variable [FiniteDimensional ℂ L] [LieAlgebra.IsKilling ℂ L] [FiniteDimensional ℂ M]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  {n : ℕ} (s : Fin n ≃ b.support)

/-- Every lowering profile along distinct simple directions occurs in the
actual module through the prescribed highest vector. -/
theorem simple_string_card_le_finrank
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : ∀ i j, b.cartanMatrix (s i) (s j) = C i j)
    (a : Fin n → ℕ) (χ : Module.Dual ℂ H) (v : M) (hv : v ≠ 0)
    (hw : ∀ h : H, ⁅h,v⁆ = χ h • v) (hlabels : ∀ i, χ (coroot (s i).val.val) = (a i : ℂ))
    (hkill : ∀ i : Fin n, ∀ x ∈ rootSpace H (s i).val.val, ⁅x,v⁆ = 0)
    (w : List (Fin n)) (hnodup : w.Nodup) :
    (profiles C a w).card ≤ finrank ℂ M := by
  classical
  obtain ⟨E,F,ht,hE,hF,hm,_⟩ := ChevalleySimpleTriples.exists_simple_root_triples H b
  let basis := b.toWeightBasis.reindex s.symm
  let wt (p : Fin n → ℕ) := χ - basis.equivFun.symm (fun j => (p j : ℂ))
  have hsum (p : Fin n → ℕ) (h : H) :
      wt p h = χ h - ∑ j, (p j : ℂ) * (s j).val.val h := by
    simp [wt, basis, Basis.equivFun_symm_apply, LinearMap.sum_apply]
  have hlevel (p : Fin n → ℕ) (i : Fin n) : wt p (coroot (s i).val.val) = (level C a p i : ℂ) := by
    rw [hsum, hlabels, level]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have heq := b.algebraMap_cartanMatrixIn_apply ℤ (s j) (s i)
    change ((b.cartanMatrix (s j) (s i) : ℤ) : ℂ) = (s j).val.val (coroot (s i).val.val) at heq
    rw [← heq, hC]
  have hadj (p : Fin n → ℕ) (i : Fin n) (k : ℕ) (h : H) :
      wt (p + Pi.single i k) h = wt p h - k * (s i).val.val h := by
    simp only [hsum, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single i (f := fun j => ((((Pi.single i k : Fin n → ℕ) j) : ℕ) : ℂ) * (s j).val.val h)]
    · simp; ring
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  have witness (l : List (Fin n)) (hl : l.Nodup) (p : Fin n → ℕ) (hp : p ∈ profiles C a l) :
      ∃ m : M, m ≠ 0 ∧ (∀ h : H, ⁅h,m⁆ = wt p h • m) ∧
        ∀ j ∉ l, ⁅E (s j),m⁆ = 0 := by
    induction l generalizing p with
    | nil =>
      obtain rfl : p = 0 := Finset.mem_singleton.mp hp
      exact ⟨v,hv, fun h => by simpa [hsum] using hw h, fun j _ => hkill j _ (hE _)⟩
    | cons i l ih =>
      obtain ⟨p,hprev,himage⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨k,hk,hval⟩ := Finset.mem_image.mp himage
      rw [← hval]
      obtain ⟨m,hm₀,hmw,hme⟩ := ih hl.of_cons p hprev
      have hw₀ : (ht (s i)).HasPrimitiveVectorWith m ((level C a p i : ℤ) : ℂ) :=
        ⟨hm₀, (hlevel p i) ▸ hmw _, hme i (List.nodup_cons.mp hl).1⟩
      obtain ⟨r,hr⟩ := hw₀.exists_nat
      have hr' : level C a p i = (r : ℤ) := by exact_mod_cast hr
      have hkr : k ≤ r := by
        have hk' := Finset.mem_range.mp hk
        simp only [hr', Int.toNat_natCast] at hk'
        omega
      refine ⟨(toEnd ℂ L M (F (s i)) ^ k) m, hw₀.pow_toEnd_f_ne_zero_of_eq_nat hr hkr, ?_, ?_⟩
      · intro h
        rw [hadj]
        exact power_weight (show ⁅(h : L), F (s i)⁆ = -(s i).val.val h • F (s i) from
          lie_eq_smul_of_mem_rootSpace (hF _) h) (hmw h) k
      · intro j hj
        have hji : j ≠ i := fun hh => hj (hh ▸ List.mem_cons_self)
        rw [commute_power (hm _ _ (s.injective.ne hji)), hme j (fun h => hj (List.mem_cons_of_mem _ h)), map_zero]
  choose vec hv₀ hvw _ using fun p : ↥(profiles C a w) => witness w hnodup p.val p.property
  have inject : Function.Injective (fun p : ↥(profiles C a w) => (wt p.val : H → ℂ)) := by
    intro p q hh
    have hlin : wt p.val = wt q.val := LinearMap.ext (congrFun hh)
    have hcoeff := basis.equivFun.symm.injective (sub_right_inj.mp hlin)
    apply Subtype.ext
    funext j
    exact_mod_cast congrFun hcoeff j
  have hind : iSupIndep (fun μ : H → ℂ => (genWeightSpace M μ).toSubmodule) :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace ℂ H M)
  have hdim := ((hind.comp inject).linearIndependent _ (fun p =>
    weightSpace_le_genWeightSpace M _ ((mem_weightSpace _ _).mpr (hvw p))) hv₀).fintype_card_le_finrank
  simpa using hdim

end CubicAnomaly.Classification.ExceptionalSieveSimpleStrings
