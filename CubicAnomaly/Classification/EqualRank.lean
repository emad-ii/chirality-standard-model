import CubicAnomaly.Classification.CommonCartan
import CubicAnomaly.Classification.CompactGeometry
import CubicAnomaly.Classification.SelfDualAbsorption

/-!
# Homogeneous support from an actual common Cartan

An irreducible submodule of the ambient algebra is homogeneous for every
root grading whose degree-zero part contains the acting subalgebra.  Actual
contragredient modules have opposite degrees.  These facts turn the geometric
decomposition into three-class support, without supplying support as an input.
-/

namespace CubicAnomaly.Classification.EqualRank

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.CommonCartan

variable {K L A : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  [AddCommGroup A]

/-- Restriction of an actual ambient subrepresentation to a contained Cartan. -/
def restrictCartanSubmodule (S : LieSubalgebra K L) (hHS : H ≤ S)
    (N : LieSubmodule K S L) : LieSubmodule K H L where
  __ := N.toSubmodule
  lie_mem := fun {x} {_y} hy => N.lie_mem (x := ⟨x, hHS x.property⟩) hy

omit [CharZero K] [LieAlgebra.IsKilling K L] in
/-- A nonzero Cartan-stable subspace contains a nonzero actual root vector,
where the zero root is allowed. -/
theorem exists_nonzero_root_vector (N : LieSubmodule K H L) (hN : N ≠ ⊥) :
    ∃ α : H → K, ∃ x ∈ N, x ∈ rootSpace H α ∧ x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hN
  rw [LieSubmodule.eq_bot_iff]
  intro x hx
  suffices hall : ∀ y : N, (y : L) = 0 from hall ⟨x, hx⟩
  intro y
  have hy : y ∈ ⨆ α : H → K, genWeightSpace N α := by
    rw [iSup_genWeightSpace_eq_top]
    trivial
  induction hy using LieSubmodule.iSup_induction' with
  | mem α y hy =>
    exact h α y y.property
      (map_genWeightSpace_le N.incl ((LieSubmodule.mem_map _).mpr ⟨y, hy, rfl⟩))
  | zero => rfl
  | add x y _ _ hx hy => simp only [LieSubmodule.coe_add, hx, hy, add_zero]

/-- A root-grade is invariant under every acting subalgebra in degree zero. -/
noncomputable def ambientGradeSubmodule (S : LieSubalgebra K L)
    (degree : (H → K) →+ A)
    (hS : S.toSubmodule ≤ weightGrade H L degree 0) (a : A) : LieSubmodule K S L where
  toSubmodule := weightGrade H L degree a
  lie_mem := by
    intro x y hy
    simpa only [zero_add] using lie_mem_weightGrade H degree (hS x.property) hy

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [IsTriangularizable K H L] in
/-- One nonzero vector in an irreducible submodule fixes its entire degree. -/
theorem irreducible_submodule_le_grade_of_nonzero_mem
    (S : LieSubalgebra K L) (N : LieSubmodule K S L)
    [LieModule.IsIrreducible K S N] (degree : (H → K) →+ A)
    (hS : S.toSubmodule ≤ weightGrade H L degree 0) {a : A} {x : L}
    (hxN : x ∈ N) (hxa : x ∈ weightGrade H L degree a) (hx0 : x ≠ 0) :
    N.toSubmodule ≤ weightGrade H L degree a := by
  let P := (ambientGradeSubmodule H S degree hS a).comap N.incl
  have hP : P ≠ ⊥ := by
    intro hb
    have hxP : (⟨x, hxN⟩ : N) ∈ P := hxa
    rw [hb, LieSubmodule.mem_bot] at hxP
    exact hx0 (congrArg Subtype.val hxP)
  have hPtop : P = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top P).resolve_left hP
  intro y hy
  have hyP : (⟨y, hy⟩ : N) ∈ P := by rw [hPtop]; trivial
  exact hyP

omit [CharZero K] [LieAlgebra.IsKilling K L] in
/-- Irreducibility and Cartan containment construct a homogeneous degree. -/
theorem irreducible_submodule_homogeneous
    (S : LieSubalgebra K L) (hHS : H ≤ S) (N : LieSubmodule K S L)
    [LieModule.IsIrreducible K S N] (degree : (H → K) →+ A)
    (hS : S.toSubmodule ≤ weightGrade H L degree 0) :
    ∃ a : A, N.toSubmodule ≤ weightGrade H L degree a := by
  letI : Nontrivial N := LieModule.nontrivial_of_isIrreducible K S N
  have hN : N ≠ ⊥ := (LieSubmodule.nontrivial_iff_ne_bot K S L).mp inferInstance
  let N' := restrictCartanSubmodule H S hHS N
  have hN' : N' ≠ ⊥ := by
    intro hb
    apply hN
    apply LieSubmodule.toSubmodule_injective
    exact congrArg (fun T : LieSubmodule K H L => T.toSubmodule) hb
  obtain ⟨α, x, hxN, hxα, hx0⟩ := exists_nonzero_root_vector H N' hN'
  exact ⟨degree α, irreducible_submodule_le_grade_of_nonzero_mem H S N degree hS
    hxN (genWeightSpace_le_weightGrade H degree α hxα) hx0⟩

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
/-- A nonzero root vector in a grade identifies that grade with its root's degree. -/
theorem degree_eq_of_nonzero_root_mem_grade (degree : (H → K) →+ A)
    {α : H → K} {a : A} {x : L} (hx : x ∈ rootSpace H α)
    (hxa : x ∈ weightGrade H L degree a) (hx0 : x ≠ 0) : degree α = a := by
  by_contra hne
  have hd := (iSupIndep_weightGrade H (M := L) degree).pairwiseDisjoint hne
  have hxinf : x ∈ weightGrade H L degree (degree α) ⊓ weightGrade H L degree a :=
    ⟨genWeightSpace_le_weightGrade H degree α hx, hxa⟩
  rw [hd.eq_bot, Submodule.mem_bot] at hxinf
  exact hx0 hxinf

private theorem dual_root_pair_zero
    (S : LieSubalgebra K L) (hHS : H ≤ S)
    (P Q : LieSubmodule K S L) (e : Q ≃ₗ⁅K,S⁆ Module.Dual K P)
    {α β : H → K} (x : P) (y : Q)
    (hx : (x : L) ∈ rootSpace H α) (hy : (y : L) ∈ rootSpace H β)
    (hab : α + β ≠ 0) : e y x = 0 := by
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hab
  have ht' : α t + β t ≠ 0 := ht
  let s : S := ⟨t, hHS t.property⟩
  have hx' : ⁅s, x⁆ = α t • x := by
    apply Subtype.ext
    exact lie_eq_smul_of_mem_rootSpace hx t
  have hy' : ⁅s, y⁆ = β t • y := by
    apply Subtype.ext
    exact lie_eq_smul_of_mem_rootSpace hy t
  have h := congrArg (fun f : Module.Dual K P => f x) (e.map_lie s y)
  rw [hy', map_smul] at h
  change β t * e y x = -(e y ⁅s, x⁆) at h
  rw [hx', map_smul, smul_eq_mul] at h
  have hmul : (α t + β t) * e y x = 0 := by
    rw [add_mul, h, add_neg_cancel]
  exact (mul_eq_zero.mp hmul).resolve_left ht'

/-- Equivariant duality forces the homogeneous degrees to be opposite. -/
theorem dual_homogeneous_degrees_opposite
    (S : LieSubalgebra K L) (hHS : H ≤ S)
    (P Q : LieSubmodule K S L) [Nontrivial Q]
    (e : Q ≃ₗ⁅K,S⁆ Module.Dual K P) (degree : (H → K) →+ A)
    {a b : A} (hP : P.toSubmodule ≤ weightGrade H L degree a)
    (hQ : Q.toSubmodule ≤ weightGrade H L degree b) : b = -a := by
  apply eq_neg_of_add_eq_zero_right
  by_contra hab
  have hall : ∀ y : Q, ∀ x : P, e y x = 0 := by
    intro y x
    let P' := restrictCartanSubmodule H S hHS P
    let Q' := restrictCartanSubmodule H S hHS Q
    have hx : (x : P') ∈ ⨆ α : H → K, genWeightSpace P' α := by
      rw [iSup_genWeightSpace_eq_top]
      trivial
    induction hx using LieSubmodule.iSup_induction' with
    | mem α x hx =>
      have hxroot : (x : L) ∈ rootSpace H α :=
        map_genWeightSpace_le P'.incl ((LieSubmodule.mem_map _).mpr ⟨x, hx, rfl⟩)
      have hy : (y : Q') ∈ ⨆ β : H → K, genWeightSpace Q' β := by
        rw [iSup_genWeightSpace_eq_top]
        trivial
      induction hy using LieSubmodule.iSup_induction' with
      | mem β y hy =>
        have hyroot : (y : L) ∈ rootSpace H β :=
          map_genWeightSpace_le Q'.incl ((LieSubmodule.mem_map _).mpr ⟨y, hy, rfl⟩)
        by_cases hx0 : (x : L) = 0
        · have hx0' : x = 0 := Subtype.ext hx0
          simp only [hx0', map_zero]
        by_cases hy0 : (y : L) = 0
        · have hy0' : y = 0 := Subtype.ext hy0
          simp only [hy0', map_zero, LinearMap.zero_apply]
        have hα := degree_eq_of_nonzero_root_mem_grade H degree hxroot (hP x.property) hx0
        have hβ := degree_eq_of_nonzero_root_mem_grade H degree hyroot (hQ y.property) hy0
        apply dual_root_pair_zero H S hHS P Q e x y hxroot hyroot
        intro hzero
        apply hab
        have hdeg := congrArg degree hzero
        simpa only [map_add, map_zero, hα, hβ] using hdeg
      | zero => simp
      | add y z _ _ hy hz => simp only [map_add, LinearMap.add_apply, hy, hz, add_zero]
    | zero => simp
    | add x z _ _ hx hz => simp only [map_add, hx, hz, add_zero]
  obtain ⟨y, hy⟩ := exists_ne (0 : Q)
  apply hy
  apply e.injective
  rw [map_zero]
  ext x
  exact hall y x

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
/-- A spanning sum of three homogeneous subspaces leaves no fourth root degree. -/
theorem three_class_support_of_homogeneous_span (degree : (H → K) →+ A) (c : A)
    (S P Q : Submodule K L)
    (hspan : S ⊔ (P ⊔ Q) = ⊤)
    (hS : S ≤ weightGrade H L degree 0)
    (hP : P ≤ weightGrade H L degree c)
    (hQ : Q ≤ weightGrade H L degree (-c)) :
    ∀ α : H → K, rootSpace H α ≠ ⊥ →
      degree α = 0 ∨ degree α = c ∨ degree α = -c := by
  intro α hα
  by_contra ha
  push_neg at ha
  have htop : (⨆ (b : A) (_ : b ≠ degree α), weightGrade H L degree b) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact sup_le
      (hS.trans (le_iSup_of_le 0 (le_iSup_of_le (Ne.symm ha.1) le_rfl)))
      (sup_le
        (hP.trans (le_iSup_of_le c (le_iSup_of_le (Ne.symm ha.2.1) le_rfl)))
        (hQ.trans (le_iSup_of_le (-c) (le_iSup_of_le (Ne.symm ha.2.2) le_rfl))))
  have hd := iSupIndep_weightGrade H (M := L) degree (degree α)
  change Disjoint (weightGrade H L degree (degree α))
    (⨆ (b : A) (_ : b ≠ degree α), weightGrade H L degree b) at hd
  rw [htop, disjoint_top] at hd
  apply hα
  apply LieSubmodule.toSubmodule_injective
  apply le_antisymm _ bot_le
  simpa only [hd] using genWeightSpace_le_weightGrade H (M := L) degree α

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
/-- The actual off-zero root components equal the given complementary sum. -/
theorem off_zero_grades_eq_complement (degree : (H → K) →+ A) (c : A) (hc : c ≠ 0)
    (S P Q : Submodule K L) (hspan : S ⊔ (P ⊔ Q) = ⊤)
    (hS : S = weightGrade H L degree 0)
    (hP : P ≤ weightGrade H L degree c)
    (hQ : Q ≤ weightGrade H L degree (-c)) :
    weightGrade H L degree c ⊔ weightGrade H L degree (-c) = P ⊔ Q := by
  let O := weightGrade H L degree c ⊔ weightGrade H L degree (-c)
  have hPO : P ⊔ Q ≤ O := sup_le_sup hP hQ
  have hSO : Disjoint S O := by
    rw [hS]
    have hd := iSupIndep_weightGrade H (M := L) degree 0
    apply hd.mono_right
    exact sup_le
      (le_iSup_of_le c (le_iSup_of_le hc le_rfl))
      (le_iSup_of_le (-c) (le_iSup_of_le (neg_ne_zero.mpr hc) le_rfl))
  apply le_antisymm _ hPO
  intro x hx
  have hxspan : x ∈ S ⊔ (P ⊔ Q) := by rw [hspan]; trivial
  obtain ⟨s, hs, y, hy, hxy⟩ := Submodule.mem_sup.mp hxspan
  have hsO : s ∈ O := by
    have hsub := O.sub_mem hx (hPO hy)
    rw [← hxy, add_sub_cancel_right] at hsub
    exact hsub
  have hs0 : s = 0 := by
    have hsinf : s ∈ S ⊓ O := ⟨hs, hsO⟩
    simpa only [hSO.eq_bot, Submodule.mem_bot] using hsinf
  rw [hs0, zero_add] at hxy
  exact hxy ▸ hy

/-- A common Cartan, an invariant nondegenerate restriction, and an actual
irreducible dual-pair complement construct all three root-support identities.
No authored root subsystem or homogeneous-support hypothesis is supplied. -/
theorem common_cartan_three_class_decomposition
    (S : LieSubalgebra K L) (hHS : H ≤ S)
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant H)
    (hnd : (Φ.restrict S.toSubmodule).Nondegenerate)
    (P Q : LieSubmodule K S L)
    [LieModule.IsIrreducible K S P] [LieModule.IsIrreducible K S Q]
    (e : Q ≃ₗ⁅K,S⁆ Module.Dual K P)
    (hspan : S.toSubmodule ⊔ (P.toSubmodule ⊔ Q.toSubmodule) = ⊤)
    (hdisjoint : Disjoint S.toSubmodule (P.toSubmodule ⊔ Q.toSubmodule)) :
    let degree := QuotientAddGroup.mk'
      (AddSubgroup.closure (containedRoots H S.toSubmodule))
    ∃ c, c ≠ 0 ∧
      (∀ α : H → K, rootSpace H α ≠ ⊥ →
        degree α = 0 ∨ degree α = c ∨ degree α = -c) ∧
      weightGrade H L degree 0 = S.toSubmodule ∧
      weightGrade H L degree c ⊔ weightGrade H L degree (-c) =
        P.toSubmodule ⊔ Q.toSubmodule ∧
      P.toSubmodule ≤ weightGrade H L degree c ∧
      Q.toSubmodule ≤ weightGrade H L degree (-c) := by
  let degree := QuotientAddGroup.mk'
    (AddSubgroup.closure (containedRoots H S.toSubmodule))
  change ∃ c, _
  have hzero : weightGrade H L degree 0 = S.toSubmodule :=
    subalgebra_eq_quotient_zero_grade H S hHS Φ hΦ hnd
  have hS : S.toSubmodule ≤ weightGrade H L degree 0 := hzero.ge
  obtain ⟨c, hP⟩ := irreducible_submodule_homogeneous H S hHS P degree hS
  obtain ⟨d, hQ⟩ := irreducible_submodule_homogeneous H S hHS Q degree hS
  letI : Nontrivial P := LieModule.nontrivial_of_isIrreducible K S P
  letI : Nontrivial Q := LieModule.nontrivial_of_isIrreducible K S Q
  have hd : d = -c := dual_homogeneous_degrees_opposite H S hHS P Q e degree hP hQ
  subst d
  have hc : c ≠ 0 := by
    intro hc
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    have hxS : (x : L) ∈ S := by
      change (x : L) ∈ S.toSubmodule
      rw [← hzero, ← hc]
      exact hP x.property
    have hxO : (x : L) ∈ P.toSubmodule ⊔ Q.toSubmodule :=
      Submodule.mem_sup_left x.property
    have hx0 : (x : L) = 0 := by
      have hinf : (x : L) ∈ S.toSubmodule ⊓ (P.toSubmodule ⊔ Q.toSubmodule) := ⟨hxS, hxO⟩
      simpa only [hdisjoint.eq_bot, Submodule.mem_bot] using hinf
    exact hx (Subtype.ext hx0)
  exact ⟨c, hc,
    three_class_support_of_homogeneous_span H degree c S.toSubmodule P.toSubmodule
      Q.toSubmodule hspan hS hP hQ,
    hzero,
    off_zero_grades_eq_complement H degree c hc S.toSubmodule P.toSubmodule Q.toSubmodule
      hspan hzero.symm hP hQ, hP, hQ⟩

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
private theorem homogeneous_grade_eq_of_distinct_sup
    (degree : (H → K) →+ A) {a b : A} (hab : a ≠ b)
    (P Q : Submodule K L)
    (hsup : weightGrade H L degree a ⊔ weightGrade H L degree b = P ⊔ Q)
    (hP : P ≤ weightGrade H L degree a) (hQ : Q ≤ weightGrade H L degree b) :
    weightGrade H L degree a = P := by
  apply le_antisymm _ hP
  intro x hx
  have hxspan : x ∈ P ⊔ Q := by
    rw [← hsup]
    exact Submodule.mem_sup_left hx
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hxspan
  have hqa : q ∈ weightGrade H L degree a := by
    have hsub := (weightGrade H L degree a).sub_mem hx (hP hp)
    rw [← hpq, add_sub_cancel_left] at hsub
    exact hsub
  have hqzero : q = 0 := by
    have hd := (iSupIndep_weightGrade H (M := L) degree).pairwiseDisjoint hab
    have hqinf : q ∈ weightGrade H L degree a ⊓ weightGrade H L degree b := ⟨hqa, hQ hq⟩
    simpa only [hd.eq_bot, Submodule.mem_bot] using hqinf
  rw [hqzero, add_zero] at hpq
  exact hpq ▸ hp

/-- The nonsymmetric common-Cartan branch has a genuine cyclic grading of order
three, whose three components are exactly the supplied geometric subspaces. -/
theorem common_cartan_cyclic_grading
    (S : LieSubalgebra K L) (hHS : H ≤ S)
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant H)
    (hnd : (Φ.restrict S.toSubmodule).Nondegenerate)
    (P Q : LieSubmodule K S L)
    [LieModule.IsIrreducible K S P] [LieModule.IsIrreducible K S Q]
    (e : Q ≃ₗ⁅K,S⁆ Module.Dual K P)
    (hspan : S.toSubmodule ⊔ (P.toSubmodule ⊔ Q.toSubmodule) = ⊤)
    (hdisjoint : Disjoint S.toSubmodule (P.toSubmodule ⊔ Q.toSubmodule))
    (hnonsymmetric : ∃ x ∈ P.toSubmodule ⊔ Q.toSubmodule,
      ∃ y ∈ P.toSubmodule ⊔ Q.toSubmodule, ⁅x, y⁆ ∉ S) :
    let degree := QuotientAddGroup.mk'
      (AddSubgroup.closure (containedRoots H S.toSubmodule))
    ∃ (c : (H → K) ⧸ AddSubgroup.closure (containedRoots H S.toSubmodule))
      (horder : addOrderOf c = 3),
      DirectSum.IsInternal (orderThreeGrade H degree c horder) ∧
      orderThreeGrade H degree c horder 0 = S.toSubmodule ∧
      orderThreeGrade H degree c horder 1 = P.toSubmodule ∧
      orderThreeGrade H degree c horder (-1) = Q.toSubmodule ∧
      ∀ (i j : ZMod 3) (x y : L),
        x ∈ orderThreeGrade H degree c horder i →
        y ∈ orderThreeGrade H degree c horder j →
        ⁅x, y⁆ ∈ orderThreeGrade H degree c horder (i + j) := by
  let degree := QuotientAddGroup.mk'
    (AddSubgroup.closure (containedRoots H S.toSubmodule))
  obtain ⟨c, hc, hsupport, hzero, hoff, hP, hQ⟩ :=
    common_cartan_three_class_decomposition H S hHS Φ hΦ hnd P Q e hspan hdisjoint
  have hnonsym : ∃ x ∈ weightGrade H L degree c ⊔ weightGrade H L degree (-c),
      ∃ y ∈ weightGrade H L degree c ⊔ weightGrade H L degree (-c),
        ⁅x, y⁆ ∉ weightGrade H L degree 0 := by
    simpa only [degree, hoff, hzero] using hnonsymmetric
  let horder := order_three_of_three_class_support_and_nonsymmetric
    H degree c hc hsupport hnonsym
  have hcneg : c ≠ -c := by
    intro hneg
    have htwo : 2 • c = 0 := by
      calc
        2 • c = c + c := two_nsmul c
        _ = c + -c := congrArg (c + ·) hneg
        _ = 0 := add_neg_cancel c
    have hdiv : addOrderOf c ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
    rw [horder] at hdiv
    norm_num at hdiv
  have hpos := homogeneous_grade_eq_of_distinct_sup H degree hcneg
    P.toSubmodule Q.toSubmodule hoff hP hQ
  have hneg := homogeneous_grade_eq_of_distinct_sup H degree (Ne.symm hcneg)
    Q.toSubmodule P.toSubmodule (by simpa only [sup_comm] using hoff) hQ hP
  refine ⟨c, horder, orderThreeGrade_isInternal H degree c horder hsupport, ?_, ?_, ?_, ?_⟩
  · simpa only [orderThreeGrade, map_zero] using hzero
  · simpa only [orderThreeGrade, orderThreeClass_one] using hpos
  · simpa only [orderThreeGrade, map_neg, orderThreeClass_one] using hneg
  · intro i j x y hx hy
    exact lie_mem_orderThreeGrade H degree c horder hx hy

section CompactPair

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.ComplexDuality
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.HermitianRealization
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The original compact-pair hypotheses and an actual common Cartan construct
the complete cyclic root grading.  Its zero component is the given isotropy
algebra, and its two other components are the actual complex eigenspaces.

The only additional geometric input is `H ≤ complexifiedSubalgebra h`, with
`H` a Cartan of the ambient complexification.  Root closure, lattice support,
homogeneous component identities, nonsymmetry, and order three are all proved.
-/
theorem compact_common_cartan_cyclic_grading
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) :
    let q := orthogonalComplement B h
    let J := commutantComplexStructure e
    let degree := QuotientAddGroup.mk'
      (AddSubgroup.closure (containedRoots H (h.toSubmodule.baseChange ℂ)))
    ∃ (c : (H → ℂ) ⧸ AddSubgroup.closure (containedRoots H (h.toSubmodule.baseChange ℂ)))
      (horder : addOrderOf c = 3),
      DirectSum.IsInternal (orderThreeGrade H degree c horder) ∧
      orderThreeGrade H degree c horder 0 = h.toSubmodule.baseChange ℂ ∧
      orderThreeGrade H degree c horder 1 =
        (ambientComplexifiedHalf q J Complex.I).toSubmodule ∧
      orderThreeGrade H degree c horder (-1) =
        (ambientComplexifiedHalf q J (-Complex.I)).toSubmodule ∧
      ∀ (i j : ZMod 3) (x y : ℂ ⊗[ℝ] g),
        x ∈ orderThreeGrade H degree c horder i →
        y ∈ orderThreeGrade H degree c horder j →
        ⁅x, y⁆ ∈ orderThreeGrade H degree c horder (i + j) := by
  let q := orthogonalComplement B h
  let J := commutantComplexStructure e
  let P₀ := ambientComplexifiedHalf q J Complex.I
  let Q₀ := ambientComplexifiedHalf q J (-Complex.I)
  let S := complexifiedSubalgebra h
  let P := imageActionSubmodule h P₀
  let Q := imageActionSubmodule h Q₀
  have hgcenter := (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) :=
    compact_complexification_isKilling B hgcenter
  letI : LieModule.IsIrreducible ℝ h q :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).1
  have hirred := ambient_complex_halves_irreducible q J (commutant_complex_structure_square e)
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) P₀ := hirred.1
  letI : LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) Q₀ := hirred.2
  letI : LieModule.IsIrreducible ℂ S P := imageActionSubmodule_irreducible h P₀
  letI : LieModule.IsIrreducible ℂ S Q := imageActionSubmodule_irreducible h Q₀
  obtain ⟨D⟩ := (compact_complement_complex_type_decomposition B h hproper e).2.2.2.1
  let D₀ : Q₀ ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Module.Dual ℂ P₀ :=
    (ambientHalfEquiv q J (-Complex.I)).symm.trans
      (D.trans (SelfDualAbsorption.contragredientEquiv (ambientHalfEquiv q J Complex.I).symm))
  let E : Q ≃ₗ⁅ℂ,S⁆ Module.Dual ℂ P := imageActionDualEquiv h P₀ Q₀ D₀
  have hPQ : P.toSubmodule ⊔ Q.toSubmodule = q.toSubmodule.baseChange ℂ :=
    congrArg LieSubmodule.toSubmodule
      (ambient_complex_halves_sup q J (commutant_complex_structure_square e))
  have hcompl := compact_pair_complexification_isCompl B h
  have hspan : S.toSubmodule ⊔ (P.toSubmodule ⊔ Q.toSubmodule) = ⊤ := by
    rw [hPQ]
    exact hcompl.sup_eq_top
  have hdisjoint : Disjoint S.toSubmodule (P.toSubmodule ⊔ Q.toSubmodule) := by
    rw [hPQ]
    exact hcompl.disjoint
  have hΦ : (B.form.baseChange ℂ).lieInvariant H := by
    intro x y z
    exact complexified_invariantForm_invariant B.form B.invariant (x : ℂ ⊗[ℝ] g) y z
  have hnonsym : ∃ x ∈ P.toSubmodule ⊔ Q.toSubmodule,
      ∃ y ∈ P.toSubmodule ⊔ Q.toSubmodule, ⁅x, y⁆ ∉ S := by
    by_contra hn
    push_neg at hn
    have hcomplex : ∀ x ∈ q.toSubmodule.baseChange ℂ,
        ∀ y ∈ q.toSubmodule.baseChange ℂ, ⁅x, y⁆ ∈ h.toSubmodule.baseChange ℂ := by
      intro x hx y hy
      exact hn x (by rwa [hPQ]) y (by rwa [hPQ])
    have hreal := complexification_bracket_inclusion_reflects
      q.toSubmodule q.toSubmodule h.toSubmodule hcomplex
    exact hradical (CyclicBracket.symmetric_complex_complement_cubic_radical_eq_bot
      B h heff hproper e (fun x y => hreal x.val x.property y.val y.property))
  exact common_cartan_cyclic_grading H S hH (B.form.baseChange ℂ) hΦ
    (compact_complexified_subalgebra_form_nondegenerate B h) P Q E hspan hdisjoint hnonsym

end CompactPair

end CubicAnomaly.Classification.EqualRank
