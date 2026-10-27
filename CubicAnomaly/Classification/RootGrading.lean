import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import CubicAnomaly.Classification.RootReduction
import CubicAnomaly.Classification.RootSaturation
import CubicAnomaly.Classification.CyclicBracket
import CubicAnomaly.Classification.Complexification

/-!
# Root-lattice homogeneity and additive root gradings

Root operators shift weights by actual roots.  Grouping Mathlib's generalized
weight spaces by an additive degree therefore gives compatible homogeneous
components for a Lie algebra and its modules.  An irreducible module is
supported in a single class modulo the integer span of the algebra's roots.

This is a representation-theoretic bridge in the cyclic root-grading reduction;
it is uniform in rank and uses neither a classification nor a finite census.
-/

namespace CubicAnomaly.Classification.RootGrading

open LieModule

variable {K L M A : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H] [AddCommGroup A]

/-- The sum of all generalized weight spaces with the specified additive degree. -/
noncomputable def weightGrade (M : Type*) [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M]
    (degree : (H → K) →+ A) (a : A) : Submodule K M :=
  ⨆ χ : H → K, ⨆ (_ : degree χ = a), (genWeightSpace M χ).toSubmodule

/-- Every generalized weight space belongs to its assigned homogeneous component. -/
theorem genWeightSpace_le_weightGrade (degree : (H → K) →+ A) (χ : H → K) :
    (genWeightSpace M χ).toSubmodule ≤ weightGrade H M degree (degree χ) :=
  le_iSup_of_le χ (le_iSup_of_le rfl le_rfl)

/-- The actual Lie action adds degrees, because root operators add weights. -/
theorem lie_mem_weightGrade (degree : (H → K) →+ A) {a b : A} {x : L} {m : M}
    (hx : x ∈ weightGrade H L degree a) (hm : m ∈ weightGrade H M degree b) :
    ⁅x, m⁆ ∈ weightGrade H M degree (a + b) := by
  unfold weightGrade at hx hm
  refine Submodule.iSup_induction (motive := fun x : L =>
    ⁅x, m⁆ ∈ weightGrade H M degree (a + b)) _ hx (fun α x hx => ?_) ?_ ?_
  · refine Submodule.iSup_induction (motive := fun x : L =>
      ⁅x, m⁆ ∈ weightGrade H M degree (a + b)) _ hx (fun hα x hx => ?_) ?_ ?_
    · refine Submodule.iSup_induction (motive := fun m : M =>
        ⁅x, m⁆ ∈ weightGrade H M degree (a + b)) _ hm (fun χ m hm => ?_) ?_ ?_
      · refine Submodule.iSup_induction (motive := fun m : M =>
          ⁅x, m⁆ ∈ weightGrade H M degree (a + b)) _ hm (fun hχ m hm => ?_) ?_ ?_
        · have h := genWeightSpace_le_weightGrade H (M := M) degree (α + χ)
            (LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hx hm)
          simpa only [map_add, hα, hχ] using h
        · simpa only [lie_zero] using (weightGrade H M degree (a + b)).zero_mem
        · intro y z hy hz
          simpa only [lie_add] using (weightGrade H M degree (a + b)).add_mem hy hz
      · simpa only [lie_zero] using (weightGrade H M degree (a + b)).zero_mem
      · intro y z hy hz
        simpa only [lie_add] using (weightGrade H M degree (a + b)).add_mem hy hz
    · simpa only [zero_lie] using (weightGrade H M degree (a + b)).zero_mem
    · intro y z hy hz
      simpa only [add_lie] using (weightGrade H M degree (a + b)).add_mem hy hz
  · simpa only [zero_lie] using (weightGrade H M degree (a + b)).zero_mem
  · intro y z hy hz
    simpa only [add_lie] using (weightGrade H M degree (a + b)).add_mem hy hz

/-- The homogeneous components span every finite-dimensional triangularizable module. -/
theorem iSup_weightGrade_eq_top [FiniteDimensional K M] [IsTriangularizable K H M]
    (degree : (H → K) →+ A) :
    ⨆ a, weightGrade H M degree a = ⊤ := by
  apply top_unique
  have htop : (⨆ χ : H → K, (genWeightSpace M χ).toSubmodule) = ⊤ := by
    rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_eq_top,
      LieSubmodule.top_toSubmodule]
  rw [← htop]
  exact iSup_le fun χ => le_iSup_of_le (degree χ)
    (genWeightSpace_le_weightGrade H degree χ)

/-- Grouping independent weight spaces into disjoint degree classes preserves independence. -/
theorem iSupIndep_weightGrade [FiniteDimensional K M]
    (degree : (H → K) →+ A) : iSupIndep (weightGrade H M degree) := by
  classical
  let weights := (finite_genWeightSpace_ne_bot K H M).toFinset
  let spaces : (H → K) → Submodule K M := fun χ => (genWeightSpace M χ).toSubmodule
  have hind : iSupIndep spaces :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace K H M)
  have heq (a : A) : weightGrade H M degree a =
      (weights.filter fun χ => degree χ = a).sup spaces := by
    apply le_antisymm
    · refine iSup_le fun χ => iSup_le fun hχ => ?_
      by_cases hz : genWeightSpace M χ = ⊥
      · simp [hz]
      · apply Finset.le_sup (f := spaces) (b := χ)
        simpa [weights, hz] using hχ
    · refine Finset.sup_le fun χ hχ => ?_
      have hχ := (Finset.mem_filter.mp hχ).2
      simpa only [hχ] using genWeightSpace_le_weightGrade H (M := M) degree χ
  intro a
  change Disjoint (weightGrade H M degree a) (⨆ (b : A) (_ : b ≠ a), weightGrade H M degree b)
  rw [heq]
  have hd : Disjoint ((weights.filter fun χ => degree χ = a).sup spaces)
      ((weights.filter fun χ => degree χ ≠ a).sup spaces) := by
    apply (hind.supIndep' weights).disjoint_sup_sup
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    exact Finset.disjoint_left.mpr fun χ hχ hχ' =>
      (Finset.mem_filter.mp hχ').2 (Finset.mem_filter.mp hχ).2
  apply hd.mono_right
  refine iSup_le fun b => iSup_le fun hba => ?_
  rw [heq]
  apply Finset.sup_mono
  intro χ hχ
  rcases Finset.mem_filter.mp hχ with ⟨hχ, hχb⟩
  exact Finset.mem_filter.mpr ⟨hχ, by rwa [hχb]⟩

/-- These are genuine internal homogeneous components, not merely a covering by subspaces. -/
theorem weightGrade_isInternal [FiniteDimensional K M] [IsTriangularizable K H M]
    [DecidableEq A] (degree : (H → K) →+ A) :
    DirectSum.IsInternal (weightGrade H M degree) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_weightGrade H degree) (iSup_weightGrade_eq_top H degree)

/-- The degree-zero component of the root grading is an actual Lie subalgebra. -/
noncomputable def zeroGradeSubalgebra (degree : (H → K) →+ A) : LieSubalgebra K L where
  toSubmodule := weightGrade H L degree 0
  lie_mem' := by
    intro x y hx hy
    simpa only [zero_add] using lie_mem_weightGrade H degree hx hy

/-- A homogeneous component with no weights of its degree is zero. -/
theorem weightGrade_eq_bot (degree : (H → K) →+ A) (a : A)
    (h : ∀ χ : H → K, degree χ = a → genWeightSpace M χ = ⊥) :
    weightGrade H M degree a = ⊥ := by
  apply le_antisymm _ bot_le
  refine iSup_le fun χ => iSup_le fun hχ => ?_
  simp only [h χ hχ, LieSubmodule.bot_toSubmodule, le_refl]

/-- A nonzero homogeneous vector detects an actual weight in that degree. -/
theorem exists_weight_of_mem_weightGrade (degree : (H → K) →+ A) {a : A} {m : M}
    (hm : m ∈ weightGrade H M degree a) (hne : m ≠ 0) :
    ∃ χ : H → K, degree χ = a ∧ genWeightSpace M χ ≠ ⊥ := by
  by_contra h
  have hz : weightGrade H M degree a = ⊥ :=
    weightGrade_eq_bot H degree a (by simpa only [not_exists, not_and, not_not] using h)
  rw [hz, Submodule.mem_bot] at hm
  exact hne hm

/-- If every root has degree zero, the algebra itself has degree zero. -/
theorem weightGrade_zero_eq_top [FiniteDimensional K L] [IsTriangularizable K H L]
    (degree : (H → K) →+ A)
    (hzero : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ → degree χ = 0) :
    weightGrade H L degree 0 = ⊤ := by
  apply top_unique
  have htop : (⨆ χ : H → K, (genWeightSpace L χ).toSubmodule) = ⊤ := by
    rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_eq_top,
      LieSubmodule.top_toSubmodule]
  rw [← htop]
  refine iSup_le fun χ => ?_
  by_cases hχ : genWeightSpace L χ = ⊥
  · simp only [hχ, LieSubmodule.bot_toSubmodule, bot_le]
  · simpa only [hzero χ hχ] using genWeightSpace_le_weightGrade H (M := L) degree χ

/-- Properness of the zero component forces the nonzero class in a three-class support. -/
theorem nonzero_class_of_proper_zero_grade
    [FiniteDimensional K L] [IsTriangularizable K H L]
    (degree : (H → K) →+ A) (c : A)
    (hsupport : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c)
    (hproper : weightGrade H L degree 0 ≠ ⊤) : c ≠ 0 := by
  intro hc
  apply hproper
  apply weightGrade_zero_eq_top H degree
  intro χ hχ
  simpa only [hc, neg_zero, or_self] using hsupport χ hχ

/-- A homogeneous component is a subrepresentation when the acting algebra has degree zero. -/
noncomputable def homogeneousLieSubmodule (degree : (H → K) →+ A)
    (hzero : weightGrade H L degree 0 = ⊤) (a : A) : LieSubmodule K L M where
  toSubmodule := weightGrade H M degree a
  lie_mem := by
    intro x m hm
    have hx : x ∈ weightGrade H L degree 0 := by rw [hzero]; trivial
    simpa only [zero_add] using lie_mem_weightGrade H degree hx hm

/-- An irreducible representation cannot have nonzero weight spaces in different degree classes. -/
theorem degree_eq_of_irreducible [LieModule.IsIrreducible K L M]
    (degree : (H → K) →+ A) (hzero : weightGrade H L degree 0 = ⊤)
    {χ ψ : H → K} (hχ : genWeightSpace M χ ≠ ⊥) (hψ : genWeightSpace M ψ ≠ ⊥) :
    degree χ = degree ψ := by
  let N : LieSubmodule K L M := homogeneousLieSubmodule H degree hzero (degree χ)
  have hN : N ≠ ⊥ := by
    intro heq
    apply hχ
    apply LieSubmodule.toSubmodule_injective
    apply le_antisymm _ bot_le
    have hle := genWeightSpace_le_weightGrade H (M := M) degree χ
    change (genWeightSpace M χ).toSubmodule ≤ N.toSubmodule at hle
    simpa only [heq, LieSubmodule.bot_toSubmodule] using hle
  have hNtop : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN
  have hgrade : weightGrade H M degree (degree χ) = ⊤ :=
    congrArg LieSubmodule.toSubmodule hNtop
  by_contra hne
  have hd : Disjoint (genWeightSpace M ψ).toSubmodule
      (weightGrade H M degree (degree χ)) := by
    have hind : iSupIndep fun α : H → K => (genWeightSpace M α).toSubmodule :=
      LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace K H M)
    exact hind.disjoint_biSup (by simpa using Ne.symm hne)
  rw [hgrade, disjoint_top] at hd
  exact hψ (LieSubmodule.toSubmodule_injective hd)

/-- The integer span of the nonzero generalized adjoint weights of the nilpotent subalgebra. -/
def rootLattice : AddSubgroup (H → K) :=
  AddSubgroup.closure {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥}

/-- Every adjoint weight, including zero, belongs to the root lattice. -/
theorem root_mem_rootLattice {χ : H → K} (hχ : LieAlgebra.rootSpace H χ ≠ ⊥) :
    χ ∈ rootLattice H := by
  by_cases hz : χ = 0
  · simpa only [hz] using (rootLattice H).zero_mem
  · exact AddSubgroup.subset_closure ⟨hz, hχ⟩

/-- Root operators act within a single root-lattice coset of an irreducible module.

This proves the lattice-support assertion in the cyclic-root-grading argument
directly for Mathlib Lie modules.  No highest-weight or classification theorem is
assumed, and only the acting algebra needs a spanning weight decomposition.
-/
theorem irreducible_weights_sub_mem_rootLattice
    [FiniteDimensional K L] [IsTriangularizable K H L]
    [LieModule.IsIrreducible K L M]
    {χ ψ : H → K} (hχ : genWeightSpace M χ ≠ ⊥) (hψ : genWeightSpace M ψ ≠ ⊥) :
    χ - ψ ∈ rootLattice H := by
  let degree := QuotientAddGroup.mk' (rootLattice H)
  have hzero : weightGrade H L degree 0 = ⊤ := by
    apply weightGrade_zero_eq_top H degree
    intro α hα
    exact (QuotientAddGroup.eq_zero_iff _).mpr (root_mem_rootLattice H hα)
  have heq := degree_eq_of_irreducible H degree hzero hχ hψ
  have hsub : degree (χ - ψ) = 0 := by rw [map_sub, heq, sub_self]
  exact (QuotientAddGroup.eq_zero_iff _).mp hsub

/-- Three-class root support and a nonzero bracket of two degree-one vectors
force the grading class to have exact order three.  The class constraint on the
bracket is derived from the actual Lie bracket, not supplied separately. -/
theorem order_three_of_three_class_support_and_nonzero_bracket
    (degree : (H → K) →+ A) (c : A) (hc : c ≠ 0) (h2c : 2 • c ≠ 0)
    (hsupport : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c)
    (hbracket : ∃ x ∈ weightGrade H L degree c,
      ∃ y ∈ weightGrade H L degree c, ⁅x, y⁆ ≠ 0) :
    addOrderOf c = 3 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hbracket
  obtain ⟨χ, hχ, hχne⟩ := exists_weight_of_mem_weightGrade H degree
    (lie_mem_weightGrade H degree hx hy) hxy
  apply RootReduction.three_class_noninvolutive_order c hc h2c
  simpa only [hχ, ← two_nsmul] using hsupport χ hχne

/-- The canonical embedding of the cyclic group of order three generated by `c`. -/
noncomputable def orderThreeClass (c : A) (hc : addOrderOf c = 3) : ZMod 3 →+ A :=
  ZMod.lift 3 ⟨{
    toFun := fun n : ℤ => n • c
    map_zero' := zero_zsmul c
    map_add' := fun m n => add_zsmul c m n
  }, by
    change (3 : ℤ) • c = 0
    rw [show (3 : ℤ) = (3 : ℕ) by rfl, natCast_zsmul, ← hc]
    exact addOrderOf_nsmul_eq_zero c⟩

/-- The cyclic generator maps to the given root-lattice class. -/
theorem orderThreeClass_one (c : A) (hc : addOrderOf c = 3) :
    orderThreeClass c hc 1 = c := by
  change ZMod.lift 3 _ (1 : ℤ) = c
  rw [ZMod.lift_coe]
  exact one_zsmul c

/-- Exact additive order ensures that the three degree classes are distinct. -/
theorem orderThreeClass_injective (c : A) (hc : addOrderOf c = 3) :
    Function.Injective (orderThreeClass c hc) := by
  apply (ZMod.lift_injective (n := 3)).mpr
  intro n hn
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd n 3).mpr
  have hd : (addOrderOf c : ℤ) ∣ n := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hn
  simpa only [hc] using hd

/-- The cyclic root components, indexed by the actual additive group `ZMod 3`. -/
noncomputable def orderThreeGrade (degree : (H → K) →+ A) (c : A)
    (hc : addOrderOf c = 3) (i : ZMod 3) : Submodule K L :=
  weightGrade H L degree (orderThreeClass c hc i)

/-- Brackets respect addition in the cyclic group of order three. -/
theorem lie_mem_orderThreeGrade (degree : (H → K) →+ A) (c : A)
    (hc : addOrderOf c = 3) {i j : ZMod 3} {x y : L}
    (hx : x ∈ orderThreeGrade H degree c hc i)
    (hy : y ∈ orderThreeGrade H degree c hc j) :
    ⁅x, y⁆ ∈ orderThreeGrade H degree c hc (i + j) := by
  simpa only [orderThreeGrade, map_add] using lie_mem_weightGrade H degree hx hy

/-- Three-class support yields a genuine internal `ZMod 3` root decomposition. -/
theorem orderThreeGrade_isInternal [FiniteDimensional K L] [IsTriangularizable K H L]
    (degree : (H → K) →+ A) (c : A) (hc : addOrderOf c = 3)
    (hsupport : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c) :
    DirectSum.IsInternal (orderThreeGrade H degree c hc) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (iSupIndep_weightGrade H (M := L) degree).comp (orderThreeClass_injective c hc)
  · apply top_unique
    have htop : (⨆ χ : H → K, (genWeightSpace L χ).toSubmodule) = ⊤ := by
      rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_eq_top,
        LieSubmodule.top_toSubmodule]
    rw [← htop]
    refine iSup_le fun χ => ?_
    by_cases hχ : genWeightSpace L χ = ⊥
    · simp only [hχ, LieSubmodule.bot_toSubmodule, bot_le]
    obtain ⟨i, hi⟩ : ∃ i : ZMod 3, orderThreeClass c hc i = degree χ := by
      rcases hsupport χ hχ with hz | hone | hneg
      · exact ⟨0, by rw [map_zero, hz]⟩
      · exact ⟨1, by rw [orderThreeClass_one, hone]⟩
      · exact ⟨-1, by rw [map_neg, orderThreeClass_one, hneg]⟩
    exact le_iSup_of_le i (by
      simpa only [orderThreeGrade, hi] using genWeightSpace_le_weightGrade H (M := L) degree χ)

/-- The non-involutive three-class alternative produces an actual cyclic Lie grading.

The homogeneous components are direct, span the whole algebra, and satisfy the
Lie bracket law.  Only the remaining nonzero-bracket step is an input here.
-/
theorem cyclic_root_grading_of_three_class_support
    [FiniteDimensional K L] [IsTriangularizable K H L]
    (degree : (H → K) →+ A) (c : A) (hc : c ≠ 0) (h2c : 2 • c ≠ 0)
    (hsupport : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c)
    (hbracket : ∃ x ∈ weightGrade H L degree c,
      ∃ y ∈ weightGrade H L degree c, ⁅x, y⁆ ≠ 0) :
    ∃ horder : addOrderOf c = 3,
      DirectSum.IsInternal (orderThreeGrade H degree c horder) ∧
      ∀ (i j : ZMod 3) (x y : L),
        x ∈ orderThreeGrade H degree c horder i →
        y ∈ orderThreeGrade H degree c horder j →
        ⁅x, y⁆ ∈ orderThreeGrade H degree c horder (i + j) := by
  let horder := order_three_of_three_class_support_and_nonzero_bracket
    H degree c hc h2c hsupport hbracket
  exact ⟨horder, orderThreeGrade_isInternal H degree c horder hsupport,
    fun _ _ _ _ hx hy => lie_mem_orderThreeGrade H degree c horder hx hy⟩

private theorem bracket_same_degree_mem_zero_of_order_ne_three
    (degree : (H → K) →+ A) (c : A) (hc : c ≠ 0) (horder : addOrderOf c ≠ 3)
    (hsupport : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c)
    {x y : L} (hx : x ∈ weightGrade H L degree c)
    (hy : y ∈ weightGrade H L degree c) :
    ⁅x, y⁆ ∈ weightGrade H L degree 0 := by
  by_cases h2c : 2 • c = 0
  · simpa only [← two_nsmul, h2c] using lie_mem_weightGrade H degree hx hy
  by_cases hxy : ⁅x, y⁆ = 0
  · simpa only [hxy] using (weightGrade H L degree 0).zero_mem
  exact (horder (order_three_of_three_class_support_and_nonzero_bracket
    H degree c hc h2c hsupport ⟨x, hx, y, hy, hxy⟩)).elim

/-- If the three-class support is not genuinely cyclic of order three, the
entire off-zero component has symmetric-pair brackets.

This simultaneously covers the involutive case and the hypothetical vanishing
of both same-sign brackets.  It avoids an inner-derivation argument.
-/
theorem complement_bracket_mem_zero_of_order_ne_three
    (degree : (H → K) →+ A) (c : A) (hc : c ≠ 0) (horder : addOrderOf c ≠ 3)
    (hsupport : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c)
    {x y : L}
    (hx : x ∈ weightGrade H L degree c ⊔ weightGrade H L degree (-c))
    (hy : y ∈ weightGrade H L degree c ⊔ weightGrade H L degree (-c)) :
    ⁅x, y⁆ ∈ weightGrade H L degree 0 := by
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
  have hpp := bracket_same_degree_mem_zero_of_order_ne_three
    H degree c hc horder hsupport hx₁ hy₁
  have hpm : ⁅x₁, y₂⁆ ∈ weightGrade H L degree 0 := by
    simpa only [add_neg_cancel] using lie_mem_weightGrade H degree hx₁ hy₂
  have hmp : ⁅x₂, y₁⁆ ∈ weightGrade H L degree 0 := by
    simpa only [neg_add_cancel] using lie_mem_weightGrade H degree hx₂ hy₁
  have hsupportNeg : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = -c ∨ degree χ = -(-c) := by
    intro χ hχ
    rcases hsupport χ hχ with hz | hp | hn
    · exact Or.inl hz
    · exact Or.inr (Or.inr (by simpa only [neg_neg] using hp))
    · exact Or.inr (Or.inl hn)
  have hmm := bracket_same_degree_mem_zero_of_order_ne_three H degree (-c)
    (neg_ne_zero.mpr hc) (by simpa only [addOrderOf_neg] using horder) hsupportNeg hx₂ hy₂
  simpa only [add_lie, lie_add] using
    (weightGrade H L degree 0).add_mem
      ((weightGrade H L degree 0).add_mem hpp hmp)
      ((weightGrade H L degree 0).add_mem hpm hmm)

/-- A nonsymmetric quotient bracket forces exact order three directly.

Unlike the preliminary nonzero-bracket version, this theorem requires neither
the exclusion of order two nor a separate nonzero bracket within one complex
half.  Both follow from the single nonsymmetry input.
-/
theorem order_three_of_three_class_support_and_nonsymmetric
    (degree : (H → K) →+ A) (c : A) (hc : c ≠ 0)
    (hsupport : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c)
    (hnonsymmetric : ∃ x ∈ weightGrade H L degree c ⊔ weightGrade H L degree (-c),
      ∃ y ∈ weightGrade H L degree c ⊔ weightGrade H L degree (-c),
        ⁅x, y⁆ ∉ weightGrade H L degree 0) :
    addOrderOf c = 3 := by
  by_contra horder
  obtain ⟨x, hx, y, hy, hxy⟩ := hnonsymmetric
  exact hxy (complement_bracket_mem_zero_of_order_ne_three H degree c hc horder hsupport hx hy)

/-- Three-class support and a nonsymmetric complement produce an internal cyclic
Lie grading, without either of the manuscript's separate involutive/derivation branches. -/
theorem cyclic_root_grading_of_nonsymmetric
    [FiniteDimensional K L] [IsTriangularizable K H L]
    (degree : (H → K) →+ A) (c : A) (hc : c ≠ 0)
    (hsupport : ∀ χ : H → K, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c)
    (hnonsymmetric : ∃ x ∈ weightGrade H L degree c ⊔ weightGrade H L degree (-c),
      ∃ y ∈ weightGrade H L degree c ⊔ weightGrade H L degree (-c),
        ⁅x, y⁆ ∉ weightGrade H L degree 0) :
    ∃ horder : addOrderOf c = 3,
      DirectSum.IsInternal (orderThreeGrade H degree c horder) ∧
      ∀ (i j : ZMod 3) (x y : L),
        x ∈ orderThreeGrade H degree c horder i →
        y ∈ orderThreeGrade H degree c horder j →
        ⁅x, y⁆ ∈ orderThreeGrade H degree c horder (i + j) := by
  let horder := order_three_of_three_class_support_and_nonsymmetric
    H degree c hc hsupport hnonsymmetric
  exact ⟨horder, orderThreeGrade_isInternal H degree c horder hsupport,
    fun _ _ _ _ hx hy => lie_mem_orderThreeGrade H degree c horder hx hy⟩

section QuotientRootDegree

variable [CharZero K] [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- For the actual quotient by a closed subsystem's integer root lattice, the
degree-zero subspace consists exactly of the common Cartan and the subsystem's
root spaces.

The inclusion from degree zero to the subsystem uses the field-general
saturation theorem.  Thus the grading's fixed algebra is identified from actual
root data, rather than supplied as an unrelated equality.
-/
theorem quotient_root_grade_zero_eq
    (Ψ : Set (H → K))
    (hsub : Ψ ⊆ {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥})
    (hneg : ∀ a ∈ Ψ, -a ∈ Ψ)
    (hclosed : ∀ a ∈ Ψ, ∀ b ∈ Ψ,
      a + b ∈ {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥} → a + b ∈ Ψ) :
    weightGrade H L (QuotientAddGroup.mk' (AddSubgroup.closure Ψ)) 0 =
      H.toSubmodule ⊔ ⨆ χ ∈ Ψ, (LieAlgebra.rootSpace H χ).toSubmodule := by
  let degree := QuotientAddGroup.mk' (AddSubgroup.closure Ψ)
  change weightGrade H L degree 0 = _
  have hsat := RootSaturation.lie_weight_closed_subsystem_saturated H Ψ hsub hneg hclosed
  have hzeroSpace : (LieAlgebra.rootSpace H (0 : H → K)).toSubmodule = H.toSubmodule := by
    rw [LieAlgebra.rootSpace_zero_eq K L H]
    rfl
  apply le_antisymm
  · refine iSup_le fun χ => iSup_le fun hχ => ?_
    by_cases hz : χ = 0
    · rw [hz, hzeroSpace]
      exact le_sup_left
    by_cases hb : LieAlgebra.rootSpace H χ = ⊥
    · simp only [hb, LieSubmodule.bot_toSubmodule, bot_le]
    have hχL : χ ∈ AddSubgroup.closure Ψ := (QuotientAddGroup.eq_zero_iff χ).mp hχ
    have hχΨ : χ ∈ Ψ := by
      have : χ ∈ {χ : H → K | χ ≠ 0 ∧ LieAlgebra.rootSpace H χ ≠ ⊥} ∩
          (AddSubgroup.closure Ψ : Set (H → K)) := ⟨⟨hz, hb⟩, hχL⟩
      simpa only [hsat] using this
    exact le_sup_of_le_right (le_iSup_of_le χ (le_iSup_of_le hχΨ le_rfl))
  · refine sup_le ?_ (iSup_le fun χ => iSup_le fun hχ => ?_)
    · have h := genWeightSpace_le_weightGrade H (M := L) degree (0 : H → K)
      simpa only [map_zero, hzeroSpace] using h
    · have hz : degree χ = 0 :=
        (QuotientAddGroup.eq_zero_iff χ).mpr (AddSubgroup.subset_closure hχ)
      simpa only [hz] using genWeightSpace_le_weightGrade H (M := L) degree χ

end QuotientRootDegree

section CompactPair

open CubicAnomaly.Classification.Structural
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- In an actual compact pair with nonzero full cubic radical, a three-class
common-Cartan decomposition has exact order three.

The zero and off-zero components are explicitly identified with the scalar
extensions of the isotropy algebra and its orthogonal complement.  A failure of
order three would make the complex complement symmetric; bracket reflection
would then make the real complement symmetric, contradicting the full radical.
No involution census, same-half bracket, or nonsymmetry assumption is an input.
-/
theorem compact_pair_three_class_order_three
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (HermitianRealization.hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [LieRing.IsNilpotent H]
    (degree : (H → ℂ) →+ A) (c : A)
    (hsupport : ∀ χ : H → ℂ, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c)
    (hzero : weightGrade H (ℂ ⊗[ℝ] g) degree 0 = h.toSubmodule.baseChange ℂ)
    (hoff : weightGrade H (ℂ ⊗[ℝ] g) degree c ⊔
      weightGrade H (ℂ ⊗[ℝ] g) degree (-c) =
        (orthogonalComplement B h).toSubmodule.baseChange ℂ) :
    addOrderOf c = 3 := by
  have hgradeproper : weightGrade H (ℂ ⊗[ℝ] g) degree 0 ≠ ⊤ := by
    intro htop
    apply hproper
    apply top_unique
    intro x _
    apply (Complexification.complexification_real_mem_baseChange_iff
      g h.toSubmodule x).mp
    rw [← hzero, htop]
    trivial
  have hc := nonzero_class_of_proper_zero_grade H degree c hsupport hgradeproper
  by_contra horder
  have hcomplex : ∀ x ∈ (orthogonalComplement B h).toSubmodule.baseChange ℂ,
      ∀ y ∈ (orthogonalComplement B h).toSubmodule.baseChange ℂ,
        ⁅x, y⁆ ∈ h.toSubmodule.baseChange ℂ := by
    intro x hx y hy
    rw [← hoff] at hx hy
    rw [← hzero]
    exact complement_bracket_mem_zero_of_order_ne_three H degree c hc horder hsupport hx hy
  have hreal := Complexification.complexification_bracket_inclusion_reflects
    (orthogonalComplement B h).toSubmodule (orthogonalComplement B h).toSubmodule
    h.toSubmodule hcomplex
  exact hradical (CyclicBracket.symmetric_complex_complement_cubic_radical_eq_bot
    B h heff hproper e (fun x y => hreal x.val x.property y.val y.property))

/-- The compact-pair bridge produces genuine internal cyclic root components.
The only remaining full-rank interfaces are the common-Cartan root support and
the identifications of its zero/off-zero components with the given pair.
-/
theorem compact_pair_cyclic_root_grading
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (HermitianRealization.hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [LieRing.IsNilpotent H]
    (degree : (H → ℂ) →+ A) (c : A)
    (hsupport : ∀ χ : H → ℂ, LieAlgebra.rootSpace H χ ≠ ⊥ →
      degree χ = 0 ∨ degree χ = c ∨ degree χ = -c)
    (hzero : weightGrade H (ℂ ⊗[ℝ] g) degree 0 = h.toSubmodule.baseChange ℂ)
    (hoff : weightGrade H (ℂ ⊗[ℝ] g) degree c ⊔
      weightGrade H (ℂ ⊗[ℝ] g) degree (-c) =
        (orthogonalComplement B h).toSubmodule.baseChange ℂ) :
    ∃ horder : addOrderOf c = 3,
      DirectSum.IsInternal (orderThreeGrade H degree c horder) ∧
      ∀ (i j : ZMod 3) (x y : ℂ ⊗[ℝ] g),
        x ∈ orderThreeGrade H degree c horder i →
        y ∈ orderThreeGrade H degree c horder j →
        ⁅x, y⁆ ∈ orderThreeGrade H degree c horder (i + j) := by
  let horder := compact_pair_three_class_order_three
    B h heff hproper e hradical H degree c hsupport hzero hoff
  exact ⟨horder, orderThreeGrade_isInternal H degree c horder hsupport,
    fun _ _ _ _ hx hy => lie_mem_orderThreeGrade H degree c horder hx hy⟩

end CompactPair

end CubicAnomaly.Classification.RootGrading
