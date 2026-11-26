import CubicAnomaly.Classification.CompactGeometry
import Mathlib.Data.Nat.Lattice

/-!
# Constructing a common Cartan from compact abelian rank

Here `abelianRank` is explicitly the largest dimension of an abelian Lie
subalgebra.  Positivity of an invariant real form makes a subalgebra attaining
this dimension self-normalizing, hence Cartan.  Equal abelian ranks therefore
produce an actual ambient Cartan inside the complexified isotropy algebra.

No equality with Mathlib's independently defined polynomial `LieAlgebra.rank`
is asserted in this module.
-/

namespace CubicAnomaly.Classification.CompactCartan

open LieAlgebra Module
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open scoped TensorProduct

section Rank

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

/-- Largest dimension of an actual abelian Lie subalgebra.  In the compact
real setting this is the geometric abelian-rank convention used here. -/
noncomputable def abelianRank : ℕ :=
  sSup {n : ℕ | ∃ A : LieSubalgebra K L, IsLieAbelian A ∧ finrank K A = n}

private theorem abelian_dimensions_bdd :
    BddAbove {n : ℕ | ∃ A : LieSubalgebra K L, IsLieAbelian A ∧ finrank K A = n} := by
  refine ⟨finrank K L, ?_⟩
  rintro n ⟨A, _, rfl⟩
  exact Submodule.finrank_le A.toSubmodule

/-- Every abelian subalgebra satisfies the defining rank bound. -/
theorem finrank_le_abelianRank (A : LieSubalgebra K L) [IsLieAbelian A] :
    finrank K A ≤ abelianRank K L :=
  le_csSup (abelian_dimensions_bdd K L) ⟨A, inferInstance, rfl⟩

/-- The abelian rank is attained by an actual subalgebra. -/
theorem exists_abelian_finrank_eq_abelianRank :
    ∃ A : LieSubalgebra K L, IsLieAbelian A ∧ finrank K A = abelianRank K L := by
  have hb : IsLieAbelian (⊥ : LieSubalgebra K L) := by
    constructor
    intro x y
    apply Subtype.ext
    have hx : (x : L) = 0 := x.property
    change ⁅(x : L), (y : L)⁆ = 0
    rw [hx, zero_lie]
  have hn : Set.Nonempty
      {n : ℕ | ∃ A : LieSubalgebra K L, IsLieAbelian A ∧ finrank K A = n} :=
    ⟨finrank K (⊥ : LieSubalgebra K L), ⊥, hb, rfl⟩
  exact Nat.sSup_mem hn (abelian_dimensions_bdd K L)

/-- An injective Lie homomorphism cannot decrease the maximum dimension of
an abelian subalgebra. -/
theorem abelianRank_le_of_injective
    {L' : Type*} [LieRing L'] [LieAlgebra K L'] [Module.Finite K L']
    (f : L →ₗ⁅K⁆ L') (hf : Function.Injective f) :
    abelianRank K L ≤ abelianRank K L' := by
  obtain ⟨T, hT, hdim⟩ := exists_abelian_finrank_eq_abelianRank K L
  let F : T →ₗ⁅K⁆ L' := f.comp T.incl
  have hF : Function.Injective F := hf.comp Subtype.val_injective
  let E := LieEquiv.ofInjective F hF
  letI : IsLieAbelian T := hT
  letI : IsLieAbelian F.range := (lie_abelian_iff_equiv_lie_abelian E).mp hT
  rw [← hdim, E.toLinearEquiv.finrank_eq]
  exact finrank_le_abelianRank K L' F.range

/-- The abelian rank of an actual subalgebra is bounded by the ambient rank. -/
theorem abelianRank_subalgebra_le (h : LieSubalgebra K L) :
    abelianRank K h ≤ abelianRank K L :=
  abelianRank_le_of_injective K h h.incl Subtype.val_injective

end Rank

section Compact

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

omit [Module.Finite ℝ g] in
/-- In a compact Lie algebra, the normalizer of an abelian subalgebra acts
trivially on it.  Positivity and invariance exclude nonzero normalizer brackets. -/
theorem compact_abelian_normalizer_bracket_zero (B : CompactForm g)
    (A : LieSubalgebra ℝ g) [IsLieAbelian A] {x : g} (hx : x ∈ A.normalizer)
    {y : g} (hy : y ∈ A) : ⁅x, y⁆ = 0 := by
  have hw : ⁅x, y⁆ ∈ A := (A.mem_normalizer_iff x).mp hx y hy
  have hyw : ⁅y, ⁅x, y⁆⁆ = 0 := by
    exact congrArg Subtype.val (trivial_lie_zero A A (⟨y, hy⟩ : A) (⟨⁅x, y⁆, hw⟩ : A))
  have hform := B.invariant y x ⁅x, y⁆
  rw [hyw, map_zero, neg_zero, ← lie_skew y x, map_neg, LinearMap.neg_apply] at hform
  have hz : B.form ⁅x, y⁆ ⁅x, y⁆ = 0 := neg_eq_zero.mp hform
  by_contra hne
  exact (ne_of_gt (B.positive ⁅x, y⁆ hne)) hz

/-- An abelian subalgebra of maximum possible dimension is an actual Cartan
subalgebra of the compact algebra. -/
theorem compact_maximum_abelian_isCartan (B : CompactForm g)
    (A : LieSubalgebra ℝ g) [IsLieAbelian A]
    (hmax : finrank ℝ A = abelianRank ℝ g) : A.IsCartanSubalgebra := by
  refine ⟨inferInstance, le_antisymm ?_ A.le_normalizer⟩
  intro x hx
  let T := LieSubalgebra.lieSpan ℝ g (insert x (A : Set g))
  have hxcomm : ∀ y : g, y ∈ A → ⁅x, y⁆ = 0 :=
    fun y hy => compact_abelian_normalizer_bracket_zero B A hx hy
  letI : IsLieAbelian T := by
    apply LieSubalgebra.isLieAbelian_lieSpan_iff.mpr
    intro y hy z hz
    rcases hy with rfl | hy <;> rcases hz with rfl | hz
    · exact lie_self _
    · exact hxcomm z hz
    · rw [← lie_skew, hxcomm y hy, neg_zero]
    · exact congrArg Subtype.val
        (trivial_lie_zero A A (⟨y, hy⟩ : A) (⟨z, hz⟩ : A))
  have hAT : A ≤ T := fun y hy => LieSubalgebra.subset_lieSpan (Or.inr hy)
  have hdim : finrank ℝ T ≤ finrank ℝ A := by
    rw [hmax]
    exact finrank_le_abelianRank ℝ g T
  have heq : A = T := LieSubalgebra.toSubmodule_injective
    (Submodule.eq_of_le_of_finrank_le hAT hdim)
  rw [heq]
  exact LieSubalgebra.subset_lieSpan (Set.mem_insert _ _)

/-- Equal geometric abelian ranks construct a real ambient Cartan contained
in the given subalgebra.  The Cartan is a conclusion, not an input witness. -/
theorem compact_equal_abelianRank_exists_real_cartan (B : CompactForm g)
    (h : LieSubalgebra ℝ g) (hrank : abelianRank ℝ h = abelianRank ℝ g) :
    ∃ A : LieSubalgebra ℝ g, A ≤ h ∧ IsLieAbelian A ∧ A.IsCartanSubalgebra ∧
      finrank ℝ A = abelianRank ℝ g := by
  obtain ⟨T, hT, hdim⟩ := exists_abelian_finrank_eq_abelianRank ℝ h
  let f : T →ₗ⁅ℝ⁆ g := h.incl.comp T.incl
  have hf : Function.Injective f := fun x y hxy => Subtype.ext (Subtype.ext hxy)
  let E := LieEquiv.ofInjective f hf
  letI : IsLieAbelian T := hT
  letI : IsLieAbelian f.range := (lie_abelian_iff_equiv_lie_abelian E).mp hT
  have hfin : finrank ℝ f.range = abelianRank ℝ g :=
    E.toLinearEquiv.finrank_eq.symm.trans (hdim.trans hrank)
  refine ⟨f.range, ?_, inferInstance, compact_maximum_abelian_isCartan B f.range hfin, hfin⟩
  rintro x ⟨y, rfl⟩
  exact y.val.property

end Compact

section ComplexCartan

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

private theorem realPart_bracket_real (z : ℂ ⊗[ℝ] g) (x : g) :
    tensorRealPart g ⁅z, 1 ⊗ₜ[ℝ] x⁆ = ⁅tensorRealPart g z, x⁆ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [LieAlgebra.ExtendScalars.bracket_tmul, tensorRealPart]
  | add y z hy hz => simp only [add_lie, map_add, hy, hz]

private theorem imagPart_bracket_real (z : ℂ ⊗[ℝ] g) (x : g) :
    tensorImagPart g ⁅z, 1 ⊗ₜ[ℝ] x⁆ = ⁅tensorImagPart g z, x⁆ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [LieAlgebra.ExtendScalars.bracket_tmul, tensorImagPart]
  | add y z hy hz => simp only [add_lie, map_add, hy, hz]

/-- The actual complexified image of a real abelian subalgebra is abelian. -/
theorem complexified_abelian_subalgebra (A : LieSubalgebra ℝ g) [IsLieAbelian A] :
    IsLieAbelian (complexifiedSubalgebra A) := by
  constructor
  intro x y
  apply Subtype.ext
  have hx := (complexification_mem_baseChange_iff_parts g A.toSubmodule x.val).mp x.property
  have hy := (complexification_mem_baseChange_iff_parts g A.toSubmodule y.val).mp y.property
  have hzero (r s : g) (hr : r ∈ A) (hs : s ∈ A) : ⁅r, s⁆ = 0 :=
    congrArg Subtype.val (trivial_lie_zero A A (⟨r, hr⟩ : A) (⟨s, hs⟩ : A))
  change ⁅x.val, y.val⁆ = 0
  rw [complexification_real_imag_decomposition g x.val,
    complexification_real_imag_decomposition g y.val]
  simp only [add_lie, lie_add, LieAlgebra.ExtendScalars.bracket_tmul,
    hzero _ _ hx.1 hy.1, hzero _ _ hx.1 hy.2,
    hzero _ _ hx.2 hy.1, hzero _ _ hx.2 hy.2, TensorProduct.tmul_zero, add_zero]

/-- Complexification preserves an abelian real Cartan as an actual Cartan
inside the ambient complex algebra.  Real and imaginary parts reflect the
normalizer condition. -/
theorem complexified_abelian_cartan (A : LieSubalgebra ℝ g)
    [IsLieAbelian A] [A.IsCartanSubalgebra] :
    (complexifiedSubalgebra A).IsCartanSubalgebra := by
  letI := complexified_abelian_subalgebra A
  refine ⟨inferInstance, le_antisymm ?_ (complexifiedSubalgebra A).le_normalizer⟩
  intro z hz
  apply (complexification_mem_baseChange_iff_parts g A.toSubmodule z).mpr
  have hparts (x : g) (hx : x ∈ A) :
      ⁅tensorRealPart g z, x⁆ ∈ A ∧ ⁅tensorImagPart g z, x⁆ ∈ A := by
    have hbr := ((complexifiedSubalgebra A).mem_normalizer_iff z).mp hz
      (1 ⊗ₜ[ℝ] x) (A.toSubmodule.tmul_mem_baseChange_of_mem 1 hx)
    have hh := (complexification_mem_baseChange_iff_parts g A.toSubmodule _).mp hbr
    rwa [realPart_bracket_real, imagPart_bracket_real] at hh
  constructor
  · have hr : tensorRealPart g z ∈ A.normalizer :=
      (A.mem_normalizer_iff _).mpr fun x hx => (hparts x hx).1
    rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at hr
  · have hi : tensorImagPart g z ∈ A.normalizer :=
      (A.mem_normalizer_iff _).mpr fun x hx => (hparts x hx).2
    rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at hi

/-- Inclusion of real subalgebras gives inclusion of their actual complexified
ambient images. -/
theorem complexified_subalgebra_mono {A h : LieSubalgebra ℝ g} (hAh : A ≤ h) :
    complexifiedSubalgebra A ≤ complexifiedSubalgebra h := by
  intro z hz
  have hp := (complexification_mem_baseChange_iff_parts g A.toSubmodule z).mp hz
  exact (complexification_mem_baseChange_iff_parts g h.toSubmodule z).mpr
    ⟨hAh hp.1, hAh hp.2⟩

/-- Equality of actual maximal abelian dimensions constructs the ambient
complex Cartan needed by the root-grading reduction. -/
theorem compact_equal_abelianRank_exists_complex_cartan [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (hrank : abelianRank ℝ h = abelianRank ℝ g) :
    ∃ H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g),
      H.IsCartanSubalgebra ∧ H ≤ complexifiedSubalgebra h ∧
        finrank ℂ H = abelianRank ℝ g := by
  obtain ⟨A, hAh, hab, hcartan, hdim⟩ :=
    compact_equal_abelianRank_exists_real_cartan B h hrank
  letI := hab
  letI := hcartan
  refine ⟨complexifiedSubalgebra A, complexified_abelian_cartan A,
    complexified_subalgebra_mono hAh, ?_⟩
  change finrank ℂ (A.toSubmodule.baseChange ℂ) = _
  rw [complexification_submodule_finrank]
  exact hdim

end ComplexCartan

end CubicAnomaly.Classification.CompactCartan
