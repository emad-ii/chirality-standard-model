import CubicAnomaly.Classification.CorootComponents

/-!
# Internal cubic tests on actual simple ideals

An invariant symmetric cubic on a semisimple Lie algebra has no terms mixing
complementary ideals.  Consequently an ideal belongs to the full mixed
radical precisely when the cubic vanishes on three inputs from that ideal.

For a finite-dimensional splitting Killing Lie algebra, this identifies the
full radical as the sum of the actual simple coroot ideals whose internal
cubic vanishes.  The argument does not assume a tensor factorization of a
representation, a classification of simple Lie algebras, or component labels.
-/

namespace CubicAnomaly.Classification.CubicIdealDecomposition

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanCubic
open CubicAnomaly.Classification.CartanCoroot
open CubicAnomaly.Classification.CorootComponents

section Perfect

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra.IsSemisimple R L]

/-- Every ideal of a semisimple Lie algebra is perfect. -/
theorem semisimple_ideal_perfect (I : LieIdeal R L) : ⁅I, I⁆ = I := by
  apply le_antisymm (LieSubmodule.lie_le_left I I)
  obtain ⟨T, hT, hIT⟩ := (LieAlgebra.IsSemisimple.booleanGenerators R L).atomistic I
    (by rw [LieAlgebra.IsSemisimple.sSup_atoms_eq_top]; exact le_top)
  conv_lhs => rw [hIT]
  apply sSup_le
  intro J hJ
  have hJI : J ≤ I := by rw [hIT]; exact le_sSup hJ
  have hp : ⁅J, J⁆ = J := lie_eq_self_of_isAtom_of_nonabelian J (hT hJ)
    (LieAlgebra.IsSemisimple.non_abelian_of_isAtom J (hT hJ))
  exact hp.symm.le.trans (LieSubmodule.mono_lie hJI hJI)

private theorem bracket_eq_zero_of_disjoint_ideals (I J : LieIdeal R L)
    (hIJ : Disjoint I J) {x y : L} (hx : x ∈ I) (hy : y ∈ J) : ⁅x, y⁆ = 0 := by
  have hmem : ⁅x, y⁆ ∈ I ⊓ J :=
    ⟨lie_mem_left R L I x y hx, lie_mem_right R L J x y hy⟩
  simpa only [hIJ.eq_bot, LieSubmodule.mem_bot] using hmem

end Perfect

section Cubic

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsSemisimple K L]

/-- Vanishing here tests only three inputs from the indicated actual ideal. -/
def VanishesOnIdeal (c : TrilinearForm (R := K) (L := L) (S := K))
    (I : LieIdeal K L) : Prop :=
  ∀ x y z : I, c (x : L) (y : L) (z : L) = 0

private theorem cubic_zero_of_one_two_disjoint
    (c : TrilinearForm (R := K) (L := L) (S := K)) (hc : IsInvariant c)
    (I J : LieIdeal K L) (hIJ : Disjoint I J)
    {x y z : L} (hx : x ∈ I) (hy : y ∈ J) (hz : z ∈ J) : c x y z = 0 := by
  have hx' : x ∈ Submodule.span K {⁅(a : L), (b : L)⁆ | (a : I) (b : I)} := by
    rw [← LieSubmodule.lieIdeal_oper_eq_linear_span, semisimple_ideal_perfect]
    exact hx
  refine Submodule.span_induction (p := fun t _ => c t y z = 0) ?_ ?_ ?_ ?_ hx'
  · rintro _ ⟨a, b, rfl⟩
    have h := hc a b y z
    rw [bracket_eq_zero_of_disjoint_ideals I J hIJ a.property hy,
      bracket_eq_zero_of_disjoint_ideals I J hIJ a.property hz] at h
    simpa only [map_zero, LinearMap.zero_apply, add_zero] using h
  · simp
  · intro a b _ _ ha hb
    simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
  · intro t a _ ha
    simp only [map_smul, LinearMap.smul_apply, ha, smul_zero]

/-- Every mixed cubic term between complementary ideals vanishes, with no
restriction on the remaining input. -/
theorem cubic_mixed_ideal_compl_eq_zero
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c)
    (I : LieIdeal K L) {x y : L} (hx : x ∈ I) (hy : y ∈ Iᶜ) (z : L) :
    c x y z = 0 := by
  have hz : z ∈ I ⊔ Iᶜ := by rw [sup_compl_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := (LieSubmodule.mem_sup I Iᶜ z).mp hz
  rw [map_add]
  have h₁ : c x y a = 0 := by
    rw [hs.1]
    exact cubic_zero_of_one_two_disjoint c hc Iᶜ I disjoint_compl_left hy hx ha
  have h₂ : c x y b = 0 :=
    cubic_zero_of_one_two_disjoint c hc I Iᶜ disjoint_compl_right hx hy hb
  rw [h₁, h₂, add_zero]

/-- Internal vanishing on an ideal is equivalent to membership of that whole
ideal in the full mixed radical. -/
theorem vanishesOnIdeal_iff_le_radical
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) (I : LieIdeal K L) :
    VanishesOnIdeal c I ↔ I ≤ CubicRadical.radical c hc := by
  constructor
  · intro hi x hx
    apply (mem_radical_iff c hc x).mpr
    intro y z
    have hy : y ∈ I ⊔ Iᶜ := by rw [sup_compl_eq_top]; trivial
    have hz : z ∈ I ⊔ Iᶜ := by rw [sup_compl_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := (LieSubmodule.mem_sup I Iᶜ y).mp hy
    obtain ⟨d, hd, e, he, rfl⟩ := (LieSubmodule.mem_sup I Iᶜ z).mp hz
    have h₁ : c x a d = 0 := hi ⟨x, hx⟩ ⟨a, ha⟩ ⟨d, hd⟩
    have h₂ : c x a e = 0 := by
      rw [hs.2]
      exact cubic_mixed_ideal_compl_eq_zero c hc hs I hx he a
    have h₃ : c x b (d + e) = 0 :=
      cubic_mixed_ideal_compl_eq_zero c hc hs I hx hb (d + e)
    simpa only [map_add, LinearMap.add_apply, h₁, h₂, zero_add] using h₃
  · intro hi x y z
    exact (mem_radical_iff c hc (x : L)).mp (hi x.property) y z

end Cubic

section Coroots

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

omit [CharZero K] [IsTriangularizable K H L] in
/-- A coroot lies in the full radical exactly when the cubic vanishes
internally on the actual simple ideal it generates. -/
theorem coroot_mem_radical_iff_internal_cubic_zero
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) (α : H.root) :
    (coroot α.val : L) ∈ CubicRadical.radical c hc ↔
      VanishesOnIdeal c (corootIdeal H α) := by
  rw [vanishesOnIdeal_iff_le_radical c hc hs]
  change _ ↔ LieSubmodule.lieSpan K L {(coroot α.val : L)} ≤ _
  rw [LieSubmodule.lieSpan_le]
  simp

variable [IsAlgClosed K]

/-- The full mixed radical is the sum of actual simple coroot ideals on
which the internal cubic vanishes. -/
theorem radical_eq_iSup_internal_zero_corootIdeals
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) :
    CubicRadical.radical c hc = ⨆ α : H.root,
      ⨆ (_ : VanishesOnIdeal c (corootIdeal H α)), corootIdeal H α := by
  rw [ideal_eq_iSup_corootIdeals H (CubicRadical.radical c hc)]
  congr 1
  funext α
  rw [coroot_mem_radical_iff_internal_cubic_zero H c hc hs α]

/-- Nonzero full radical is equivalent to an internally vanishing cubic on
at least one actual simple coroot ideal. -/
theorem radical_ne_bot_iff_exists_internal_zero_corootIdeal
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) :
    CubicRadical.radical c hc ≠ ⊥ ↔
      ∃ α : H.root, VanishesOnIdeal c (corootIdeal H α) := by
  rw [ideal_ne_bot_iff_exists_coroot H]
  exact exists_congr fun α => coroot_mem_radical_iff_internal_cubic_zero H c hc hs α

end Coroots

end CubicAnomaly.Classification.CubicIdealDecomposition
