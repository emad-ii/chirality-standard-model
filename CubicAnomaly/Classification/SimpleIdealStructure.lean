import CubicAnomaly.Classification.Complexification
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Simple-ideal alternatives and descent from actual complexification

A nonzero semisimple algebra is either simple or contains two disjoint
simple ideals. This follows from its actual atomic ideal lattice, without
a factorization or classified simple-type list. Simplicity of the actual
complexification also descends to the original real algebra.
-/

namespace CubicAnomaly.Classification.SimpleIdealStructure

open LieAlgebra LieModule
open CubicAnomaly.Classification.Complexification
open scoped TensorProduct

/-- A nonzero semisimple algebra is simple or has two actual disjoint
simple ideals. No finite-dimensionality or type classification is needed. -/
theorem semisimple_simple_or_disjoint_atoms
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieAlgebra.IsSemisimple R L] [Nontrivial L] :
    LieAlgebra.IsSimple R L ∨ ∃ I J : LieIdeal R L,
      IsAtom I ∧ IsAtom J ∧ Disjoint I J := by
  letI : Nontrivial (LieIdeal R L) :=
    (LieSubmodule.nontrivial_iff R L L).mpr inferInstance
  obtain ⟨I, hI⟩ := IsAtomic.exists_atom (α := LieIdeal R L)
  by_cases htop : I = ⊤
  · left
    have ha : IsAtom (⊤ : LieIdeal R L) := htop ▸ hI
    letI : IsSimpleOrder (LieIdeal R L) := isSimpleOrder_iff_isAtom_top.mpr ha
    refine ⟨IsSimpleOrder.eq_bot_or_eq_top, ?_⟩
    intro hab
    letI := hab
    letI : Subsingleton L := LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian R L
    obtain ⟨x, y, hxy⟩ := exists_pair_ne L
    exact hxy (Subsingleton.elim x y)
  · right
    have hcomp : Iᶜ ≠ ⊥ := by
      intro hz
      have he := congrArg Compl.compl hz
      exact htop (by simpa only [compl_compl, compl_bot] using he)
    obtain ⟨J, hJ, hJI⟩ := (eq_bot_or_exists_atom_le Iᶜ).resolve_left hcomp
    exact ⟨I, J, hI, hJ, disjoint_compl_right.mono_right hJI⟩

/-- The atomic alternative gives two disjoint ideals that are actually
simple as Lie algebras, without any supplied list of simple factors. -/
theorem semisimple_simple_or_disjoint_simple_ideals
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieAlgebra.IsSemisimple R L] [Nontrivial L] :
    LieAlgebra.IsSimple R L ∨ ∃ I J : LieIdeal R L,
      LieAlgebra.IsSimple R I ∧ LieAlgebra.IsSimple R J ∧ Disjoint I J := by
  rcases semisimple_simple_or_disjoint_atoms (R := R) (L := L) with h | ⟨I, J, hI, hJ, hIJ⟩
  · exact Or.inl h
  · exact Or.inr ⟨I, J, LieAlgebra.IsSemisimple.isSimple_of_isAtom I hI,
      LieAlgebra.IsSemisimple.isSimple_of_isAtom J hJ, hIJ⟩

/-- Excluding three pairwise disjoint atoms leaves either a simple algebra
or two actual simple ideals whose sum is the entire algebra. -/
theorem semisimple_simple_or_two_atoms_of_no_three
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieAlgebra.IsSemisimple R L] [Nontrivial L]
    (hno : ∀ I J T : LieIdeal R L, IsAtom I → IsAtom J → IsAtom T →
      Disjoint I J → Disjoint I T → Disjoint J T → False) :
    LieAlgebra.IsSimple R L ∨ ∃ I J : LieIdeal R L,
      IsAtom I ∧ IsAtom J ∧ Disjoint I J ∧ I ⊔ J = ⊤ := by
  rcases semisimple_simple_or_disjoint_atoms (R := R) (L := L) with
    hsimple | ⟨I, J, hI, hJ, hIJ⟩
  · exact Or.inl hsimple
  · right
    refine ⟨I, J, hI, hJ, hIJ, ?_⟩
    by_contra htop
    have hcomp : (I ⊔ J)ᶜ ≠ ⊥ := by
      intro hz
      have he := congrArg Compl.compl hz
      exact htop (by simpa only [compl_compl, compl_bot] using he)
    obtain ⟨T, hT, hle⟩ := (eq_bot_or_exists_atom_le (I ⊔ J)ᶜ).resolve_left hcomp
    exact hno I J T hI hJ hT hIJ
      (disjoint_compl_right.mono le_sup_left hle)
      (disjoint_compl_right.mono le_sup_right hle)

/-- Simplicity of the actual tensor complexification implies simplicity
of the original real Lie algebra. Ideal membership is reflected through
the actual pure-tensor inclusion. -/
theorem simple_of_complexification_simple
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    [LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] L)] : LieAlgebra.IsSimple ℝ L := by
  constructor
  · intro I
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (I.baseChange ℂ) with hb | ht
    · left
      apply le_antisymm ?_ bot_le
      intro x hx
      change x = 0
      have hxC := I.tmul_mem_baseChange_of_mem (A := ℂ) 1 hx
      rw [hb, LieSubmodule.mem_bot] at hxC
      have he := congrArg (tensorRealPart L) hxC
      simpa [tensorRealPart] using he
    · right
      apply top_unique
      intro x _
      apply (complexification_real_mem_baseChange_iff L I.toSubmodule x).mp
      change (1 : ℂ) ⊗ₜ[ℝ] x ∈ I.baseChange ℂ
      rw [ht]
      trivial
  · intro hab
    letI := hab
    have hc : IsLieAbelian (ℂ ⊗[ℝ] L) := by
      constructor
      intro x y
      rw [complexification_real_imag_decomposition L x,
        complexification_real_imag_decomposition L y]
      simp
    exact LieAlgebra.IsSimple.non_abelian ℂ hc

end CubicAnomaly.Classification.SimpleIdealStructure
