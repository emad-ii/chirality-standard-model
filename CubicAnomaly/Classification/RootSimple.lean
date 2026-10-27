import CubicAnomaly.Classification.CartanCubic
import Mathlib.Algebra.Lie.Weights.IsSimple

/-!
# Irreducible root systems and simple Lie algebras

For a finite-dimensional Killing Lie algebra, an ideal's intersection with a
splitting Cartan is invariant under every coroot reflection.  Actual root
`sl₂` triples prove this invariance.  Root-system irreducibility then forces
the ideal to be zero or the whole algebra, using Cartan detection of ideals.

Together with Mathlib's forward implication, this identifies simple Lie
algebras with irreducible actual root systems over algebraically closed fields
of characteristic zero.  No list of simple types is used.
-/

namespace CubicAnomaly.Classification.RootSimple

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- An ideal's Cartan intersection is preserved by all coroot reflections of
the actual Lie root system. -/
theorem cartan_intersection_invariant_coreflection (I : LieIdeal K L)
    (α : H.root) :
    I.toSubmodule.comap H.subtype ∈
      Module.End.invtSubmodule ((rootSystem H).coreflection α) := by
  rw [Module.End.mem_invtSubmodule]
  intro t ht
  change (t : L) ∈ I at ht
  change ((t - α.val t • coroot α.val : H) : L) ∈ I
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  by_cases hat : α.val t = 0
  · simpa only [hat, zero_smul, sub_zero] using ht
  obtain ⟨s, e, f, hsl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have heI : e ∈ I := by
    apply (I.toSubmodule.smul_mem_iff hat).mp
    rw [← lie_eq_smul_of_mem_rootSpace he t]
    exact lie_mem_left K L I t e ht
  have hsI : s ∈ I := by
    rw [← hsl2.lie_e_f]
    exact lie_mem_left K L I e f heI
  have hcoroot : (coroot α.val : L) ∈ I := by
    rwa [hsl2.h_eq_coroot hα he hf] at hsI
  exact I.sub_mem ht (I.smul_mem (α.val t) hcoroot)

/-- Irreducibility of the actual root system implies simplicity of the Lie
algebra.  In particular this converse applies to complexified compact algebras
with nondegenerate Killing form. -/
theorem isSimple_of_irreducible_rootSystem [IsAlgClosed K]
    [(rootSystem H).IsIrreducible] : LieAlgebra.IsSimple K L := by
  letI : Nontrivial H := RootPairing.IsIrreducible.nontrivial' (rootSystem H)
  constructor
  · intro I
    by_cases hI : I = ⊥
    · exact Or.inl hI
    right
    let q : Submodule K H := I.toSubmodule.comap H.subtype
    have hqne : q ≠ ⊥ := by
      intro hq
      apply hI
      apply le_antisymm _ bot_le
      apply CartanCubic.ideal_le_of_cartan_intersection_le H I ⊥
      intro x hx
      have hxq : x ∈ q := hx
      rw [hq, Submodule.mem_bot] at hxq
      simpa only [hxq, ZeroMemClass.coe_zero] using (⊥ : LieIdeal K L).zero_mem
    have hqtop : q = ⊤ :=
      RootPairing.IsIrreducible.eq_top_of_invtSubmodule_coreflection
        (P := rootSystem H) q (cartan_intersection_invariant_coreflection H I) hqne
    apply top_unique
    apply CartanCubic.ideal_le_of_cartan_intersection_le H ⊤ I
    intro x _
    have hx : x ∈ q := by rw [hqtop]; trivial
    exact hx
  · intro habelian
    letI : IsLieAbelian L := habelian
    letI : Subsingleton L := LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian K L
    obtain ⟨x, y, hxy⟩ := exists_pair_ne H
    exact hxy (Subtype.ext (Subsingleton.elim _ _))

/-- For actual splitting Killing Lie algebras over algebraically closed fields
of characteristic zero, simplicity and irreducibility of the root system are equivalent. -/
theorem isSimple_iff_irreducible_rootSystem [IsAlgClosed K] :
    LieAlgebra.IsSimple K L ↔ (rootSystem H).IsIrreducible := by
  constructor
  · intro hs
    letI := hs
    infer_instance
  · intro hr
    letI := hr
    exact isSimple_of_irreducible_rootSystem H

end CubicAnomaly.Classification.RootSimple
