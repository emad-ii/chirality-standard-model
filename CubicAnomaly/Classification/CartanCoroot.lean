import CubicAnomaly.Classification.RootSimple

/-!
# Coroot witnesses for ideals and the full cubic radical

A nonzero ideal in a splitting Killing Lie algebra contains an actual coroot.
Consequently ideal containment is determined by coroot membership, and an
invariant symmetric cubic has nonzero full radical exactly when one coroot
annihilates all pairs of Cartan basis vectors.  This replaces an arbitrary
kernel-vector search by a finite search through the actual roots.

The construction uses root spaces, their `sl₂` triples, and the Boolean lattice
of ideals of a semisimple Lie algebra.  No classification of simple factors or
authored component labels enters the proof.
-/

namespace CubicAnomaly.Classification.CartanCoroot

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanCubic

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- If a Cartan element of an ideal is not annihilated by a root, that root's
coroot belongs to the ideal.  The proof uses the actual root `sl₂` triple. -/
theorem coroot_mem_ideal_of_cartan_eval_ne_zero
    (I : LieIdeal K L) (α : H.root) (x : H)
    (hx : (x : L) ∈ I) (hαx : α.val x ≠ 0) :
    (coroot α.val : L) ∈ I := by
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨t, e, f, hsl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have heI : e ∈ I := by
    apply (I.toSubmodule.smul_mem_iff hαx).mp
    rw [← lie_eq_smul_of_mem_rootSpace he x]
    exact lie_mem_left K L I x e hx
  have htI : t ∈ I := by
    rw [← hsl2.lie_e_f]
    exact lie_mem_left K L I e f heI
  rwa [hsl2.h_eq_coroot hα he hf] at htI

/-- A nonzero Cartan element is detected by at least one actual root. -/
theorem exists_root_eval_ne_zero (x : H) (hx : x ≠ 0) :
    ∃ α : H.root, α.val x ≠ 0 := by
  by_contra! h
  apply hx
  have hxker : x ∈ ⨅ α : Weight K H L, α.ker := by
    refine (Submodule.mem_iInf _).mpr fun α => ?_
    by_cases hα : α.IsZero
    · change α x = 0
      rw [hα.eq]
      rfl
    · exact h ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩⟩
  simpa only [iInf_ker_weight_eq_bot, Submodule.mem_bot] using hxker

/-- Every actual coroot is nonzero. -/
theorem actual_coroot_ne_zero (α : H.root) : (coroot α.val : L) ≠ 0 := by
  intro h
  have hc : coroot α.val = 0 := Subtype.ext h
  exact (Finset.mem_filter.mp α.property).2 (coroot_eq_zero_iff.mp hc)

/-- Roots connected by nonzero Cartan pairings belong to the same root
component.  This definition refers to the actual Lie root system. -/
def CorootConnected (α β : H.root) : Prop :=
  Relation.EqvGen (fun a b : H.root => b.val (coroot a.val) ≠ 0) α β

/-- Nonorthogonal coroots have the same membership in every Lie ideal. -/
theorem coroot_mem_ideal_iff_of_pairing_ne_zero
    (I : LieIdeal K L) (α β : H.root) (hab : β.val (coroot α.val) ≠ 0) :
    (coroot α.val : L) ∈ I ↔ (coroot β.val : L) ∈ I := by
  have hba : α.val (coroot β.val) ≠ 0 := by
    change (rootSystem H).pairing α β ≠ 0
    exact ((rootSystem H).pairing_eq_zero_iff).not.mpr hab
  exact ⟨fun h => coroot_mem_ideal_of_cartan_eval_ne_zero H I β (coroot α.val) h hab,
    fun h => coroot_mem_ideal_of_cartan_eval_ne_zero H I α (coroot β.val) h hba⟩

/-- Coroot membership is constant throughout each actual root component. -/
theorem coroot_mem_ideal_iff_of_connected
    (I : LieIdeal K L) {α β : H.root} (h : CorootConnected H α β) :
    (coroot α.val : L) ∈ I ↔ (coroot β.val : L) ∈ I := by
  induction h with
  | rel a b hab => exact coroot_mem_ideal_iff_of_pairing_ne_zero H I a b hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

variable [IsAlgClosed K]

/-- A nonzero ideal contains an actual coroot.  In particular the witness is
drawn from a finite root set, rather than an arbitrary vector space. -/
theorem ideal_ne_bot_iff_exists_coroot (I : LieIdeal K L) :
    I ≠ ⊥ ↔ ∃ α : H.root, (coroot α.val : L) ∈ I := by
  constructor
  · intro hI
    have hex : ∃ x : H, (x : L) ∈ I ∧ x ≠ 0 := by
      by_contra! h
      apply hI
      apply le_antisymm _ bot_le
      apply ideal_le_of_cartan_intersection_le H I ⊥
      intro x hx
      simp only [h x hx, ZeroMemClass.coe_zero, LieSubmodule.mem_bot]
    obtain ⟨x, hxI, hx⟩ := hex
    obtain ⟨α, hα⟩ := exists_root_eval_ne_zero H x hx
    exact ⟨α, coroot_mem_ideal_of_cartan_eval_ne_zero H I α x hxI hα⟩
  · rintro ⟨α, hα⟩ hI
    rw [hI, LieSubmodule.mem_bot] at hα
    exact actual_coroot_ne_zero H α hα

/-- Ideal containment is determined by membership of the actual coroots. -/
theorem ideal_le_iff_coroot (I J : LieIdeal K L) :
    I ≤ J ↔ ∀ α : H.root, (coroot α.val : L) ∈ I → (coroot α.val : L) ∈ J := by
  constructor
  · intro h α hα
    exact h hα
  · intro h
    have hbot : I ⊓ Jᶜ = ⊥ := by
      by_contra hne
      obtain ⟨α, hα⟩ := (ideal_ne_bot_iff_exists_coroot H (I ⊓ Jᶜ)).mp hne
      have hz : (coroot α.val : L) ∈ J ⊓ Jᶜ := ⟨h α hα.1, hα.2⟩
      rw [inf_compl_eq_bot, LieSubmodule.mem_bot] at hz
      exact actual_coroot_ne_zero H α hz
    calc
      I = I ⊓ J ⊔ I ⊓ Jᶜ := sup_inf_inf_compl.symm
      _ = I ⊓ J := by rw [hbot, sup_bot_eq]
      _ ≤ J := inf_le_right

/-- Every ideal is generated, as a Lie ideal, by the coroots that it contains. -/
theorem ideal_eq_lieSpan_coroots (I : LieIdeal K L) :
    I = LieSubmodule.lieSpan K L
      {x : L | ∃ α : H.root, (coroot α.val : L) ∈ I ∧ x = coroot α.val} := by
  apply le_antisymm
  · apply (ideal_le_iff_coroot H I _).mpr
    intro α hα
    exact LieSubmodule.subset_lieSpan ⟨α, hα, rfl⟩
  · apply LieSubmodule.lieSpan_le.mpr
    rintro x ⟨α, hα, rfl⟩
    exact hα

/-- The full mixed radical is nonzero exactly when one coroot annihilates
all pairs of Cartan elements. -/
theorem radical_ne_bot_iff_coroot
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) :
    radical c hc ≠ ⊥ ↔
      ∃ α : H.root, ∀ y z : H, c (coroot α.val) y z = 0 := by
  rw [ideal_ne_bot_iff_exists_coroot H]
  apply exists_congr
  intro α
  exact cartan_mem_radical_iff H c hc hs (coroot α.val)

/-- A finite coroot-by-Cartan-basis test detects the full mixed radical. -/
theorem radical_ne_bot_iff_coroot_basis {ι : Type*} (b : Basis ι K H)
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) :
    radical c hc ≠ ⊥ ↔
      ∃ α : H.root, ∀ i j, c (coroot α.val) (b i) (b j) = 0 := by
  rw [ideal_ne_bot_iff_exists_coroot H]
  apply exists_congr
  intro α
  exact cartan_mem_radical_iff_basis H b c hc hs (coroot α.val)

/-- The radical itself, not only its nonvanishing, is the ideal generated by
the coroots passing the finite mixed Cartan test. -/
theorem radical_eq_lieSpan_null_coroots {ι : Type*} (b : Basis ι K H)
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) :
    radical c hc = LieSubmodule.lieSpan K L
      {x : L | ∃ α : H.root,
        (∀ i j, c (coroot α.val) (b i) (b j) = 0) ∧ x = coroot α.val} := by
  rw [ideal_eq_lieSpan_coroots H (radical c hc)]
  congr 1
  ext x
  apply exists_congr
  intro α
  rw [cartan_mem_radical_iff_basis H b c hc hs (coroot α.val)]

omit [IsAlgClosed K] in
/-- Passing the finite mixed cubic test propagates through an entire root
component, because the full radical is an actual Lie ideal. -/
theorem coroot_cubic_zero_iff_of_connected {ι : Type*} (b : Basis ι K H)
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c)
    {α β : H.root} (h : CorootConnected H α β) :
    (∀ i j, c (coroot α.val) (b i) (b j) = 0) ↔
      (∀ i j, c (coroot β.val) (b i) (b j) = 0) := by
  rw [← cartan_mem_radical_iff_basis H b c hc hs (coroot α.val),
    ← cartan_mem_radical_iff_basis H b c hc hs (coroot β.val)]
  exact coroot_mem_ideal_iff_of_connected H (radical c hc) h

end CubicAnomaly.Classification.CartanCoroot
