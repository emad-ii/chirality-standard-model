import CubicAnomaly.Classification.AllRankGrading

/-!
# Full span of the actual zero-grade roots

The roots of a Cartan-containing centreless subalgebra span the whole dual
of the ambient Cartan.  Thus the full-rank zero-root condition used by a
toral census follows from actual isotropy semisimplicity.  The argument
uses the actual root-space decomposition and dual annihilators, without
assigning a root-system type or assuming a finite-coordinate realization.
-/

namespace CubicAnomaly.Classification.FullRankRoots

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling
open CubicAnomaly.Classification.CommonCartan

section General

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The actual ambient root forms whose root spaces lie in the given
subalgebra, considered in the actual linear dual of the Cartan. -/
def containedRootForms (S : LieSubalgebra K L) : Set (Dual K H) :=
  {φ | ∃ α : H.root, (rootSpace H α.val).toSubmodule ≤ S.toSubmodule ∧
    φ = (α.val : Dual K H)}

/-- A Cartan element annihilating all actual contained roots centralizes
the whole Cartan-containing subalgebra. -/
theorem cartan_centralizes_of_contained_roots_zero
    (S : LieSubalgebra K L) (hHS : H ≤ S) (x : H)
    (hx : ∀ α : H.root, (rootSpace H α.val).toSubmodule ≤ S.toSubmodule →
      α.val x = 0) :
    ∀ y : S, ⁅(x : L), (y : L)⁆ = 0 := by
  have hle : S.toSubmodule ≤ (ad K L (x : L)).ker := by
    rw [subalgebra_eq_root_decomposition H S hHS]
    refine sup_le ?_ (iSup_le fun α => iSup_le fun hα => ?_)
    · intro y hy
      change ⁅(x : L), y⁆ = 0
      exact congrArg Subtype.val (trivial_lie_zero H H x (⟨y, hy⟩ : H))
    · intro y hy
      change ⁅(x : L), y⁆ = 0
      let a : Weight K H L := ⟨α, hα.2.1⟩
      let a' : H.root := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα.1⟩⟩
      change ⁅x, y⁆ = 0
      rw [lie_eq_smul_of_mem_rootSpace hy x]
      have hz : α x = 0 := hx a' hα.2.2
      rw [hz, zero_smul]
  exact fun y => hle y.property

/-- For centreless isotropy, actual contained roots separate points of
the common Cartan. -/
theorem cartan_eq_zero_of_contained_roots_zero
    (S : LieSubalgebra K L) (hHS : H ≤ S)
    (hcenter : LieAlgebra.center K S = ⊥) (x : H)
    (hx : ∀ α : H.root, (rootSpace H α.val).toSubmodule ≤ S.toSubmodule →
      α.val x = 0) : x = 0 := by
  have hcomm := cartan_centralizes_of_contained_roots_zero H S hHS x hx
  have hc : (⟨x, hHS x.property⟩ : S) ∈ LieAlgebra.center K S := by
    intro y
    apply Subtype.ext
    change ⁅(y : L), (x : L)⁆ = 0
    rw [← lie_skew, hcomm y, neg_zero]
  rw [hcenter, LieSubmodule.mem_bot] at hc
  exact Subtype.ext (congrArg (fun y : S => (y : L)) hc)

/-- The full-rank condition for the actual zero-grade roots follows from
centrelessness of the Cartan-containing subalgebra. -/
theorem contained_root_forms_span_eq_top
    (S : LieSubalgebra K L) (hHS : H ≤ S)
    (hcenter : LieAlgebra.center K S = ⊥) :
    Submodule.span K (containedRootForms H S) = ⊤ := by
  have hbot : (Submodule.span K (containedRootForms H S)).dualCoannihilator = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    apply cartan_eq_zero_of_contained_roots_zero H S hHS hcenter x
    intro α hα
    exact (Submodule.mem_dualCoannihilator x).mp hx ((rootSystem H).root α)
      (Submodule.subset_span ⟨α, hα, rfl⟩)
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq
    (W := Submodule.span K (containedRootForms H S)), hbot, Submodule.dualAnnihilator_bot]

/-- The span of the actual contained roots has the full Cartan dimension. -/
theorem contained_root_forms_finrank
    (S : LieSubalgebra K L) (hHS : H ≤ S)
    (hcenter : LieAlgebra.center K S = ⊥) :
    finrank K (Submodule.span K (containedRootForms H S)) = finrank K H := by
  rw [contained_root_forms_span_eq_top H S hHS hcenter,
    finrank_top, Subspace.dual_finrank_eq]

end General

section RationalRank

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- The actual contained roots have full rational rank as well as full
complex span.  The upper bound uses crystallographic root-pairing rank;
the lower bound is scalar extension of the finite rational span. -/
theorem contained_root_forms_finrank_rat
    (S : LieSubalgebra ℂ L) (hHS : H ≤ S)
    (hcenter : LieAlgebra.center ℂ S = ⊥) :
    finrank ℚ (Submodule.span ℚ (containedRootForms H S)) = finrank ℂ H := by
  letI : Module ℚ H := Module.compHom H (algebraMap ℚ ℂ)
  have hsub : containedRootForms H S ⊆ Set.range (rootSystem H).root := by
    rintro φ ⟨α, _, rfl⟩
    exact ⟨α, rfl⟩
  have hfinite : (containedRootForms H S).Finite := (Set.finite_range _).subset hsub
  let N := Submodule.span ℚ (containedRootForms H S)
  let P := (rootSystem H).rootSpan ℚ
  letI : Module.Finite ℚ N := Module.Finite.of_fg (Submodule.fg_span hfinite)
  letI : Module.Finite ℚ P :=
    Module.Finite.of_fg (Submodule.fg_span (Set.finite_range _))
  apply le_antisymm
  · calc
      finrank ℚ N ≤ finrank ℚ P := Submodule.finrank_mono (Submodule.span_mono hsub)
      _ = finrank ℂ (Dual ℂ H) := (rootSystem H).finrank_rootSpanIn ℚ
      _ = finrank ℂ H := Subspace.dual_finrank_eq
  · have hd := (N.tensorToSpan ℂ).finrank_range_le
    rw [LinearMap.range_eq_top.mpr (N.surjective_tensorToSpan ℂ),
      finrank_top, Module.finrank_baseChange] at hd
    have hs : Submodule.span ℂ (N : Set (Dual ℂ H)) = ⊤ := by
      dsimp only [N]
      rw [Submodule.span_span_of_tower,
        contained_root_forms_span_eq_top H S hHS hcenter]
    rw [hs, finrank_top, Subspace.dual_finrank_eq] at hd
    exact hd

end RationalRank

section CompactPair

open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.CompactCartan

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- For the original compact-pair hypotheses, a common ambient Cartan has
full span of its actual contained isotropy roots. -/
theorem compact_common_cartan_root_forms_span_eq_top
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) :
    Submodule.span ℂ (containedRootForms H (complexifiedSubalgebra h)) = ⊤ := by
  have hgcenter := (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) :=
    compact_complexification_isKilling B hgcenter
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  letI : LieAlgebra.IsKilling ℂ (complexifiedSubalgebra h) :=
    (subalgebraComplexificationEquiv h).isKilling
  exact contained_root_forms_span_eq_top H (complexifiedSubalgebra h) hH
    (LieAlgebra.center_eq_bot ℂ (complexifiedSubalgebra h))

/-- The full rational rank of the actual zero-grade roots follows from the
original hypotheses and a common ambient Cartan. -/
theorem compact_common_cartan_root_forms_finrank_rat
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) :
    finrank ℚ (Submodule.span ℚ (containedRootForms H (complexifiedSubalgebra h))) =
      finrank ℂ H := by
  have hgcenter := (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g) :=
    compact_complexification_isKilling B hgcenter
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  letI : LieAlgebra.IsKilling ℂ (complexifiedSubalgebra h) :=
    (subalgebraComplexificationEquiv h).isKilling
  exact contained_root_forms_finrank_rat H (complexifiedSubalgebra h) hH
    (LieAlgebra.center_eq_bot ℂ (complexifiedSubalgebra h))

/-- Equality of geometric abelian ranks constructs a common Cartan whose
actual isotropy roots have full span, directly from the original hypotheses. -/
theorem equal_abelianRank_exists_full_span_cartan
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (hrank : abelianRank ℝ h = abelianRank ℝ g) :
    ∃ (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) (hH : H.IsCartanSubalgebra),
      letI := hH
      H ≤ complexifiedSubalgebra h ∧
      finrank ℂ H = abelianRank ℝ g ∧
      Submodule.span ℂ (containedRootForms H (complexifiedSubalgebra h)) = ⊤ := by
  obtain ⟨H, hH, hContained, hdim⟩ :=
    compact_equal_abelianRank_exists_complex_cartan B h hrank
  letI := hH
  exact ⟨H, hH, hContained, hdim,
    compact_common_cartan_root_forms_span_eq_top B h heff hproper e hradical H hContained⟩

end CompactPair

end CubicAnomaly.Classification.FullRankRoots
