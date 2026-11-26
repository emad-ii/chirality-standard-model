import CubicAnomaly.Classification.EqualRank
import CubicAnomaly.Classification.ClassicalModuleBridge

/-!
# A faithful defining module obstructs a common Cartan

A representation irreducible under degree-zero operators is concentrated in a
single weight grade. Operators of every other degree annihilate the module.
Faithfulness therefore forces the ambient algebra to have degree zero.
-/

namespace CubicAnomaly.Classification.CommonCartanDefining

open LieModule RootGrading

theorem faithful_irreducible_restriction_forces_zero_grade
    {K L S M A : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [LieRing S] [LieAlgebra K S] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [LieRingModule L M] [LieModule K L M] [LieRingModule S M] [LieModule K S M]
    [LieModule.IsIrreducible K S M] [AddCommGroup A]
    (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
    [IsTriangularizable K H L] [IsTriangularizable K H M]
    (degree : (H → K) →+ A) (f : S →ₗ⁅K⁆ L)
    (hcompat : ∀ x, LieModule.toEnd K L M (f x) = LieModule.toEnd K S M x)
    (himage : ∀ x, f x ∈ weightGrade H L degree 0)
    (hfaith : Function.Injective (LieModule.toEnd K L M)) :
    weightGrade H L degree 0 = ⊤ := by
  classical
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible K S M
  obtain ⟨a, ha⟩ : ∃ a, weightGrade H M degree a ≠ ⊥ := by
    by_contra! h
    have ht := iSup_weightGrade_eq_top H (M := M) degree
    simp [h] at ht
  let N : LieSubmodule K S M :=
    { toSubmodule := weightGrade H M degree a
      lie_mem := by
        intro x y hy
        have hxy : ⁅f x, y⁆ = ⁅x, y⁆ := DFunLike.congr_fun (hcompat x) y
        simpa only [zero_add, hxy] using lie_mem_weightGrade H degree (himage x) hy }
  have hN : N ≠ ⊥ := fun he => ha (congrArg LieSubmodule.toSubmodule he)
  have htop : weightGrade H M degree a = ⊤ :=
    congrArg LieSubmodule.toSubmodule ((IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN)
  apply weightGrade_zero_eq_top H degree
  intro χ hχ
  by_contra hne
  apply hχ
  rw [LieSubmodule.eq_bot_iff]
  intro x hx
  apply hfaith
  rw [map_zero]
  ext y
  change ⁅x, y⁆ = 0
  have hz := (iSupIndep_weightGrade H (M := M) degree).pairwiseDisjoint
    (show degree χ + a ≠ a by simpa using hne)
  change Disjoint (weightGrade H M degree (degree χ + a)) (weightGrade H M degree a) at hz
  rw [htop, disjoint_top] at hz
  have hy : y ∈ weightGrade H M degree a := htop.symm ▸ Submodule.mem_top
  have hxy := lie_mem_weightGrade H degree (genWeightSpace_le_weightGrade H degree χ hx) hy
  simpa only [hz, Submodule.mem_bot] using hxy

open Structural Complexification CompactGeometry CommonCartan HermitianRealization
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- A common Cartan is incompatible with a faithful ambient representation
whose restriction to the complexified isotropy remains irreducible. -/
theorem compact_common_cartan_defining_obstruction
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (M : Type*) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [LieRingModule (ℂ ⊗[ℝ] g) M] [LieModule ℂ (ℂ ⊗[ℝ] g) M]
    [LieRingModule (ℂ ⊗[ℝ] h) M] [LieModule ℂ (ℂ ⊗[ℝ] h) M]
    [LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] h) M]
    (hcompat : ∀ x, LieModule.toEnd ℂ (ℂ ⊗[ℝ] g) M (complexifiedLieHom h.incl x) =
      LieModule.toEnd ℂ (ℂ ⊗[ℝ] h) M x)
    (hfaith : Function.Injective (LieModule.toEnd ℂ (ℂ ⊗[ℝ] g) M))
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra] :
    ¬ H ≤ complexifiedSubalgebra h := by
  intro hH
  let degree := QuotientAddGroup.mk'
    (AddSubgroup.closure (containedRoots H (h.toSubmodule.baseChange ℂ)))
  obtain ⟨c, hc, _, hzero, _⟩ :=
    EqualRank.compact_common_cartan_cyclic_grading B h heff hp e hr H hH
  have hz : weightGrade H (ℂ ⊗[ℝ] g) degree 0 = h.toSubmodule.baseChange ℂ := by
    simpa only [orderThreeGrade, map_zero] using hzero
  have ht := faithful_irreducible_restriction_forces_zero_grade (M := M) H degree
    (complexifiedLieHom h.incl) hcompat (fun x => hz.symm ▸ ⟨x, rfl⟩) hfaith
  rw [hz] at ht
  apply hp
  apply top_unique
  intro x _
  apply (complexification_real_mem_baseChange_iff g h.toSubmodule x).mp
  rw [ht]
  trivial

open OrthogonalDefining ClassicalModuleBridge SymplecticDefining SymplecticGeometry ComplexDefining

/-- In an actual orthogonal algebra the isotropy cannot contain an ambient Cartan. -/
theorem orthogonal_isotropy_contains_no_cartan
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (B : CompactForm (orthogonalAlgebra W)) (h : LieSubalgebra ℝ (orthogonalAlgebra W))
    (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] orthogonalAlgebra W)) [H.IsCartanSubalgebra] :
    ¬ H ≤ complexifiedSubalgebra h := by
  letI := all_rank_orthogonal_defining_complex_irreducible B h heff hp e hr
  exact compact_common_cartan_defining_obstruction B h heff hp e hr (ℂ ⊗[ℝ] W)
    (orthogonal_complexified_inclusion_natural h) (orthogonal_ambient_operator_map_injective h) H

/-- In an actual compact symplectic algebra the isotropy cannot contain an ambient Cartan. -/
theorem symplectic_isotropy_contains_no_cartan
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (J : QuaternionicStructure W) (B : CompactForm (symplecticAlgebra J))
    (h : LieSubalgebra ℝ (symplecticAlgebra J)) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] symplecticAlgebra J)) [H.IsCartanSubalgebra] :
    ¬ H ≤ complexifiedSubalgebra h := by
  letI := complexifiedDefiningAction (symplecticAlgebra J).incl
  letI := complexified_defining_lieModule (symplecticAlgebra J).incl
  letI := complexifiedDefiningAction (symplecticDefiningRepresentation J h)
  letI := complexified_defining_lieModule (symplecticDefiningRepresentation J h)
  letI := all_rank_symplectic_complexified_defining_irreducible J B h heff hp e hr
  exact compact_common_cartan_defining_obstruction B h heff hp e hr W
    (symplectic_complexified_inclusion_natural J h) (symplectic_ambient_operator_map_injective J h) H

end CubicAnomaly.Classification.CommonCartanDefining
