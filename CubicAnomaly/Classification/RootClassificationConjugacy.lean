import CubicAnomaly.Classification.RootReflectionAutomorphism
import CubicAnomaly.Classification.RootClassificationOrbit

/-!
# Lie conjugacy of the surviving character grading

The certified Weyl word on the actual E₈ root lattice lifts to a composition
of Lie algebra automorphisms and carries all three homogeneous subspaces to
the grades of the standard one-node character on the same ambient algebra.
-/

namespace CubicAnomaly.Classification.RootClassificationConjugacy

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.RootClassificationExceptional
open CubicAnomaly.Classification.RootClassificationOrbit
open CubicAnomaly.Classification.RootReflectionAutomorphism
open CubicAnomaly.Classification.RootCharacterCoordinates
open CubicAnomaly.Classification.RootLatticeBasis
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.ToralCharacter

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- A word in simple reflections is represented by an actual Cartan-preserving
Lie automorphism inducing the prescribed permutation of root spaces. -/
theorem exists_automorphism_realizing_root_word
    (b : (rootSystem H).Base) (s : Index e8Datum ≃ b.support) (w : List (Fin 8)) :
    ∃ σ : L ≃ₗ⁅K⁆ L,
      (∀ x : L, σ x ∈ H ↔ x ∈ H) ∧
      ∀ (j : H.root) (x : L), σ x ∈ rootSpace H (rootWord H b s w j).val ↔
        x ∈ rootSpace H j.val := by
  induction w with
  | nil => exact ⟨LieEquiv.refl, fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  | cons i w ih =>
    obtain ⟨τ, htH, ht⟩ := ih
    obtain ⟨σ, hsH, hs⟩ := exists_automorphism_reflecting_rootSpaces H (s i)
    refine ⟨σ.trans τ, fun x => (htH _).trans ⟨?_, ?_⟩, fun j x => (ht _ _).trans (hs j x)⟩
    · intro hx
      let z : H := ⟨σ x, hx⟩
      have heq : σ (((rootSystem H).coreflection (s i) z : H) : L) = σ x := by simp [hsH, z]
      exact σ.injective heq ▸ ((rootSystem H).coreflection (s i) z).property
    · intro hx
      exact hsH ⟨x, hx⟩ ▸ ((rootSystem H).coreflection (s i) ⟨x, hx⟩).property

omit [CharZero K] [LieAlgebra.IsKilling K L] [IsTriangularizable K H L] in
private theorem map_character_grade_le (σ : L ≃ₗ⁅K⁆ L) (π : Equiv.Perm H.root)
    (χ ψ : rootLattice H →+ ZMod 3) (hsH : ∀ x ∈ H, σ x ∈ H)
    (hs : ∀ (j : H.root) (x : L), x ∈ rootSpace H j.val → σ x ∈ rootSpace H (π j).val)
    (hd : ∀ j, χ (rootLatticeElement H j) = ψ (rootLatticeElement H (π j)))
    (i : ZMod 3) :
    (rootCharacterGrade H χ i).map σ.toLinearMap ≤ rootCharacterGrade H ψ i := by
  apply Submodule.map_le_iff_le_comap.mpr
  refine iSup_le fun α => iSup_le fun hα x hx => ?_
  change σ x ∈ rootCharacterGrade H ψ i
  by_cases hz : (α : H → K) = 0
  · have hz' : (⟨α, root_mem_rootLattice H α.genWeightSpace_ne_bot⟩ : rootLattice H) = 0 :=
      Subtype.ext hz
    have hψ : ψ ⟨α, root_mem_rootLattice H α.genWeightSpace_ne_bot⟩ = i := by
      simpa only [hz', map_zero] using hα
    have hle : (rootSpace H α).toSubmodule ≤ rootCharacterGrade H ψ i :=
      le_iSup_of_le α (le_iSup_of_le hψ le_rfl)
    apply hle
    change σ x ∈ rootSpace H α
    change x ∈ rootSpace H α at hx
    simpa only [hz, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using
      hsH x (by simpa only [hz, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hx)
  · let j : H.root := ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
    have hψ : ψ (rootLatticeElement H (π j)) = i := (hd j).symm.trans hα
    exact (root_space_le_character_grade_iff H ψ (π j) i).mpr hψ (hs j x hx)

/-- A word relating two characters transports their full homogeneous subspaces. -/
theorem map_character_grades_of_word_preserving_cartan
    (b : (rootSystem H).Base) (s : Index e8Datum ≃ b.support) (w : List (Fin 8))
    (χ ψ : rootLattice H →+ ZMod 3) (hw : χ = ψ.comp (latticeWord H b s w).toAddMonoidHom) :
    ∃ σ : L ≃ₗ⁅K⁆ L, (∀ x : L, σ x ∈ H ↔ x ∈ H) ∧
      ∀ i : ZMod 3, (rootCharacterGrade H χ i).map σ.toLinearMap =
      rootCharacterGrade H ψ i := by
  let π := rootWord H b s w
  have hd (j : H.root) : χ (rootLatticeElement H j) = ψ (rootLatticeElement H (π j)) := by
    conv_lhs => rw [hw, AddMonoidHom.comp_apply]
    exact congrArg ψ (lattice_word_on_root H b s w j)
  obtain ⟨σ, hH, hσ⟩ := exists_automorphism_realizing_root_word H b s w
  refine ⟨σ, hH, fun i => le_antisymm (map_character_grade_le H σ π χ ψ
    (fun x => (hH x).mpr) (fun j x => (hσ j x).mpr) hd i) ?_⟩
  have hinvH (x : L) (hx : x ∈ H) : σ.symm x ∈ H :=
    (hH _).mp (by simpa using hx)
  have hinv (j : H.root) (x : L) (hx : x ∈ rootSpace H j.val) :
      σ.symm x ∈ rootSpace H (π.symm j).val :=
    (hσ (π.symm j) _).mp (by simpa only [← show π = rootWord H b s w from rfl,
      Equiv.apply_symm_apply, LieEquiv.apply_symm_apply] using hx)
  have hback := map_character_grade_le H σ.symm π.symm ψ χ hinvH hinv
    (fun j => by simpa only [Equiv.apply_symm_apply] using (hd (π.symm j)).symm) i
  intro x hx
  exact ⟨σ.symm x, hback ⟨x, hx, rfl⟩, σ.apply_symm_apply x⟩

/-- A word relating two characters transports their full homogeneous subspaces. -/
theorem map_character_grades_of_word
    (b : (rootSystem H).Base) (s : Index e8Datum ≃ b.support) (w : List (Fin 8))
    (χ ψ : rootLattice H →+ ZMod 3) (hw : χ = ψ.comp (latticeWord H b s w).toAddMonoidHom) :
    ∃ σ : L ≃ₗ⁅K⁆ L, ∀ i : ZMod 3, (rootCharacterGrade H χ i).map σ.toLinearMap =
      rootCharacterGrade H ψ i := by
  obtain ⟨σ, _, hσ⟩ := map_character_grades_of_word_preserving_cartan H b s w χ ψ hw
  exact ⟨σ, hσ⟩

/-- Conjugation realizes the E₈ character-orbit calculation on the full
homogeneous components, including the Cartan in degree zero. -/
theorem e8_actual_grading_lie_conjugacy
    (b : (rootSystem H).Base) (s : Index e8Datum ≃ b.support)
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j)
    (χ : rootLattice H →+ ZMod 3)
    (hc : (gradeTable e8Datum (simpleCharacterEquiv H b s χ) 0).card = 78) :
    ∃ σ : L ≃ₗ⁅K⁆ L, ∀ i : ZMod 3, (rootCharacterGrade H χ i).map σ.toLinearMap =
      rootCharacterGrade H ((simpleCharacterEquiv H b s).symm canonical) i := by
  let ψ := (simpleCharacterEquiv H b s).symm canonical
  obtain ⟨w, hw⟩ := e8_actual_character_weyl_word H b s h χ hc
  exact map_character_grades_of_word H b s w χ ψ hw

end CubicAnomaly.Classification.RootClassificationConjugacy
