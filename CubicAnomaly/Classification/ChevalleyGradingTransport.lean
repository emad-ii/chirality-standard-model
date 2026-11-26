import CubicAnomaly.Classification.RootClassificationGrades

/-!
# Transport of character gradings between matched Cartans

A Lie isomorphism matching the simple root evaluations carries every component
of a labeled root-lattice character to the same component on the target.
This includes the Cartan in degree zero.
-/

namespace CubicAnomaly.Classification.ChevalleyGradingTransport

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open Exceptional RootClassificationExceptional RootGrading RootCharacterCoordinates ToralCharacter

variable {K L M : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)
  [LieRing M] [LieAlgebra K M] [FiniteDimensional K M] [IsKilling K M]
  (J : LieSubalgebra K M) [J.IsCartanSubalgebra] [IsTriangularizable K J M]
  (d : (rootSystem J).Base)

private def evaluate (h : H) : rootLattice H →ₗ[ℤ] K :=
  ((Pi.evalAddMonoidHom (fun _ : H => K) h).comp (rootLattice H).subtype).toIntLinearMap

private lemma map_grade_le (s : b.support ≃ d.support) (T : H ≃ₗ[K] J)
    (ht : ∀ i h, (s i).val.val (T h) = i.val.val h)
    (Φ : L ≃ₗ⁅K⁆ M) (hΦ : ∀ h : H, Φ h.val = (T h).val)
    (χ : rootLattice H →+ ZMod 3) (ψ : rootLattice J →+ ZMod 3)
    (hχ : ∀ i, ψ (rootLatticeElement J (s i).val) = χ (rootLatticeElement H i.val))
    (k : ZMod 3) :
    (rootCharacterGrade H χ k).map Φ.toLinearMap ≤ rootCharacterGrade J ψ k := by
  let E := (simpleLatticeBasis H b).equiv (simpleLatticeBasis J d) s
  have eb (i : b.support) :
      E ((simpleLatticeBasis H b) i) = (simpleLatticeBasis J d) (s i) := Basis.equiv_apply _ _ _ _
  have ev (x : rootLattice H) (h : H) : (E x).val (T h) = x.val h := by
    have heq : (evaluate J (T h)).comp E.toLinearMap = evaluate H h := by
      apply (simpleLatticeBasis H b).ext
      intro i
      change (E ((simpleLatticeBasis H b) i)).val (T h) = ((simpleLatticeBasis H b) i).val h
      rw [eb, simpleLatticeBasis_apply, simpleLatticeBasis_apply]
      exact ht i h
    exact LinearMap.congr_fun heq x
  have chars (x : rootLattice H) : ψ (E x) = χ x := by
    have heq : ψ.toIntLinearMap.comp E.toLinearMap = χ.toIntLinearMap := by
      apply (simpleLatticeBasis H b).ext
      intro i
      change ψ (E ((simpleLatticeBasis H b) i)) = χ ((simpleLatticeBasis H b) i)
      rw [eb, simpleLatticeBasis_apply, simpleLatticeBasis_apply]
      exact hχ i
    exact LinearMap.congr_fun heq x
  apply Submodule.map_le_iff_le_comap.mpr
  refine iSup_le fun α => iSup_le fun hα => ?_
  let a : rootLattice H := ⟨α, root_mem_rootLattice H α.genWeightSpace_ne_bot⟩
  have rootMap {x : L} (hx : x ∈ rootSpace H α) : Φ x ∈ rootSpace J (E a).val := by
    apply weightSpace_le_genWeightSpace
    apply (mem_weightSpace _ _).mpr
    rintro z
    obtain ⟨h, rfl⟩ := T.surjective z
    change ⁅(T h).val, Φ x⁆ = (E a).val (T h) • Φ x
    rw [← hΦ h, ← Φ.map_lie, ev, ← map_smul Φ]
    exact congrArg Φ (lie_eq_smul_of_mem_rootSpace hx h)
  obtain ⟨v, hv, hv0⟩ := α.exists_ne_zero
  have hβ : rootSpace J (E a).val ≠ ⊥ := by
    intro hz
    have hm := hz ▸ rootMap hv
    exact hv0 (Φ.injective ((show Φ v = 0 from hm).trans (map_zero Φ).symm))
  let β : Weight K J M := Weight.mk (E a).val hβ
  have hψ : ψ ⟨β, root_mem_rootLattice J β.genWeightSpace_ne_bot⟩ = k :=
    (chars a).trans hα
  exact fun _ hx => (le_iSup_of_le β (le_iSup_of_le hψ le_rfl) :
    (rootSpace J β).toSubmodule ≤ rootCharacterGrade J ψ k) (rootMap hx)

/-- An isomorphism matching labeled simple evaluations transports every
character grading with matching values on those simple roots. -/
theorem map_character_grade_of_matching (s : b.support ≃ d.support) (T : H ≃ₗ[K] J)
    (ht : ∀ i h, (s i).val.val (T h) = i.val.val h)
    (Φ : L ≃ₗ⁅K⁆ M) (hΦ : ∀ h : H, Φ h.val = (T h).val)
    (χ : rootLattice H →+ ZMod 3) (ψ : rootLattice J →+ ZMod 3)
    (hχ : ∀ i, ψ (rootLatticeElement J (s i).val) = χ (rootLatticeElement H i.val))
    (k : ZMod 3) :
    (rootCharacterGrade H χ k).map Φ.toLinearMap = rootCharacterGrade J ψ k := by
  refine le_antisymm (map_grade_le H b J d s T ht Φ hΦ χ ψ hχ k) ?_
  have back := map_grade_le J d H b s.symm T.symm (by
    intro i h
    simpa only [Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply] using
      (ht (s.symm i) (T.symm h)).symm) Φ.symm (by
    intro h
    apply Φ.injective
    change Φ (Φ.symm h.val) = Φ (T.symm h).val
    rw [LieEquiv.apply_symm_apply, hΦ, LinearEquiv.apply_symm_apply]) ψ χ
    (fun i => by simpa only [Equiv.apply_symm_apply] using (hχ (s.symm i)).symm) k
  intro x hx
  exact ⟨Φ.symm x, back ⟨x, hx, rfl⟩, Φ.apply_symm_apply x⟩

/-- Simple roots carrying the same indexed assignment define the same
grading under the matched Lie isomorphism. -/
theorem map_labeled_character_grade {D : RootDatum}
    (s₁ : Index D ≃ b.support) (s₂ : Index D ≃ d.support) (T : H ≃ₗ[K] J)
    (ht : ∀ i h, (s₂ i).val.val (T h) = (s₁ i).val.val h)
    (Φ : L ≃ₗ⁅K⁆ M) (hΦ : ∀ h : H, Φ h.val = (T h).val)
    (c : Index D → ZMod 3) (k : ZMod 3) :
    (rootCharacterGrade H ((simpleCharacterEquiv H b s₁).symm c) k).map Φ.toLinearMap =
      rootCharacterGrade J ((simpleCharacterEquiv J d s₂).symm c) k := by
  apply map_character_grade_of_matching H b J d (s₁.symm.trans s₂) T
      (fun i h => by simpa using ht (s₁.symm i) h) Φ hΦ
  intro i
  obtain ⟨j, rfl⟩ := s₁.surjective i
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, ← simpleCharacterEquiv_apply,
    Equiv.apply_symm_apply]

end CubicAnomaly.Classification.ChevalleyGradingTransport
