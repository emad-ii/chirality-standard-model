import CubicAnomaly.Classification.RootClassificationGrades
import CubicAnomaly.Classification.FullRankRoots

/-! A bounded integral lift of the values of a character on simple roots
obstructs full span of its grade-zero roots. The bound propagates to every
actual root by induction under simple reflections. -/

namespace CubicAnomaly.Classification.RootClassificationBoundedLift

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open RootGrading RootClassificationExceptional RootCharacterCoordinates
open CommonCartan FullRankRoots ToralCharacter

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L] (H : LieSubalgebra K L)
  [H.IsCartanSubalgebra] [IsTriangularizable K H L] (b : (rootSystem H).Base)
  {n : ℕ} (s : Fin n ≃ b.support)

private noncomputable def functional (v : Fin n → ℤ) : Dual K (Dual K H) :=
  (b.toWeightBasis.reindex s.symm).constr K (fun i => (v i : K))

private theorem eval_simple (v : Fin n → ℤ) (i : Fin n) :
    functional H b s v ((rootSystem H).root (s i)) = (v i : K) := by
  have h := (b.toWeightBasis.reindex s.symm).constr_basis K (fun i => (v i : K)) i
  simpa [functional] using h

private theorem reflected_functional (v : Fin n → ℤ) (i : Fin n) :
    (functional H b s v).comp ((rootSystem H).reflection (s i)).toLinearMap =
      functional H b s (fun j => v j - b.cartanMatrix (s j) (s i) * v i) := by
  apply (b.toWeightBasis.reindex s.symm).ext
  intro j
  simp only [Basis.reindex_apply, Equiv.symm_symm, RootPairing.Base.toWeightBasis_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, RootPairing.reflection_apply,
    RootPairing.root_coroot'_eq_pairing, map_sub, map_smul, eval_simple,
    Int.cast_sub, Int.cast_mul, smul_eq_mul]
  rw [← b.algebraMap_cartanMatrixIn_apply ℤ (s j) (s i)]
  rfl

private theorem root_values_bounded (F : Set (Fin n → ℤ))
    (hbound : ∀ v ∈ F, ∀ i, -2 ≤ v i ∧ v i ≤ 2)
    (hreflect : ∀ v ∈ F, ∀ i, (fun j => v j - b.cartanMatrix (s j) (s i) * v i) ∈ F)
    (α : H.root) : ∀ v ∈ F, ∃ z : ℤ, -2 ≤ z ∧ z ≤ 2 ∧
        functional H b s v ((rootSystem H).root α) = (z : K) := by
  apply b.induction_reflect α
  · intro k ih v hv
    obtain ⟨z, h₁, h₂, hz⟩ := ih v hv
    exact ⟨-z, by omega, by omega, by rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, map_neg, hz, Int.cast_neg]⟩
  · intro k hk v hv
    let i := s.symm ⟨k, hk⟩
    have hi : (s i).val = k := congrArg Subtype.val (s.apply_symm_apply ⟨k, hk⟩)
    exact ⟨v i, (hbound v hv i).1, (hbound v hv i).2, hi ▸ eval_simple H b s v i⟩
  · intro k l ih hl v hv
    let i := s.symm ⟨l, hl⟩
    have hi : (s i).val = l := congrArg Subtype.val (s.apply_symm_apply ⟨l, hl⟩)
    obtain ⟨z, h₁, h₂, hz⟩ := ih _ (hreflect v hv i)
    refine ⟨z, h₁, h₂, ?_⟩
    rw [← reflected_functional] at hz
    simpa only [RootPairing.root_reflectionPerm, LinearMap.comp_apply, LinearEquiv.coe_coe, hi] using hz

/-- Bounded integral lifts closed under simple reflections force every
character with full grade-zero span to vanish. The index reordering is
part of the argument, allowing either numbering of the classical diagrams. -/
theorem full_zero_grade_span_forces_zero_character
    (χ : rootLattice H →+ ZMod 3) (S : LieSubalgebra K L)
    (hzero : S.toSubmodule = rootCharacterGrade H χ 0)
    (hspan : Submodule.span K (containedRootForms H S) = ⊤)
    (F : Set (Fin n → ℤ)) (w : Fin n → ℤ) (hw : w ∈ F)
    (hmod : ∀ i, (w i : ZMod 3) = χ (rootLatticeElement H (s i)))
    (hbound : ∀ v ∈ F, ∀ i, -2 ≤ v i ∧ v i ≤ 2)
    (hreflect : ∀ v ∈ F, ∀ i, (fun j => v j - b.cartanMatrix (s j) (s i) * v i) ∈ F) :
    χ = 0 := by
  classical
  let B := (simpleLatticeBasis H b).reindex s.symm
  have hB (i : Fin n) : B i = rootLatticeElement H (s i) := by simp [B]
  have hkill : Submodule.span K (containedRootForms H S) ≤
      LinearMap.ker (functional H b s w) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    change functional H b s w ((rootSystem H).root α) = 0
    let c := B.repr (rootLatticeElement H α)
    have hc : ∑ i, c i • B i = rootLatticeElement H α := B.sum_repr _
    have hform : ∑ i, c i • (rootSystem H).root (s i) = (rootSystem H).root α := by
      ext t
      have ht := congrArg (fun u : rootLattice H => u.val t) hc
      simpa [hB, rootLatticeElement, Finset.sum_apply] using ht
    let q : ℤ := ∑ i, c i * w i
    have hval : functional H b s w ((rootSystem H).root α) = (q : K) := by
      rw [← hform]
      simp only [q, map_sum, map_zsmul, eval_simple, zsmul_eq_mul, Int.cast_sum, Int.cast_mul]
    have hg : χ (rootLatticeElement H α) = 0 :=
      (root_space_le_character_grade_iff H χ α 0).mp (hzero ▸ hα)
    have hm : (q : ZMod 3) = 0 := by
      rw [← hc, map_sum] at hg
      simpa [q, hmod, hB, zsmul_eq_mul] using hg
    obtain ⟨z, hl, hu, hz⟩ := root_values_bounded H b s F hbound hreflect α w hw
    have he : z = q := Int.cast_injective (hz.symm.trans hval)
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd q 3).mp hm
    norm_num at hk
    have hq : q = 0 := by omega
    simpa [hq] using hval
  have hfun : functional H b s w = 0 := by
    rw [hspan] at hkill
    exact LinearMap.ker_eq_top.mp (top_unique hkill)
  apply AddMonoidHom.toIntLinearMap_injective
  apply B.ext
  intro i
  have hi := eval_simple H b s w i
  rw [hfun, LinearMap.zero_apply] at hi
  have hwi : w i = 0 := Int.cast_eq_zero.mp hi.symm
  change χ (B i) = 0
  rw [hB, ← hmod, hwi, Int.cast_zero]

end CubicAnomaly.Classification.RootClassificationBoundedLift
