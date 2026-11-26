import CubicAnomaly.Classification.ChevalleyRecognition
import CubicAnomaly.Classification.ChevalleyGradingTransport
import CubicAnomaly.Classification.ChevalleyRootTransport
import CubicAnomaly.Classification.CompactChevalleyDescent

/-! A complex isomorphism carrying one complexified compact Cartan onto
another can be normalized on its simple-root lines. The new isomorphism
intertwines compact conjugations and has the same image on every grade. -/

namespace CubicAnomaly.Classification.CompactCartanStraightening

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open CompactGeometry Structural RootGrading ToralCharacter
open CompactChevalleyConjugation CompactChevalleyDescent ChevalleyRecognition
open ChevalleySimpleTriples ChevalleyRootGeneration ChevalleyRootTransport
open scoped TensorProduct

private theorem map_triple {K L M : Type*} [Field K] [LieRing L] [LieRing M]
    [LieAlgebra K L] [LieAlgebra K M] (Φ : L ≃ₗ⁅K⁆ M) {h e f : L}
    (ht : IsSl2Triple h e f) : IsSl2Triple (Φ h) (Φ e) (Φ f) where
  h_ne_zero := fun he => ht.h_ne_zero (Φ.injective (he.trans (map_zero Φ).symm))
  lie_e_f := by rw [← Φ.map_lie, ht.lie_e_f]
  lie_h_e_nsmul := by rw [← Φ.map_lie, ht.lie_h_e_nsmul, map_nsmul]
  lie_h_f_nsmul := by rw [← Φ.map_lie, ht.lie_h_f_nsmul, map_neg, map_nsmul]

variable {g k : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  [LieRing k] [LieAlgebra ℝ k] [Module.Finite ℝ k]
  [IsKilling ℂ (ℂ ⊗[ℝ] g)] [IsKilling ℂ (ℂ ⊗[ℝ] k)]
  (A : LieSubalgebra ℝ g) (C : LieSubalgebra ℝ k)
  [(complexifiedSubalgebra A).IsCartanSubalgebra] [(complexifiedSubalgebra C).IsCartanSubalgebra]
  [LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g)] [Nontrivial (complexifiedSubalgebra A)]

/-- Straighten a Cartan-preserving isomorphism to respect the compact forms.
Its image on every homogeneous subspace of every root character is retained. -/
theorem exists_compact_equiv_preserving_grade_images (B : CompactForm g) (D : CompactForm k)
    (Φ : (ℂ ⊗[ℝ] g) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] k))
    (T : complexifiedSubalgebra A ≃ₗ[ℂ] complexifiedSubalgebra C)
    (hT : ∀ h : complexifiedSubalgebra A, Φ h.val = (T h).val)
    (b : (rootSystem (complexifiedSubalgebra A)).Base) :
    ∃ Ψ : (ℂ ⊗[ℝ] g) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] k),
      (∀ x, Ψ (scalarConjugation x) = scalarConjugation (Ψ x)) ∧
      (∀ h : complexifiedSubalgebra A, Ψ h.val = Φ h.val) ∧
      ∀ (χ : rootLattice (complexifiedSubalgebra A) →+ ZMod 3) (n : ZMod 3),
        (rootCharacterGrade (complexifiedSubalgebra A) χ n).map Ψ.toLinearMap =
        (rootCharacterGrade (complexifiedSubalgebra A) χ n).map Φ.toLinearMap := by
  classical
  let H := complexifiedSubalgebra A
  let J := complexifiedSubalgebra C
  choose e f ht he hf hconj using fun i : b.support =>
    exists_compact_normalized_root_triple A B i.val
  choose β hβ hp hn hcor using fun i : b.support =>
    exists_root_transport H J Φ T hT i.val
  choose u v htrip hu hv hconj' using fun i : b.support =>
    exists_compact_normalized_root_triple C D (β i)
  let u₀ (i : b.support) := Φ.symm (u i)
  let v₀ (i : b.support) := Φ.symm (v i)
  have ht' (i : b.support) : IsSl2Triple (coroot i.val.val : ℂ ⊗[ℝ] g) (u₀ i) (v₀ i) := by
    have hx := map_triple Φ.symm (htrip i)
    rwa [← hcor i, LieEquiv.symm_apply_apply] at hx
  have hu₀ (i : b.support) : u₀ i ∈ rootSpace H i.val.val :=
    (hp i _).mp (by simpa only [u₀, LieEquiv.apply_symm_apply] using hu i)
  have hv₀ (i : b.support) : v₀ i ∈ rootSpace H (-(i.val.val : H → ℂ)) :=
    (hn i _).mp (by simpa only [v₀, LieEquiv.apply_symm_apply] using hv i)
  obtain ⟨θ, hθ, hθe, hθf⟩ := exists_lie_equiv_matching_simple_triples H b H b (Equiv.refl _)
    (fun _ _ => rfl) e f u₀ v₀ ht he hf (fun i j hij =>
      lie_simple_opposite_of_ne H b hij (he i) (hf j)) ht' hu₀ hv₀ (fun i j hij =>
        lie_simple_opposite_of_ne H b hij (hu₀ i) (hv₀ j))
  have hfix (h : H) : θ h.val = h.val := by
    simpa only [ChevalleyCartanMatching.cartanEquiv, Basis.equiv_refl,
      LinearEquiv.refl_apply] using hθ h
  let Ψ := θ.trans Φ
  have heq (i : b.support) : Ψ (e i) = u i := by
    change Φ (θ (e i)) = u i
    rw [hθe]; exact Φ.apply_symm_apply _
  have hfq (i : b.support) : Ψ (f i) = v i := by
    change Φ (θ (f i)) = v i
    rw [hθf]; exact Φ.apply_symm_apply _
  refine ⟨Ψ, intertwines_conjugation_of_normalized_generators Ψ e f u v
    (lieSpan_simple_root_vectors_eq_top H b e f he (fun i => (ht i).e_ne_zero) hf
      (fun i => (ht i).f_ne_zero)) hconj hconj' heq hfq,
    fun h => congrArg Φ (hfix h), ?_⟩
  intro χ n
  have heqgrade := ChevalleyGradingTransport.map_character_grade_of_matching H b H b
    (Equiv.refl _) (LinearEquiv.refl ℂ H) (fun _ _ => rfl) θ hfix χ χ (fun _ => rfl) n
  change (rootCharacterGrade H χ n).map (Φ.toLinearMap.comp θ.toLinearMap) = _
  rw [Submodule.map_comp, heqgrade]

end CubicAnomaly.Classification.CompactCartanStraightening
