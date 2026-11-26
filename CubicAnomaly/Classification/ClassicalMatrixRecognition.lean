import CubicAnomaly.Classification.TypeACompactRecognition

/-! Recognition of an explicit matrix realization from its simple relations,
with a dimension bound obtained from the actual simple root system. -/
namespace CubicAnomaly.Classification.ClassicalMatrixRecognition

open LieAlgebra LieModule Module LieAlgebra.IsKilling ChevalleySimpleTriples ChevalleyRootGeneration

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  [LieAlgebra.IsSimple ℂ L] [LieRing M] [LieAlgebra ℂ M] [FiniteDimensional ℂ M]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

/-- An injective Cartan map and model simple triples recognize the algebra
using only explicit generator brackets, root values and a dimension bound. -/
theorem classical_exists_matrix_equiv (p : H →ₗ⁅ℂ⁆ M) (hp : Function.Injective p) (E F : b.support → M)
    (hE : ∀ h i, ⁅p h,E i⁆ = i.val.val h • E i)
    (hF : ∀ h i, ⁅p h,F i⁆ = -i.val.val h • F i)
    (hEF : ∀ i, ⁅E i,F i⁆ = p (coroot i.val.val)) (hc : ∀ i j, i ≠ j → ⁅E i,F j⁆ = 0)
    (hdim : finrank ℂ M ≤ finrank ℂ L)
    (e f : b.support → L) (ht : ∀ i, IsSl2Triple (coroot i.val.val : L) (e i) (f i))
    (he : ∀ i, e i ∈ rootSpace H i.val.val)
    (hf : ∀ i, f i ∈ rootSpace H (-(i.val.val : H → ℂ))) :
    ∃ Φ : L ≃ₗ⁅ℂ⁆ M, (∀ h : H, Φ h.val = p h) ∧ (∀ i, Φ (e i) = E i) ∧ ∀ i, Φ (f i) = F i := by
  letI : Nontrivial H := RootPairing.IsIrreducible.nontrivial' (rootSystem H)
  let J := p.range
  let T : H ≃ₗ⁅ℂ⁆ J := LieEquiv.ofInjective p hp
  letI : IsLieAbelian J := (lie_abelian_iff_equiv_lie_abelian T).mp inferInstance
  let height := b.toWeightBasis.constr ℂ (fun _ => (1 : ℂ))
  let t := (Module.evalEquiv ℂ H).symm height
  have hheight (i : b.support) : i.val.val t = 1 := by
    change (rootSystem H).root i ((Module.evalEquiv ℂ H).symm height) = 1
    rw [Module.apply_evalEquiv_symm_apply ℂ H, ← b.toWeightBasis_apply]
    exact b.toWeightBasis.constr_basis ℂ _ i
  refine ChevalleyGraphRecognition.exists_equiv_of_matched_generators_of_finrank_le H J T.toLinearEquiv e f
    E F (fun h i => ⟨_, lie_eq_smul_of_mem_rootSpace (he i) h, hE h i⟩)
    (fun h i => ⟨_, lie_eq_smul_of_mem_rootSpace (hf i) h, hF h i⟩) ?_ t ?_ ?_ (fun i => (ht i).e_ne_zero)
    (fun i => (ht i).f_ne_zero) ?_ hdim
  · intro i j
    by_cases hij : i = j
    · subst j; exact ⟨_, (ht i).lie_e_f, hEF i⟩
    · exact ⟨0, lie_simple_opposite_of_ne H b hij (he i) (hf j),
        (hc i j hij).trans (congrArg Subtype.val (map_zero T)).symm⟩
  · intro i
    simpa only [hheight, one_smul] using lie_eq_smul_of_mem_rootSpace (he i) t
  · intro i
    simpa only [Pi.neg_apply, hheight, neg_one_smul] using lie_eq_smul_of_mem_rootSpace (hf i) t
  · exact lieSpan_simple_root_vectors_eq_top H b e f he (fun i => (ht i).e_ne_zero) hf
      (fun i => (ht i).f_ne_zero)

open CompactGeometry Structural CompactChevalleyConjugation CompactChevalleyDescent
open scoped TensorProduct

/-- A matrix realization respecting the compact adjoints of the selected
raising operators descends to a real Lie equivalence. -/
theorem exists_compact_equiv {g k M : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
    [LieRing k] [LieAlgebra ℝ k] [LieRing M] [LieAlgebra ℂ M] [IsKilling ℂ (ℂ ⊗[ℝ] g)]
    (B : CompactForm g) (A : LieSubalgebra ℝ g) [(complexifiedSubalgebra A).IsCartanSubalgebra]
    (b : (rootSystem (complexifiedSubalgebra A)).Base) (F : (ℂ ⊗[ℝ] k) ≃ₗ⁅ℂ⁆ M)
    (u v : b.support → M)
    (hF : ∀ i, scalarConjugation (F.symm (u i)) = -F.symm (v i))
    (hmodel : ∀ (e f : b.support → ℂ ⊗[ℝ] g),
      (∀ i, IsSl2Triple (coroot i.val.val : ℂ ⊗[ℝ] g) (e i) (f i)) →
      (∀ i, e i ∈ rootSpace (complexifiedSubalgebra A) i.val.val) →
      (∀ i, f i ∈ rootSpace (complexifiedSubalgebra A) (-(i.val.val : complexifiedSubalgebra A → ℂ))) →
      ∃ Φ : (ℂ ⊗[ℝ] g) ≃ₗ⁅ℂ⁆ M, (∀ i, Φ (e i) = u i) ∧ ∀ i, Φ (f i) = v i) :
    Nonempty (g ≃ₗ⁅ℝ⁆ k) := by
  classical
  choose e f ht he hf hconj using fun i : b.support => exists_compact_normalized_root_triple A B i.val
  obtain ⟨Φ,hΦe,hΦf⟩ := hmodel e f ht he hf
  let Ψ := Φ.trans F.symm
  have hc := intertwines_conjugation_of_normalized_generators Ψ e f
    (fun i => F.symm (u i)) (fun i => F.symm (v i))
    (lieSpan_simple_root_vectors_eq_top _ b e f he (fun i => (ht i).e_ne_zero) hf
      (fun i => (ht i).f_ne_zero)) hconj hF (fun i => congrArg F.symm (hΦe i)) (fun i => congrArg F.symm (hΦf i))
  obtain ⟨ψ,_⟩ := exists_real_equiv_of_conjugation Ψ hc
  exact ⟨ψ⟩

end CubicAnomaly.Classification.ClassicalMatrixRecognition
