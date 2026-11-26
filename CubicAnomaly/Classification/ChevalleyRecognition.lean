import CubicAnomaly.Classification.ChevalleyCartanMatching
import CubicAnomaly.Classification.ChevalleySimpleTriples
import CubicAnomaly.Classification.ChevalleyGraphRecognition

/-! A matching Cartan matrix recognizes the split simple Lie algebra.
Any two systems of normalized simple-root triples can be prescribed. -/

namespace CubicAnomaly.Classification.ChevalleyRecognition

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ChevalleyCartanMatching ChevalleySimpleTriples ChevalleyRootGeneration

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L] (H : LieSubalgebra K L)
  [H.IsCartanSubalgebra] [IsTriangularizable K H L] (b : (rootSystem H).Base)
  [LieRing M] [LieAlgebra K M] [FiniteDimensional K M] [LieAlgebra.IsKilling K M]
  (J : LieSubalgebra K M) [J.IsCartanSubalgebra] [IsTriangularizable K J M]
  (d : (rootSystem J).Base) (s : b.support ≃ d.support)
  [LieAlgebra.IsSimple K L] [LieAlgebra.IsSimple K M] [Nontrivial H]

omit [LieAlgebra.IsSimple K L] [Nontrivial H] in
private theorem exists_simple_height_one :
    ∃ t : H, ∀ i : b.support, i.val.val t = 1 := by
  let F := b.toWeightBasis.constr K (fun _ => (1 : K))
  refine ⟨(Module.evalEquiv K H).symm F, fun i => ?_⟩
  change (rootSystem H).root i ((Module.evalEquiv K H).symm F) = 1
  rw [Module.apply_evalEquiv_symm_apply K H, ← b.toWeightBasis_apply]
  exact b.toWeightBasis.constr_basis K _ i

/-- The Lie equivalence matches all prescribed raising and lowering operators
and restricts to the linear equivalence defined by the coroot bases. -/
theorem exists_lie_equiv_matching_simple_triples
    (hm : ∀ i j, b.cartanMatrix i j = d.cartanMatrix (s i) (s j))
    (e f : b.support → L) (u v : d.support → M)
    (ht : ∀ i, IsSl2Triple (coroot i.val.val : L) (e i) (f i))
    (he : ∀ i, e i ∈ rootSpace H i.val.val)
    (hf : ∀ i, f i ∈ rootSpace H (-(i.val.val : H → K)))
    (hcross : ∀ i j, i ≠ j → ⁅e i, f j⁆ = 0)
    (huv : ∀ i, IsSl2Triple (coroot i.val.val : M) (u i) (v i))
    (hu : ∀ i, u i ∈ rootSpace J i.val.val)
    (hv : ∀ i, v i ∈ rootSpace J (-(i.val.val : J → K)))
    (hcross' : ∀ i j, i ≠ j → ⁅u i, v j⁆ = 0) :
    ∃ Φ : L ≃ₗ⁅K⁆ M, (∀ h : H, Φ h.val = (cartanEquiv H b J d s h).val) ∧
      (∀ i, Φ (e i) = u (s i)) ∧ ∀ i, Φ (f i) = v (s i) := by
  let T := cartanEquiv H b J d s
  have hmatch (i : b.support) (h : H) := matched_simple_root_value H b J d s hm i h
  obtain ⟨t, hheight⟩ := exists_simple_height_one H b
  refine ChevalleyGraphRecognition.exists_equiv_of_matched_generators H J T e f
    (u ∘ s) (v ∘ s) ?_ ?_ ?_ t ?_ ?_ ?_ ?_ ?_ ?_
  · intro h i
    exact ⟨i.val.val h, lie_eq_smul_of_mem_rootSpace (he i) h,
      (lie_eq_smul_of_mem_rootSpace (hu (s i)) (T h)).trans (congrArg (· • u (s i)) (hmatch i h))⟩
  · intro h i
    exact ⟨-i.val.val h, lie_eq_smul_of_mem_rootSpace (hf i) h,
      (lie_eq_smul_of_mem_rootSpace (hv (s i)) (T h)).trans
        (congrArg (fun a : K => (-a) • v (s i)) (hmatch i h))⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      exact ⟨coroot i.val.val, (ht i).lie_e_f, (huv (s i)).lie_e_f.trans
        (congrArg Subtype.val (matched_simple_coroot H b J d s i)).symm⟩
    · exact ⟨0, hcross i j hij, (hcross' _ _ (s.injective.ne hij)).trans
        (congrArg Subtype.val T.map_zero).symm⟩
  · intro i
    simpa only [hheight, one_smul] using lie_eq_smul_of_mem_rootSpace (he i) t
  · intro i
    simpa only [Pi.neg_apply, hheight, neg_one_smul] using lie_eq_smul_of_mem_rootSpace (hf i) t
  · exact fun i => (ht i).e_ne_zero
  · exact fun i => (ht i).f_ne_zero
  · exact lieSpan_simple_root_vectors_eq_top H b e f he (fun i => (ht i).e_ne_zero) hf
      (fun i => (ht i).f_ne_zero)
  · simpa only [Set.range_comp, s.surjective.range_eq, Set.image_univ] using
      lieSpan_simple_root_vectors_eq_top J d u v hu (fun i => (huv i).e_ne_zero) hv
        (fun i => (huv i).f_ne_zero)

/-- Two finite-dimensional simple Killing Lie algebras with splitting
Cartans and the same reindexed simple Cartan matrix are Lie-isomorphic.
The equivalence sends every simple coroot to its specified partner. -/
theorem lie_equiv_of_matching_cartan_matrix
    (hm : ∀ i j, b.cartanMatrix i j = d.cartanMatrix (s i) (s j)) :
    ∃ Φ : L ≃ₗ⁅K⁆ M, ∀ h : H, Φ h.val = (cartanEquiv H b J d s h).val := by
  obtain ⟨e, f, ht, he, hf, hc, _⟩ := exists_simple_root_triples H b
  obtain ⟨u, v, ht', hu, hv, hc', _⟩ := exists_simple_root_triples J d
  obtain ⟨Φ, hΦ, _⟩ := exists_lie_equiv_matching_simple_triples H b J d s hm
    e f u v ht he hf hc ht' hu hv hc'
  exact ⟨Φ, hΦ⟩

end CubicAnomaly.Classification.ChevalleyRecognition
