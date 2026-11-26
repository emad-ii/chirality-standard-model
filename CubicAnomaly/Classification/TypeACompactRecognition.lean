import Mathlib.Algebra.Lie.Weights.IsSimple
import CubicAnomaly.Classification.SpecialLinearCartan
import CubicAnomaly.Classification.SpecialLinearSimplicity
import CubicAnomaly.Classification.SpecialUnitaryNormalizedDescent
import CubicAnomaly.Classification.CompactChevalleyDescent
import CubicAnomaly.Classification.ChevalleyGraphRecognition

/-! The compact simple Lie algebra with simple Cartan matrix Aₙ is isomorphic
over the reals to the traceless skew-adjoint operators on complex (n+1)-space. -/

namespace CubicAnomaly.Classification.TypeACompactRecognition

open LieAlgebra LieModule Module LieAlgebra.IsKilling SpecialLinear
open CompactGeometry Structural SpecialLinearGenerators SpecialLinearCartan
open UnitaryGeometry UnitaryComplexification CompactChevalleyConjugation CompactChevalleyDescent
open ChevalleySimpleTriples ChevalleyRootGeneration
open scoped TensorProduct

variable {n : ℕ} {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [IsKilling ℂ L] [LieAlgebra.IsSimple ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  (b : (rootSystem H).Base) (s : b.support ≃ Fin n)
  (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n)

include hm in
/-- The complex isomorphism realizes any chosen system of simple-root triples
as adjacent matrix units, with the corresponding diagonal Cartan map. -/
theorem exists_matrix_equiv (e f : b.support → L)
    (ht : ∀ i, IsSl2Triple (coroot i.val.val : L) (e i) (f i))
    (he : ∀ i, e i ∈ rootSpace H i.val.val)
    (hf : ∀ i, f i ∈ rootSpace H (-(i.val.val : H → ℂ))) :
    ∃ Φ : L ≃ₗ⁅ℂ⁆ sl (Fin (n+1)) ℂ,
      (∀ h : H, Φ h.val = diagonalHom H b s h) ∧
      (∀ i, Φ (e i) = raising (s i)) ∧ ∀ i, Φ (f i) = lowering (s i) := by
  letI : Nontrivial H := RootPairing.IsIrreducible.nontrivial' (rootSystem H)
  obtain ⟨i₀⟩ := b.toCoweightBasis.index_nonempty
  have hn := (s i₀).isLt
  letI : LieAlgebra.IsSimple ℂ (sl (Fin (n+1)) ℂ) := SpecialLinearSimplicity.isSimple (by
    rw [Fintype.card_fin]; omega)
  let p := diagonalHom H b s
  let J := p.range
  let T : H ≃ₗ⁅ℂ⁆ J := LieEquiv.ofInjective p (diagonalHom_injective H b s hm)
  letI : IsLieAbelian J := (lie_abelian_iff_equiv_lie_abelian T).mp inferInstance
  let height := b.toWeightBasis.constr ℂ (fun _ => (1 : ℂ))
  let t := (Module.evalEquiv ℂ H).symm height
  have hheight (i : b.support) : i.val.val t = 1 := by
    change (rootSystem H).root i ((Module.evalEquiv ℂ H).symm height) = 1
    rw [Module.apply_evalEquiv_symm_apply ℂ H, ← b.toWeightBasis_apply]
    exact b.toWeightBasis.constr_basis ℂ _ i
  refine ChevalleyGraphRecognition.exists_equiv_of_matched_generators H J T.toLinearEquiv e f
    (raising ∘ s) (lowering ∘ s) ?_ ?_ ?_ t ?_ ?_ (fun i => (ht i).e_ne_zero)
    (fun i => (ht i).f_ne_zero) ?_ ?_
  · intro h i
    exact ⟨i.val.val h, lie_eq_smul_of_mem_rootSpace (he i) h, diagonalMap_raising H b s hm h i⟩
  · intro h i
    exact ⟨-i.val.val h, lie_eq_smul_of_mem_rootSpace (hf i) h, diagonalMap_lowering H b s hm h i⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      refine ⟨coroot i.val.val, (ht i).lie_e_f, ?_⟩
      change ⁅raising (s i), lowering (s i)⁆ = diagonalMap H b s (coroot i.val.val)
      rw [mixed_same, ← rootSystem_coroot_apply, ← b.toCoweightBasis_apply i, diagonalMap_basis]
    · refine ⟨0, lie_simple_opposite_of_ne H b hij (he i) (hf j), ?_⟩
      exact (mixed_distinct _ _ (s.injective.ne hij)).trans (congrArg Subtype.val (map_zero T)).symm
  · intro i
    simpa only [hheight, one_smul] using lie_eq_smul_of_mem_rootSpace (he i) t
  · intro i
    simpa only [Pi.neg_apply, hheight, neg_one_smul] using lie_eq_smul_of_mem_rootSpace (hf i) t
  · exact lieSpan_simple_root_vectors_eq_top H b e f he (fun i => (ht i).e_ne_zero) hf
      (fun i => (ht i).f_ne_zero)
  · simpa only [Set.range_comp, s.surjective.range_eq, Set.image_univ] using neighboring_generate (n := n)

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  [IsKilling ℂ (ℂ ⊗[ℝ] g)] [LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g)]

/-- A compact real algebra whose complexification has type Aₙ admits the
standard special-unitary model of dimension (n+1) on its defining space. -/
theorem exists_special_unitary_equiv (B : CompactForm g) (A : LieSubalgebra ℝ g)
    [(complexifiedSubalgebra A).IsCartanSubalgebra]
    (b : (rootSystem (complexifiedSubalgebra A)).Base) (s : b.support ≃ Fin n)
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n) :
    Nonempty (g ≃ₗ⁅ℝ⁆ specialUnitaryAlgebra (EuclideanSpace ℂ (Fin (n+1)))) := by
  classical
  let H := complexifiedSubalgebra A
  choose e f ht he hf hconj using fun i : b.support => exists_compact_normalized_root_triple A B i.val
  obtain ⟨Φ, _, hΦe, hΦf⟩ := exists_matrix_equiv H b s hm e f ht he hf
  let F := specialUnitaryMatrixEquiv (EuclideanSpace.basisFun (Fin (n+1)) ℂ).toBasis
  let Ψ := Φ.trans F.symm
  have hc := intertwines_conjugation_of_normalized_generators Ψ e f
    (fun i => F.symm (raising (s i))) (fun i => F.symm (lowering (s i)))
    (lieSpan_simple_root_vectors_eq_top H b e f he (fun i => (ht i).e_ne_zero) hf
      (fun i => (ht i).f_ne_zero)) hconj
    (fun i => SpecialUnitaryNormalizedDescent.scalar_conjugation_raising (s i))
    (fun i => congrArg F.symm (hΦe i)) (fun i => congrArg F.symm (hΦf i))
  obtain ⟨ψ, _⟩ := exists_real_equiv_of_conjugation Ψ hc
  exact ⟨ψ⟩

end CubicAnomaly.Classification.TypeACompactRecognition
