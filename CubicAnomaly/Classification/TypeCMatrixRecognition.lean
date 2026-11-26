import CubicAnomaly.Classification.TypeCCartanCoordinates
import CubicAnomaly.Classification.TypeACompactRecognition

/-! Realize compact type-C simple-root triples as standard Hamiltonian matrices. -/

namespace CubicAnomaly.Classification.TypeCMatrixRecognition

open LieAlgebra LieAlgebra.IsKilling LieModule Module SymplecticMatrixGenerators TypeCCartanCoordinates
open ChevalleySimpleTriples ChevalleyRootGeneration

variable {n : ℕ} {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  (s : b.support ≃ Fin (n+1)) (hm : b.cartanMatrix.reindex s s = CartanMatrix.C (n+1))

/-- The actual Cartan mapped to the standard diagonal symplectic matrices. -/
noncomputable def cartanHom : H →ₗ⁅ℂ⁆ Symplectic.sp (Fin (n+1)) ℂ where
  toLinearMap := generalLinear.toLinearMap.comp
    ((Matrix.diagonalLinearMap (Fin (n+1)) ℂ ℂ).comp (coordinates H b s).toLinearMap)
  map_lie' {x y} := by
    change generalLinear (Matrix.diagonal (coordinates H b s ⁅x,y⁆)) =
      ⁅generalLinear (Matrix.diagonal (coordinates H b s x)), generalLinear (Matrix.diagonal (coordinates H b s y))⁆
    rw [trivial_lie_zero, map_zero, ← LieHom.map_lie]
    congr 1
    simp [Ring.lie_def, Matrix.diagonal_mul_diagonal, mul_comm]

theorem cartanHom_injective : Function.Injective (cartanHom H b s) := by
  intro x y h
  apply (coordinates H b s).injective
  ext i
  have h' := congrArg (fun A : Symplectic.sp (Fin (n+1)) ℂ => A.val (.inl i) (.inl i)) h
  change Matrix.diagonal (coordinates H b s x) i i = Matrix.diagonal (coordinates H b s y) i i at h'
  simpa using h'

set_option maxHeartbeats 1200000 in
include hm in
/-- Matching the standard simple symplectic matrices uses only an upper
bound on the dimension of the matrix space. -/
theorem exists_matrix_equiv_of_dim [LieAlgebra.IsSimple ℂ L]
    (hdim : finrank ℂ (Symplectic.sp (Fin (n+1)) ℂ) ≤ finrank ℂ L)
    (e f : b.support → L) (ht : ∀ i, IsSl2Triple (coroot i.val.val : L) (e i) (f i))
    (he : ∀ i, e i ∈ rootSpace H i.val.val)
    (hf : ∀ i, f i ∈ rootSpace H (-(i.val.val : H → ℂ))) :
    ∃ Φ : L ≃ₗ⁅ℂ⁆ Symplectic.sp (Fin (n+1)) ℂ,
      (∀ h : H, Φ h.val = cartanHom H b s h) ∧
      (∀ i, Φ (e i) = raising (s i)) ∧ ∀ i, Φ (f i) = lowering (s i) := by
  letI : Nontrivial H := RootPairing.IsIrreducible.nontrivial' (rootSystem H)
  let p := cartanHom H b s
  let J := p.range
  let T : H ≃ₗ⁅ℂ⁆ J := LieEquiv.ofInjective p (cartanHom_injective H b s)
  letI : IsLieAbelian J := (lie_abelian_iff_equiv_lie_abelian T).mp inferInstance
  let height := b.toWeightBasis.constr ℂ (fun _ => (1 : ℂ))
  let t := (Module.evalEquiv ℂ H).symm height
  have hheight (i : b.support) : i.val.val t = 1 := by
    change (rootSystem H).root i ((Module.evalEquiv ℂ H).symm height) = 1
    rw [Module.apply_evalEquiv_symm_apply ℂ H, ← b.toWeightBasis_apply]
    exact b.toWeightBasis.constr_basis ℂ _ i
  have hwt (i : b.support) (h : H) : weight (s i) (coordinates H b s h) = i.val.val h := by
    simpa only [s.symm_apply_apply] using weight_coordinates H b s h (s i)
  refine ChevalleyGraphRecognition.exists_equiv_of_matched_generators_of_finrank_le H J T.toLinearEquiv e f
    (raising ∘ s) (lowering ∘ s) ?_ ?_ ?_ t ?_ ?_ (fun i => (ht i).e_ne_zero)
    (fun i => (ht i).f_ne_zero) ?_ hdim
  · intro h i
    refine ⟨i.val.val h, lie_eq_smul_of_mem_rootSpace (he i) h, ?_⟩
    exact (symplectic_diagonal_raising _ (s i)).trans (congrArg (· • raising (s i)) (hwt i h))
  · intro h i
    refine ⟨-i.val.val h, lie_eq_smul_of_mem_rootSpace (hf i) h, ?_⟩
    exact (symplectic_diagonal_lowering _ (s i)).trans (congrArg (fun c : ℂ => -c • lowering (s i)) (hwt i h))
  · intro i j
    by_cases hij : i = j
    · subst j
      refine ⟨coroot i.val.val, (ht i).lie_e_f, ?_⟩
      have hc := coordinates_coroot H b s hm (s i)
      rw [s.symm_apply_apply] at hc
      change ⁅raising (s i), lowering (s i)⁆ = generalLinear (Matrix.diagonal (coordinates H b s (coroot i.val.val)))
      rw [symplectic_mixed_same, diagonal_eq, hc]
    · refine ⟨0, lie_simple_opposite_of_ne H b hij (he i) (hf j), ?_⟩
      exact (symplectic_mixed_distinct _ _ (s.injective.ne hij)).trans (congrArg Subtype.val (map_zero T)).symm
  · intro i
    simpa only [hheight, one_smul] using lie_eq_smul_of_mem_rootSpace (he i) t
  · intro i
    simpa only [Pi.neg_apply, hheight, neg_one_smul] using lie_eq_smul_of_mem_rootSpace (hf i) t
  · exact lieSpan_simple_root_vectors_eq_top H b e f he (fun i => (ht i).e_ne_zero) hf
      (fun i => (ht i).f_ne_zero)

end CubicAnomaly.Classification.TypeCMatrixRecognition
