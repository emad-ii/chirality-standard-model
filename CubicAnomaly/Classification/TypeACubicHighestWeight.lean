import CubicAnomaly.Classification.TypeACubicOperator
import CubicAnomaly.Classification.TypeAMatrixUnits
import CubicAnomaly.Classification.ClassicalConstituentOrthogonal

/-! # The actual compact constituents and the type-A cubic criterion -/

namespace CubicAnomaly.Classification.TypeACubicHighestWeight

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentHighest
open TypeAMatrixUnits TypeACubicOperator TypeACubicArithmetic SpecialLinearGenerators
open SpecialLinearCartan ChevalleySimpleTriples TypeACompactRecognition

noncomputable section

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  [IsSimple ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  {n : ℕ} (s : b.support ≃ Fin n) (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n)
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]

/-- Zero-sum diagonal coordinates are uniquely determined by simple coroot
evaluations, which are the consecutive differences. -/
theorem coords_unique {p q : Fin (n+1) → ℂ} (hp : ∑ i, p i = 0) (hq : ∑ i, q i = 0)
    (he : ∀ i : Fin n, p i.castSucc - p i.succ = q i.castSucc - q i.succ) : p = q := by
  have hconst (i : Fin (n+1)) : p i - q i = p 0 - q 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih => linear_combination ih - he j
  have h' := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hconst i)
  rw [Finset.sum_sub_distrib, hp, hq, sub_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h'
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hz := (mul_eq_zero.mp h'.symm).resolve_left hn
  exact funext fun i => sub_eq_zero.mp ((hconst i).trans hz)

include hm in
/-- Converting an actual highest vector into traceless matrix-unit
coordinates preserves the given simple Dynkin labels and the sum-zero condition. -/
theorem highest_matrix_coordinates (μ : H → ℂ) (v : M) (hv : IsHighestVector H b μ v) :
    ∃ (Φ : L ≃ₗ⁅ℂ⁆ SpecialLinear.sl (Fin (n+1)) ℂ) (u : Fin (n+1) → ℂ),
      (∑ i, u i = 0) ∧ (∀ i : b.support, u (s i).castSucc - u (s i).succ = μ (coroot i.val.val)) ∧
      (∀ i, ⁅family Φ i i,v⁆ = u i • v) ∧ ∀ i j, i < j → ⁅family Φ i j,v⁆ = 0 := by
  obtain ⟨e, f, ht, he, hf, _, _⟩ := exists_simple_root_triples H b
  obtain ⟨Φ, hH, hE, -⟩ := exists_matrix_equiv H b s hm e f ht he hf
  have hdiag (i : b.support) : Φ.symm (diagonal (s i)) = ((coroot i.val.val : H) : L) := by
    apply Φ.injective
    change Φ (Φ.symm (diagonal (s i))) = Φ ((coroot i.val.val : H) : L)
    rw [Φ.apply_symm_apply, hH]
    change _ = diagonalMap H b s (coroot i.val.val)
    rw [← rootSystem_coroot_apply, ← b.toCoweightBasis_apply i, diagonalMap_basis]
  obtain ⟨u, hu⟩ := diagonal_eigenvalues Φ v (fun i => by
    obtain ⟨j,rfl⟩ := s.surjective i
    exact ⟨μ (coroot j.val.val), hdiag j ▸ hv.2.1 _⟩)
  refine ⟨Φ, u, ?_, ?_, hu, upper_kills Φ v ?_⟩
  · apply smul_left_injective ℂ hv.1
    change (∑ i, u i) • v = (0 : ℂ) • v
    rw [Finset.sum_smul, zero_smul]
    calc
      _ = ∑ i, ⁅family Φ i i, v⁆ := Finset.sum_congr rfl fun i _ => (hu i).symm
      _ = 0 := by rw [← sum_lie, sum_diagonal, zero_lie]
  · intro i
    apply smul_left_injective ℂ hv.1
    change (u (s i).castSucc - u (s i).succ) • v = μ (coroot i.val.val) • v
    rw [sub_smul, ← hu, ← hu, ← sub_lie, ← hv.2.1]
    change ⁅_,v⁆ = ⁅((coroot i.val.val : H) : L),v⁆
    rw [← hdiag i]
    change ⁅Φ.symm (unit (s i).castSucc (s i).castSucc) - Φ.symm (unit (s i).succ (s i).succ),v⁆ = _
    rw [← map_sub, adjacent_difference]
  · intro i
    obtain ⟨j, rfl⟩ := s.surjective i
    rw [← hE j, Φ.symm_apply_apply]
    exact hv.2.2 j.val (b.isPos_of_mem_support j.property) (e j) (he j)

private def symTrace {R : Type*} [LieRing R] [LieAlgebra ℂ R]
    (U : Type*) [AddCommGroup U] [Module ℂ U] [LieRingModule R U] [LieModule ℂ R U] (a b c : R) : ℂ :=
  LinearMap.trace ℂ U ((toEnd ℂ R U a * toEnd ℂ R U b + toEnd ℂ R U b * toEnd ℂ R U a) * toEnd ℂ R U c)

include hm in
private theorem highest_eq_of_trace_zero [FiniteDimensional ℂ M] [IsIrreducible ℂ L M]
    (μ : H → ℂ) (v : M) (hv : IsHighestVector H b μ v) (u : Fin (n+1) → ℂ)
    (hz : ∑ i, u i = 0) (hu : ∀ i : b.support, u (s i).castSucc - u (s i).succ = μ (coroot i.val.val))
    (htr : ∀ a b c : L, symTrace M a b c = 0) :
    gelfandEigenvalue u = gelfandEigenvalue (fun i => -u i.rev) := by
  obtain ⟨Φ,w,hs,hd,hw,hp⟩ := highest_matrix_coordinates H b s hm μ v hv
  have he := coords_unique hz hs fun i => by
    obtain ⟨j,rfl⟩ := s.surjective i
    exact (hu j).trans (hd j).symm
  subst w
  exact highest_eigenvalue_eq_of_zero_cubic (family Φ) (family_bracket Φ) (family_span Φ)
    u v hv.1 hw hp htr

section Traces

variable {R U V : Type*} [LieRing R] [LieAlgebra ℂ R]
    [AddCommGroup U] [Module ℂ U] [LieRingModule R U] [LieModule ℂ R U]
    [AddCommGroup V] [Module ℂ V] [LieRingModule R V] [LieModule ℂ R V]

private theorem equiv_trace (f : U ≃ₗ⁅ℂ,R⁆ V) (a b c : R) :
    symTrace V a b c = symTrace U a b c := by
  have he (x : R) : toEnd ℂ R V x = f.toLinearEquiv.conj (toEnd ℂ R U x) := by
    apply LinearMap.ext
    intro z
    change ⁅x,z⁆ = f ⁅x,f.symm z⁆
    have hh := f.map_lie x (f.symm z)
    change f ⁅x,f.symm z⁆ = ⁅x,f (f.symm z)⁆ at hh
    rw [f.apply_symm_apply] at hh
    exact hh.symm
  simp only [symTrace, he, Module.End.mul_eq_comp, ← LinearEquiv.conj_comp, ← map_add,
    LinearMap.trace_conj']

private theorem dual_trace [FiniteDimensional ℂ U] (a b c : R) :
    symTrace (Dual ℂ U) a b c = -symTrace U a b c := by
  have h (x y z : R) : toEnd ℂ R (Dual ℂ U) x * toEnd ℂ R (Dual ℂ U) y * toEnd ℂ R (Dual ℂ U) z =
      -Module.Dual.transpose (toEnd ℂ R U z * toEnd ℂ R U y * toEnd ℂ R U x) := by
    ext f m
    change -(-(-f ⁅z,⁅y,⁅x,m⁆⁆⁆)) = -f ⁅z,⁅y,⁅x,m⁆⁆⁆
    simp
  simp only [symTrace, add_mul, map_add, h, map_neg, LinearMap.trace_transpose']
  rw [← LinearMap.trace_mul_cycle ℂ (toEnd ℂ R U b) (toEnd ℂ R U a) (toEnd ℂ R U c),
      ← LinearMap.trace_mul_cycle ℂ (toEnd ℂ R U a) (toEnd ℂ R U b) (toEnd ℂ R U c)]
  abel

end Traces

open scoped TensorProduct
open Structural HermitianRealization Complexification ComplexDuality AnomalyComplexification
open CartanTrace MatrixCubic CanonicalHalf CubicRadical CompactOperatorModel SelfDualAbsorption
open ClassicalConstituentWeights ClassicalConstituentCompact

variable {g W : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)] [IsSimple ℂ (ℂ ⊗[ℝ] h)]

include hr in
omit [IsKilling ℂ (ℂ ⊗[ℝ] h)] in
private theorem positive_trace_zero (a b c : ℂ ⊗[ℝ] h) :
    let P := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    symTrace P a b c = 0 := by
  let ρ := complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
  have hR : complexTraceRadical ρ ≠ ⊥ := (hermitian_complex_radical_ne_bot_iff _).mpr hr
  have ht := (IsSimple.eq_bot_or_eq_top (complexTraceRadical ρ)).resolve_left hR
  have hc : c ∈ complexTraceRadical ρ := ht ▸ LieSubmodule.mem_top _
  have he := (mem_radical_iff _ _ c).mp hc a b
  change matrixTraceCubic (ρ c) (ρ a) (ρ b) = 0 at he
  rw [matrix_trace_cubic_of_intertwining (canonicalPositiveHalfEquiv B h e) _
    (canonicalPositiveHalfEquiv_intertwines B h e), LinearMap.trace_mul_comm] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

include hp hr in
/-- For a compact form-preserving model with simple type-A isotropy,
every actual skew highest weight satisfies the shifted cubic constraint. -/
theorem skew_highest_eigenvalue_eq
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    (s : b.support ≃ Fin n) (hm : b.cartanMatrix.reindex s s = CartanMatrix.A n)
    [AddCommGroup W] [Module ℂ W] [LieRingModule (ℂ ⊗[ℝ] h) W] [LieModule ℂ (ℂ ⊗[ℝ] h) W]
    [FiniteDimensional ℂ W] (β : LinearMap.BilinForm ℂ W) (A : Model h β)
    (μ : H → ℂ) (hμ : HasSkewHighestWeight H b β μ) (u : Fin (n+1) → ℂ)
    (hz : ∑ i, u i = 0)
    (hu : ∀ i : b.support, u (s i).castSucc - u (s i).succ = μ (coroot i.val.val)) :
    gelfandEigenvalue u = gelfandEigenvalue (fun i => -u i.rev) := by
  let P := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let Q := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I)
  obtain ⟨_,hP,hQ,⟨d⟩,-⟩ := compact_complement_complex_type_decomposition B h hp e
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) P := hP
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) Q := hQ
  obtain ⟨θ,p,q,⟨z,hz'⟩,⟨v,hv⟩,⟨w,hw⟩,hall⟩ := compact_model_highest_weights B h hp e H b A
  rcases hall μ hμ with rfl | rfl | rfl
  · apply highest_eq_of_trace_zero H b s hm _ z hz' u hz hu
    intro a b c
    obtain ⟨k⟩ := invariant_nondegenerate_form_self_dual (killingForm ℂ (ℂ ⊗[ℝ] h))
      (traceForm_lieInvariant ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] h)) (IsKilling.killingForm_nondegenerate ℂ (ℂ ⊗[ℝ] h))
    have he := equiv_trace k a b c
    rw [dual_trace] at he
    linear_combination -he / 2
  · exact highest_eq_of_trace_zero H b s hm _ v hv u hz hu (positive_trace_zero B h e hr)
  · apply highest_eq_of_trace_zero H b s hm _ w hw u hz hu
    intro a b c
    rw [← equiv_trace d, dual_trace]
    simp only [positive_trace_zero B h e hr, neg_zero]

end
end CubicAnomaly.Classification.TypeACubicHighestWeight
