import CubicAnomaly.Classification.Complexification

/-! # Invariant complex halves of a real Lie module -/

namespace CubicAnomaly.Classification.Complexification

open scoped TensorProduct

section ComplexStructure

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]

/-- Scalar extension of an equivariant real endomorphism, with its actual
equivariance for the complexified Lie algebra. -/
noncomputable def complexifiedEnd (J : M →ₗ⁅ℝ,L⁆ M) :
    (ℂ ⊗[ℝ] M) →ₗ⁅ℂ,ℂ ⊗[ℝ] L⁆ (ℂ ⊗[ℝ] M) := {
  J.toLinearMap.baseChange ℂ with
  map_lie' := by
    intro x m
    change (J.toLinearMap.baseChange ℂ)
        ((LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) x) m) =
      (LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) x)
        ((J.toLinearMap.baseChange ℂ) m)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      induction m using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b m => simp [LieModule.toEnd_apply_apply, J.map_lie]
      | add m n hm hn => simp only [map_add, hm, hn]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy] }

/-- A real complex structure still squares to minus the identity after
complexification. -/
theorem complexifiedEnd_square (J : M →ₗ⁅ℝ,L⁆ M) (hJ : ∀ m, J (J m) = -m)
    (z : ℂ ⊗[ℝ] M) : complexifiedEnd J (complexifiedEnd J z) = -z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    change a ⊗ₜ[ℝ] J (J m) = -(a ⊗ₜ[ℝ] m)
    simp only [hJ, TensorProduct.tmul_neg]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

end ComplexStructure

section EigenspaceSplitting

variable {L V : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

/-- Eigenspaces of equivariant maps are Lie submodules. -/
def invariantEigenspace (J : V →ₗ⁅ℂ,L⁆ V) (a : ℂ) : LieSubmodule ℂ L V :=
  (J - a • LieModuleHom.id).ker

private theorem mem_invariantEigenspace (J : V →ₗ⁅ℂ,L⁆ V) (a : ℂ) (v : V) :
    v ∈ invariantEigenspace J a ↔ J v = a • v := by
  change J v - a • v = 0 ↔ _
  exact sub_eq_zero

/-- A complex structure on a complex Lie module splits the whole module
as the direct sum of its `+I` and `-I` eigenspaces.  No dimension bound or
diagonalizability hypothesis is needed. -/
theorem complex_structure_eigenspaces_isCompl (J : V →ₗ⁅ℂ,L⁆ V)
    (hJ : ∀ v, J (J v) = -v) :
    IsCompl (invariantEigenspace J Complex.I) (invariantEigenspace J (-Complex.I)) := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor
  · apply le_antisymm
    · intro v hv
      have hp := (mem_invariantEigenspace J Complex.I v).mp hv.1
      have hn := (mem_invariantEigenspace J (-Complex.I) v).mp hv.2
      have hzero : ((2 : ℂ) * Complex.I) • v = 0 := by
        calc
          ((2 : ℂ) * Complex.I) • v = Complex.I • v - (-Complex.I) • v := by module
          _ = 0 := by rw [← hp, ← hn, sub_self]
      exact (smul_eq_zero.mp hzero).resolve_left
        (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    · exact bot_le
  · apply eq_top_iff.mpr
    intro v _
    let vp : V := (2 : ℂ)⁻¹ • (v - Complex.I • J v)
    let vn : V := (2 : ℂ)⁻¹ • (v + Complex.I • J v)
    have hp : vp ∈ invariantEigenspace J Complex.I := by
      rw [mem_invariantEigenspace]
      dsimp [vp]
      simp only [map_smul, map_sub, hJ]
      match_scalars
      all_goals ring_nf
      all_goals norm_num [Complex.I_sq]
    have hn : vn ∈ invariantEigenspace J (-Complex.I) := by
      rw [mem_invariantEigenspace]
      dsimp [vn]
      simp only [map_smul, map_add, hJ]
      match_scalars
      all_goals ring_nf
      all_goals norm_num [Complex.I_sq]
    apply (LieSubmodule.mem_sup _ _ v).mpr
    refine ⟨vp, hp, vn, hn, ?_⟩
    dsimp [vp, vn]
    module

end EigenspaceSplitting

section RealSplitting

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]

/-- The actual complexification of a real module with an invariant complex
structure is the direct sum of two invariant complex eigenspaces. -/
theorem complexified_complex_structure_isCompl (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) :
    IsCompl (invariantEigenspace (complexifiedEnd J) Complex.I)
      (invariantEigenspace (complexifiedEnd J) (-Complex.I)) :=
  complex_structure_eigenspaces_isCompl (complexifiedEnd J) (complexifiedEnd_square J hJ)

end RealSplitting

section IrreducibilityTransport

variable {L M K V : Type*} [LieRing L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M]
  [LieRing K]
  [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  [LieRingModule K V]

/-- A real-linear equivariant bijection transfers real irreducibility
to a complex module for any larger acting algebra. -/
theorem complex_irreducible_of_real_equivariant_bijection
    [LieModule.IsIrreducible ℝ L M]
    (i : L → K) (f : M →ₗ[ℝ] V) (hf : Function.Bijective f)
    (hact : ∀ x m, f ⁅x, m⁆ = ⁅i x, f m⁆) :
    LieModule.IsIrreducible ℂ K V := by
  letI : Nontrivial M := LieModule.nontrivial_of_isIrreducible ℝ L M
  letI : Nontrivial V := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    refine ⟨⟨f m, 0, ?_⟩⟩
    intro h
    apply hm
    apply hf.1
    simpa using h
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  let N : LieSubmodule ℝ L M := {
    (W.toSubmodule.restrictScalars ℝ).comap f with
    lie_mem := by
      intro x m hm
      change f ⁅x, m⁆ ∈ W
      rw [hact]
      exact W.lie_mem hm }
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · left
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨m, rfl⟩ := hf.2 v
    have hm : m ∈ N := hv
    rw [hN, LieSubmodule.mem_bot] at hm
    simp [hm]
  · right
    apply top_unique
    intro v _
    obtain ⟨m, rfl⟩ := hf.2 v
    have hm : m ∈ N := by rw [hN]; trivial
    exact hm

end IrreducibilityTransport

section PositiveHalf

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]

private noncomputable def positiveVector (J : M →ₗ⁅ℝ,L⁆ M) :
    M →ₗ[ℝ] (ℂ ⊗[ℝ] M) :=
  TensorProduct.mk ℝ ℂ M 1 -
    (TensorProduct.mk ℝ ℂ M Complex.I).comp J.toLinearMap

private theorem positiveVector_mem (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) (m : M) :
    positiveVector J m ∈ invariantEigenspace (complexifiedEnd J) Complex.I := by
  rw [mem_invariantEigenspace]
  change (J.toLinearMap.baseChange ℂ) (1 ⊗ₜ[ℝ] m - Complex.I ⊗ₜ[ℝ] J m) =
    Complex.I • (1 ⊗ₜ[ℝ] m - Complex.I ⊗ₜ[ℝ] J m)
  simp only [map_sub, LinearMap.baseChange_tmul, LieModuleHom.coe_toLinearMap, hJ, smul_sub,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, Complex.I_mul_I,
    TensorProduct.tmul_neg, TensorProduct.neg_tmul, sub_neg_eq_add]
  abel

private noncomputable def positiveEmbedding (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) :
    M →ₗ[ℝ] invariantEigenspace (complexifiedEnd J) Complex.I where
  toFun m := ⟨positiveVector J m, positiveVector_mem J hJ m⟩
  map_add' x y := Subtype.ext ((positiveVector J).map_add x y)
  map_smul' r x := Subtype.ext ((positiveVector J).map_smul r x)

private theorem positiveEmbedding_realPart (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) (m : M) :
    tensorRealPart M (positiveEmbedding J hJ m) = m := by
  simp [positiveEmbedding, positiveVector, tensorRealPart]

private theorem positiveEmbedding_bijective (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) : Function.Bijective (positiveEmbedding J hJ) := by
  constructor
  · intro x y hxy
    have h := congrArg (fun z : invariantEigenspace (complexifiedEnd J) Complex.I =>
      tensorRealPart M z) hxy
    simpa only [positiveEmbedding_realPart] using h
  · intro z
    refine ⟨tensorRealPart M z, ?_⟩
    apply Subtype.ext
    have heig := (mem_invariantEigenspace (complexifiedEnd J) Complex.I z.val).mp z.property
    have hdec := complexification_real_imag_decomposition M z.val
    have hparts : J (tensorRealPart M z.val) = -tensorImagPart M z.val := by
      conv_lhs at heig => rw [hdec]
      conv_rhs at heig => rw [hdec]
      have hp := congrArg (tensorRealPart M) heig
      simpa [complexifiedEnd, tensorRealPart, tensorImagPart,
        TensorProduct.smul_tmul'] using hp
    change 1 ⊗ₜ[ℝ] tensorRealPart M z.val -
      Complex.I ⊗ₜ[ℝ] J (tensorRealPart M z.val) = z.val
    rw [hparts, TensorProduct.tmul_neg, sub_neg_eq_add]
    exact hdec.symm

private theorem positiveEmbedding_map_lie (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) (x : L) (m : M) :
    positiveEmbedding J hJ ⁅x, m⁆ = ⁅(1 ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] L),
      positiveEmbedding J hJ m⁆ := by
  apply Subtype.ext
  change 1 ⊗ₜ[ℝ] ⁅x, m⁆ - Complex.I ⊗ₜ[ℝ] J ⁅x, m⁆ =
    ⁅(1 ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] L), 1 ⊗ₜ[ℝ] m - Complex.I ⊗ₜ[ℝ] J m⁆
  change 1 ⊗ₜ[ℝ] ⁅x, m⁆ - Complex.I ⊗ₜ[ℝ] J ⁅x, m⁆ =
    (LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) (1 ⊗ₜ[ℝ] x))
      (1 ⊗ₜ[ℝ] m - Complex.I ⊗ₜ[ℝ] J m)
  rw [map_sub]
  simp [LieModule.toEnd_apply_apply, J.map_lie]

/-- Real irreducibility makes the positive eigenspace an irreducible
module for the complexified Lie algebra. -/
theorem complexification_positive_half_irreducible [LieModule.IsIrreducible ℝ L M]
    (J : M →ₗ⁅ℝ,L⁆ M) (hJ : ∀ m, J (J m) = -m) :
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] L)
      (invariantEigenspace (complexifiedEnd J) Complex.I) :=
  complex_irreducible_of_real_equivariant_bijection
    (fun x => 1 ⊗ₜ[ℝ] x) (positiveEmbedding J hJ)
    (positiveEmbedding_bijective J hJ) (positiveEmbedding_map_lie J hJ)

/-- The real module is canonically isomorphic to its positive complex
half; the inverse is the real-coordinate projection. -/
noncomputable def positiveHalfRealEquiv (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) :
    M ≃ₗ[ℝ] invariantEigenspace (complexifiedEnd J) Complex.I := {
  positiveEmbedding J hJ with
  invFun z := tensorRealPart M z
  left_inv := positiveEmbedding_realPart J hJ
  right_inv := by
    intro z
    obtain ⟨m, rfl⟩ := (positiveEmbedding_bijective J hJ).2 z
    change positiveEmbedding J hJ (tensorRealPart M (positiveEmbedding J hJ m)) = _
    rw [positiveEmbedding_realPart] }

/-- The explicit positive-half embedding. -/
theorem positiveHalfRealEquiv_apply (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) (m : M) :
    (positiveHalfRealEquiv J hJ m : ℂ ⊗[ℝ] M) =
      1 ⊗ₜ[ℝ] m - Complex.I ⊗ₜ[ℝ] J m := rfl

/-- The positive-half equivalence has the real-coordinate projection as
its actual inverse. -/
theorem positiveHalfRealEquiv_symm_apply (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m)
    (z : invariantEigenspace (complexifiedEnd J) Complex.I) :
    (positiveHalfRealEquiv J hJ).symm z = tensorRealPart M z := rfl

/-- Equivariance of the positive-half real equivalence. -/
theorem positiveHalfRealEquiv_map_lie (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) (x : L) (m : M) :
    positiveHalfRealEquiv J hJ ⁅x, m⁆ =
      ⁅(1 ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] L), positiveHalfRealEquiv J hJ m⁆ :=
  positiveEmbedding_map_lie J hJ x m

/-- On the positive half, the original real complex structure becomes
multiplication by `I`. -/
theorem positiveHalfRealEquiv_map_complexStructure (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) (m : M) :
    positiveHalfRealEquiv J hJ (J m) = Complex.I • positiveHalfRealEquiv J hJ m := by
  apply Subtype.ext
  change 1 ⊗ₜ[ℝ] J m - Complex.I ⊗ₜ[ℝ] J (J m) =
    Complex.I • (1 ⊗ₜ[ℝ] m - Complex.I ⊗ₜ[ℝ] J m)
  simp only [hJ, smul_sub, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one, Complex.I_mul_I, TensorProduct.tmul_neg,
    TensorProduct.neg_tmul, sub_neg_eq_add]
  abel

omit [LieAlgebra ℝ L] [LieModule ℝ L M] in
private theorem neg_complexStructure_square (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) : ∀ m, (-J) ((-J) m) = -m := by
  intro m
  simp [hJ]

private theorem complexifiedEnd_neg_apply (J : M →ₗ⁅ℝ,L⁆ M) (z : ℂ ⊗[ℝ] M) :
    complexifiedEnd (-J) z = -complexifiedEnd J z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    change a ⊗ₜ[ℝ] (-J) m = -(a ⊗ₜ[ℝ] J m)
    simp only [LieModuleHom.neg_apply, TensorProduct.tmul_neg]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

private theorem negativeHalf_eq_positive_neg (J : M →ₗ⁅ℝ,L⁆ M) :
    invariantEigenspace (complexifiedEnd (-J)) Complex.I =
      invariantEigenspace (complexifiedEnd J) (-Complex.I) := by
  ext z
  simp only [mem_invariantEigenspace, complexifiedEnd_neg_apply, neg_smul]
  exact neg_eq_iff_eq_neg

/-- The actual negative eigenspace is also irreducible over the
complexified Lie algebra. -/
theorem complexification_negative_half_irreducible [LieModule.IsIrreducible ℝ L M]
    (J : M →ₗ⁅ℝ,L⁆ M) (hJ : ∀ m, J (J m) = -m) :
    LieModule.IsIrreducible ℂ (ℂ ⊗[ℝ] L)
      (invariantEigenspace (complexifiedEnd J) (-Complex.I)) := by
  rw [← negativeHalf_eq_positive_neg]
  exact complexification_positive_half_irreducible (-J) (neg_complexStructure_square J hJ)

/-- The negative half as a real copy of the original module. -/
noncomputable def negativeHalfRealEquiv (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) :
    M ≃ₗ[ℝ] invariantEigenspace (complexifiedEnd J) (-Complex.I) :=
  (positiveHalfRealEquiv (-J) (neg_complexStructure_square J hJ)).trans
    ((LinearEquiv.ofEq
      (invariantEigenspace (complexifiedEnd (-J)) Complex.I).toSubmodule
      (invariantEigenspace (complexifiedEnd J) (-Complex.I)).toSubmodule
      (congrArg LieSubmodule.toSubmodule (negativeHalf_eq_positive_neg J))).restrictScalars ℝ)

/-- The explicit negative-half embedding. -/
theorem negativeHalfRealEquiv_apply (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) (m : M) :
    (negativeHalfRealEquiv J hJ m : ℂ ⊗[ℝ] M) =
      1 ⊗ₜ[ℝ] m + Complex.I ⊗ₜ[ℝ] J m := by
  change 1 ⊗ₜ[ℝ] m - Complex.I ⊗ₜ[ℝ] (-J) m = _
  simp only [LieModuleHom.neg_apply, TensorProduct.tmul_neg, sub_neg_eq_add]

/-- The inverse negative-half equivalence is again real projection. -/
theorem negativeHalfRealEquiv_symm_apply (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m)
    (z : invariantEigenspace (complexifiedEnd J) (-Complex.I)) :
    (negativeHalfRealEquiv J hJ).symm z = tensorRealPart M z := rfl

/-- Equivariance of the negative-half real equivalence. -/
theorem negativeHalfRealEquiv_map_lie (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) (x : L) (m : M) :
    negativeHalfRealEquiv J hJ ⁅x, m⁆ =
      ⁅(1 ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] L), negativeHalfRealEquiv J hJ m⁆ := by
  apply Subtype.ext
  change (negativeHalfRealEquiv J hJ ⁅x, m⁆ : ℂ ⊗[ℝ] M) =
    (LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) (1 ⊗ₜ[ℝ] x))
      (negativeHalfRealEquiv J hJ m : ℂ ⊗[ℝ] M)
  rw [negativeHalfRealEquiv_apply, negativeHalfRealEquiv_apply, map_add]
  simp [LieModule.toEnd_apply_apply, J.map_lie]

/-- On the negative half, the original real complex structure becomes
multiplication by `-I`. -/
theorem negativeHalfRealEquiv_map_complexStructure (J : M →ₗ⁅ℝ,L⁆ M)
    (hJ : ∀ m, J (J m) = -m) (m : M) :
    negativeHalfRealEquiv J hJ (J m) = (-Complex.I) • negativeHalfRealEquiv J hJ m := by
  apply Subtype.ext
  change (negativeHalfRealEquiv J hJ (J m) : ℂ ⊗[ℝ] M) =
    (-Complex.I) • (negativeHalfRealEquiv J hJ m : ℂ ⊗[ℝ] M)
  rw [negativeHalfRealEquiv_apply, negativeHalfRealEquiv_apply]
  simp only [hJ, smul_add, TensorProduct.smul_tmul', smul_eq_mul, neg_mul,
    mul_one, Complex.I_mul_I, TensorProduct.tmul_neg,
    TensorProduct.neg_tmul, neg_neg]
  abel

end PositiveHalf

end CubicAnomaly.Classification.Complexification
