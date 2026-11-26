import CubicAnomaly.Classification.CompactGeometry

/-!
# Dimension and quadratic-trace restriction for the actual complex half

Trace forms add across invariant complementary subspaces and agree on
contragredient representations.  Applied to the actual complexified compact
pair, these identities give the dimension and Killing-form restrictions
needed by the rank-deficient arithmetic sieve.  No Dynkin index, highest
weight, factorization, or census label is assumed.
-/

namespace CubicAnomaly.Classification.QuadraticRestriction

open LieAlgebra LieModule Module
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.ComplexDuality
open CubicAnomaly.Classification.CompactGeometry
open scoped TensorProduct

section Trace

variable {K L M N : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- The trace form is independent of an equivariant choice of coordinates. -/
theorem traceForm_equivariant_equiv (e : M ≃ₗ⁅K,L⁆ N) :
    traceForm K L N = traceForm K L M := by
  have ha (x : L) : toEnd K L N x = e.toLinearEquiv.conj (toEnd K L M x) := by
    apply LinearMap.ext
    intro n
    change ⁅x, n⁆ = e ⁅x, e.symm n⁆
    have h := e.map_lie x (e.symm n)
    change e ⁅x, e.symm n⁆ = ⁅x, e (e.symm n)⁆ at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  ext x y
  simp only [traceForm_apply_apply, ha, ← LinearEquiv.conj_comp, LinearMap.trace_conj']

/-- A finite-dimensional representation and its contragredient have the
same quadratic trace form. -/
theorem traceForm_contragredient [FiniteDimensional K M] :
    traceForm K L (Module.Dual K M) = traceForm K L M := by
  ext x y
  have hprod : toEnd K L (Module.Dual K M) x ∘ₗ toEnd K L (Module.Dual K M) y =
      Module.Dual.transpose (toEnd K L M y ∘ₗ toEnd K L M x) := by
    ext f m
    change -(-f ⁅y, ⁅x, m⁆⁆) = f ⁅y, ⁅x, m⁆⁆
    exact neg_neg _
  rw [traceForm_apply_apply, hprod]
  change (LinearMap.trace K (Module.Dual K M) ∘ₗ Module.Dual.transpose)
    (toEnd K L M y ∘ₗ toEnd K L M x) = traceForm K L M x y
  rw [LinearMap.trace_transpose]
  exact LinearMap.trace_comp_comm' _ _

/-- Quadratic trace forms add across actual invariant complementary subspaces. -/
theorem traceForm_complementary_submodules [FiniteDimensional K M]
    (P Q : LieSubmodule K L M) (hc : IsCompl P Q) :
    traceForm K L M = traceForm K L P + traceForm K L Q := by
  let E := P.toSubmodule.prodEquivOfIsCompl Q.toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr hc)
  ext x y
  have heq : toEnd K L M x ∘ₗ toEnd K L M y =
      E.conj (LinearMap.prodMap (toEnd K L P x ∘ₗ toEnd K L P y)
        (toEnd K L Q x ∘ₗ toEnd K L Q y)) := by
    apply LinearMap.ext
    intro m
    obtain ⟨⟨p, q⟩, rfl⟩ := E.surjective m
    change ⁅x, ⁅y, E (p, q)⁆⁆ =
      E ((toEnd K L P x) ((toEnd K L P y) (E.symm (E (p, q))).1),
        (toEnd K L Q x) ((toEnd K L Q y) (E.symm (E (p, q))).2))
    rw [E.symm_apply_apply]
    change ⁅x, ⁅y, (p : M) + (q : M)⁆⁆ = ⁅x, ⁅y, (p : M)⁆⁆ + ⁅x, ⁅y, (q : M)⁆⁆
    simp only [lie_add]
  simp only [LinearMap.add_apply, traceForm_apply_apply, heq,
    LinearMap.trace_conj', LinearMap.trace_prodMap']
  rfl

end Trace

section CompactPair

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The dimension equation for the actual complex half of the entire
adjoint complement, with no highest-weight or census input. -/
theorem compact_pair_dimension_equation (B : CompactForm g)
    (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    finrank ℝ g = finrank ℝ h + 2 * finrank ℂ V := by
  let q := orthogonalComplement B h
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let W := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I)
  obtain ⟨hc, _, _, ⟨D⟩, _⟩ := compact_complement_complex_type_decomposition B h hproper e
  have hq := Submodule.finrank_add_eq_of_isCompl (LieSubmodule.isCompl_toSubmodule.mpr hc)
  have hD := D.toLinearEquiv.finrank_eq
  rw [Subspace.dual_finrank_eq] at hD
  have hbase : finrank ℂ (ℂ ⊗[ℝ] q) = finrank ℝ q := Module.finrank_baseChange
  have hg := Submodule.finrank_add_eq_of_isCompl (compact_orthogonal_complement_isCompl B h)
  change finrank ℝ h + finrank ℝ q = finrank ℝ g at hg
  change finrank ℂ V + finrank ℂ W = finrank ℂ (ℂ ⊗[ℝ] q) at hq
  change finrank ℂ W = finrank ℂ V at hD
  change finrank ℝ g = finrank ℝ h + 2 * finrank ℂ V
  omega

/-- Restriction of the actual ambient Killing form to the actual isotropy
algebra is its own Killing form plus twice the trace form of the actual
positive complex half.  This is the quadratic identity underlying the
Dynkin-index sieve, before choosing any index normalization. -/
theorem compact_pair_quadratic_restriction (B : CompactForm g)
    (h : LieSubalgebra ℝ g) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (x y : ℂ ⊗[ℝ] h) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    killingForm ℂ (ℂ ⊗[ℝ] g) (complexifiedLieHom h.incl x) (complexifiedLieHom h.incl y) =
      killingForm ℂ (ℂ ⊗[ℝ] h) x y + 2 * traceForm ℂ (ℂ ⊗[ℝ] h) V x y := by
  let q := orthogonalComplement B h
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let W := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I)
  obtain ⟨hc, _, _, ⟨D⟩, _⟩ := compact_complement_complex_type_decomposition B h hproper e
  have hqTrace : traceForm ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] q) =
      (2 : ℂ) • traceForm ℂ (ℂ ⊗[ℝ] h) V := by
    rw [traceForm_complementary_submodules V W hc,
      ← traceForm_equivariant_equiv D, traceForm_contragredient]
    exact (two_smul ℂ _).symm
  let A := h.toLieSubmodule.baseChange ℂ
  let Q := q.baseChange ℂ
  have hAQ : IsCompl A Q := LieSubmodule.isCompl_toSubmodule.mp
    (complexification_submodules_isCompl _ _ (compact_orthogonal_complement_isCompl B h))
  have hsplit := traceForm_complementary_submodules A Q hAQ
  have hA := traceForm_equivariant_equiv (lieSubmoduleComplexificationEquiv h.toLieSubmodule)
  have hQ := traceForm_equivariant_equiv (lieSubmoduleComplexificationEquiv q)
  have hambient :
      killingForm ℂ (ℂ ⊗[ℝ] g) (complexifiedLieHom h.incl x) (complexifiedLieHom h.incl y) =
        traceForm ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] g) x y := by
    rw [killingForm_apply_apply, traceForm_apply_apply]
    congr 1
    apply LinearMap.ext
    intro z
    change ⁅complexifiedLieHom h.incl x, ⁅complexifiedLieHom h.incl y, z⁆⁆ = ⁅x, ⁅y, z⁆⁆
    rw [complexifiedLieHom_inclusion_action, complexifiedLieHom_inclusion_action]
  change killingForm ℂ (ℂ ⊗[ℝ] g) _ _ = killingForm ℂ (ℂ ⊗[ℝ] h) x y +
    2 * traceForm ℂ (ℂ ⊗[ℝ] h) V x y
  rw [hambient, hsplit, hA, hQ, hqTrace]
  rfl

end CompactPair

end CubicAnomaly.Classification.QuadraticRestriction
