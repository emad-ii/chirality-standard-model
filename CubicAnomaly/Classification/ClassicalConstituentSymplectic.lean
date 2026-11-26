import CubicAnomaly.Classification.ClassicalConstituentCompact
import CubicAnomaly.Classification.ClassicalConstituentComparison
import CubicAnomaly.Classification.ClassicalConstituentSquare
import CubicAnomaly.Classification.ClassicalSimplicity

/-!
# The symplectic Cartan square is the adjoint constituent

The operator of a pure highest tensor square has a nonzero projection
onto the compact isotropy. Otherwise it belongs to one of the two
inequivalent quotient halves: simultaneous nonzero projections would
give them the same highest weight. Either half containing the square
would be self-dual by nonvanishing of its squared matrix coefficient,
contradicting their actual equivariant duality and inequivalence.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentSymplectic

open LieAlgebra LieModule Module LieAlgebra.IsKilling Submodule
open ClassicalConstituentHighest ClassicalConstituentCompact ClassicalConstituentComparison
open ClassicalConstituentSquare ClassicalConstituents Structural ComplexDuality Complexification
open CompactGeometry SelfDualQuotientObstruction CompactOperatorModel DualPairSkew SelfDualAbsorption
open scoped TensorProduct

noncomputable section

section Detection

variable {L V : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] {b : (rootSystem H).Base}
    [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

private theorem mem_half_of_highest (P Q : LieSubmodule ℂ L V) (hc : IsCompl P Q)
    [IsIrreducible ℂ L P] [IsIrreducible ℂ L Q] (hne : ¬ Nonempty (P ≃ₗ⁅ℂ,L⁆ Q))
    {μ : H → ℂ} {u : V} (hu : IsHighestVector H b μ u) : u ∈ P ∨ u ∈ Q := by
  let p := invariantSummandProjection P Q hc
  let q := invariantSummandProjection Q P hc.symm
  by_cases hp : p u = 0
  · exact Or.inr ((LieSubmodule.isCompl_toSubmodule.mpr hc).projection_apply_eq_zero_iff.mp
      (congrArg Subtype.val hp))
  by_cases hq : q u = 0
  · exact Or.inl ((LieSubmodule.isCompl_toSubmodule.mpr hc.symm).projection_apply_eq_zero_iff.mp
      (congrArg Subtype.val hq))
  obtain ⟨E, _⟩ := irreducible_equiv_of_highest_weight H (highest_map H p hu hp) (highest_map H q hu hq)
  exact (hne ⟨E⟩).elim

end Detection

section Compact

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)

private def isotropyProjection : (ℂ ⊗[ℝ] g) →ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ (ℂ ⊗[ℝ] h) :=
  complexifiedHom (invariantProjection h.toLieSubmodule (orthogonalComplement B h)
      (compact_orthogonal_complement_isCompl B h))

private theorem ambient_projection_sum (z : ℂ ⊗[ℝ] g) :
    complexifiedHom h.toLieSubmodule.incl (isotropyProjection B h z) +
      complexifiedHom (orthogonalComplement B h).incl (complexifiedComplementProjection B h z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
    change a ⊗ₜ[ℝ] ((compact_orthogonal_complement_isCompl B h).projection z) +
      a ⊗ₜ[ℝ] ((compact_orthogonal_complement_isCompl B h).symm.projection z) = a ⊗ₜ[ℝ] z
    rw [← TensorProduct.tmul_add, Submodule.IsCompl.projection_add_projection_eq_self]
  | add z w hz hw => simp only [map_add]; rw [add_add_add_comm, hz, hw]

variable (hp : h ≠ ⊤) (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)] (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [LieRingModule (ℂ ⊗[ℝ] h) W]
    [LieModule ℂ (ℂ ⊗[ℝ] h) W] [FiniteDimensional ℂ W] [IsIrreducible ℂ (ℂ ⊗[ℝ] h) W]
    {β : LinearMap.BilinForm ℂ W}

omit [IsIrreducible ℂ (ℂ ⊗[ℝ] h) W] in
private theorem model_square_preimage (b : (rootSystem H).Base) (A : Model h β)
    (hβ : β.Nondegenerate) (hi : β.lieInvariant (ℂ ⊗[ℝ] h)) (ha : β.IsAlt)
    {χ : H → ℂ} {v : W} (hv : IsHighestVector H b χ v) :
    ∃ z : ℂ ⊗[ℝ] g,
      A.operatorMap z = formTensorEndEquiv β hβ hi (v ⊗ₜ[ℂ] v) ∧
      IsHighestVector H b (fun x => 2 * χ x) z := by
  let E := formTensorEndEquiv β hβ hi
  let t := v ⊗ₜ[ℂ] v
  obtain ⟨ht, hflip, hw, hk⟩ := symmetric_square_highest_vector (K := ℂ) (L := ℂ ⊗[ℝ] h) v hv.1
  have htop : IsHighestVector H b (fun x => 2 * χ x) t :=
    ⟨ht, fun x => hw x _ (hv.2.1 x), fun α hα x hx => hk x (hv.2.2 α hα x hx)⟩
  have hT := highest_map H E.toLieModuleHom htop (fun hz => ht (E.injective (hz.trans (map_zero E).symm)))
  have hsk : E t ∈ skewAdjointLieSubalgebra β := by
    apply (form_tensor_mem_skew_adjoint_iff β hβ hi (-1) (by norm_num)
      (fun u w => by simpa using (ha.neg_eq w u).symm) t).mpr
    simp [t]
  obtain ⟨z, hz⟩ := (A.range_iff _).mpr hsk
  have hzt := highest_preimage H A.operatorMap A.injective (hz ▸ hT)
  exact ⟨z, hz, hzt⟩

include hp e in
/-- Every highest vector in a symplectic operator model supplies an actual
adjoint highest vector of twice its weight. -/
theorem symplectic_model_twice_highest (b : (rootSystem H).Base) (A : Model h β)
    (hβ : β.Nondegenerate) (hi : β.lieInvariant (ℂ ⊗[ℝ] h)) (ha : β.IsAlt)
    {χ : H → ℂ} {v : W} (hv : IsHighestVector H b χ v) :
    ∃ y : ℂ ⊗[ℝ] h, IsHighestVector H b (fun x => 2 * χ x) y := by
  let E := formTensorEndEquiv β hβ hi
  let t := v ⊗ₜ[ℂ] v
  obtain ⟨z, hz, hzt⟩ := model_square_preimage h H b A hβ hi ha hv
  let π := complexifiedComplementProjection B h
  let ι := complexifiedHom (orthogonalComplement B h).incl
  refine ⟨isotropyProjection B h z, highest_map H _ hzt ?_⟩
  intro hzero
  have he : ι (π z) = z := by simpa only [hzero, map_zero, zero_add] using ambient_projection_sum B h z
  have hπ : π z ≠ 0 := fun hn => hzt.1 (by rw [← he, hn, map_zero])
  let P := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let Q := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I)
  obtain ⟨hc, hP, hQ, ⟨d⟩, hpq⟩ := compact_complement_complex_type_decomposition B h hp e
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) P := hP
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) Q := hQ
  have hn := inequivalent_dual_pair_not_self_dual d hpq
  have hself (S : LieSubmodule ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] orthogonalComplement B h))
      [IsIrreducible ℂ (ℂ ⊗[ℝ] h) S] (hm : π z ∈ S) :
      Nonempty (S ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Dual ℂ S) := by
    let F := E.symm.toLieModuleHom.comp (A.operatorMap.comp (ι.comp S.incl))
    apply constituent_of_pure_square_self_dual β hβ hi F v hv.1
    refine ⟨⟨π z, hm⟩, ?_⟩
    change E.symm (A.operatorMap (ι (π z))) = t
    rw [he, hz, LieModuleEquiv.symm_apply_apply]
  exact (mem_half_of_highest H P Q hc hpq (highest_map H π hzt hπ)).elim
    (fun hm => hn.1 (hself P hm)) (fun hm => hn.2 (hself Q hm))

include hp e in
/-- With simple isotropy, the pure highest square belongs to the literal
image of the complexified isotropy action on the defining module. -/
theorem symplectic_model_square_mem_action [IsSimple ℂ (ℂ ⊗[ℝ] h)]
    (b : (rootSystem H).Base) (A : Model h β)
    (hβ : β.Nondegenerate) (hi : β.lieInvariant (ℂ ⊗[ℝ] h)) (ha : β.IsAlt)
    {χ : H → ℂ} {v : W} (hv : IsHighestVector H b χ v) :
    formTensorEndEquiv β hβ hi (v ⊗ₜ[ℂ] v) ∈ (toEnd ℂ (ℂ ⊗[ℝ] h) W).range := by
  obtain ⟨z, hz, hzt⟩ := model_square_preimage h H b A hβ hi ha hv
  rw [← hz, ← A.mem_isotropy_iff z, ← complexified_complement_projection_eq_zero_iff B h z]
  let π := complexifiedComplementProjection B h
  by_contra hn
  have hπ := highest_map H π hzt hn
  obtain ⟨a, ha'⟩ := symplectic_model_twice_highest B h hp e H b A hβ hi ha hv
  have hs := invariant_nondegenerate_form_self_dual (killingForm ℂ (ℂ ⊗[ℝ] h))
    (traceForm_lieInvariant ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] h))
    (IsKilling.killingForm_nondegenerate ℂ (ℂ ⊗[ℝ] h))
  let P := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let Q := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I)
  obtain ⟨hc, hP, hQ, _, hpq⟩ := compact_complement_complex_type_decomposition B h hp e
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) P := hP
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) Q := hQ
  have hexclude (S : LieSubmodule ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] orthogonalComplement B h))
      [IsIrreducible ℂ (ℂ ⊗[ℝ] h) S] (hm : π z ∈ S) : False := by
    have hs' := highest_preimage H S.incl Subtype.val_injective
      (show IsHighestVector H b _ (S.incl ⟨π z, hm⟩) from hπ)
    obtain ⟨E, hE⟩ := irreducible_equiv_of_highest_weight H ha' hs'
    let F := S.incl.comp E.toLieModuleHom
    have hF := compact_complement_self_dual_irreducible_hom_eq_zero B h hp e hs F
    have he : F a = 0 := DFunLike.congr_fun hF a
    apply hπ.1
    exact (congrArg Subtype.val hE).symm.trans he
  exact (mem_half_of_highest H P Q hc hpq hπ).elim (hexclude P) (hexclude Q)

end Compact

end

end CubicAnomaly.Classification.ClassicalConstituentSymplectic
