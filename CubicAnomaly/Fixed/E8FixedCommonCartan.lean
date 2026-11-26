import CubicAnomaly.Fixed.E8CanonicalPair
import CubicAnomaly.Classification.ContainedCartan

/-!
# A common Cartan for the constructed compact E8 pair

Geck's abelian subalgebra has precisely eight zero-weight coordinates on
the defining module. The adjoint equivalence identifies them with the eight
Cartan generators themselves, making this subalgebra self-normalizing in
the ambient algebra. All eight coordinates belong to degree zero.
-/

namespace CubicAnomaly.Fixed.E8FixedCommonCartan

open CubicAnomaly.Fixed.E8Geck CubicAnomaly.Fixed.E8RootPairing
open CubicAnomaly.Fixed.E8Adjoint CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8Compact CubicAnomaly.Fixed.E8CompactPair
open CubicAnomaly.Fixed.E8GradingData CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8CanonicalPair CubicAnomaly.Fixed.E8CompactGrading
open CubicAnomaly.Fixed.E8FullCubic
open CubicAnomaly.Classification.CompactGeometry
open LieModule LieAlgebra RootPairing.GeckConstruction
open scoped TensorProduct

noncomputable section

private abbrev T := E8Geck.cartanSubalgebra

private instance : IsLieAbelian T := cartanSubalgebra_abelian

/-- The fixed adjoint equivalence restricted to the toral action. -/
private def toralEquiv : E8Geck.DefiningSpace ≃ₗ⁅ℂ,T⁆ E8Geck.lieAlgebra where
  __ := adjointEquiv.toLinearEquiv
  map_lie' {x v} := adjointEquiv.map_lie x.val v

private theorem u_is_label (j : Fin 8) :
    u (simpleIndex j) = basisVector (.inl j) := by
  have hd : dataIndex (.inl (simpleIndexEquiv j)) = .inl j := by simp [dataIndex]
  rw [← hd, e8_basisVector_dataIndex]
  rfl

private theorem zero_root_coordinates {x : E8Geck.lieAlgebra}
    (hx : x ∈ rootSpace T 0) :
    ∃ v ∈ Submodule.span ℂ (Set.range (u (b := base))), adjointEquiv v = x := by
  change x ∈ genWeightSpace E8Geck.lieAlgebra (0 : T → ℂ) at hx
  rw [← LieModule.map_genWeightSpace_eq toralEquiv] at hx
  obtain ⟨v, hv, hvx⟩ := hx
  refine ⟨v, ?_, hvx⟩
  change v ∈ (genWeightSpace E8Geck.DefiningSpace (0 : T → ℂ)).toSubmodule at hv
  rwa [coe_genWeightSpace_zero_eq_span_range_u (b := base)] at hv

private theorem toral_coordinate_mem (i : base.support) : adjointEquiv (u i) ∈ T := by
  obtain ⟨j, rfl⟩ := simpleIndex_bijective.2 i
  change bracketMatrixMap (u (simpleIndex j)) ∈ RootPairing.GeckConstruction.cartanSubalgebra base
  rw [u_is_label, e8_h_bracketMatrixMap_image]
  exact zsmul_mem (h_mem_cartanSubalgebra (simpleIndex j)) _

/-- The distinguished abelian subalgebra of the fixed Geck algebra is a Cartan. -/
theorem geck_cartan_isCartanSubalgebra : T.IsCartanSubalgebra := by
  apply is_cartan_of_zeroRootSubalgebra_eq
  refine le_antisymm (fun x hx => ?_) (le_zeroRootSubalgebra ℂ _ _)
  obtain ⟨v, hv, rfl⟩ := zero_root_coordinates hx
  exact (Submodule.span_le.mpr (fun _ ⟨i, hi⟩ => hi ▸ toral_coordinate_mem i) :
    Submodule.span ℂ (Set.range (u (b := base))) ≤ T.toSubmodule.comap adjointEquiv.toLinearEquiv.toLinearMap) hv

/-- The actual toral coordinates of the fixed algebra have degree zero. -/
theorem geck_cartan_le_zeroSubalgebra : T ≤ zeroSubalgebra := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := zero_root_coordinates (toLieSubmodule_le_rootSpace_zero ℂ _ T hx)
  refine ⟨v, ?_, rfl⟩
  apply (Submodule.span_le.mpr ?_ : Submodule.span ℂ (Set.range (u (b := base))) ≤ gradeSpace 0) hv
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, rfl⟩ := simpleIndex_bijective.2 i
  rw [u_is_label]
  exact e8_basisVector_homogeneous (.inl j)

/-- The Cartan transported into the tensor complexification of the compact algebra. -/
def fixedCartan : LieSubalgebra ℂ (ℂ ⊗[ℝ] compactRealAlgebra) :=
  T.comap complexificationEquiv.toLieHom

theorem fixedCartan_isCartanSubalgebra : fixedCartan.IsCartanSubalgebra := by
  letI := geck_cartan_isCartanSubalgebra
  exact Classification.ContainedCartan.isCartanSubalgebra_comap_of_le_range
    complexificationEquiv.toLieHom complexificationEquiv.injective T
    (fun x _ => complexificationEquiv.surjective x)

theorem fixedCartan_le_complexifiedSubalgebra :
    fixedCartan ≤ complexifiedSubalgebra compactZero := by
  intro x hx
  let z : zeroSubalgebra := ⟨complexificationEquiv x, geck_cartan_le_zeroSubalgebra hx⟩
  obtain ⟨w, hw⟩ := zeroComplexificationEquiv.surjective z
  refine ⟨w, complexificationEquiv.injective ?_⟩
  exact congrArg Subtype.val hw

/-- The compact pair constructed in the repository has a common complex Cartan. -/
theorem exists_fixed_common_cartan :
    ∃ H : LieSubalgebra ℂ (ℂ ⊗[ℝ] compactRealAlgebra),
      H.IsCartanSubalgebra ∧ H ≤ complexifiedSubalgebra compactZero :=
  ⟨fixedCartan, fixedCartan_isCartanSubalgebra, fixedCartan_le_complexifiedSubalgebra⟩

/-- The real intersection of the Geck Cartan with the constructed compact real form. -/
def fixedRealCartan : LieSubalgebra ℝ compactRealAlgebra where
  toSubmodule := (T.toSubmodule.restrictScalars ℝ).comap compactToComplex.toLinearMap
  lie_mem' {x y} hx hy := by
    change compactToComplex ⁅x, y⁆ ∈ T
    rw [LieHom.map_lie]
    exact T.lie_mem hx hy

theorem fixedRealCartan_le_compactZero : fixedRealCartan ≤ compactZero :=
  fun _ hx => geck_cartan_le_zeroSubalgebra hx

private theorem cartan_matrix_mem (j : Fin 8) : (cartan j).val ∈ T := by
  change (cartan j).val.val ∈ RootPairing.GeckConstruction.cartanSubalgebra base
  rw [e8_full_cartan_matrix]
  exact h_mem_cartanSubalgebra _

private theorem compact_cartan_mem (j : Fin 8) : (compactCartan j).val ∈ fixedRealCartan := by
  change (compactZeroToComplex (compactCartan j)).val ∈ T
  rw [e8_compact_cartan_image]
  exact T.smul_mem _ (cartan_matrix_mem j)

private theorem eval_tmul (c : ℂ) (x : compactRealAlgebra) :
    complexificationEquiv (c ⊗ₜ[ℝ] x) = c • compactToComplex x := by
  apply Subtype.ext
  exact (e8_compact_complexification_tmul c x).trans (map_smul operatorEquiv.symm c x.val)

private theorem cartan_generator_in_range (j : Fin 8) :
    complexificationEquiv.symm (cartan j).val ∈ complexifiedSubalgebra fixedRealCartan := by
  let t : fixedRealCartan := ⟨(compactCartan j).val, compact_cartan_mem j⟩
  refine ⟨(-Complex.I) ⊗ₜ[ℝ] t, complexificationEquiv.injective ?_⟩
  change complexificationEquiv ((-Complex.I) ⊗ₜ[ℝ] (compactCartan j).val) =
    complexificationEquiv (complexificationEquiv.symm (cartan j).val)
  rw [eval_tmul, complexificationEquiv.apply_symm_apply]
  have he := congrArg Subtype.val (e8_compact_cartan_image j)
  change compactToComplex (compactCartan j).val = Complex.I • (cartan j).val at he
  rw [he, smul_smul]
  simp

/-- All the complex toral directions descend to compact real directions:
the eight imaginary simple coroots span the complex Cartan. -/
theorem complexified_fixedRealCartan_eq : complexifiedSubalgebra fixedRealCartan = fixedCartan := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp [fixedCartan]
    | tmul a t =>
      change complexificationEquiv (a ⊗ₜ[ℝ] t.val) ∈ T
      rw [eval_tmul]
      exact T.smul_mem a t.property
    | add a b ha hb => rw [map_add]; exact fixedCartan.add_mem ha hb
  · intro x hx
    let t : T := ⟨complexificationEquiv x, hx⟩
    let F := complexificationEquiv.symm.toLinearEquiv.toLinearMap.comp T.subtype
    let U := (complexifiedSubalgebra fixedRealCartan).toSubmodule.comap F
    have hspan : (⊤ : Submodule ℂ T) ≤ U := by
      rw [← span_range_h'_eq_top base, Submodule.span_le]
      rintro _ ⟨i,rfl⟩
      obtain ⟨j,rfl⟩ := simpleIndex_bijective.2 i
      have hm : (h' (simpleIndex j)).val = (cartan j).val :=
        Subtype.ext (e8_full_cartan_matrix j).symm
      change complexificationEquiv.symm (h' (simpleIndex j)).val ∈ complexifiedSubalgebra fixedRealCartan
      rw [hm]
      exact cartan_generator_in_range j
    have ht := hspan (show t ∈ (⊤ : Submodule ℂ T) from trivial)
    change complexificationEquiv.symm (complexificationEquiv x) ∈ complexifiedSubalgebra fixedRealCartan at ht
    simpa only [complexificationEquiv.symm_apply_apply] using ht

/-- A compact toral subalgebra inside the constructed isotropy whose complexification
is a Cartan in the ambient complex E8. -/
theorem exists_fixed_real_common_cartan :
    ∃ A : LieSubalgebra ℝ compactRealAlgebra,
      A ≤ compactZero ∧ (complexifiedSubalgebra A).IsCartanSubalgebra :=
  ⟨fixedRealCartan, fixedRealCartan_le_compactZero,
    complexified_fixedRealCartan_eq.symm ▸ fixedCartan_isCartanSubalgebra⟩

end

end CubicAnomaly.Fixed.E8FixedCommonCartan
