import CubicAnomaly.Classification.ClassicalConstituents
import CubicAnomaly.Classification.TensorFormFactorization
import CubicAnomaly.Classification.ExceptionalSieveWeights

/-!
# The actual Casimir operator and the trace index

The invariant tensor corresponding to the identity under the Killing form
acts on a representation by composition. On an irreducible complex module
it acts by a scalar. Contracting its trace against a Killing-dual basis
relates that scalar to the actual quadratic trace form.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveCasimir

open LieAlgebra LieModule Module
open CubicAnomaly.Classification.ClassicalConstituents
open CubicAnomaly.Classification.TensorFormFactorization
open scoped TensorProduct

noncomputable section

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] [AddCommGroup M] [Module ℂ M]
  [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]

private def productActionLinear : L ⊗[ℂ] L →ₗ[ℂ] Module.End ℂ M :=
  TensorProduct.lift ((LinearMap.mul ℂ (Module.End ℂ M)).compl₁₂
    (toEnd ℂ L M).toLinearMap (toEnd ℂ L M).toLinearMap)

private def productAction : L ⊗[ℂ] L →ₗ⁅ℂ,L⁆ Module.End ℂ M where
  __ := productActionLinear
  map_lie' := by
    intro x z
    change productActionLinear (M := M) ⁅x, z⁆ = ⁅x, productActionLinear z⁆
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.LieModule.lie_tmul_right, map_add]
      change toEnd ℂ L M ⁅x, a⁆ * toEnd ℂ L M b + toEnd ℂ L M a * toEnd ℂ L M ⁅x, b⁆ =
        toEnd ℂ L M x * (toEnd ℂ L M a * toEnd ℂ L M b) -
          (toEnd ℂ L M a * toEnd ℂ L M b) * toEnd ℂ L M x
      rw [LieHom.map_lie, LieHom.map_lie]
      change (_*_ - _*_) * _ + _ * (_*_ - _*_) = _
      noncomm_ring
    | add a b ha hb => simp [ha, hb]

private def tensorEnd (L : Type*) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [LieAlgebra.IsKilling ℂ L] : (L ⊗[ℂ] L) ≃ₗ⁅ℂ,L⁆ Module.End ℂ L :=
  formTensorEndEquiv (killingForm ℂ L) (IsKilling.killingForm_nondegenerate ℂ L)
    (traceForm_lieInvariant ℂ L L)

/-- The canonical inverse Killing tensor, independent of any basis. -/
def casimirTensor (L : Type*) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [LieAlgebra.IsKilling ℂ L] : L ⊗[ℂ] L := (tensorEnd L).symm LinearMap.id

variable (L M) in
/-- The Casimir tensor acts on the actual module by the product of its
two infinitesimal actions. -/
def casimirOperator : Module.End ℂ M := (productAction (L := L) (M := M)) (casimirTensor L)

omit [FiniteDimensional ℂ M] in
private theorem commute_casimir (x : L) :
    ⁅x, (casimirOperator (L := L) (M := M))⁆ = 0 := by
  change ⁅x, (productAction (L := L) (M := M)) (casimirTensor L)⁆ = 0
  rw [← LieModuleHom.map_lie]
  have hz : ⁅x, casimirTensor L⁆ = 0 := by
    apply (tensorEnd L).injective
    rw [map_zero]
    change (tensorEnd L).toLieModuleHom ⁅x, casimirTensor L⁆ = 0
    rw [LieModuleHom.map_lie]
    change ⁅x, (tensorEnd L) (casimirTensor L)⁆ = 0
    simp only [casimirTensor, LieModuleEquiv.apply_symm_apply]
    ext w
    change ⁅x, w⁆ - ⁅x, w⁆ = 0
    exact sub_self _
  rw [hz, map_zero]

/-- Schur's lemma for the Casimir built from the actual Killing form. -/
theorem irreducible_casimir_scalar [IsIrreducible ℂ L M] :
    ∃ c : ℂ, casimirOperator (L := L) (M := M) = c • LinearMap.id := by
  let C := casimirOperator (L := L) (M := M)
  let E : M →ₗ⁅ℂ,L⁆ M := { C with
    map_lie' := by
      intro x v
      have h := LinearMap.congr_fun (commute_casimir (M := M) x) v
      change ⁅x, C v⁆ - C ⁅x, v⁆ = 0 at h
      exact (sub_eq_zero.mp h).symm }
  obtain ⟨c, hc⟩ := equivariant_end_eq_smul_id E
  exact ⟨c, congrArg LieModuleHom.toLinearMap hc⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expansion of the inverse Killing tensor in any basis and its Killing-dual. -/
theorem casimir_tensor_basis (b : Basis ι ℂ L) :
    casimirTensor L = ∑ i, (killingForm ℂ L).dualBasis
      (IsKilling.killingForm_nondegenerate ℂ L) b i ⊗ₜ[ℂ] b i := by
  let K := killingForm ℂ L
  let hd := IsKilling.killingForm_nondegenerate ℂ L
  apply (tensorEnd L).injective
  rw [casimirTensor, LieModuleEquiv.apply_symm_apply, map_sum]
  apply b.ext
  intro j
  change b j = (∑ i, tensorEnd L (K.dualBasis hd b i ⊗ₜ[ℂ] b i)) (b j)
  rw [LinearMap.sum_apply]
  change b j = ∑ i, K (K.dualBasis hd b i) (b j) • b i
  simp [LinearMap.BilinForm.apply_dualBasis_left]

omit [FiniteDimensional ℂ M] in
/-- On a simple algebra every actual quadratic module trace form is a
multiple of the Killing form. -/
theorem trace_form_proportional [LieAlgebra.IsSimple ℂ L] :
    ∃ m : ℂ, traceForm ℂ L M = m • killingForm ℂ L := by
  let K := killingForm ℂ L
  let hd := IsKilling.killingForm_nondegenerate ℂ L
  let D := (K.toDual hd).symm.toLinearMap.comp (traceForm ℂ L M)
  have hD (x y : L) : K (D x) y = traceForm ℂ L M x y :=
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hd) _ _
  let E : L →ₗ⁅ℂ,L⁆ L := { D with
    map_lie' := by
      intro x y
      apply (K.toDual hd).injective
      ext z
      change K (D ⁅x, y⁆) z = K ⁅x, D y⁆ z
      rw [hD, traceForm_apply_lie_apply' ℂ L M, traceForm_apply_lie_apply' ℂ L L, hD] }
  obtain ⟨m, hm⟩ := equivariant_end_eq_smul_id E
  refine ⟨m, ?_⟩
  ext x y
  have h : D x = m • x := LieModuleHom.congr_fun hm x
  rw [← hD, h]
  simp [K]

/-- The Casimir scalar times the module dimension equals the Killing-form
multiple of its quadratic trace times the algebra dimension. -/
theorem casimir_scalar_trace_index [LieAlgebra.IsSimple ℂ L] [IsIrreducible ℂ L M] :
    ∃ c m : ℂ, casimirOperator (L := L) (M := M) = c • LinearMap.id ∧
      traceForm ℂ L M = m • killingForm ℂ L ∧
      c * finrank ℂ M = m * finrank ℂ L := by
  classical
  obtain ⟨c, hc⟩ := irreducible_casimir_scalar (L := L) (M := M)
  obtain ⟨m, hm⟩ := trace_form_proportional (L := L) (M := M)
  refine ⟨c, m, hc, hm, ?_⟩
  let b := Module.finBasis ℂ L
  let bd := (killingForm ℂ L).dualBasis (IsKilling.killingForm_nondegenerate ℂ L) b
  have ht : LinearMap.trace ℂ M (casimirOperator (L := L) (M := M)) =
      ∑ i, traceForm ℂ L M (bd i) (b i) := by
    rw [casimirOperator, casimir_tensor_basis b, map_sum, map_sum]
    rfl
  rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul, hm] at ht
  simpa [bd, LinearMap.BilinForm.apply_dualBasis_left, mul_comm] using ht

section Highest

open LieAlgebra.IsKilling

variable (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

private structure RootPair (α : H.root) where
  e : L
  f : L
  triple : IsSl2Triple (coroot α.val : L) e f
  he : e ∈ rootSpace H α.val
  hf : f ∈ rootSpace H (-α.val)

private def rootPair (α : H.root) : RootPair H α := Classical.choice <| by
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨h, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have h := t.h_eq_coroot hα he hf
  exact ⟨⟨e, f, h ▸ t, he, hf⟩⟩

private def pairScale (α : H.root) := killingForm ℂ L (rootPair H α).e (rootPair H α).f

private theorem pairScale_ne_zero (α : H.root) : pairScale H α ≠ 0 := by
  let P := rootPair H α
  have h := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg P.he P.hf
  change ⁅P.e, P.f⁆ = pairScale H α • _ at h
  intro hzero
  apply P.triple.h_ne_zero
  rw [← P.triple.lie_e_f, h, hzero, zero_smul]

omit [FiniteDimensional ℂ L] [LieAlgebra.IsKilling ℂ L] [H.IsCartanSubalgebra] in
private theorem killing_vanish_of_weights {a b : H → ℂ} {v w : L}
    (ha : ∀ s : H, ⁅(s : L), v⁆ = a s • v) (hb : ∀ s : H, ⁅(s : L), w⁆ = b s • w)
    (hab : ∃ s : H, a s + b s ≠ 0) : killingForm ℂ L v w = 0 := by
  obtain ⟨s, hs⟩ := hab
  have h := traceForm_apply_lie_apply' ℂ L L (s : L) v w
  change killingForm ℂ L ⁅(s : L), v⁆ w = -killingForm ℂ L v ⁅(s : L), w⁆ at h
  rw [ha, hb, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact (mul_eq_zero.mp (show (a s + b s) * killingForm ℂ L v w = 0 by linear_combination h)).resolve_left hs

private theorem zero_lie_cartan (x y : H) : ⁅(x : L), (y : L)⁆ = 0 :=
  congrArg Subtype.val (trivial_lie_zero H H x y)

private theorem root_eigen {a : H → ℂ} {v : L} (hv : v ∈ rootSpace H a) (s : H) :
    ⁅(s : L), v⁆ = a s • v := lie_eq_smul_of_mem_rootSpace hv s

private theorem rootpair_orthogonal (α β : H.root) (hne : β ≠ α) {y : L}
    (hy : y ∈ rootSpace H β.val) : killingForm ℂ L (rootPair H α).f y = 0 := by
  apply killing_vanish_of_weights H (root_eigen H (rootPair H α).hf) (root_eigen H hy)
  by_contra! hz
  apply hne
  apply Subtype.ext
  apply Weight.ext
  intro s
  have hs := hz s
  change -α.val s + β.val s = 0 at hs
  linear_combination hs

private theorem rootpair_orthogonal_cartan (α : H.root) (y : H) :
    killingForm ℂ L (rootPair H α).f (y : L) = 0 := by
  apply killing_vanish_of_weights (b := 0) H (root_eigen H (rootPair H α).hf)
    (fun s => by simp [zero_lie_cartan])
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨x, hx⟩ : ∃ x, α.val x ≠ 0 := by simpa [Weight.IsNonZero, Weight.IsZero, funext_iff] using hα
  exact ⟨x, by simpa using hx⟩

private theorem cartan_orthogonal_root (α : H.root) (x : H) {y : L}
    (hy : y ∈ rootSpace H α.val) : killingForm ℂ L (x : L) y = 0 := by
  apply killing_vanish_of_weights (a := 0) H (fun s => by simp [zero_lie_cartan])
    (root_eigen H hy)
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨z, hz⟩ : ∃ z, α.val z ≠ 0 := by simpa [Weight.IsNonZero, Weight.IsZero, funext_iff] using hα
  exact ⟨z, by simpa using hz⟩

private def cartanDual (b : Basis ι ℂ H) :=
  (traceForm ℂ H L).dualBasis (traceForm_cartan_nondegenerate ℂ L H) b

private def cartanTensor (b : Basis ι ℂ H) : L ⊗[ℂ] L :=
  ∑ i, ((cartanDual H b i : H) : L) ⊗ₜ[ℂ] ((b i : H) : L)

private def rootTensor (α : H.root) : L ⊗[ℂ] L :=
  (pairScale H α)⁻¹ • ((rootPair H α).f ⊗ₜ[ℂ] (rootPair H α).e)

private theorem tensorEnd_rootTensor (α : H.root) (y : L) :
    tensorEnd L (rootTensor H α) y =
      ((pairScale H α)⁻¹ * killingForm ℂ L (rootPair H α).f y) • (rootPair H α).e := by
  rw [rootTensor, map_smul, LinearMap.smul_apply, ← smul_smul]
  rfl

private theorem tensorEnd_cartanTensor (b : Basis ι ℂ H) (y : L) :
    tensorEnd L (cartanTensor H b) y =
      ∑ i, killingForm ℂ L ((cartanDual H b i : H) : L) y • ((b i : H) : L) := by
  rw [cartanTensor, map_sum, LinearMap.sum_apply]
  rfl

private theorem casimir_tensor_by_roots (b : Basis ι ℂ H) :
    casimirTensor L = cartanTensor H b + ∑ α : H.root, rootTensor H α := by
  classical
  apply (tensorEnd L).injective
  rw [casimirTensor, LieModuleEquiv.apply_symm_apply, map_add, map_sum]
  let C := tensorEnd L (cartanTensor H b) + ∑ α : H.root, tensorEnd L (rootTensor H α)
  have hcart (x : H) : (x : L) = C x := by
    have hz (α : H.root) : tensorEnd L (rootTensor H α) (x : L) = 0 := by
      simp [tensorEnd_rootTensor, rootpair_orthogonal_cartan]
    change (x : L) = tensorEnd L (cartanTensor H b) x + (∑ α : H.root, tensorEnd L (rootTensor H α)) x
    rw [LinearMap.sum_apply]
    simp only [hz, Finset.sum_const_zero, add_zero, tensorEnd_cartanTensor]
    have hb : ∀ i, traceForm ℂ H L (cartanDual H b i) x = b.repr x i := by
      intro i
      have hh := LinearMap.BilinForm.apply_toDual_symm_apply
        (hB := traceForm_cartan_nondegenerate ℂ L H) (b.dualBasis i) x
      simpa only [cartanDual, LinearMap.BilinForm.dualBasis, Basis.map_apply, Basis.dualBasis_apply] using hh
    change (x : L) = ∑ i, traceForm ℂ H L (cartanDual H b i) x • ((b i : H) : L)
    simp_rw [hb, ← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, b.sum_repr]
  have hroot (β : H.root) {y : L} (hy : y ∈ rootSpace H β.val) : y = C y := by
    change y = tensorEnd L (cartanTensor H b) y + (∑ α : H.root, tensorEnd L (rootTensor H α)) y
    rw [tensorEnd_cartanTensor, LinearMap.sum_apply]
    simp only [cartan_orthogonal_root H β _ hy, zero_smul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single β (fun α _ h => by
      simp [tensorEnd_rootTensor, rootpair_orthogonal H α β h.symm hy]) (by simp)]
    let P := rootPair H β
    have hβ : β.val.IsNonZero := (Finset.mem_filter.mp β.property).2
    have hd := finrank_rootSpace_eq_one _ hβ
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨P.e, P.he⟩ : rootSpace H β.val)
      (by simpa using P.triple.e_ne_zero)).mp hd ⟨y, hy⟩
    have hay : a • P.e = y := congrArg Subtype.val ha
    rw [← hay, map_smul, tensorEnd_rootTensor]
    rw [show killingForm ℂ L P.f P.e = pairScale H β from (traceForm_isSymm ℂ L L).eq ..]
    simp [pairScale_ne_zero, P]
  apply LinearMap.ext
  intro x
  have hx : x ∈ ⨆ χ : H → ℂ, genWeightSpace L χ := by rw [iSup_genWeightSpace_eq_top]; trivial
  change x = C x
  induction hx using LieSubmodule.iSup_induction' with
  | mem χ y hy =>
    by_cases hχ : χ = 0
    · change y ∈ rootSpace H χ at hy
      exact hcart ⟨y, by simpa only [hχ, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hy⟩
    · by_cases hspace : genWeightSpace L χ = ⊥
      · have hy0 : y = 0 := by simpa [hspace] using hy
        simp [hy0]
      · exact hroot ⟨⟨χ, hspace⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hχ⟩⟩ hy
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, ← hx, ← hy]

end Highest

end

end CubicAnomaly.Classification.ExceptionalSieveCasimir
