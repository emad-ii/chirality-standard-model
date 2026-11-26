import CubicAnomaly.Classification.ChevalleySimpleTriples

/-!
# Transport of Cartan roots and coroots by an actual Lie equivalence

Compatibility on the Cartan subalgebras carries every root eigenvector
to an eigenvector with the pulled-back weight. The image of its normalized
root triple identifies the coroot in the target.
-/

namespace CubicAnomaly.Classification.ChevalleyRootTransport

open LieAlgebra LieModule Module LieAlgebra.IsKilling

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [LieRing M] [LieAlgebra K M] [FiniteDimensional K M] [LieAlgebra.IsKilling K M]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (J : LieSubalgebra K M) [J.IsCartanSubalgebra] [IsTriangularizable K J M]
  (Φ : L ≃ₗ⁅K⁆ M) (T : H ≃ₗ[K] J) (hT : ∀ t : H, Φ t.val = (T t).val)

include hT

omit [FiniteDimensional K M] [IsKilling K M] [IsTriangularizable K J M] in
private theorem transport_mem {a : H → K} {b : J → K} (hb : ∀ t : H, b (T t) = a t)
    {x : L} (hx : x ∈ rootSpace H a) : Φ x ∈ rootSpace J b := by
  apply weightSpace_le_genWeightSpace
  apply (mem_weightSpace _ _).mpr
  intro z
  obtain ⟨t, rfl⟩ := T.surjective z
  change ⁅(T t).val, Φ x⁆ = b (T t) • Φ x
  rw [← hT, ← Φ.map_lie, hb, ← map_smul Φ]
  exact congrArg Φ (lie_eq_smul_of_mem_rootSpace hx t)

private theorem transport_mem_iff {a : H → K} {b : J → K} (hb : ∀ t : H, b (T t) = a t)
    (x : L) : Φ x ∈ rootSpace J b ↔ x ∈ rootSpace H a := by
  refine ⟨fun hx => ?_, transport_mem H J Φ T hT hb⟩
  have hsym (t : J) : Φ.symm t.val = (T.symm t).val := by
    apply Φ.injective
    change Φ (Φ.symm t.val) = Φ (T.symm t).val
    rw [Φ.apply_symm_apply, hT, T.apply_symm_apply]
  have h := transport_mem J H Φ.symm T.symm hsym (fun t =>
    (hb (T.symm t)).symm.trans (congrArg b (T.apply_symm_apply t))) hx
  simpa only [Φ.symm_apply_apply] using h

/-- A match of Cartans transports both opposite root spaces, their weights on
all Cartan elements, and the distinguished coroot. -/
theorem exists_root_transport (α : H.root) :
    ∃ β : J.root, (∀ z : J, β.val z = α.val (T.symm z)) ∧
      (∀ x : L, Φ x ∈ rootSpace J β.val ↔ x ∈ rootSpace H α.val) ∧
      (∀ x : L, Φ x ∈ rootSpace J (-(β.val : J → K)) ↔ x ∈ rootSpace H (-(α.val : H → K))) ∧
      Φ (coroot α.val : L) = (coroot β.val : M) := by
  let a (z : J) := α.val (T.symm z)
  have ha (t : H) : a (T t) = α.val t := congrArg α.val (T.symm_apply_apply t)
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  have ha₀ : a ≠ 0 := by
    intro h
    exact hα (funext fun t => (ha t).symm.trans (congrFun h (T t)))
  obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := ht.h_eq_coroot hα he hf
  have he' := transport_mem H J Φ T hT ha he
  have hn : rootSpace J a ≠ ⊥ := by
    intro hz
    rw [hz, LieSubmodule.mem_bot] at he'
    exact ht.e_ne_zero (Φ.injective (he'.trans (map_zero Φ).symm))
  let β : J.root := ⟨Weight.mk a hn, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₀⟩⟩
  have hpos (x : L) := transport_mem_iff H J Φ T hT ha x
  have hneg (x : L) := transport_mem_iff H J Φ T hT
    (a := -(α.val : H → K)) (b := -a) (fun t => congrArg Neg.neg (ha t)) x
  refine ⟨β, fun _ => rfl, hpos, hneg, ?_⟩
  have ht' : IsSl2Triple (Φ (coroot α.val : L)) (Φ e) (Φ f) := {
    h_ne_zero := fun hz => ht.h_ne_zero (Φ.injective (hz.trans (map_zero Φ).symm))
    lie_e_f := by rw [← Φ.map_lie, ht.lie_e_f]
    lie_h_e_nsmul := by rw [← Φ.map_lie, ht.lie_h_e_nsmul, map_nsmul]
    lie_h_f_nsmul := by rw [← Φ.map_lie, ht.lie_h_f_nsmul, map_neg, map_nsmul] }
  exact ht'.h_eq_coroot (α := β.val) ha₀ he' ((hneg f).mpr hf)

end CubicAnomaly.Classification.ChevalleyRootTransport
