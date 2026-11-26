import CubicAnomaly.Classification.ClassicalConstituentChamber
import CubicAnomaly.Classification.ClassicalConstituentOpposition
import CubicAnomaly.Classification.ClassicalConstituentCompact
import CubicAnomaly.Classification.ClassicalSimplicity

/-!
# Fixed and exchanged support in the orthogonal defining module

Under Weyl opposition the defining module and the adjoint are self-dual,
while the two actual quotient halves are dual and inequivalent. The
first-lowering constituent for a fixed support node is therefore adjoint.
All nonfixed support nodes form at most one exchanged pair.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentOrthogonal

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ClassicalConstituentHighest ClassicalConstituentWeyl ClassicalConstituentChamber
open ClassicalConstituentCompact ClassicalConstituentComparison ClassicalConstituentOpposition
open ClassicalConstituentWeights CompactOperatorModel Structural ComplexDuality SelfDualAbsorption Complexification
open scoped TensorProduct

variable {L V : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] [IsIrreducible ℂ L V]

private theorem fixed_highest_of_self_dual (w : List H.root)
    (hw : ∀ i : H.root, b.IsPos i ↔ ¬ b.IsPos (rootWord H w i))
    (d : Nonempty (V ≃ₗ⁅ℂ,L⁆ Dual ℂ V)) {μ : H → ℂ} {v : V}
    (hv : IsHighestVector H b μ v) : ∀ z : H, μ z = -μ (cartanWord H w z) := by
  obtain ⟨E⟩ := d
  have he := highest_map H E.toLieModuleHom hv
    (fun h => hv.1 (E.injective (h.trans (map_zero E).symm)))
  exact dual_highest_weight_of_reversing_word H b w hw hv he

section Model

variable {g W : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)] [IsSimple ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    [AddCommGroup W] [Module ℂ W] [LieRingModule (ℂ ⊗[ℝ] h) W]
    [LieModule ℂ (ℂ ⊗[ℝ] h) W] [FiniteDimensional ℂ W] [IsIrreducible ℂ (ℂ ⊗[ℝ] h) W]

/-- Highest weight, natural simple labels, adjoint highest weight, and the
action of opposition on all nonzero labels of the orthogonal module. -/
def OrthogonalSupportOrbit : Prop :=
    ∃ (χ : Weight ℂ H W) (v : W) (a : b.support → Fin (finrank ℂ W))
        (θ : H → ℂ) (w : List H.root) (δ : Equiv.Perm b.support),
      IsHighestVector H b χ v ∧ (∃ y : ℂ ⊗[ℝ] h, IsHighestVector H b θ y) ∧
      (∃ r : H.root, (r.val : H → ℂ) = θ ∧ b.IsPos r ∧ ∀ j : H.root, b.height j ≤ b.height r) ∧
      (∀ i : b.support, χ (coroot i.val.val) = ((a i : ℕ) : ℂ) ∧
        a (δ i) = a i ∧ (∀ z : H, (δ i).val.val z = -i.val.val (cartanWord H w z)) ∧
        (1 ≤ (a i : ℕ) → ((fun z => 2 * χ z - i.val.val z) = θ ↔ δ i = i)) ∧
        (δ i ≠ i → (a i : ℕ) ≤ 2)) ∧
      (∀ i j : b.support, 1 ≤ (a i : ℕ) → δ i ≠ i → 1 ≤ (a j : ℕ) → δ j ≠ j →
        j = i ∨ j = δ i)

include hp e in
set_option maxHeartbeats 1500000 in
/-- The actual node permutation fixes precisely the supported
first-lowering weights that are adjoint. Every two nonfixed supported
nodes are either the same node or its opposite. -/
theorem orthogonal_model_opposition_support (β : LinearMap.BilinForm ℂ W) (A : Model h β)
    (hnd : β.Nondegenerate) (hi : β.lieInvariant (ℂ ⊗[ℝ] h)) (hsym : β.IsSymm) :
    OrthogonalSupportOrbit (W := W) h H b := by
  letI := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) W
  obtain ⟨w, hw⟩ := exists_reversing_word H b
  obtain ⟨δ, hδ⟩ := exists_opposition_nodes H b w hw
  obtain ⟨χ, v, a, hv, hc, hk, hlabels⟩ := orthogonal_support_weights H b β hnd hi hsym
  have hv' : IsHighestVector H b χ v := ⟨hv, hc, hk⟩
  obtain ⟨θ, p, q, ⟨y, hy⟩, ⟨s, hs⟩, ⟨t, ht⟩, hall⟩ := compact_model_highest_weights B h hp e H b A
  let P := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let Q := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I)
  obtain ⟨_, hP, hQ, ⟨d⟩, hpq⟩ := compact_complement_complex_type_decomposition B h hp e
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) P := hP
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) Q := hQ
  have hpq' : p ≠ q := by
    intro he
    obtain ⟨E, _⟩ := irreducible_equiv_of_highest_weight H hs (he ▸ ht)
    exact hpq ⟨E⟩
  let O := fun (f : H → ℂ) (z : H) => -f (cartanWord H w z)
  have ho : Function.Injective O := by
    intro f g he
    funext y
    obtain ⟨z, rfl⟩ := (cartanWord H w).surjective y
    exact neg_inj.mp (congrFun he z)
  have hqp : q = O p := funext <| dual_highest_weight_of_reversing_word H b w hw hs
    (highest_map H d.toLieModuleHom ht (fun hz => ht.1 (d.injective (hz.trans (map_zero d).symm))))
  have hθ : θ = O θ := funext <| fixed_highest_of_self_dual H b w hw
    (invariant_nondegenerate_form_self_dual (killingForm ℂ (ℂ ⊗[ℝ] h))
      (traceForm_lieInvariant ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] h))
      (IsKilling.killingForm_nondegenerate ℂ (ℂ ⊗[ℝ] h))) hy
  have hχ := fixed_highest_of_self_dual H b w hw (invariant_nondegenerate_form_self_dual β hi hnd) hv'
  let shift := fun (i : b.support) (z : H) => 2 * χ z - i.val.val z
  have hshift (i : b.support) : shift (δ i) = O (shift i) := by
    funext z
    change 2 * χ z - (δ i).val.val z = -(2 * χ (cartanWord H w z) - i.val.val (cartanWord H w z))
    rw [(hδ i).1, hχ z]
    ring
  have hinj : Function.Injective shift := by
    intro i j he
    apply Subtype.ext
    apply Subtype.ext
    apply Weight.ext
    intro z
    exact sub_right_inj.mp (congrFun he z)
  have heqa (i : b.support) : a (δ i) = a i := by
    apply Fin.ext
    have hwgt := hχ (coroot (δ i).val.val)
    rw [(hδ i).2] at hwgt
    have hn : χ (-coroot i.val.val) = -χ (coroot i.val.val) := by
      apply smul_left_injective ℂ hv
      change χ (-coroot i.val.val) • v = -χ (coroot i.val.val) • v
      rw [neg_smul, ← hc, ← hc]
      change ⁅-((coroot i.val.val : H) : ℂ ⊗[ℝ] h), v⁆ = - ⁅((coroot i.val.val : H) : ℂ ⊗[ℝ] h), v⁆
      rw [neg_lie]
    rw [hn, neg_neg, (hlabels _).1, (hlabels _).1] at hwgt
    exact_mod_cast hwgt
  have hiff (i : b.support) (hpos : 1 ≤ (a i : ℕ)) : shift i = θ ↔ δ i = i := by
    constructor
    · intro hθ'
      exact hinj ((hshift i).trans (by rw [hθ', ← hθ]))
    · intro hf
      have he : shift i = O (shift i) := by simpa only [hf] using hshift i
      rcases hall _ ((hlabels i).2.1 hpos) with h | h | h
      · exact h
      · change shift i = p at h
        exact (hpq' (by rw [← h, he, hqp]; exact congrArg O h)).elim
      · change shift i = q at h
        rw [h] at he
        exact (hpq' (ho (hqp.symm.trans he))).elim
  have hside (i : b.support) (hpos : 1 ≤ (a i : ℕ)) (hne : δ i ≠ i) : shift i = p ∨ shift i = q :=
    (hall _ ((hlabels i).2.1 hpos)).resolve_left (fun h => hne ((hiff _ hpos).mp h))
  have covered (i : b.support) (hi : 1 ≤ (a i : ℕ)) (hne : δ i ≠ i) (f : H → ℂ)
      (hf : f = p ∨ f = q) : f = shift i ∨ f = shift (δ i) := by
    have hj : 1 ≤ (a (δ i) : ℕ) := heqa i ▸ hi
    have hnj : δ (δ i) ≠ δ i := fun h => hne (δ.injective h)
    have hdist : shift (δ i) ≠ shift i := fun h => hne (hinj h)
    rcases hside i hi hne with h | h <;> rcases hside (δ i) hj hnj with h' | h' <;> rcases hf with hf | hf <;>
      first | exact Or.inl (hf.trans h.symm) | exact Or.inr (hf.trans h'.symm) |
        exact (hdist (h'.trans h.symm)).elim
  have hsmall (i : b.support) (hne : δ i ≠ i) : (a i : ℕ) ≤ 2 := by
    by_contra! hbig
    let f := fun z : H => 2 * χ z - 3 * i.val.val z
    have hf : f ≠ θ := by
      intro h
      have ho' : f = O f := h ▸ hθ
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      apply Weight.ext
      intro z
      have he := congrFun ho' z
      change 2 * χ z - 3 * i.val.val z = -(2 * χ (cartanWord H w z) - 3 * i.val.val (cartanWord H w z)) at he
      rw [hχ z] at he
      rw [(hδ i).1]
      linear_combination he / 3
    have h := covered i (by omega) hne f ((hall _ ((hlabels i).2.2 (by omega))).resolve_left hf)
    obtain ⟨t, ht⟩ := ExceptionalSieveWeights.exists_height_element H b
    have ht' (i : b.support) : i.val.val t = 1 := by
      rw [ht, b.height_one_of_mem_support i.property, Int.cast_one]
    have hn (j : b.support) : f ≠ shift j := by
      intro he
      have hf' := congrFun he t
      change 2 * χ t - 3 * i.val.val t = 2 * χ t - j.val.val t at hf'
      rw [ht', ht', sub_right_inj] at hf'
      norm_num at hf'
    exact h.elim (hn i) (hn _)
  refine ⟨χ, v, a, θ, w, δ, hv', ⟨y, hy⟩, adjoint_highest_is_maximal_root H b hy,
    fun i => ⟨(hlabels i).1, heqa i, (hδ i).1, hiff i, hsmall i⟩, ?_⟩
  intro i j hi hni hj hnj
  exact (covered i hi hni _ (hside j hj hnj)).imp (fun h => hinj h) (fun h => hinj h)

end Model

section Orthogonal

open HermitianRealization OrthogonalDefining OrthogonalComplexification ClassicalModuleBridge
open ClassicalSimplicity AllRankComplex

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

set_option maxHeartbeats 1500000 in
/-- For the original compact orthogonal pair in every rank, the lowering
weight at a fixed supported node equals the adjoint highest root and
the nonfixed supported nodes form at most one exchanged pair. -/
theorem all_rank_orthogonal_opposition_support (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra] :
    letI : IsKilling ℂ (ℂ ⊗[ℝ] h) := (all_rank_complex_structural_reduction B h heff hp e hr).2.2.2.1
    ∀ b : (rootSystem H).Base, OrthogonalSupportOrbit (W := ℂ ⊗[ℝ] W) h H b := by
  letI : IsKilling ℂ (ℂ ⊗[ℝ] h) := (all_rank_complex_structural_reduction B h heff hp e hr).2.2.2.1
  letI : IsSimple ℂ (ℂ ⊗[ℝ] h) := all_rank_orthogonal_complexified_isotropy_simple B h heff hp e hr
  letI := all_rank_orthogonal_defining_complex_irreducible B h heff hp e hr
  intro b
  have hnd : (orthogonalExtendedForm (W := W)).Nondegenerate := by
    apply complexified_bilinForm_nondegenerate (innerₗ W)
    constructor <;> intro x hx <;> exact inner_self_eq_zero.mp (hx x)
  have hsym : (orthogonalExtendedForm (W := W)).IsSymm := by
    apply LinearMap.BilinForm.isSymm_iff.mpr
    exact LinearMap.BilinForm.IsSymm.baseChange ℂ (B₂ := innerₗ W) ⟨fun x y => real_inner_comm y x⟩
  exact orthogonal_model_opposition_support B h hp e H b _ (orthogonalModel h) hnd
    (orthogonal_complexified_defining_form_invariant h) hsym

end Orthogonal

end CubicAnomaly.Classification.ClassicalConstituentOrthogonal
