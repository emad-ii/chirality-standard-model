import CubicAnomaly.Classification.ClassicalConstituents
import CubicAnomaly.Classification.ExceptionalSieveWeights

/-!
# Highest weights inside the classical ambient algebras

Fix a Cartan and a base of the actual complex root system. For a module
with a nondegenerate invariant symmetric or alternating form, the
highest vectors constructed in the tensor square give operators in the
actual form-preserving algebra. Every positive root space kills these
operators. The weight and its bounded simple labels are constructed
from the given defining module.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentWeights

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open CubicAnomaly.Classification.ClassicalConstituents
open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [FiniteDimensional ℂ M]

/-- A nonzero form-preserving operator of the specified Cartan weight,
annihilated under commutator by every positive root space. -/
def HasSkewHighestWeight (b : (rootSystem H).Base) (β : LinearMap.BilinForm ℂ M)
    (μ : H → ℂ) : Prop :=
  ∃ A : Module.End ℂ M, A ∈ skewAdjointLieSubalgebra β ∧ A ≠ 0 ∧
    (∀ x : H, ⁅(x : L), A⁆ = μ x • A) ∧
    ∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, A⁆ = 0

private theorem scalar_of_root {i : H.root} {v w : L}
    (hv : v ∈ rootSpace H i.val) (hv₀ : v ≠ 0) (hw : w ∈ rootSpace H i.val) :
    ∃ c : ℂ, c • v = w := by
  exact (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : rootSpace H i.val) (by simpa using hv₀)).mp
    (finrank_rootSpace_eq_one i.val (Finset.mem_filter.mp i.property).2) ⟨w, hw⟩ |>.imp
      fun c hc => congrArg Subtype.val hc

private theorem simple_roots_commute_opposite (b : (rootSystem H).Base)
    (i j : b.support) (hji : j ≠ i) {x f : L}
    (hx : x ∈ rootSpace H j.val.val) (hf : f ∈ rootSpace H (-i.val.val)) :
    ⁅x, f⁆ = 0 := by
  let δ := (j.val.val : H → ℂ) - i.val.val
  have hδ : δ ≠ 0 := by
    intro hz
    apply hji
    apply Subtype.ext
    apply Subtype.ext
    exact Weight.ext (congrFun (sub_eq_zero.mp hz))
  have hx' : ⁅x, f⁆ ∈ rootSpace H δ := by
    simpa only [δ, sub_eq_add_neg, Weight.coe_neg] using
      lie_mem_genWeightSpace_of_mem_genWeightSpace hx hf
  by_contra hne
  have hspace : rootSpace H δ ≠ ⊥ := fun hz => hne (by simpa [hz] using hx')
  let γ : H.root := ⟨⟨δ, hspace⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hδ⟩⟩
  exact b.sub_notMem_range_root j.property i.property ⟨γ, LinearMap.ext (fun _ => rfl)⟩

omit [FiniteDimensional ℂ M] in
private theorem kill_positive_of_kill_simple (b : (rootSystem H).Base) {w : M}
    (hs : ∀ i : b.support, ∀ x ∈ rootSpace H i.val.val, ⁅x, w⁆ = 0)
    (k : H.root) (hk : b.IsPos k) : ∀ x ∈ rootSpace H k.val, ⁅x, w⁆ = 0 := by
  refine hk.induction_on_add (p := fun i => ∀ x ∈ rootSpace H i.val, ⁅x, w⁆ = 0)
    (fun i hi => hs ⟨i, hi⟩) ?_
  intro i j k hroot hi hj x hx
  have hsum : (k.val : H → ℂ) = (i.val : H → ℂ) + j.val := funext (LinearMap.congr_fun hroot)
  have hrootspace : rootSpace H ((i.val : H → ℂ) + j.val) ≠ ⊥ := hsum ▸ k.val.genWeightSpace_ne_bot
  obtain ⟨u, hu, v, hv, huv⟩ := RootBracket.exists_nonzero_root_bracket i.val j.val
    (Finset.mem_filter.mp i.property).2 hrootspace
  have hmem : ⁅u, v⁆ ∈ rootSpace H k.val := hsum ▸ lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv
  obtain ⟨c, rfl⟩ := scalar_of_root H hmem huv hx
  rw [smul_lie, lie_lie, hi _ hu, hs ⟨j, hj⟩ _ hv, lie_zero, lie_zero, sub_self, smul_zero]

private theorem transport_skew_highest (b : (rootSystem H).Base) (β : LinearMap.BilinForm ℂ M)
    (hβ : β.Nondegenerate) (hInv : β.lieInvariant L) (ε : ℂ) (h₀ : ε ≠ 0)
    (hε : ∀ a b, β a b = ε * β b a) (μ : H → ℂ) (z : M ⊗[ℂ] M)
    (hz : z ≠ 0) (hflip : TensorProduct.comm ℂ M M z = -ε • z)
    (hμ : ∀ x : H, ⁅(x : L), z⁆ = μ x • z)
    (hs : ∀ i : b.support, ∀ x ∈ rootSpace H i.val.val, ⁅x, z⁆ = 0) :
    HasSkewHighestWeight H b β μ := by
  let E := formTensorEndEquiv β hβ hInv
  refine ⟨E z, (form_tensor_mem_skew_adjoint_iff β hβ hInv ε h₀ hε z).mpr hflip,
    fun hz' => hz (E.injective ((map_zero E).symm ▸ hz')), ?_, ?_⟩
  · intro x
    exact (E.map_lie (x : L) z).symm.trans (by rw [hμ, map_smul]; rfl)
  · intro α hα x hx
    exact (E.map_lie x z).symm.trans (by
      rw [kill_positive_of_kill_simple H b hs α hα x hx, map_zero])

variable [Nontrivial M]

/-- An alternating defining form places weight twice the actual highest
weight in its symplectic algebra. -/
theorem symplectic_cartan_square_weight (b : (rootSystem H).Base)
    (β : LinearMap.BilinForm ℂ M) (hβ : β.Nondegenerate) (hInv : β.lieInvariant L)
    (ha : β.IsAlt) :
    ∃ (χ : Weight ℂ H M) (v : M), v ≠ 0 ∧ (∀ x : H, ⁅x, v⁆ = χ x • v) ∧
      (∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, v⁆ = 0) ∧
      HasSkewHighestWeight H b β (fun x => 2 * χ x) := by
  obtain ⟨χ, v, _, hv, hχ, hpos, _⟩ :=
    ExceptionalSieveWeights.exists_bounded_dominant_highest_weight (M := M) H b
  obtain ⟨hz, hflip, hw, he⟩ := symmetric_square_highest_vector (K := ℂ) (L := L) v hv
  refine ⟨χ, v, hv, hχ, hpos,
    transport_skew_highest H b β hβ hInv (-1) (by norm_num)
      (fun u w => by simpa using (ha.neg_eq w u).symm) _ _ hz (by simp)
      (fun x => hw x _ (hχ x)) ?_⟩
  intro i x hx
  exact he x (hpos _ (RootPairing.Base.isPos_of_mem_support i.property) x hx)

/-- At every positive simple label the orthogonal algebra contains a highest
vector of weight `2λ-αᵢ`. A label at least three gives another at
`2λ-3αᵢ`, for the same actual highest weight and root-system base. -/
theorem orthogonal_support_weights (b : (rootSystem H).Base)
    (β : LinearMap.BilinForm ℂ M) (hβ : β.Nondegenerate) (hInv : β.lieInvariant L)
    (hsym : β.IsSymm) :
    ∃ (χ : Weight ℂ H M) (v : M) (a : b.support → Fin (finrank ℂ M)), v ≠ 0 ∧
      (∀ x : H, ⁅x, v⁆ = χ x • v) ∧
      (∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, v⁆ = 0) ∧
      ∀ i : b.support, χ (coroot i.val.val) = ((a i : ℕ) : ℂ) ∧
        (1 ≤ (a i : ℕ) → HasSkewHighestWeight H b β (fun x => 2 * χ x - i.val.val x)) ∧
        (3 ≤ (a i : ℕ) → HasSkewHighestWeight H b β (fun x => 2 * χ x - 3 * i.val.val x)) := by
  obtain ⟨χ, v, a, hv, hw, hp, hc⟩ :=
    ExceptionalSieveWeights.exists_bounded_dominant_highest_weight (M := M) H b
  refine ⟨χ, v, a, hv, hw, hp, ?_⟩
  intro i
  have hi := (Finset.mem_filter.mp i.val.property).2
  obtain ⟨s, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hi
  obtain rfl := t.h_eq_coroot hi he hf
  have P : t.HasPrimitiveVectorWith v ((a i : ℕ) : ℂ) :=
    ⟨hv, hc i ▸ hw _, hp _ (RootPairing.Base.isPos_of_mem_support i.property) e he⟩
  have hfw (x : H) : ⁅(x : L), f⁆ = -(i.val.val x • f) := by
    simpa only [Weight.coe_neg, Pi.neg_apply, neg_smul] using lie_eq_smul_of_mem_rootSpace hf x
  have hkill (z : M ⊗[ℂ] M) (hz : ⁅e, z⁆ = 0)
      (hother : ∀ x : L, ⁅x, v⁆ = 0 → ⁅x, f⁆ = 0 → ⁅x, z⁆ = 0)
      (j : b.support) (x : L) (hx : x ∈ rootSpace H j.val.val) : ⁅x, z⁆ = 0 := by
    by_cases hji : j = i
    · subst j
      obtain ⟨c, rfl⟩ := scalar_of_root H he t.e_ne_zero hx
      rw [smul_lie, hz, smul_zero]
    · exact hother x (hp _ (RootPairing.Base.isPos_of_mem_support j.property) x hx)
        (simple_roots_commute_opposite H b i j hji hx hf)
  have hε (u w : M) : β u w = (1 : ℂ) * β w u := by simpa using hsym.eq u w
  refine ⟨hc i, ?_, ?_⟩
  · intro h
    obtain ⟨hz, hflip, hez, hwz, hother⟩ := alternating_square_first_highest_vector P h
    exact transport_skew_highest H b β hβ hInv 1 one_ne_zero hε _ _ hz (by simpa using hflip)
      (fun x => hwz x _ _ (hw x) (hfw x)) (hkill _ hez hother)
  · intro h
    obtain ⟨hz, hflip, hez, hwz, hother⟩ := alternating_square_third_highest_vector P h
    exact transport_skew_highest H b β hβ hInv 1 one_ne_zero hε _ _ hz (by simpa using hflip)
      (fun x => hwz x _ _ (hw x) (hfw x)) (hkill _ hez hother)

end CubicAnomaly.Classification.ClassicalConstituentWeights
