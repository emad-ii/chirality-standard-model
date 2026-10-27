import CubicAnomaly.Classification.CubicRadical
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Tactic.LinearCombination

/-!
# Detecting the full cubic radical on a Cartan subalgebra

For an invariant symmetric trilinear form, a Cartan element belongs to the
full mixed radical if and only if all its remaining Cartan insertions vanish.
The proof uses root spaces and invariance directly, without the general
Chevalley restriction theorem or a classification of simple Lie algebras.
-/

namespace CubicAnomaly.Classification.CartanCubic

open LieAlgebra LieModule Matrix
open CubicAnomaly.Classification.CubicRadical

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- Adjacent transpositions express full symmetry of the cubic. -/
def IsSymmetric (c : TrilinearForm (R := K) (L := L) (S := K)) : Prop :=
  (∀ x y z, c x y z = c y x z) ∧ (∀ x y z, c x y z = c x z y)

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem cyclic
    (c : TrilinearForm (R := K) (L := L) (S := K)) (hs : IsSymmetric c)
    (x y z : L) : c x y z = c z x y := by
  rw [hs.2, hs.1]

omit [CharZero K] [IsTriangularizable K H L] in
private theorem cartan_lie_zero (x y : H) : ⁅(x : L), (y : L)⁆ = 0 := by
  change (⁅x, y⁆ : H).val = 0
  rw [trivial_lie_zero]
  rfl

private theorem root_lie {α : H → K} {y : L} (hy : y ∈ rootSpace H α) (s : H) :
    ⁅(s : L), y⁆ = α s • y := by
  exact IsKilling.lie_eq_smul_of_mem_rootSpace hy s

private theorem cartan_cubic_root_pair_zero
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c)
    (x : H) (hx : ∀ u v : H, c x u v = 0)
    {α β : H → K} {y z : L}
    (hy : y ∈ rootSpace H α) (hz : z ∈ rootSpace H β) : c x y z = 0 := by
  by_cases hab : α + β = 0
  · by_cases ha : α = 0
    · have hb : β = 0 := by simpa [ha] using hab
      have hyH : y ∈ H := by
        simpa only [ha, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hy
      have hzH : z ∈ H := by
        simpa only [hb, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hz
      exact hx ⟨y, hyH⟩ ⟨z, hzH⟩
    · obtain ⟨t, ht⟩ := Function.ne_iff.mp ha
      have ht' : α t ≠ 0 := ht
      have hyz : ⁅y, z⁆ ∈ H := by
        have hh := mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α β hy hz
        simpa only [hab, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hh
      have rel (s : H) : α s * c x y z + α x * c s y z = 0 := by
        have h := hc y s z x
        have hys : ⁅y, (s : L)⁆ = -(α s) • y := by
          rw [← lie_skew, root_lie H hy s, neg_smul]
        have hyx : ⁅y, (x : L)⁆ = -(α x) • y := by
          rw [← lie_skew, root_lie H hy x, neg_smul]
        have hmid : c s ⁅y, z⁆ x = 0 := by
          rw [cyclic c hs]
          exact hx s ⟨⁅y, z⁆, hyz⟩
        rw [hys, hyx, hmid] at h
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, add_zero] at h
        rw [cyclic c hs y z x, hs.2 s z y] at h
        linear_combination -h
      by_cases hax : α x = 0
      · have h := rel t
        rw [hax, zero_mul, add_zero] at h
        exact (mul_eq_zero.mp h).resolve_left ht'
      · have h : (2 : K) * (α x * c x y z) = 0 := by
          linear_combination rel x
        exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))).resolve_left hax
  · obtain ⟨t, ht⟩ := Function.ne_iff.mp hab
    have ht' : α t + β t ≠ 0 := ht
    have h := hc t x y z
    rw [cartan_lie_zero H t x, root_lie H hy t, root_lie H hz t] at h
    simp only [map_zero, LinearMap.zero_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, zero_add] at h
    have h' : (α t + β t) * c x y z = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left ht'

/-- A Cartan element is in the full radical exactly when the cubic vanishes
on all its Cartan insertions. Both non-Cartan slots are discharged by roots. -/
theorem cartan_mem_radical_iff
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) (x : H) :
    (x : L) ∈ radical c hc ↔ ∀ u v : H, c x u v = 0 := by
  rw [mem_radical_iff]
  constructor
  · intro h u v
    exact h u v
  · intro hx y z
    have hy : y ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    have hz : z ∈ ⨆ β : H → K, rootSpace H β := by simp [iSup_genWeightSpace_eq_top]
    induction hy using LieSubmodule.iSup_induction' with
    | mem α y hy =>
      induction hz using LieSubmodule.iSup_induction' with
      | mem β z hz => exact cartan_cubic_root_pair_zero H c hc hs x hx hy hz
      | zero => simp
      | add z w _ _ hz hw => simp [map_add, hz, hw]
    | zero => simp
    | add y w _ _ hy hw => simp [map_add, hy, hw]

/-- The remaining Cartan insertions can be tested on any Cartan basis. -/
theorem cartan_mem_radical_iff_basis {ι : Type*} (b : Module.Basis ι K H)
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) (x : H) :
    (x : L) ∈ radical c hc ↔ ∀ i j, c x (b i) (b j) = 0 := by
  rw [cartan_mem_radical_iff H c hc hs x]
  constructor
  · intro h i j
    exact h (b i) (b j)
  · intro h y z
    let d : LinearMap.BilinForm K H := LinearMap.BilinForm.restrict (c x) H.toSubmodule
    have hd : d = 0 := b.ext fun i => b.ext fun j => h i j
    exact congrArg (fun f : LinearMap.BilinForm K H => f y z) hd

section AlgebraicallyClosed

variable [IsAlgClosed K]

/-- In a splitting Lie algebra with nondegenerate Killing form, an ideal is
determined by its intersection with a Cartan subalgebra. -/
theorem ideal_le_of_cartan_intersection_le (I J : LieIdeal K L)
    (hIJ : ∀ x : H, (x : L) ∈ I → (x : L) ∈ J) : I ≤ J := by
  intro x hx
  suffices hall : ∀ y : I, (y : L) ∈ J from hall ⟨x, hx⟩
  intro xI
  have hxI : xI ∈ ⨆ α : H → K, genWeightSpace I α := by
    simp [iSup_genWeightSpace_eq_top]
  induction hxI using LieSubmodule.iSup_induction' with
  | mem α x hx =>
    have hr : (x : L) ∈ rootSpace H α :=
      map_genWeightSpace_le ((LieSubmodule.incl I).restrictLie H)
        ((LieSubmodule.mem_map _).mpr ⟨x, hx, rfl⟩)
    by_cases ha : α = 0
    · have hxH : (x : L) ∈ H := by
        simpa only [ha, rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule] using hr
      exact hIJ ⟨x, hxH⟩ x.property
    · by_cases hx0 : (x : L) = 0
      · simp [hx0]
      let a : Weight K H L := ⟨α, by
        intro hbot
        exact hx0 (by simpa only [hbot, LieSubmodule.mem_bot] using hr)⟩
      have ha' : a.IsNonZero := ha
      obtain ⟨f, hf, hxf⟩ : ∃ f ∈ rootSpace H (-α), killingForm K L (x : L) f ≠ 0 := by
        by_contra h
        push_neg at h
        have hker := mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H hr h
        exact hx0 (by simpa using hker)
      have hbr := IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
        (H := H) (α := a) hr hf
      let t : H := killingForm K L (x : L) f • (IsKilling.cartanEquivDual H).symm a
      have ht : (t : L) = ⁅(x : L), f⁆ := hbr.symm
      have htI : (t : L) ∈ I := by
        rw [ht]
        exact lie_mem_left K L I x f x.property
      have htJ : (t : L) ∈ J := hIJ t htI
      have hat : α t ≠ 0 := by
        change a (killingForm K L (x : L) f • (IsKilling.cartanEquivDual H).symm a) ≠ 0
        rw [map_smul, smul_eq_mul]
        exact mul_ne_zero hxf (IsKilling.root_apply_cartanEquivDual_symm_ne_zero ha')
      have htx : α t • (x : L) ∈ J := by
        rw [← root_lie H hr t]
        exact lie_mem_left K L J t x htJ
      exact (J.toSubmodule.smul_mem_iff hat).mp htx
  | zero => exact J.zero_mem
  | add x y _ _ hx hy => exact J.add_mem hx hy

/-- Full ideal membership in the cubic radical is detected using only
Cartan insertions. This is the bridge used by finite Cartan cubic tests. -/
theorem ideal_le_radical_iff_cartan
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) (I : LieIdeal K L) :
    I ≤ radical c hc ↔
      ∀ x : H, (x : L) ∈ I → ∀ y z : H, c x y z = 0 := by
  constructor
  · intro h x hx
    exact (cartan_mem_radical_iff H c hc hs x).mp (h hx)
  · intro h
    exact ideal_le_of_cartan_intersection_le H I (radical c hc)
      (fun x hx => (cartan_mem_radical_iff H c hc hs x).mpr (h x hx))

/-- An invariant symmetric cubic is determined by its Cartan restriction. -/
theorem invariant_cubic_eq_zero_of_cartan
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c)
    (hH : ∀ x y z : H, c x y z = 0) : c = 0 := by
  have htop : (⊤ : LieIdeal K L) ≤ radical c hc :=
    (ideal_le_radical_iff_cartan H c hc hs ⊤).mpr (fun x _ => hH x)
  ext x y z
  exact (mem_radical_iff c hc x).mp (htop (LieSubmodule.mem_top x)) y z

/-- A nonzero full radical is detected by a nonzero Cartan vector. -/
theorem radical_ne_bot_iff_cartan
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) :
    radical c hc ≠ ⊥ ↔ ∃ x : H, x ≠ 0 ∧ ∀ y z : H, c x y z = 0 := by
  constructor
  · intro hrad
    by_contra h
    push_neg at h
    have hle : radical c hc ≤ ⊥ :=
      ideal_le_of_cartan_intersection_le H (radical c hc) ⊥ (by
        intro x hx
        have hx0 : x = 0 := by
          by_contra hne
          obtain ⟨y, z, hyz⟩ := h x hne
          exact hyz ((cartan_mem_radical_iff H c hc hs x).mp hx y z)
        simp [hx0])
    exact hrad (le_antisymm hle bot_le)
  · rintro ⟨x, hx, hzero⟩ hrad
    have hmem := (cartan_mem_radical_iff H c hc hs x).mpr hzero
    rw [hrad, LieSubmodule.mem_bot] at hmem
    exact hx (Subtype.ext hmem)

/-- Finite Cartan-basis tests detect the full radical, including mixed terms. -/
theorem radical_ne_bot_iff_cartan_basis {ι : Type*} (b : Module.Basis ι K H)
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) :
    radical c hc ≠ ⊥ ↔ ∃ x : H, x ≠ 0 ∧ ∀ i j, c x (b i) (b j) = 0 := by
  rw [radical_ne_bot_iff_cartan H c hc hs]
  apply exists_congr
  intro x
  rw [← cartan_mem_radical_iff H c hc hs x, cartan_mem_radical_iff_basis H b c hc hs x]

/-- Flatten the last two slots of the Cartan restriction into a matrix.
Its ordinary linear kernel detects the full Lie-ideal radical. -/
noncomputable def cartanCubicMatrix {ι : Type*} (b : Module.Basis ι K H)
    (c : TrilinearForm (R := K) (L := L) (S := K)) : Matrix (ι × ι) ι K :=
  fun jk i => c (b i) (b jk.1) (b jk.2)

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [H.IsCartanSubalgebra] [IsTriangularizable K H L] [IsAlgClosed K] in
/-- The Cartan tensor matrix is the coordinate matrix of first-slot contraction. -/
theorem cartan_cubic_matrix_mulVec {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K H) (c : TrilinearForm (R := K) (L := L) (S := K))
    (v : ι → K) (j k : ι) :
    (cartanCubicMatrix H b c *ᵥ v) (j, k) = c (b.equivFun.symm v) (b j) (b k) := by
  rw [Module.Basis.equivFun_symm_apply]
  change (cartanCubicMatrix H b c *ᵥ v) (j, k) =
    c (H.incl (∑ i, v i • b i)) (b j) (b k)
  simp only [cartanCubicMatrix, Matrix.mulVec, dotProduct,
    map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The full cubic radical is nonzero exactly when the finite Cartan tensor
matrix has a nonzero kernel vector. No classification of invariant polynomials
or simple factors is required. -/
theorem radical_ne_bot_iff_cartan_matrix_kernel {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K H) (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c) :
    radical c hc ≠ ⊥ ↔
      ∃ v : ι → K, v ≠ 0 ∧ cartanCubicMatrix H b c *ᵥ v = 0 := by
  rw [radical_ne_bot_iff_cartan_basis H b c hc hs]
  constructor
  · rintro ⟨x, hx, hzero⟩
    refine ⟨b.equivFun x, fun hz => hx (b.equivFun.injective (by simpa using hz)), ?_⟩
    funext ⟨j, k⟩
    simpa only [cartan_cubic_matrix_mulVec, b.equivFun.symm_apply_apply, Pi.zero_apply]
      using hzero j k
  · rintro ⟨v, hv, hzero⟩
    refine ⟨b.equivFun.symm v, fun hx => hv (b.equivFun.symm.injective (by simpa using hx)), ?_⟩
    intro j k
    have h := congrFun hzero (j, k)
    simpa only [cartan_cubic_matrix_mulVec, Pi.zero_apply] using h

end AlgebraicallyClosed

end CubicAnomaly.Classification.CartanCubic
