import CubicAnomaly.Classification.TensorFormFactorization
import CubicAnomaly.Classification.TypeACubicArithmetic
import Mathlib.Data.Fin.Rev

/-! # The cubic trace and the highest weight of a type-A representation

Contractions of the traceless matrix-unit operators commute with the Lie action.
Their eigenvalues on a highest vector can be read by moving the raising
operators past a single lowering operator.
-/

namespace CubicAnomaly.Classification.TypeACubicOperator

open Module LieModule TensorFormFactorization

noncomputable section

variable {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

private abbrev Family (N : ℕ) (M : Type*) [AddCommGroup M] [Module ℂ M] :=
  Fin N → Fin N → Module.End ℂ M

private def Covariant (F P : Family N M) : Prop :=
  ∀ a b i j, ⁅F a b, P i j⁆ = (if b = i then P a j else 0) - (if j = a then P i b else 0)

private def product (P Q : Family N M) (i j : Fin N) : Module.End ℂ M :=
  ∑ k, P i k * Q k j

private theorem bracket_mul (x y z : Module.End ℂ M) : ⁅x,y*z⁆ = ⁅x,y⁆*z + y*⁅x,z⁆ := by
  simp only [Ring.lie_def, sub_mul, mul_sub, mul_assoc]
  abel

private theorem covariant_product {F P Q : Family N M} (hP : Covariant F P)
    (hQ : Covariant F Q) : Covariant F (product P Q) := by
  intro a b i j
  unfold Covariant at hP hQ
  simp only [product, lie_sum, bracket_mul, hP, hQ, sub_mul, mul_sub,
    ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

private def contraction (P : Family N M) : Module.End ℂ M := ∑ i, P i i

private theorem covariant_contraction {F P : Family N M} (hp : Covariant F P) (a b : Fin N) :
    ⁅F a b, contraction P⁆ = 0 := by
  unfold Covariant at hp
  simp [contraction, lie_sum, hp, Finset.sum_sub_distrib]

private def cubic (F : Family N M) : Module.End ℂ M := contraction (product (product F F) F)

private theorem central {F : Family N M} (hF : Covariant F F) (i j : Fin N) :
    ⁅F i j, cubic F⁆ = 0 :=
  covariant_contraction (covariant_product (covariant_product hF hF) hF) i j

private theorem commute_at {F P : Family N M} (hP : Covariant F P)
    (i j k : Fin N) (v : M) :
    P i k (F k j v) = F k j (P i k v) -
      ((if j = i then P k k else 0) - P i j) v := by
  have h := LinearMap.congr_fun (hP k j i k) v
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, if_true] at h ⊢
  rw [← h]
  abel

private theorem product_upper {F P : Family N M} (hP : Covariant F P)
    (v : M) (hF : ∀ i j, i < j → F i j v = 0) (hu : ∀ i j, i < j → P i j v = 0) :
    ∀ i j, i < j → product P F i j v = 0 := by
  intro i j hij
  rw [product, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  change P i k (F k j v) = 0
  by_cases h : k < j
  · rw [hF k j h, map_zero]
  · rw [commute_at hP, hu i k (lt_of_lt_of_le hij (le_of_not_gt h)), map_zero,
      if_neg (ne_of_gt hij), LinearMap.sub_apply, LinearMap.zero_apply, hu i j hij]
    simp

private def diagonalStep (p u : Fin N → ℂ) (i : Fin N) : ℂ :=
  u i * p i + ∑ k, if i < k then p i - p k else 0

private theorem product_diagonal {F P : Family N M} (hP : Covariant F P)
    (v : M) (u p : Fin N → ℂ) (hd : ∀ i, F i i v = u i • v)
    (he : ∀ i, P i i v = p i • v) (hF : ∀ i j, i < j → F i j v = 0)
    (hu : ∀ i j, i < j → P i j v = 0) (i : Fin N) :
    product P F i i v = diagonalStep p u i • v := by
  rw [product, LinearMap.sum_apply, diagonalStep, add_smul, Finset.sum_smul]
  calc
    _ = ∑ k : Fin N, ((if k = i then u i * p i else 0) • v +
          (if i < k then p i - p k else 0) • v) := by
      apply Finset.sum_congr rfl
      intro k _
      change P i k (F k i v) = _
      rcases lt_trichotomy k i with h | rfl | h
      · simp [hF k i h, ne_of_lt h, not_lt_of_gt h]
      · simp [hd, he, smul_smul]
      · rw [commute_at hP, hu i k h, map_zero, if_pos rfl, LinearMap.sub_apply, he, he]
        simp [h.ne', h, sub_smul]
    _ = _ := by simp [Finset.sum_add_distrib, ite_smul]

private def second (u : Fin N → ℂ) (i : Fin N) := (u i)^2 + ∑ k, if i < k then u i - u k else 0

private def eigenvalue (u : Fin N → ℂ) : ℂ := ∑ i, diagonalStep (second u) u i

private theorem cubic_apply {F : Family N M} (hF : Covariant F F)
    (v : M) (u : Fin N → ℂ) (hd : ∀ i, F i i v = u i • v)
    (hu : ∀ i j, i < j → F i j v = 0) : cubic F v = eigenvalue u • v := by
  have hS (i : Fin N) : product F F i i v = second u i • v := by
    simpa only [diagonalStep, second, sq] using product_diagonal hF v u u hd hd hu hu i
  simp only [cubic, contraction, LinearMap.sum_apply, eigenvalue, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => product_diagonal (covariant_product hF hF) v u
    (second u) hd hS hu (product_upper hF v hu hu) i

private def opposite (F : Family N M) (i j : Fin N) : Module.End ℂ M := -F j.rev i.rev

private theorem opposite_covariant {F : Family N M} (hf : Covariant F F) :
    Covariant (opposite F) (opposite F) := by
  intro a b i j
  simp only [opposite, neg_lie, lie_neg, neg_neg, hf _ _ _ _, Fin.rev_inj]
  by_cases h : a = j
  · subst j
    by_cases w : b = i
    · subst i
      simp
      abel
    · simp [w, Ne.symm w]
  · by_cases w : b = i
    · subst i
      simp [h, Ne.symm h]
    · simp [h, Ne.symm h, w, Ne.symm w]

private theorem reverse_triple_sum (f : Fin N → Fin N → Fin N → ℂ) :
    (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, f i.rev j.rev k.rev) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    _ = ∑ i : Fin N, ∑ j : Fin N, ∑ k, f i.rev j.rev k :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Equiv.sum_comp Fin.revPerm (f i.rev j.rev)
    _ = ∑ i : Fin N, ∑ j, ∑ k, f i.rev j k := Finset.sum_congr rfl fun i _ =>
      Equiv.sum_comp Fin.revPerm (fun j => ∑ k, f i.rev j k)
    _ = _ := Equiv.sum_comp Fin.revPerm (fun i => ∑ j, ∑ k, f i j k)

private theorem trace_cubic (F : Family N M) : LinearMap.trace ℂ M (cubic F) =
    ∑ i, ∑ j, ∑ k, LinearMap.trace ℂ M (F i k * F k j * F j i) := by
  simp only [cubic, contraction, product, Finset.sum_mul, map_sum]

private theorem trace_opposite (F : Family N M) : LinearMap.trace ℂ M (cubic (opposite F)) =
    -(∑ i, ∑ j, ∑ k, LinearMap.trace ℂ M (F k j * F i k * F j i)) := by
  rw [trace_cubic]
  simp only [opposite, neg_mul, mul_neg, neg_neg, map_neg, Finset.sum_neg_distrib]
  congr 1
  rw [reverse_triple_sum (fun i j k => LinearMap.trace ℂ M (F k i * F j k * F i j))]
  exact Finset.sum_comm

private theorem trace_eq_of_cubic_zero {F : Family N M}
    (hz : ∀ i j k, LinearMap.trace ℂ M
      ((F i k * F k j + F k j * F i k) * F j i) = 0) :
    LinearMap.trace ℂ M (cubic F) = LinearMap.trace ℂ M (cubic (opposite F)) := by
  rw [trace_cubic, trace_opposite, eq_neg_iff_add_eq_zero]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  simpa only [add_mul, map_add] using hz i j k

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRingModule L M] [LieModule ℂ L M]
  [FiniteDimensional ℂ M] [IsIrreducible ℂ L M]

private theorem scalar_of_spanning_commute (x : Fin N → Fin N → L)
    (hs : Submodule.span ℂ (Set.range fun ij : Fin N × Fin N => x ij.1 ij.2) = ⊤)
    (D : Module.End ℂ M) (hD : ∀ i j, ⁅toEnd ℂ L M (x i j), D⁆ = 0) :
    ∃ c : ℂ, D = c • LinearMap.id := by
  have hcomm (z : L) : ⁅toEnd ℂ L M z, D⁆ = 0 := by
    have hz : z ∈ Submodule.span ℂ (Set.range fun ij : Fin N × Fin N => x ij.1 ij.2) := by simp [hs]
    refine Submodule.span_induction (p := fun z _ => ⁅toEnd ℂ L M z,D⁆ = 0) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨ij,rfl⟩
      exact hD _ _
    · simp
    · intro a b _ _ ha hb
      simp [add_lie, ha, hb]
    · intro a z _ hz
      simp [smul_lie, hz]
  let E : M →ₗ⁅ℂ,L⁆ M := { D with
    map_lie' := by
      intro z v
      have h := LinearMap.congr_fun (hcomm z) v
      change ⁅z, D v⁆ - D ⁅z, v⁆ = 0 at h
      exact (sub_eq_zero.mp h).symm }
  obtain ⟨c, hc⟩ := equivariant_end_eq_smul_id E
  exact ⟨c, congrArg LieModuleHom.toLinearMap hc⟩

/-- A zero polarized trace cubic forces identical eigenvalues on the two
opposite orientations of the third matrix-unit contraction. -/
theorem highest_eigenvalue_eq_of_zero_cubic (x : Fin N → Fin N → L)
    (hx : ∀ i j k l, ⁅x i j, x k l⁆ =
      (if j = k then x i l else 0) - (if l = i then x k j else 0))
    (hs : Submodule.span ℂ (Set.range fun ij : Fin N × Fin N => x ij.1 ij.2) = ⊤)
    (u : Fin N → ℂ) (v : M) (hv : v ≠ 0)
    (hd : ∀ i, ⁅x i i,v⁆ = u i • v) (hp : ∀ i j, i < j → ⁅x i j,v⁆ = 0)
    (hz : ∀ a b c : L, LinearMap.trace ℂ M
      (((toEnd ℂ L M a) * (toEnd ℂ L M b) + (toEnd ℂ L M b) * (toEnd ℂ L M a)) *
        toEnd ℂ L M c) = 0) :
    TypeACubicArithmetic.gelfandEigenvalue u = TypeACubicArithmetic.gelfandEigenvalue (fun i => -u i.rev) := by
  let F : Family N M := fun i j => toEnd ℂ L M (x i j)
  have hF : Covariant F F := by
    intro a b i j
    change ⁅toEnd ℂ L M (x a b), toEnd ℂ L M (x i j)⁆ = _
    rw [← LieHom.map_lie, hx]
    split_ifs <;> simp [F]
  have htr := trace_eq_of_cubic_zero (F := F) (fun i j k => hz (x i k) (x k j) (x j i))
  obtain ⟨c, hc⟩ := scalar_of_spanning_commute x hs (cubic F) (central hF)
  have hOp : Covariant (opposite F) (opposite F) := opposite_covariant hF
  obtain ⟨d, hd'⟩ := scalar_of_spanning_commute x hs (cubic (opposite F)) (fun i j => by
    have h := central hOp j.rev i.rev
    simpa only [opposite, Fin.rev_rev, neg_lie, neg_eq_zero] using h)
  have hc' := cubic_apply hF v u hd hp
  have hd'' := cubic_apply hOp v (fun i => -u i.rev)
    (fun i => by simpa only [opposite, LinearMap.neg_apply, neg_smul, F, toEnd_apply_apply] using congrArg Neg.neg (hd i.rev))
    (fun i j hij => by
      change -⁅x j.rev i.rev,v⁆ = 0
      rw [hp j.rev i.rev (Fin.rev_lt_rev.mpr hij), neg_zero])
  rw [hc, hd'] at htr
  rw [hc] at hc'
  rw [hd'] at hd''
  have heqc := smul_left_injective ℂ hv (show c • v = eigenvalue u • v from hc')
  have heqd := smul_left_injective ℂ hv (show d • v = eigenvalue (fun i => -u i.rev) • v from hd'')
  simp only [map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  haveI : Nontrivial M := nontrivial_of_isIrreducible ℂ L M
  have hdim : (finrank ℂ M : ℂ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℂ) (M := M)).ne'
  rw [← TypeACubicArithmetic.pair_sum_eq_gelfandEigenvalue u,
    ← TypeACubicArithmetic.pair_sum_eq_gelfandEigenvalue (fun i => -u i.rev)]
  exact heqc.symm.trans ((mul_right_cancel₀ hdim htr).trans heqd)

end
end CubicAnomaly.Classification.TypeACubicOperator
