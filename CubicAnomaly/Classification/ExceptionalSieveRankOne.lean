import CubicAnomaly.Classification.ExceptionalSieveWeights
import CubicAnomaly.Classification.RankOneObstruction

/-!
# The rank-one dimension and quadratic index in the exceptional sieve

For an irreducible module the lowering string of a primitive vector spans
the module when the triple spans the algebra. Its explicit basis diagonalizes
the coroot. The quadratic trace gives the normalization used in equation (6)
of the paper, namely one quarter of the trace on a long coroot squared.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveRankOne

open LieAlgebra LieModule Module
open LieAlgebra.IsKilling

section String

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M] [IsIrreducible K L M]
  {h e f : L} {v : M} {n : ℕ}

private theorem lowering_string_basis (t : IsSl2Triple h e f)
    (ht : t.toLieSubalgebra K = ⊤) (p : t.HasPrimitiveVectorWith v (n : K)) :
    ∃ b : Basis (Fin (n + 1)) K M, ∀ i, b i = (toEnd K L M f ^ (i : ℕ)) v := by
  let w (i : ℕ) := (toEnd K L M f ^ i) v
  let S := Submodule.span K (Set.range fun i : Fin (n + 1) => w i)
  have hmem (i : ℕ) (hi : i ≤ n) : w i ∈ S :=
    Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩
  have hstab (x : L) (i : Fin (n + 1)) : ⁅x, w i⁆ ∈ S := by
    have hx : x ∈ t.toLieSubalgebra K := ht ▸ LieSubalgebra.mem_top x
    obtain ⟨a, b, c, rfl⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp hx
    rw [t.lie_e_f, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
    refine S.add_mem (S.add_mem (S.smul_mem a ?_) (S.smul_mem b ?_)) (S.smul_mem c ?_)
    · cases hi : (i : ℕ) with
      | zero => simp [w, p.lie_e]
      | succ k =>
        rw [show ⁅e, w (k + 1)⁆ = _ from p.lie_e_pow_succ_toEnd_f k]
        exact S.smul_mem _ (hmem k (by omega))
    · rw [show ⁅f, w i⁆ = w (i + 1) from p.lie_f_pow_toEnd_f i]
      by_cases hi : (i : ℕ) < n
      · exact hmem _ (by omega)
      · have hlast : (i : ℕ) = n := by omega
        rw [hlast, show w (n + 1) = 0 from p.pow_toEnd_f_eq_zero_of_eq_nat rfl]
        exact S.zero_mem
    · rw [show ⁅h, w i⁆ = _ from p.lie_h_pow_toEnd_f i]
      exact S.smul_mem _ (hmem i (by omega))
  let U : LieSubmodule K L M := { S with
    lie_mem := by
      intro x y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hstab x i
      | zero => simp
      | add y z hy hz iy iz => simpa only [lie_add] using S.add_mem iy iz
      | smul r y hy ih => simpa only [lie_smul] using S.smul_mem r ih }
  have hv : v ∈ U := by simpa [w] using hmem 0 (Nat.zero_le _)
  have htop : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left (fun h => by
    exact p.ne_zero (by simpa [h] using hv))
  have hspan : S = ⊤ := congrArg LieSubmodule.toSubmodule htop
  have hind : LinearIndependent K (fun i : Fin (n + 1) => w i) := by
    apply (toEnd K L M h).eigenvectors_linearIndependent' (fun i : Fin (n + 1) => (n : K) - 2 * (i : ℕ)) _
    · intro i
      exact ⟨Module.End.mem_eigenspace_iff.mpr (p.lie_h_pow_toEnd_f i),
        p.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega)⟩
    · intro i j hij
      apply Fin.ext
      simpa using hij
  exact ⟨Basis.mk hind hspan.ge, fun _ => Basis.mk_apply _ _ _⟩

private theorem sum_string_square (a : K) (m : ℕ) :
    3 * ∑ i ∈ Finset.range m, (a - 2 * i) ^ 2 =
      3 * m * a ^ 2 - 6 * a * m * (m - 1) + 2 * m * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- The actual rank-one string has dimension n+1 and quadratic trace
n(n+1)(n+2)/3 on the standard coroot. -/
theorem sl2_dimension_and_quadratic_trace (t : IsSl2Triple h e f)
    (ht : t.toLieSubalgebra K = ⊤) (p : t.HasPrimitiveVectorWith v (n : K)) :
    finrank K M = n + 1 ∧
      traceForm K L M h h = (n : K) * (n + 1) * (n + 2) / 3 := by
  obtain ⟨b, hb⟩ := lowering_string_basis t ht p
  refine ⟨by simpa using finrank_eq_card_basis b, ?_⟩
  rw [traceForm_apply_apply, LinearMap.trace_eq_matrix_trace K b, Matrix.trace]
  have hentry (i : Fin (n + 1)) :
      LinearMap.toMatrix b b (toEnd K L M h ∘ₗ toEnd K L M h) i i =
        ((n : K) - 2 * (i : ℕ)) ^ 2 := by
    have hs : (toEnd K L M h) (b i) = ((n : K) - 2 * (i : ℕ)) • b i := by
      rw [hb]; exact p.lie_h_pow_toEnd_f i
    simp [LinearMap.toMatrix_apply, hs, pow_two]
  change ∑ i, LinearMap.toMatrix b b _ i i = _
  simp_rw [hentry]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((n : K) - 2 * i) ^ 2)]
  have h := sum_string_square (n : K) (n + 1)
  push_cast at h
  linear_combination h / 3

variable {N : Type*} [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [FiniteDimensional K N] [IsIrreducible K L N]

private theorem equiv_of_primitive_strings (t : IsSl2Triple h e f)
    (ht : t.toLieSubalgebra K = ⊤) (p : t.HasPrimitiveVectorWith v (n : K))
    {w : N} (q : t.HasPrimitiveVectorWith w (n : K)) : Nonempty (M ≃ₗ⁅K,L⁆ N) := by
  obtain ⟨b, hb⟩ := lowering_string_basis t ht p
  obtain ⟨c, hc⟩ := lowering_string_basis t ht q
  let E := b.equiv c (Equiv.refl _)
  have hE (i : Fin (n + 1)) : E (b i) = c i := b.equiv_apply _ _ _
  have hop (i : ℕ) (hi : i ≤ n) :
      E ((toEnd K L M f ^ i) v) = (toEnd K L N f ^ i) w := by
    simpa only [hb, hc] using hE ⟨i, by omega⟩
  have hbasis (x : L) (i : Fin (n + 1)) : E ⁅x, b i⁆ = ⁅x, E (b i)⁆ := by
    have hx : x ∈ t.toLieSubalgebra K := ht ▸ LieSubalgebra.mem_top x
    obtain ⟨a, d, r, rfl⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp hx
    have he : E ⁅e, b i⁆ = ⁅e, c i⁆ := by
      rw [hb, hc]
      cases h : (i : ℕ) with
      | zero => simp [p.lie_e, q.lie_e]
      | succ k =>
        rw [p.lie_e_pow_succ_toEnd_f, q.lie_e_pow_succ_toEnd_f, map_smul, hop _ (by omega)]
    have hf : E ⁅f, b i⁆ = ⁅f, c i⁆ := by
      rw [hb, hc, p.lie_f_pow_toEnd_f, q.lie_f_pow_toEnd_f]
      by_cases hi : (i : ℕ) < n
      · exact hop _ (by omega)
      · rw [show (i : ℕ) = n by omega, p.pow_toEnd_f_eq_zero_of_eq_nat rfl,
          q.pow_toEnd_f_eq_zero_of_eq_nat rfl, map_zero]
    have hh : E ⁅h, b i⁆ = ⁅h, c i⁆ := by
      rw [hb, hc, p.lie_h_pow_toEnd_f, q.lie_h_pow_toEnd_f, map_smul, hop _ (by omega)]
    simp only [hE, t.lie_e_f, add_lie, smul_lie, map_add, map_smul, he, hf, hh]
  refine ⟨{ E with map_lie' := fun {x v} => ?_ }⟩
  have hmaps : E.toLinearMap ∘ₗ toEnd K L M x = toEnd K L N x ∘ₗ E.toLinearMap :=
    b.ext (fun i => hbasis x i)
  exact LinearMap.congr_fun hmaps v

end String

section RankOne

open CubicAnomaly.Classification.RankOneObstruction
open CubicAnomaly.Classification.ExceptionalSieveWeights
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanCubic

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [FiniteDimensional ℂ M] [IsIrreducible ℂ L M]

omit [LieAlgebra.IsKilling ℂ L] in
private theorem triple_spans_of_finrank_three {h e f : L}
    (t : IsSl2Triple h e f) (hdim : finrank ℂ L = 3) : t.toLieSubalgebra ℂ = ⊤ := by
  let w : Fin 3 → L := ![e, f, h]
  let evals : Fin 3 → ℂ := ![2, -2, 0]
  have hind : LinearIndependent ℂ w := by
    apply (toEnd ℂ L L h).eigenvectors_linearIndependent' evals _
    · intro i
      fin_cases i
      · exact ⟨Module.End.mem_eigenspace_iff.mpr (t.lie_h_e_smul ℂ), t.e_ne_zero⟩
      · exact ⟨Module.End.mem_eigenspace_iff.mpr (by simpa [w, evals] using t.lie_lie_smul_f ℂ),
          t.f_ne_zero⟩
      · exact ⟨Module.End.mem_eigenspace_iff.mpr (by simp [evals, w]), t.h_ne_zero⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num [evals] at *
  have hs := hind.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  apply LieSubalgebra.toSubmodule_injective
  change Submodule.span ℂ {e, f, h} = ⊤
  have hr : Set.range w = {e, f, h} := by
    ext x
    simp [w, Matrix.range_cons, or_comm, or_left_comm]
  rwa [hr] at hs

/-- With a one-dimensional splitting Cartan, every irreducible module has
the actual rank-one Weyl dimension and long-coroot index used by the sieve.
The base, highest weight and nonzero vector are constructed from the module. -/
theorem rank_one_module_dimension_and_index (hrank : finrank ℂ H = 1) :
    ∃ (α : H.root) (χ : Weight ℂ H M) (n : ℕ),
      χ (coroot α.val) = (n : ℂ) ∧ finrank ℂ M = n + 1 ∧
        traceForm ℂ L M (coroot α.val) (coroot α.val) / 4 =
          (n : ℂ) * (n + 1) * (n + 2) / 12 := by
  classical
  letI : Nontrivial M := nontrivial_of_isIrreducible ℂ L M
  haveI : Nonempty H.root := Fintype.card_pos_iff.mp
    (by rw [rank_one_actual_root_count H hrank]; decide)
  obtain ⟨b⟩ := RootPairing.nonempty_base (rootSystem H)
  obtain ⟨α, hαb⟩ := b.support_nonempty
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨s, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have hs := t.h_eq_coroot hα he hf
  subst s
  obtain ⟨χ, v, a, hv, hev, hkill, hlabel⟩ :=
    exists_bounded_dominant_highest_weight (M := M) H b
  let i : b.support := ⟨α, hαb⟩
  have hχ : χ (coroot α.val) = ((a i : ℕ) : ℂ) := hlabel i
  have p : t.HasPrimitiveVectorWith v ((a i : ℕ) : ℂ) :=
    ⟨hv, hχ ▸ hev (coroot α.val), hkill α (RootPairing.Base.isPos_of_mem_support hαb) e he⟩
  obtain ⟨hdim, hquad⟩ := sl2_dimension_and_quadratic_trace t
    (triple_spans_of_finrank_three t (rank_one_killing_finrank_eq_three H hrank)) p
  exact ⟨α, χ, a i, hχ, hdim, by rw [hquad]; ring⟩

/-- Rank-one isotropy admits no symmetric invariant cubic. This proves the
rank-one zero-cubic filter for all modules at once. -/
theorem rank_one_invariant_cubic_eq_zero (hrank : finrank ℂ H = 1)
    (c : TrilinearForm (R := ℂ) (L := L) (S := ℂ)) (hc : IsInvariant c) (cs : IsSymmetric c) :
    c = 0 := by
  classical
  obtain ⟨α⟩ := Fintype.card_pos_iff.mp
    (show 0 < Fintype.card H.root by rw [rank_one_actual_root_count H hrank]; decide)
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨h, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have hhef : c h f e = 0 := by
    have hz := hc e f f e
    rw [t.lie_e_f, lie_self, map_zero, add_zero, ← cs.1 h f e] at hz
    linear_combination hz / 2
  have hhhh : c h h h = 0 := by
    have hz := hc e f h h
    have heh : ⁅e, h⁆ = (-2 : ℂ) • e := by rw [← lie_skew, t.lie_h_e_smul ℂ, neg_smul]
    rw [t.lie_e_f, heh] at hz
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hz
    rw [cs.2 f e h, ← cs.1 h f e, hhef] at hz
    linear_combination hz
  have hs := t.h_eq_coroot hα he hf
  have hne : coroot α.val ≠ 0 := by
    intro hz
    apply t.h_ne_zero
    rw [hs, hz, ZeroMemClass.coe_zero]
  have hlin := (finrank_eq_one_iff_of_nonzero' _ hne).mp hrank
  apply invariant_cubic_eq_zero_of_cartan H c hc cs
  intro x y z
  obtain ⟨a, rfl⟩ := hlin x
  obtain ⟨b, rfl⟩ := hlin y
  obtain ⟨d, rfl⟩ := hlin z
  change c (a • (coroot α.val : L)) (b • (coroot α.val : L)) (d • (coroot α.val : L)) = 0
  simp only [← hs, map_smul, LinearMap.smul_apply, hhhh, smul_zero]

variable {N : Type*} [AddCommGroup N] [Module ℂ N] [LieRingModule L N] [LieModule ℂ L N]
  [FiniteDimensional ℂ N] [IsIrreducible ℂ L N]

/-- Rank-one irreducibles of equal dimension are equivariantly isomorphic.
The isomorphism sends each lowering-string basis to the corresponding basis
for the same triple. -/
theorem rank_one_irreducibles_equiv_of_finrank_eq (hrank : finrank ℂ H = 1)
    (hdim : finrank ℂ M = finrank ℂ N) : Nonempty (M ≃ₗ⁅ℂ,L⁆ N) := by
  classical
  letI : Nontrivial M := nontrivial_of_isIrreducible ℂ L M
  letI : Nontrivial N := nontrivial_of_isIrreducible ℂ L N
  haveI : Nonempty H.root := Fintype.card_pos_iff.mp
    (by rw [rank_one_actual_root_count H hrank]; decide)
  obtain ⟨b⟩ := RootPairing.nonempty_base (rootSystem H)
  obtain ⟨α, hαb⟩ := b.support_nonempty
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨s, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have hs := t.h_eq_coroot hα he hf
  subst s
  let i : b.support := ⟨α, hαb⟩
  have ht := triple_spans_of_finrank_three t (rank_one_killing_finrank_eq_three H hrank)
  obtain ⟨χ, v, a, hv, hev, hkill, hlabel⟩ :=
    exists_bounded_dominant_highest_weight (M := M) H b
  obtain ⟨ψ, w, d, hw, hew, hkill', hlabel'⟩ :=
    exists_bounded_dominant_highest_weight (M := N) H b
  have p : t.HasPrimitiveVectorWith v ((a i : ℕ) : ℂ) :=
    ⟨hv, hlabel i ▸ hev _, hkill α (RootPairing.Base.isPos_of_mem_support hαb) e he⟩
  have q : t.HasPrimitiveVectorWith w ((d i : ℕ) : ℂ) :=
    ⟨hw, hlabel' i ▸ hew _, hkill' α (RootPairing.Base.isPos_of_mem_support hαb) e he⟩
  have hm := (sl2_dimension_and_quadratic_trace t ht p).1
  have hn := (sl2_dimension_and_quadratic_trace t ht q).1
  have heq : (d i : ℕ) = (a i : ℕ) := by omega
  exact equiv_of_primitive_strings t ht p (heq ▸ q)

end RankOne

section CompactPair

open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.CompactCartan
open CubicAnomaly.Classification.ComplexDuality
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.SieveBounds
open CubicAnomaly.Classification.RankOneObstruction

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The original compact-pair hypotheses force geometric isotropy rank at
least two. If it were one, the two irreducible halves of the complexified
complement would have the same dimension and hence be equivalent. -/
theorem all_rank_isotropy_rank_ge_two
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    2 ≤ abelianRank ℝ h := by
  have hthree := (all_rank_isotropy_dimension_bounds B h heff hproper e hradical).1
  letI : Nontrivial h := finrank_pos_iff.mp (by omega : 0 < finrank ℝ h)
  have hpos := compact_abelianRank_pos (B.restrict h)
  by_contra! hlt
  have hone : abelianRank ℝ h = 1 := by omega
  obtain ⟨A, hA, hdim⟩ := exists_abelian_finrank_eq_abelianRank ℝ h
  letI := hA
  letI : A.IsCartanSubalgebra := compact_maximum_abelian_isCartan (B.restrict h) A hdim
  let H := complexifiedSubalgebra A
  letI : H.IsCartanSubalgebra := complexified_abelian_cartan A
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  have hrank : finrank ℂ H = 1 := by
    change finrank ℂ (A.toSubmodule.baseChange ℂ) = 1
    rw [complexification_submodule_finrank]
    exact hdim.trans hone
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let W := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) (-Complex.I)
  obtain ⟨-, hV, hW, ⟨D⟩, hne⟩ := compact_complement_complex_type_decomposition B h hproper e
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) V := hV
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) W := hW
  have hd : finrank ℂ W = finrank ℂ V := by
    simpa using D.toLinearEquiv.finrank_eq
  exact hne (rank_one_irreducibles_equiv_of_finrank_eq H hrank hd.symm)

/-- In odd ambient dimension the actual isotropy has odd rank at least
three and therefore dimension at least nine. At ambient dimension 133 this
sharpens the half-dimension cutoff in equation (6b) from 65 to 62. -/
theorem all_rank_odd_dimension_half_bound
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (hodd : Odd (finrank ℝ g)) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    3 ≤ abelianRank ℝ h ∧ 2 * finrank ℂ V + 9 ≤ finrank ℝ g ∧
      (finrank ℝ g = 133 → finrank ℂ V ≤ 62) := by
  have hrank := all_rank_isotropy_rank_ge_two B h heff hproper e hradical
  obtain ⟨A, hA, hdim⟩ := exists_abelian_finrank_eq_abelianRank ℝ h
  letI := hA
  letI : A.IsCartanSubalgebra := compact_maximum_abelian_isCartan (B.restrict h) A hdim
  let H := complexifiedSubalgebra A
  letI : H.IsCartanSubalgebra := complexified_abelian_cartan A
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h) :=
    compact_complexification_isKilling (B.restrict h) (LieAlgebra.center_eq_bot ℝ h)
  have hH : finrank ℂ H = abelianRank ℝ h := by
    change finrank ℂ (A.toSubmodule.baseChange ℂ) = _
    rw [complexification_submodule_finrank]
    exact hdim
  obtain ⟨r, hr, hd⟩ := KillingDimension.killing_dimension_eq_rank_add_twice H
  rw [Module.finrank_baseChange, hH] at hd
  rw [hH] at hr
  have htotal := QuadraticRestriction.compact_pair_dimension_equation B h hproper e
  obtain ⟨k, hk⟩ := hodd
  dsimp only at htotal ⊢
  omega

end CompactPair

end CubicAnomaly.Classification.ExceptionalSieveRankOne
