import CubicAnomaly.Classification.ChevalleySimpleTriples
import CubicAnomaly.Classification.ExceptionalSieveWeights
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# A dimension bound on the edges of the A₂ dominant chamber

For a highest vector with labels `(a,0)`, the two simple lowering
operators generate a two-step nilpotent Lie algebra. Moving the
second lowering operator past powers of the first bounds the spanning
vectors by the integer points of the triangle `p + q ≤ a`.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveA2

open LieAlgebra LieModule Module LieAlgebra.IsKilling LieSubalgebra

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]

private def act (x : L) (n : ℕ) (v : M) : M := (toEnd ℂ L M x ^ n) v

private theorem act_zero (x : L) (v : M) : act x 0 v = v := rfl

private theorem act_succ (x : L) (n : ℕ) (v : M) :
    act x (n+1) v = ⁅x, act x n v⁆ := by
  simp [act, pow_succ', Module.End.mul_apply]

private theorem commute_act {x y : L} (hxy : ⁅x,y⁆ = 0) (n : ℕ) (v : M) :
    ⁅x, act y n v⁆ = act y n ⁅x,v⁆ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [act_succ, act_succ, leibniz_lie, hxy, zero_lie, zero_add, ih]

private def normal (f z : L) (v : M) (p q : ℕ) := act z q (act f p v)

private theorem first_normal (f z : L) (v : M) (hfz : ⁅f,z⁆ = 0) (p q : ℕ) :
    ⁅f, normal f z v p q⁆ = normal f z v (p+1) q := by
  exact (commute_act hfz q _).trans (congrArg (act z q) (act_succ f p v).symm)

private theorem second_normal {f g z : L} {v : M} (hgf : ⁅g,f⁆ = z)
    (hfz : ⁅f,z⁆ = 0) (hgz : ⁅g,z⁆ = 0) (hgv : ⁅g,v⁆ = 0) (p q : ℕ) :
    ⁅g, normal f z v (p+1) q⁆ = ((p+1 : ℕ) : ℂ) • normal f z v p (q+1) := by
  have aux (n : ℕ) : ⁅g, act f (n+1) v⁆ = ((n+1 : ℕ) : ℂ) • ⁅z,act f n v⁆ := by
    induction n with
    | zero => simp [act_succ, act_zero, leibniz_lie, hgf, hgv]
    | succ n ih =>
      rw [act_succ f (n+1), leibniz_lie, hgf, ih, lie_smul, leibniz_lie f z, hfz, zero_lie,
        zero_add, ← act_succ f n, Nat.cast_add_one]
      module
  unfold normal
  rw [commute_act hgz, aux]
  change (toEnd ℂ L M z ^ q) (_ • _) = _
  rw [map_smul]
  congr 1

private theorem outside_triangle {f g z : L} {v : M} (a : ℕ)
    (hgf : ⁅g,f⁆ = z) (hfz : ⁅f,z⁆ = 0) (hgz : ⁅g,z⁆ = 0)
    (hgv : ⁅g,v⁆ = 0) (htop : act f (a+1) v = 0) (p q : ℕ) (hbig : a < p+q) :
    normal f z v p q = 0 := by
  induction q generalizing p with
  | zero =>
    change (toEnd ℂ L M f ^ p) v = 0
    exact Module.End.pow_map_zero_of_le (by omega : a+1 ≤ p) htop
  | succ q ih =>
    have eqn := second_normal hgf hfz hgz hgv p q
    rw [ih (p+1) (by omega), lie_zero] at eqn
    exact (smul_eq_zero.mp eqn.symm).resolve_left (by exact_mod_cast Nat.succ_ne_zero p)

abbrev Triangle (a : ℕ) := (p : Fin (a+1)) × Fin (a+1-p.val)

private def stableSubalgebra (N : Submodule ℂ M) : LieSubalgebra ℂ L where
  carrier := {x | ∀ v ∈ N, ⁅x,v⁆ ∈ N}
  zero_mem' := fun v _ => by rw [zero_lie]; exact N.zero_mem
  add_mem' hx hy v hv := by rw [add_lie]; exact N.add_mem (hx v hv) (hy v hv)
  smul_mem' c x hx v hv := by rw [smul_lie]; exact N.smul_mem _ (hx v hv)
  lie_mem' {x y} hx hy v hv := by
    have h : ⁅⁅x,y⁆,v⁆ = ⁅x,⁅y,v⁆⁆ - ⁅y,⁅x,v⁆⁆ := by rw [leibniz_lie]; abel
    rw [h]
    exact N.sub_mem (hx _ (hy v hv)) (hy _ (hx v hv))

private theorem stable_of_generators (N : Submodule ℂ M) (w : Triangle a → M)
    (hspan : N = Submodule.span ℂ (Set.range w)) (x : L) (hx : ∀ i, ⁅x,w i⁆ ∈ N) :
    x ∈ stableSubalgebra N := by
  intro v hv
  rw [hspan] at hv
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨i,rfl⟩ := hy; exact hx i
  | zero => rw [lie_zero]; exact N.zero_mem
  | add _ _ _ _ h₁ h₂ => rw [lie_add]; exact N.add_mem h₁ h₂
  | smul _ _ _ h => rw [lie_smul]; exact N.smul_mem _ h

variable [FiniteDimensional ℂ L] [FiniteDimensional ℂ M] [IsIrreducible ℂ L M]

private theorem triangle_bound (a : ℕ) {h j e u f g : L} {v : M}
    (t : IsSl2Triple h e f) (t' : IsSl2Triple j u g)
    (P : t.HasPrimitiveVectorWith v (a : ℂ)) (Q : t'.HasPrimitiveVectorWith v (0 : ℂ))
    (huf : ⁅u,f⁆ = 0) (heg : ⁅e,g⁆ = 0)
    (hjf : ⁅j,f⁆ = f) (hhg : ⁅h,g⁆ = g)
    (hgen : lieSpan ℂ L ({e,u,f,g} : Set L) = ⊤) :
    finrank ℂ M ≤ Fintype.card (Triangle a) := by
  let z := ⁅g,f⁆
  have gv : ⁅g,v⁆ = 0 := by simpa using Q.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by simp)
  have hfz : ⁅f,z⁆ = 0 := by
    have hp : t.HasPrimitiveVectorWith g (1 : ℂ) := ⟨t'.f_ne_zero, by simpa using hhg, heg⟩
    have hp' := hp.pow_toEnd_f_eq_zero_of_eq_nat (n := 1) (by simp)
    change ⁅f,⁅g,f⁆⁆ = 0
    rw [← lie_skew g f, lie_neg, neg_eq_zero]
    simpa [pow_succ', Module.End.mul_apply] using hp'
  have hgz : ⁅g,z⁆ = 0 := by
    have hp : t'.HasPrimitiveVectorWith f (1 : ℂ) := ⟨t.f_ne_zero, by simpa using hjf, huf⟩
    simpa [z, pow_succ', Module.End.mul_apply] using hp.pow_toEnd_f_eq_zero_of_eq_nat (n := 1) (by simp)
  let w (i : Triangle a) := normal f z v i.1.val i.2.val
  let N := Submodule.span ℂ (Set.range w)
  have hn (p q : ℕ) : normal f z v p q ∈ N := by
    by_cases hpq : p + q ≤ a
    · exact Submodule.subset_span ⟨⟨⟨p,by omega⟩, ⟨q,by change q < a + 1 - p; omega⟩⟩,rfl⟩
    · rw [outside_triangle a (show ⁅g,f⁆ = z from rfl) hfz hgz gv
        (P.pow_toEnd_f_eq_zero_of_eq_nat rfl) p q (by omega)]
      exact N.zero_mem
  have hf : f ∈ stableSubalgebra N := stable_of_generators N w rfl f fun i =>
    first_normal f z v hfz i.1 i.2 ▸ hn _ _
  have hz : z ∈ stableSubalgebra N := stable_of_generators N w rfl z fun i =>
    (act_succ z i.2.val (act f i.1.val v)) ▸ hn i.1 (i.2.val+1)
  have hg : g ∈ stableSubalgebra N := by
    apply stable_of_generators N w rfl
    rintro ⟨⟨p,hp⟩,q⟩
    cases p with
    | zero =>
      change ⁅g, act z q.val v⁆ ∈ N
      rw [commute_act hgz, gv]
      simp [act]
    | succ p =>
      change ⁅g, normal f z v (p+1) q.val⁆ ∈ N
      rw [second_normal (show ⁅g,f⁆ = z from rfl) hfz hgz gv]
      exact N.smul_mem _ (hn _ _)
  have ez : ⁅e,z⁆ = -g := by
    change ⁅e,⁅g,f⁆⁆ = -g
    rw [leibniz_lie, heg, zero_lie, zero_add, t.lie_e_f, ← lie_skew g h, hhg]
  have uz : ⁅u,z⁆ = f := by
    change ⁅u,⁅g,f⁆⁆ = f
    rw [leibniz_lie, t'.lie_e_f, huf, lie_zero, add_zero, hjf]
  have hpos (r : L) (hrz : ⁅r,z⁆ ∈ stableSubalgebra N)
      (hrf : ∀ p, ⁅r,act f p v⁆ ∈ N) : r ∈ stableSubalgebra N := by
    apply stable_of_generators N w rfl
    intro i
    suffices ∀ q : ℕ, ⁅r,normal f z v i.1 q⁆ ∈ N from this i.2
    intro q
    induction q with
    | zero => exact hrf _
    | succ q ih =>
      change ⁅r,act z (q+1) (act f i.1.val v)⁆ ∈ N
      rw [act_succ, leibniz_lie]
      exact N.add_mem (hrz _ (hn _ _)) (hz _ ih)
  have he : e ∈ stableSubalgebra N := by
    apply hpos e (ez ▸ (stableSubalgebra N).neg_mem hg)
    intro p
    cases p with
    | zero => rw [act_zero, P.lie_e]; exact N.zero_mem
    | succ p =>
      rw [act, P.lie_e_pow_succ_toEnd_f]
      exact N.smul_mem _ (hn p 0)
  have hu : u ∈ stableSubalgebra N := by
    apply hpos u (uz ▸ hf)
    intro p
    rw [commute_act huf, Q.lie_e]
    simp [act]
  have htop : (⊤ : LieSubalgebra ℂ L) ≤ stableSubalgebra N := by
    rw [← hgen, lieSpan_le]
    rintro x (rfl | rfl | rfl | hx)
    · exact he
    · exact hu
    · exact hf
    · obtain rfl : x = g := hx
      exact hg
  let N' : LieSubmodule ℂ L M := { N with lie_mem := fun {x _} h => htop (mem_top x) _ h }
  have hnon : N' ≠ ⊥ := fun h => P.ne_zero (by
    have hv : v ∈ N' := hn 0 0
    simpa [h] using hv)
  have hfull := (LieSubmodule.toSubmodule_eq_top N').mpr ((IsSimpleOrder.eq_bot_or_eq_top N').resolve_left hnon)
  exact finrank_le_of_span_eq_top hfull


private theorem triangle_card (a : ℕ) : Fintype.card (Triangle a) = (a+2).choose 2 := by
  simp only [Triangle, Fintype.card_sigma, Fintype.card_fin]
  induction a with
  | zero => decide
  | succ a ih =>
    rw [Fin.sum_univ_succ, Nat.choose_succ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub,
      Nat.choose_one_right]
    rw [ih]

variable [LieAlgebra.IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

private theorem cross_cartan {i j : b.support} {f : L}
    (hij : b.cartanMatrix i j = -1) (hf : f ∈ rootSpace H (-(i.val.val : H → ℂ))) :
    ⁅(coroot j.val.val : L), f⁆ = f := by
  have hm := b.algebraMap_cartanMatrixIn_apply ℤ i j
  change ((b.cartanMatrix i j : ℤ) : ℂ) = i.val.val (coroot j.val.val) at hm
  have hh := lie_eq_smul_of_mem_rootSpace hf (coroot j.val.val)
  change ⁅(coroot j.val.val : L), f⁆ = -i.val.val (coroot j.val.val) • f at hh
  simpa only [← hm, hij, Int.cast_neg, Int.cast_one, neg_neg, one_smul] using hh

/-- A module on an A₂ chamber edge is spanned by at most `choose (a+2) 2`
vectors. Either endpoint of the simple diagram can be the labeled one. -/
theorem a2_edge_highest_dimension_le (s : Fin 2 ≃ b.support)
    (h01 : b.cartanMatrix (s 0) (s 1) = -1) (h10 : b.cartanMatrix (s 1) (s 0) = -1)
    (v : M) (hv : v ≠ 0) (a : ℕ)
    (hw₀ : ⁅(coroot (s 0).val.val : L),v⁆ = (a : ℂ) • v)
    (hw₁ : ⁅(coroot (s 1).val.val : L),v⁆ = 0)
    (he : ∀ i : b.support, ∀ x ∈ rootSpace H i.val.val, ⁅x,v⁆ = 0) :
    finrank ℂ M ≤ (a+2).choose 2 := by
  obtain ⟨E, F, t, hE, hF, hm, hg⟩ := ChevalleySimpleTriples.exists_simple_root_triples H b
  have hne : s 0 ≠ s 1 := s.injective.ne (by decide)
  have hspan : lieSpan ℂ L ({E (s 0), E (s 1), F (s 0), F (s 1)} : Set L) = ⊤ := by
    apply top_unique
    rw [← hg]
    apply lieSpan_mono
    rintro _ (⟨i,rfl⟩ | ⟨i,rfl⟩) <;> obtain ⟨k,rfl⟩ := s.surjective i <;> fin_cases k <;> simp
  rw [← triangle_card]
  exact triangle_bound a (t (s 0)) (t (s 1)) ⟨hv, hw₀, he _ _ (hE _)⟩
    ⟨hv, by simpa using hw₁, he _ _ (hE _)⟩ (hm _ _ hne.symm) (hm _ _ hne)
    (cross_cartan H b h01 (hF _)) (cross_cartan H b h10 (hF _)) hspan

/-- Indices of successive strings in the second simple direction, starting
at the successive levels of the first simple-root string. -/
abbrev Strings (a c : ℕ) := (p : Fin (a+1)) × Fin (c+p.val+1)

omit [IsIrreducible ℂ L M] in
/-- Each second-direction string through the first-direction string
contributes linearly independent vectors of distinct joint weights. -/
theorem a2_two_string_dimension_lower (s : Fin 2 ≃ b.support)
    (h01 : b.cartanMatrix (s 0) (s 1) = -1) (h10 : b.cartanMatrix (s 1) (s 0) = -1)
    (v : M) (hv : v ≠ 0) (χ : H → ℂ) (hw : ∀ x : H, ⁅x,v⁆ = χ x • v)
    (a c : ℕ) (ha : χ (coroot (s 0).val.val) = (a : ℂ))
    (hc : χ (coroot (s 1).val.val) = (c : ℂ))
    (he : ∀ i : b.support, ∀ x ∈ rootSpace H i.val.val, ⁅x,v⁆ = 0) :
    Fintype.card (Strings a c) ≤ finrank ℂ M := by
  obtain ⟨E, F, t, hE, hF, hm, _⟩ := ChevalleySimpleTriples.exists_simple_root_triples H b
  have P : (t (s 0)).HasPrimitiveVectorWith v (a : ℂ) :=
    ⟨hv, ha ▸ hw _, he _ _ (hE _)⟩
  let pvec (p : ℕ) := act (F (s 0)) p v
  have hj := cross_cartan H b h01 (hF (s 0))
  have hweight (p : ℕ) : ⁅(coroot (s 1).val.val : L),pvec p⁆ = ((c+p : ℕ) : ℂ) • pvec p := by
    induction p with
    | zero => simpa [pvec, act_zero, hc] using hw (coroot (s 1).val.val)
    | succ p ih =>
      change ⁅(coroot (s 1).val.val : L), act (F (s 0)) (p+1) v⁆ = _ • act (F (s 0)) (p+1) v
      rw [act_succ, leibniz_lie, hj]
      change _ + ⁅_,⁅_,pvec p⁆⁆ = _ • _
      rw [ih, lie_smul]
      push_cast
      module
  have Q (p : Fin (a+1)) : (t (s 1)).HasPrimitiveVectorWith (pvec p) ((c+p.val : ℕ) : ℂ) :=
    ⟨P.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega), hweight p, by
      change ⁅E (s 1), act (F (s 0)) p.val v⁆ = 0
      rw [commute_act (hm _ _ (s.injective.ne (by decide : (1 : Fin 2) ≠ 0))), he _ _ (hE _)]
      exact map_zero _⟩
  let W (i : Strings a c) := act (F (s 1)) i.2.val (pvec i.1)
  have hw0 (i : Strings a c) : W i ≠ 0 :=
    (Q i.1).pow_toEnd_f_ne_zero_of_eq_nat rfl (by exact Nat.le_of_lt_succ i.2.isLt)
  let α := ((s 0).val.val : H → ℂ)
  let β := ((s 1).val.val : H → ℂ)
  let μ (i : Strings a c) : H → ℂ := i.2.val • (-β) + (i.1.val • (-α) + χ)
  have hmem (i : Strings a c) : W i ∈ genWeightSpace M (μ i) := by
    apply toEnd_pow_apply_mem (hF (s 1))
    apply toEnd_pow_apply_mem (hF (s 0))
    exact weightSpace_le_genWeightSpace M χ ((mem_weightSpace χ v).mpr hw)
  have evals (i j : b.support) : i.val.val (coroot j.val.val) = ((b.cartanMatrix i j : ℤ) : ℂ) :=
    (b.algebraMap_cartanMatrixIn_apply ℤ i j).symm
  have hμ : Function.Injective μ := by
    intro i j hij
    have coeff (i : Strings a c) (k : Fin 2) :
        μ i (coroot (s k).val.val) =
          -((i.2.val : ℂ) * b.cartanMatrix (s 1) (s k)) -
          (i.1.val : ℂ) * b.cartanMatrix (s 0) (s k) + χ (coroot (s k).val.val) := by
      simp [μ, α, β, evals, nsmul_eq_mul]
      ring
    have h₀ := congrFun hij (coroot (s 0).val.val)
    have h₁ := congrFun hij (coroot (s 1).val.val)
    simp only [coeff, h01, h10, RootPairing.Base.cartanMatrix_apply_same, Int.cast_neg,
      Int.cast_one, Int.cast_ofNat, add_left_inj] at h₀ h₁
    have hp : (i.1.val : ℂ) = j.1.val := by linear_combination (-2 * h₀ - h₁) / 3
    have hq : (i.2.val : ℂ) = j.2.val := by linear_combination (-h₀ - 2 * h₁) / 3
    rcases i with ⟨⟨p,hp'⟩,⟨q,hq'⟩⟩
    rcases j with ⟨⟨p',hp''⟩,⟨q',hq''⟩⟩
    obtain rfl : p = p' := by exact_mod_cast hp
    obtain rfl : q = q' := by exact_mod_cast hq
    rfl
  have hind : iSupIndep (fun lam : H → ℂ => (genWeightSpace M lam).toSubmodule) :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace ℂ H M)
  exact ((hind.comp hμ).linearIndependent _ hmem hw0).fintype_card_le_finrank

end CubicAnomaly.Classification.ExceptionalSieveA2
