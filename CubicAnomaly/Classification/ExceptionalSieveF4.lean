import CubicAnomaly.Classification.ExceptionalSieveRankTwo
import CubicAnomaly.Classification.ExceptionalSieveNormalization
import CubicAnomaly.Classification.ExceptionalSieveIndex
import CubicAnomaly.Classification.ExceptionalSieveProducts
import CubicAnomaly.Classification.WeylDualityObstruction
import CubicAnomaly.Classification.ClassicalConstituentOpposition

/-!
# Rank-deficient F₄ reduces to a simple eight-dimensional isotropy

At rank two every Cartan table except A₂ has a Weyl word negating the
whole Cartan. Every irreducible is then self-dual. The canonical complex
half of the compact isotropy is inequivalent to its dual, so the only
possible factor type is A₂, and its module must have dimension 22.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveF4

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ExceptionalSieveRankTwo RootClassificationExceptional
open WeylDualityObstruction ClassicalConstituentWeyl ClassicalConstituentOpposition
open ExceptionalSieveCatalog ExceptionalSieveNormalization ExceptionalSieveProducts
open Structural Complexification HermitianRealization ComplexDuality CompactCartan AllRankComplex
open ExceptionalSieveIndex ExceptionalSieveWeights ExceptionalSieveRankOne
open scoped TensorProduct

private theorem rank_two_opposition : ∀ (k : Fin 6), k ≠ 1 →
    ∃ m : Fin 4, NegatesCoroots (matrix (datum k)) m := by native_decide

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [FiniteDimensional ℂ M] [IsIrreducible ℂ L M]

private theorem cartan_words_eq (w : List H.root) : cartanWord H w = applyWord H w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [cartanWord, applyWord, ih]

private theorem simple_of_A2 (s : Fin 2 ≃ b.support)
    (hm : ∀ i j, b.cartanMatrix (s i) (s j) = matrix (datum 1) i j) :
    LieAlgebra.IsSimple ℂ L := by
  let α : H.root := s 0
  let β : H.root := s 1
  let I := CorootComponents.corootIdeal H α
  have hα : (coroot α.val : L) ∈ I := LieSubmodule.subset_lieSpan (Set.mem_singleton _)
  have hp : β.val (coroot α.val) ≠ 0 := by
    have hpair := b.algebraMap_cartanMatrixIn_apply ℤ (s 1) (s 0)
    change ((b.cartanMatrix (s 1) (s 0) : ℤ) : ℂ) = β.val (coroot α.val) at hpair
    rw [← hpair, hm, show matrix (datum 1) (1 : Fin 2) (0 : Fin 2) = -1 by decide]
    norm_num
  have hβ := CartanCoroot.coroot_mem_ideal_of_cartan_eval_ne_zero H I β (coroot α.val) hα hp
  have htop : I = ⊤ := by
    apply top_unique
    apply CartanCubic.ideal_le_of_cartan_intersection_le H
    intro x _
    rw [← b.toCoweightBasis.sum_repr x, Submodule.coe_sum]
    apply I.sum_mem
    intro j _
    obtain ⟨i, rfl⟩ := s.surjective j
    rw [Submodule.coe_smul_of_tower, b.toCoweightBasis_apply]
    apply I.smul_mem
    fin_cases i
    · exact hα
    · exact hβ
  have hatom : IsAtom (⊤ : LieIdeal ℂ L) := htop ▸ CorootComponents.corootIdeal_isAtom H α
  letI : IsSimpleOrder (LieIdeal ℂ L) := isSimpleOrder_iff_isAtom_top.mpr hatom
  refine ⟨IsSimpleOrder.eq_bot_or_eq_top, ?_⟩
  intro hab
  letI := hab
  letI : IsLieAbelian (⊤ : LieIdeal ℂ L) := ⟨fun x y => Subtype.ext (trivial_lie_zero L L x.val y.val)⟩
  have hbot := IsKilling.ideal_eq_bot_of_isLieAbelian (⊤ : LieIdeal ℂ L)
  exact hatom.ne_bot hbot

/-- Every non-self-dual rank-two irreducible forces the A₂ Cartan
matrix, simple isotropy, and algebra dimension eight. -/
theorem rank_two_nonselfdual_forces_A2
    (hn : ¬Nonempty (M ≃ₗ⁅ℂ,L⁆ Dual ℂ M)) (hr : finrank ℂ H = 2) :
    LieAlgebra.IsSimple ℂ L ∧ finrank ℂ L = 8 ∧
    ∃ s : Fin 2 ≃ b.support, ∀ i j, b.cartanMatrix (s i) (s j) = matrix (datum 1) i j := by
  obtain ⟨k, s, hm, hd⟩ := actual_rank_two_cartan_table H b hr
  have heq : k = 1 := by
    by_contra he
    obtain ⟨m, hc⟩ := rank_two_opposition k he
    obtain ⟨w, hw⟩ := actual_weyl_negation_of_coxeter H b s m hm hc
    exact hn (irreducible_self_dual_of_neg_word H b w (by simpa only [cartan_words_eq] using hw))
  subst k
  exact ⟨simple_of_A2 H b s hm, hd.trans (by native_decide), s, hm⟩

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

set_option maxHeartbeats 0 in
/-- In dimension 52 with deficient isotropy rank, the complex half is an
actual 22-dimensional irreducible of A₂ whose highest-weight labels pass
the index test whenever the ambient Cartan is of type F₄. -/
theorem compact_pair_f4_forces_A2
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (hg : finrank ℝ g = 52) (hr : abelianRank ℝ h < 4) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    let t : Factor := .a 1
    ∃ (hgK : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)) (hhK : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)),
      letI := hgK
      letI := hhK
      ∃ (A : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
        (hA : A.IsCartanSubalgebra) (hH : H.IsCartanSubalgebra),
        letI := hA
        letI := hH
        LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] h) ∧ finrank ℂ V = 22 ∧
        ∃ (b : (rootSystem A).Base) (s : Fin 2 ≃ b.support) (a : t.Label)
          (χ : Weight ℂ A V) (v : V),
          (∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j) ∧
          v ≠ 0 ∧ (∀ z : A, ⁅z, v⁆ = χ z • v) ∧
          (∀ α : A.root, b.IsPos α → ∀ z ∈ rootSpace A α.val, ⁅z, v⁆ = 0) ∧
          (∀ i, χ (coroot (s i).val.val) = (a i : ℂ)) ∧
          (∀ (bg : (rootSystem H).Base) (sg : Index Exceptional.f4Datum ≃ bg.support),
            (∀ i j, bg.cartanMatrix (sg i) (sg j) = matrix Exceptional.f4Datum i j) →
            Compatible .f4 22 (row t a)) := by
  classical
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let t : Factor := .a 1
  obtain ⟨-, -, hgK, hhK, -, hdec⟩ := all_rank_complex_structural_reduction B h heff hproper e hradical
  letI := hgK
  letI := hhK
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) V := hdec.2.1
  letI := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) V
  have hn : ¬Nonempty (V ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Dual ℂ V) :=
    fun ⟨f⟩ => hdec.2.2.2.2 ⟨f.trans hdec.2.2.2.1.some.symm⟩
  obtain ⟨A, H, hA, hH, hdim, hnest⟩ := compact_pair_nested_cartans B h
  letI := hA
  letI := hH
  have hlow := all_rank_isotropy_rank_ge_two B h heff hproper e hradical
  have hpar := KillingDimension.killing_dimension_parity A
  have htotal := QuadraticRestriction.compact_pair_dimension_equation B h hproper e
  change finrank ℝ g = finrank ℝ h + 2 * finrank ℂ V at htotal
  rw [Module.finrank_baseChange, hdim] at hpar
  have hrank : finrank ℂ A = 2 := by omega
  obtain ⟨b⟩ := RootPairing.nonempty_base (rootSystem A)
  obtain ⟨hS, hd, s, hm⟩ := rank_two_nonselfdual_forces_A2 A b hn hrank
  letI := hS
  rw [Module.finrank_baseChange] at hd
  have hN : finrank ℂ V = 22 := by omega
  have hmat : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j :=
    fun i j => (hm i j).trans ((show ∀ i j : Fin 2, matrix (datum 1) i j = matrix t.datum i j by decide) i j)
  obtain ⟨χ,v,c,hv,hev,hpos,hc⟩ := exists_bounded_dominant_highest_weight (M := V) A b
  let a : t.Label := fun i => (c (s i) : ℕ)
  have ha (i : Fin 2) : χ (coroot (s i).val.val) = (a i : ℂ) := hc (s i)
  refine ⟨hgK,hhK,A,H,hA,hH,hS,hN,b,s,a,χ,v,hmat,hv,hev,hpos,ha,?_⟩
  intro bg sg hmg
  obtain ⟨i,-,hi⟩ := actual_long_coroot_trace A b t s hmat χ a (fun i => ha i) hv hev hpos
  let α : A.root := s i
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨x,u,w,T,hu,hw⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have hx := T.h_eq_coroot hα hu hw
  subst x
  obtain ⟨m,hmult⟩ := compact_pair_index_divisibility B h hproper e H bg sg
    exceptional_root_tables_certified.2.1 hmg exceptional_killing_trace_divisors.2.1
      T (hnest (coroot α.val))
  rw [hN] at hi
  exact compatible_of_trace_multiple .f4 22 t a m (by simpa using hi.symm.trans hmult)

end CubicAnomaly.Classification.ExceptionalSieveF4
