import CubicAnomaly.Classification.ExceptionalSieveA2Cubic
import CubicAnomaly.Classification.ExceptionalSieveF4

/-! # Rank-two isotropy in an E₆ ambient algebra

The unique non-self-dual rank-two type has a coroot of intrinsic Killing
length 12. The vanishing cubic makes its representation trace a multiple
of four, contradicting the E₆ ambient Killing divisor sixteen.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveE6Singleton

open LieAlgebra LieModule Module LieAlgebra.IsKilling ExceptionalSieveA2Cubic
open ExceptionalSieveCatalog ExceptionalSieveNormalization ExceptionalSieveProducts
open ExceptionalSieveF4 ExceptionalSieveWeights ExceptionalSieveIndex RootClassificationExceptional
open Structural CompactGeometry Complexification HermitianRealization ComplexDuality AllRankComplex
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

set_option maxHeartbeats 800000 in
/-- On any prescribed nested Cartans, rank two for the isotropy excludes
an E₆ ambient Cartan under the original compact-pair hypotheses. -/
theorem compact_pair_e6_singleton_excluded
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] g)] [IsKilling ℂ (ℂ ⊗[ℝ] h)]
    (A : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [A.IsCartanSubalgebra]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hnest : ∀ z : A, complexifiedLieHom h.incl z.val ∈ H) (hRankTwo : finrank ℂ A = 2)
    (bg : (rootSystem H).Base) (sg : Index Exceptional.e6Datum ≃ bg.support)
    (hmg : ∀ i j, bg.cartanMatrix (sg i) (sg j) = matrix Exceptional.e6Datum i j) : False := by
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  have hdec := (all_rank_complex_structural_reduction B h heff hproper e hr).2.2.2.2.2
  haveI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) V := hdec.2.1
  haveI : Nontrivial V := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) V
  have hn : ¬Nonempty (V ≃ₗ⁅ℂ,ℂ ⊗[ℝ] h⁆ Dual ℂ V) :=
    fun ⟨f⟩ => hdec.2.2.2.2 ⟨f.trans hdec.2.2.2.1.some.symm⟩
  obtain ⟨b⟩ := RootPairing.nonempty_base (rootSystem A)
  obtain ⟨hS, -, s, hm⟩ := rank_two_nonselfdual_forces_A2 A b hn hRankTwo
  letI := hS
  let t : Factor := .a 1
  have hmat : ∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j :=
    fun i j => (hm i j).trans ((show ∀ i j : Fin 2,
      matrix (ExceptionalSieveRankTwo.datum 1) i j = matrix t.datum i j by decide) i j)
  obtain ⟨χ,v,c,hv,hev,hpos,hc⟩ := exists_bounded_dominant_highest_weight (M := V) A b
  let a : t.Label := fun j => (c (s j) : ℕ)
  obtain ⟨i,hiκ,-⟩ := actual_long_coroot_trace A b t s hmat χ a (fun i => hc (s i)) hv hev hpos
  obtain ⟨j,hj⟩ := (show ∀ i : Fin 2, ∃ j, matrix t.datum i j = -1 by decide) i
  let α : A.root := s i
  let β : A.root := s j
  have hp : α.val (coroot β.val) = -1 := by
    have he := b.algebraMap_cartanMatrixIn_apply ℤ (s i) (s j)
    change ((b.cartanMatrix (s i) (s j) : ℤ) : ℂ) = α.val (coroot β.val) at he
    rw [← he, hmat, hj]
    norm_num
  obtain ⟨n, hq⟩ := four_dvd_trace_of_zero_cubic A α β hp (compact_simple_cartan_cubic_zero B h e hr A _ _ _)
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨x,u,w,T,hu,hw⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have hx := T.h_eq_coroot hα hu hw
  subst x
  obtain ⟨m, hm⟩ := compact_pair_index_divisibility B h hproper e H bg sg
    exceptional_root_tables_certified.2.2.1 hmg exceptional_killing_trace_divisors.2.2.1
    T (hnest (coroot α.val))
  change killingForm ℂ (ℂ ⊗[ℝ] h) (coroot α.val : ℂ ⊗[ℝ] h) (coroot α.val : ℂ ⊗[ℝ] h) = _ at hiκ
  change killingForm ℂ (ℂ ⊗[ℝ] h) (coroot α.val : ℂ ⊗[ℝ] h) (coroot α.val : ℂ ⊗[ℝ] h) +
    2 * traceForm ℂ (ℂ ⊗[ℝ] h) V (coroot α.val : ℂ ⊗[ℝ] h) (coroot α.val : ℂ ⊗[ℝ] h) = _ at hm
  rw [hiκ, hq] at hm
  change (4 : ℂ) * (3 : ℕ) + 2 * (4 * n) = ((16 * m : ℤ) : ℂ) at hm
  have h : (4 : ℤ)*3 + 2*(4*n) = 16*m := by exact_mod_cast hm
  omega

end CubicAnomaly.Classification.ExceptionalSieveE6Singleton
