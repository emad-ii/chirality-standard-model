import CubicAnomaly.Classification.ExceptionalSieveFactorIndex
import CubicAnomaly.Classification.IdealTensorDuality
import CubicAnomaly.Classification.IdealProductRepresentation
import CubicAnomaly.Classification.ExceptionalSieveIndex
import CubicAnomaly.Classification.ExceptionalSieveProducts
import CubicAnomaly.Classification.ExceptionalSieveRankTwo

/-!
# Actual ambient divisibility for the exceptional rank-deficient sieve

Nested isotropy and ambient Cartans come from the original compact inclusion.
Identifying the ambient simple Cartan matrix with an exceptional type then
imposes the numerical sieve divisor on every actual isotropy coroot.
-/

namespace CubicAnomaly.Classification.ExceptionalSieve

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.ExceptionalSieveCatalog
open CubicAnomaly.Classification.ExceptionalSieveNormalization
open CubicAnomaly.Classification.ExceptionalSieveFactorIndex
open CubicAnomaly.Classification.ExceptionalSieveProducts
open CubicAnomaly.Classification.ExceptionalSieveIndex
open CubicAnomaly.Classification.RootClassificationExceptional
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactCartan
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.AllRankComplex
open scoped TensorProduct

def ambientDatum : Ambient → RootDatum
  | .g2 => g2Datum | .f4 => f4Datum | .e6 => e6Datum | .e7 => e7Datum | .e8 => e8Datum

private theorem ambient_certified (G : Ambient) :
    Certified (ambientDatum G) ∧ TraceDivisor (ambientDatum G) G.divisor := by
  obtain ⟨c₁,c₂,c₃,c₄,c₅⟩ := exceptional_root_tables_certified
  obtain ⟨d₁,d₂,d₃,d₄,d₅⟩ := exceptional_killing_trace_divisors
  cases G with
  | g2 => exact ⟨c₁,d₁⟩
  | f4 => exact ⟨c₂,d₂⟩
  | e6 => exact ⟨c₃,d₃⟩
  | e7 => exact ⟨c₄,d₄⟩
  | e8 => exact ⟨c₅,d₅⟩

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- For every isotropy coroot in the constructed nested Cartan, the actual
quadratic restriction is an integer multiple of the classified ambient
divisor. No normalized embedding index or integrality premise is supplied. -/
theorem all_rank_exceptional_coroot_index_test
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    ∃ (hgK : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)) (hhK : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)),
      letI := hgK
      letI := hhK
      ∃ (A : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
        (hA : A.IsCartanSubalgebra) (hH : H.IsCartanSubalgebra),
        letI := hA
        letI := hH
        finrank ℂ A = abelianRank ℝ h ∧
        ∀ (G : Ambient) (b : (rootSystem H).Base) (s : Index (ambientDatum G) ≃ b.support),
          (∀ i j, b.cartanMatrix (s i) (s j) = matrix (ambientDatum G) i j) →
          ∀ α : A.root, ∃ m : ℤ,
            let x : ℂ ⊗[ℝ] h := coroot α.val
            killingForm ℂ (ℂ ⊗[ℝ] h) x x + 2 * traceForm ℂ (ℂ ⊗[ℝ] h) V x x =
              ((G.divisor * m : ℤ) : ℂ) := by
  obtain ⟨-, -, hgK, hhK, -, -⟩ :=
    all_rank_complex_structural_reduction B h heff hproper e hradical
  letI := hgK
  letI := hhK
  obtain ⟨A, H, hA, hH, hd, hn⟩ := compact_pair_nested_cartans B h
  letI := hA
  letI := hH
  refine ⟨hgK, hhK, A, H, hA, hH, hd, ?_⟩
  intro G b s hmat α
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨x, u, v, t, hu, hv⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have hx := t.h_eq_coroot hα hu hv
  subst x
  exact compact_pair_index_divisibility B h hproper e H b s (ambient_certified G).1 hmat
    (ambient_certified G).2 t (hn (coroot α.val))

section Ideal

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L]

/-- The intrinsic Killing form of every atomic ideal is nondegenerate. -/
theorem atomic_ideal_isKilling (I : LieIdeal ℂ L) (hI : IsAtom I) : LieAlgebra.IsKilling ℂ I := by
  have hn : (killingForm ℂ I).Nondegenerate := by
    rw [LieIdeal.killingForm_eq]
    exact IdealTensorDuality.atomic_ideal_killing_form_nondegenerate I hI
  constructor
  rw [← LieSubmodule.toSubmodule_inj]
  exact (LieIdeal.coe_killingCompl_top ℂ I).trans hn.ker_eq_bot

/-- Every ideal inherits a Cartan by intersection with the ambient Cartan. -/
theorem ideal_intersection_isCartan (A : LieSubalgebra ℂ L) [A.IsCartanSubalgebra]
    (I : LieIdeal ℂ L) : (A.comap I.toLieSubalgebra.incl).IsCartanSubalgebra := by
  let C : LieSubalgebra ℂ I := A.comap I.toLieSubalgebra.incl
  letI : IsLieAbelian C := ⟨fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => (z : L)) (trivial_lie_zero A A (⟨x.val.val,x.property⟩ : A)
      (⟨y.val.val,y.property⟩ : A))⟩
  refine ⟨inferInstanceAs (LieRing.IsNilpotent C), le_antisymm ?_ C.le_normalizer⟩
  intro x hx
  change (x : L) ∈ A
  have hn : (x : L) ∈ A.normalizer := by
    apply (A.mem_normalizer_iff _).mpr
    intro y hy
    obtain ⟨u,v,hu,hv,hs⟩ := CorootComponents.cartan_ideal_parts A I ⟨y,hy⟩
    have hy' : (u : L) + v = y := congrArg Subtype.val hs
    rw [← hy', lie_add]
    have hz : ⁅(x : L), (v : L)⁆ = 0 :=
      IdealProductRepresentation.disjoint_ideals_bracket_zero I Iᶜ disjoint_compl_right x ⟨v,hv⟩
    rw [hz, add_zero]
    exact ((C.mem_normalizer_iff x).mp hx) (⟨u,hu⟩ : I) u.property
  simpa only [LieSubalgebra.IsCartanSubalgebra.self_normalizing] using hn

end Ideal

set_option maxHeartbeats 0 in
/-- Every classified simple isotropy factor supplies an actual highest-weight
row passing the exceptional sieve's index test, in the Cartans obtained
from the original compact pair. The rank of the isotropy is unrestricted. -/
theorem all_rank_exceptional_factor_index
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    ∃ (hgK : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)) (hhK : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)),
      letI := hgK
      letI := hhK
      ∃ (A : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
        (hA : A.IsCartanSubalgebra) (hH : H.IsCartanSubalgebra),
        letI := hA
        letI := hH
        finrank ℂ A = abelianRank ℝ h ∧
        ∀ (G : Ambient) (bg : (rootSystem H).Base) (sg : Index (ambientDatum G) ≃ bg.support),
          (∀ i j, bg.cartanMatrix (sg i) (sg j) = matrix (ambientDatum G) i j) →
          ∀ (I : LieIdeal ℂ (ℂ ⊗[ℝ] h)) (hI : IsAtom I),
            let C : LieSubalgebra ℂ I := A.comap I.toLieSubalgebra.incl
            letI := atomic_ideal_isKilling I hI
            letI := ideal_intersection_isCartan A I
            ∀ (b : (rootSystem C).Base) (t : Factor) (s : Index t.datum ≃ b.support),
              (∀ i j, b.cartanMatrix (s i) (s j) = matrix t.datum i j) →
              ∃ (S : LieSubmodule ℂ I V) (a : t.Label) (χ : Weight ℂ C S) (v : S),
                IsAtom S ∧ IsIrreducible ℂ I S ∧ v ≠ 0 ∧ (∀ z : C, ⁅z, v⁆ = χ z • v) ∧
                (∀ α : C.root, b.IsPos α → ∀ z ∈ rootSpace C α.val, ⁅z, v⁆ = 0) ∧
                (∀ i, χ (coroot (s i).val.val) = (a (nodes t i) : ℂ)) ∧
                Compatible G (finrank ℂ V) (row t a) := by
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  obtain ⟨-, -, hgK, hhK, -, -⟩ := all_rank_complex_structural_reduction B h heff hproper e hradical
  letI := hgK
  letI := hhK
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) V :=
    (ComplexDuality.compact_complement_complex_type_decomposition B h hproper e).2.1
  obtain ⟨A, H, hA, hH, hd, hn⟩ := compact_pair_nested_cartans B h
  letI := hA
  letI := hH
  refine ⟨hgK, hhK, A, H, hA, hH, hd, ?_⟩
  intro G bg sg hg I hI
  let C : LieSubalgebra ℂ I := A.comap I.toLieSubalgebra.incl
  letI := atomic_ideal_isKilling I hI
  letI := ideal_intersection_isCartan A I
  letI : LieAlgebra.IsSimple ℂ I := LieAlgebra.IsSemisimple.isSimple_of_isAtom I hI
  dsimp only
  intro b t s hmat
  obtain ⟨S, a, χ, v, hS, hir, hv, hev, hp, ha, i, hi⟩ :=
    simple_factor_index_numerator (W := V) I Iᶜ disjoint_compl_right sup_compl_eq_top
      C b t s hmat
  refine ⟨S, a, χ, v, hS, hir, hv, hev, hp, ha, ?_⟩
  let α : C.root := s i
  have hα : α.val.IsNonZero := (Finset.mem_filter.mp α.property).2
  obtain ⟨x, u, w, T, hu, hw⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have hx := T.h_eq_coroot hα hu hw
  subst x
  let x : I := coroot α.val
  have T' : IsSl2Triple (x : ℂ ⊗[ℝ] h) (u : ℂ ⊗[ℝ] h) (w : ℂ ⊗[ℝ] h) :=
    { h_ne_zero := fun hz => T.h_ne_zero (Subtype.ext hz)
      lie_e_f := congrArg Subtype.val T.lie_e_f
      lie_h_e_nsmul := congrArg Subtype.val T.lie_h_e_nsmul
      lie_h_f_nsmul := congrArg Subtype.val T.lie_h_f_nsmul }
  obtain ⟨m, hm⟩ := compact_pair_index_divisibility B h hproper e H bg sg
    (ambient_certified G).1 hg (ambient_certified G).2 T' (hn ⟨x, (coroot α.val).property⟩)
  exact compatible_of_trace_multiple G (finrank ℂ V) t a m (hi.symm.trans hm)

end CubicAnomaly.Classification.ExceptionalSieve
