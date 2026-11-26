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

end CubicAnomaly.Classification.ExceptionalSieve
