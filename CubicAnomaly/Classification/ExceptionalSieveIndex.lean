import CubicAnomaly.Classification.ExceptionalSieveWeights
import CubicAnomaly.Classification.CompactCartan
import CubicAnomaly.Classification.RootClassificationExceptional

/-!
# Exceptional divisibility of the Killing trace on an embedded sl₂ coroot

The eigenvalues of a triple on the ambient adjoint representation are
integers. In a Cartan containing its semisimple element the simple-root
evaluations are therefore integers. The full Killing trace is the sum of
squared evaluations over the genuine ambient roots. Its divisibility follows
from the diagonal and doubled off-diagonal coefficients of that quadratic
polynomial. This argument needs no integration of the embedding.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveIndex

open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.RootClassificationExceptional
open CubicAnomaly.Classification.ExceptionalSieveWeights
open Module LieAlgebra LieModule LieAlgebra.IsKilling

/-- Integer divisibility of all coefficients of the root sum of squares. -/
def TraceDivisor (d : RootDatum) (k : ℤ) : Prop :=
  (∀ i : Index d, k ∣ ∑ v : ↥(table d), v.val[i] ^ 2) ∧
  (∀ i j : Index d, k ∣ 2 * ∑ v : ↥(table d), v.val[i] * v.val[j])

instance (d : RootDatum) (k : ℤ) : Decidable (TraceDivisor d k) := by
  unfold TraceDivisor
  infer_instance

/-- The quadratic coefficient divisors, computed on the reflection-generated
ambient root lists in the same coordinates used for census transport. -/
theorem exceptional_killing_trace_divisors :
    TraceDivisor g2Datum 16 ∧ TraceDivisor f4Datum 36 ∧ TraceDivisor e6Datum 16 ∧
      TraceDivisor e7Datum 18 ∧ TraceDivisor e8Datum 120 := by
  native_decide

private theorem divides_root_square_sum {ι R : Type*} [Fintype R] (r : R → ι → ℤ)
    (k : ℤ) (hd : ∀ i, k ∣ ∑ v, r v i ^ 2)
    (hc : ∀ i j, k ∣ 2 * ∑ v, r v i * r v j) (z : ι → ℤ) (s : Finset ι) :
    k ∣ ∑ v, (∑ i ∈ s, r v i * z i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have expand (v : R) :
        (∑ j ∈ insert i s, r v j * z j) ^ 2 =
          r v i ^ 2 * z i ^ 2 + (∑ j ∈ s, r v j * z j) ^ 2 +
            ∑ j ∈ s, (2 * (r v i * r v j)) * (z i * z j) := by
      rw [Finset.sum_insert hi, add_sq]
      have he : 2 * (r v i * z i) * (∑ j ∈ s, r v j * z j) =
          ∑ j ∈ s, (2 * (r v i * r v j)) * (z i * z j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [he]
      ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_comm (s := Finset.univ) (t := s)]
    refine dvd_add (dvd_add (dvd_mul_of_dvd_left (hd i) _) ih) (Finset.dvd_sum fun j _ => ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    exact dvd_mul_of_dvd_left (hc i j) _

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  {d : RootDatum} (b : (rootSystem H).Base) (s : Index d ≃ b.support)

/-- For an actual triple whose coroot lies in this Cartan, matching the
simple Cartan matrix suffices to obtain the computed trace divisibility. -/
theorem triple_killing_trace_multiple (cert : Certified d)
    (hmatrix : ∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j)
    {k : ℤ} (hk : TraceDivisor d k) (x : H) {e f : L} (t : IsSl2Triple (x : L) e f) :
    ∃ m : ℤ, killingForm ℂ L x x = ((k * m : ℤ) : ℂ) := by
  classical
  obtain ⟨E, hE⟩ := exists_census_root_equiv b s cert hmatrix
  have heval (i : Index d) : ∃ a : ℤ, (s i).val.val x = (a : ℂ) := by
    obtain ⟨a, ha, -, -⟩ := sl2_eigenvalue_mem_integer_interval t ((s i).val.val.hasEigenvalueAt x)
    exact ⟨a, ha⟩
  choose z hz using heval
  let val (v : ↥(table d)) : ℤ := ∑ i, v.val[i] * z i
  have hroot (v : ↥(table d)) : (E v).val x = (val v : ℂ) := by
    change (rootSystem H).root (E v) x = _
    rw [hE]
    simp [realize, val, hz, LinearMap.sum_apply, zsmul_eq_mul]
  have hsum : killingForm ℂ L x x = ∑ α : H.root, (α.val x) ^ 2 := by
    have hh := LinearMap.congr_fun (LinearMap.congr_fun (restrict_killingForm_eq_sum (K := ℂ) (L := L) (H := H)) x) x
    rw [Finset.sum_coe_sort H.root (fun α : Weight ℂ H L => α x ^ 2)]
    convert hh using 1
    generalize H.root = S
    induction S using Finset.induction_on with
    | empty => simp
    | insert α S h ih =>
      rw [Finset.sum_insert h, Finset.sum_insert h, ih, sq]
      rfl
  rw [hsum, ← E.sum_comp (fun α : H.root => (α.val x) ^ 2)]
  simp_rw [hroot, ← Int.cast_pow, ← Int.cast_sum]
  obtain ⟨m, hm⟩ := divides_root_square_sum (fun v : ↥(table d) => fun i : Index d => v.val[i])
    k hk.1 hk.2 z Finset.univ
  exact ⟨m, congrArg (fun a : ℤ => (a : ℂ)) hm⟩

section CompactPair

open scoped TensorProduct
open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)]

open CubicAnomaly.Classification.CompactCartan

omit [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)] in
private theorem extend_compact_abelian (B : CompactForm g) (U : LieSubalgebra ℝ g)
    [IsLieAbelian U] :
    ∃ T : LieSubalgebra ℝ g, U ≤ T ∧ IsLieAbelian T ∧ T.IsCartanSubalgebra := by
  let dims := {n : ℕ | ∃ A : LieSubalgebra ℝ g, U ≤ A ∧ IsLieAbelian A ∧ finrank ℝ A = n}
  have hb : BddAbove dims := ⟨finrank ℝ g, by
    rintro n ⟨A, -, -, rfl⟩
    exact Submodule.finrank_le A.toSubmodule⟩
  have hn : dims.Nonempty := ⟨finrank ℝ U, U, le_rfl, inferInstance, rfl⟩
  obtain ⟨T, hUT, hT, hdim⟩ := Nat.sSup_mem hn hb
  letI := hT
  refine ⟨T, hUT, hT, ⟨inferInstance, le_antisymm ?_ T.le_normalizer⟩⟩
  intro x hx
  let D := LieSubalgebra.lieSpan ℝ g (insert x (T : Set g))
  have hTD : T ≤ D := fun y hy => LieSubalgebra.subset_lieSpan (Or.inr hy)
  have hcomm (y : g) (hy : y ∈ T) : ⁅x, y⁆ = 0 :=
    compact_abelian_normalizer_bracket_zero B T hx hy
  have hD : IsLieAbelian D := by
    apply LieSubalgebra.isLieAbelian_lieSpan_iff.mpr
    intro y hy z hz
    rcases hy with rfl | hy <;> rcases hz with rfl | hz
    · exact lie_self _
    · exact hcomm _ hz
    · rw [← lie_skew, hcomm _ hy, neg_zero]
    · exact congrArg Subtype.val (trivial_lie_zero T T (⟨y, hy⟩ : T) (⟨z, hz⟩ : T))
  have hle : finrank ℝ D ≤ finrank ℝ T := hdim ▸ le_csSup hb ⟨D, hUT.trans hTD, hD, rfl⟩
  have heq : T = D := LieSubalgebra.toSubmodule_injective (Submodule.eq_of_le_of_finrank_le hTD hle)
  exact heq ▸ LieSubalgebra.subset_lieSpan (Set.mem_insert _ _)

omit [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)] in
/-- Every compact inclusion has nested complexified Cartans. This extension
also applies at deficient rank: the isotropy Cartan maps into an ambient
Cartan, and attains the geometric rank of the isotropy algebra. -/
theorem compact_pair_nested_cartans (B : CompactForm g) (h : LieSubalgebra ℝ g) :
    ∃ (A : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)),
      A.IsCartanSubalgebra ∧ H.IsCartanSubalgebra ∧ finrank ℂ A = abelianRank ℝ h ∧
      ∀ x : A, complexifiedLieHom h.incl x ∈ H := by
  obtain ⟨T, hT, hdim⟩ := exists_abelian_finrank_eq_abelianRank ℝ h
  letI := hT
  letI : T.IsCartanSubalgebra := compact_maximum_abelian_isCartan (B.restrict h) T hdim
  let F := h.incl.comp T.incl
  let E := LieEquiv.ofInjective F (Subtype.val_injective.comp Subtype.val_injective)
  letI : IsLieAbelian F.range := (lie_abelian_iff_equiv_lie_abelian E).mp hT
  obtain ⟨D, hle, hD, hcart⟩ := extend_compact_abelian B F.range
  letI := hD
  letI := hcart
  refine ⟨complexifiedSubalgebra T, complexifiedSubalgebra D,
    complexified_abelian_cartan T, complexified_abelian_cartan D, ?_, ?_⟩
  · change finrank ℂ (T.toSubmodule.baseChange ℂ) = _
    rw [complexification_submodule_finrank]
    exact hdim
  · rintro ⟨x, ⟨z, rfl⟩⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c t =>
      let v : D := ⟨F t, hle ⟨t, rfl⟩⟩
      exact ⟨c ⊗ₜ[ℝ] v, rfl⟩
    | add z w hz hw => simpa only [map_add] using (complexifiedSubalgebra D).add_mem hz hw

/-- On an embedded isotropy triple the divisor applies to the actual sum of
the isotropy Killing trace and twice the trace of the canonical complex half.
This is a necessary index test using only the ambient simple Cartan matrix. -/
theorem compact_pair_index_divisibility (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    {d : RootDatum} (b : (rootSystem H).Base) (s : Index d ≃ b.support) (cert : Certified d)
    (hmatrix : ∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j)
    {k : ℤ} (hk : TraceDivisor d k) {x u v : ℂ ⊗[ℝ] h}
    (t : IsSl2Triple x u v) (hx : complexifiedLieHom h.incl x ∈ H) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    ∃ m : ℤ, killingForm ℂ (ℂ ⊗[ℝ] h) x x + 2 * traceForm ℂ (ℂ ⊗[ℝ] h) V x x =
      ((k * m : ℤ) : ℂ) := by
  let F := complexifiedLieHom h.incl
  have hinj : Function.Injective F :=
    complexification_linearMap_injective h.incl.toLinearMap Subtype.val_injective
  have t' : IsSl2Triple (F x) (F u) (F v) := {
    h_ne_zero := fun hz => t.h_ne_zero (hinj (hz.trans (map_zero F).symm))
    lie_e_f := by rw [← F.map_lie, t.lie_e_f]
    lie_h_e_nsmul := by rw [← F.map_lie, t.lie_h_e_nsmul, map_nsmul]
    lie_h_f_nsmul := by rw [← F.map_lie, t.lie_h_f_nsmul, map_neg, map_nsmul] }
  obtain ⟨m, hm⟩ := triple_killing_trace_multiple H b s cert hmatrix hk ⟨F x, hx⟩ t'
  exact ⟨m, (QuadraticRestriction.compact_pair_quadratic_restriction B h hproper e x x).symm.trans hm⟩

end CompactPair

end CubicAnomaly.Classification.ExceptionalSieveIndex
