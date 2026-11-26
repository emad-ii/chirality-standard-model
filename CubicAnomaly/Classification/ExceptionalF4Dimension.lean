import CubicAnomaly.Classification.RootClassificationDynkin
import CubicAnomaly.Classification.KillingDimension

/-! # Recognition of the exceptional 52-dimensional ambient algebra

The dimension is the Cartan dimension plus the number of roots. The
finite Cartan classification and the rank bound reduce recognition of F₄
to verifiable reflection-closed root counts at bounded classical ranks.
-/

namespace CubicAnomaly.Classification.ExceptionalF4Dimension

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open Exceptional RootClassificationExceptional Selection KillingDimension

private def canon (t : Fin 4) (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  ![CartanMatrix.A n, CartanMatrix.B n, CartanMatrix.C n, CartanMatrix.D n] t

private def datum (t : Fin 4) (n : ℕ) : RootDatum :=
  ⟨Array.ofFn (fun i : Fin n => Array.ofFn (canon t n i)), Array.replicate n 1⟩

private theorem rank_eq (t : Fin 4) (n : ℕ) : (datum t n).cartan.size = n := by simp [datum]

private def indices (t : Fin 4) (n : ℕ) : Index (datum t n) ≃ Fin n := finCongr (rank_eq t n)

private theorem matrix_eq (t : Fin 4) (n : ℕ) (i j : Index (datum t n)) :
    matrix (datum t n) i j = canon t n (indices t n i) (indices t n j) := by
  have hi : i.val < n := by simpa only [rank_eq] using i.isLt
  have hj : j.val < n := by simpa only [rank_eq] using j.isLt
  simp [matrix, datum, getElem!_pos, hi, hj, indices]
  rfl

private theorem classical_dimensions : ∀ t : Fin 4, ∀ n : Fin 18, n.val % 2 = 0 →
    Certified (datum t n) ∧ n.val + (table (datum t n)).card ≠ 52 := by native_decide

private theorem exceptional_dimensions :
    g2Datum.cartan.size + (table g2Datum).card ≠ 52 ∧
    e6Datum.cartan.size + (table e6Datum).card ≠ 52 ∧
    e7Datum.cartan.size + (table e7Datum).card ≠ 52 ∧
    e8Datum.cartan.size + (table e8Datum).card ≠ 52 := by native_decide

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] [LieAlgebra.IsSimple ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

omit [LieAlgebra.IsSimple ℂ L] in
private theorem dimension_of_equiv {d : RootDatum} (s : Index d ≃ b.support)
    (e : ↥(table d) ≃ H.root) : finrank ℂ L = d.cartan.size + (table d).card := by
  have hr : finrank ℂ H = d.cartan.size :=
    (finrank_eq_card_basis (b.toCoweightBasis.reindex s.symm)).trans (Fintype.card_fin _)
  rw [killing_finrank_eq_cartan_add_roots H, actual_root_count_eq_card H, hr,
    ← Fintype.card_congr e, Fintype.card_coe]

/-- The Cartan matrix of an arbitrary simple complex Killing algebra of
dimension 52 agrees, including its indexed entries, with F₄. -/
theorem dim52_matching_F4 (hdim : finrank ℂ L = 52) :
    ∃ s : Index f4Datum ≃ b.support, ∀ i j, b.cartanMatrix (s i) (s j) = matrix f4Datum i j := by
  rcases simple_lie_classical_or_exceptional_census H b with hcl | ⟨d, hd, s, hs, e, _⟩
  · have hnon (t : Fin 4) (n : ℕ) (e : b.support ≃ Fin n)
        (hm : b.cartanMatrix.reindex e e = canon t n) : False := by
      have hr : finrank ℂ H = n :=
        (finrank_eq_card_basis (b.toCoweightBasis.reindex e)).trans (Fintype.card_fin _)
      have hlim := three_cartan_finrank_le H
      have hpar := killing_dimension_parity H
      rw [hr, hdim] at hlim hpar
      obtain ⟨hc,hc'⟩ := classical_dimensions t ⟨n,by omega⟩ (by change n % 2 = 0; omega)
      let s := (indices t n).trans e.symm
      have h (i j : Index (datum t n)) : b.cartanMatrix (s i) (s j) = matrix (datum t n) i j := by
        rw [matrix_eq]
        exact congrFun (congrFun hm (indices t n i)) (indices t n j)
      obtain ⟨f,_⟩ := exists_census_root_equiv b s hc h
      have hd := dimension_of_equiv H b s f
      apply hc'
      change n + (table (datum t n)).card = 52
      exact (congrArg (· + (table (datum t n)).card) (rank_eq t n).symm).trans (hd.symm.trans hdim)
    rcases hcl with ⟨n,e,h⟩ | ⟨n,e,h⟩ | ⟨n,e,h⟩ | ⟨n,e,h⟩
    · exact (hnon 0 n e h).elim
    · exact (hnon 1 n e h).elim
    · exact (hnon 2 n e h).elim
    · exact (hnon 3 n e h).elim
  · have he := dimension_of_equiv H b s e
    rw [hdim] at he
    obtain rfl | rfl | rfl | rfl | rfl := hd
    · exact (exceptional_dimensions.1 he.symm).elim
    · exact ⟨s,hs⟩
    · exact (exceptional_dimensions.2.1 he.symm).elim
    · exact (exceptional_dimensions.2.2.1 he.symm).elim
    · exact (exceptional_dimensions.2.2.2 he.symm).elim

private theorem rank_four_classical_dimensions : ∀ t : Fin 4,
    Certified (datum t 4) ∧ 4 + (table (datum t 4)).card ≠ 14 := by native_decide

private theorem exceptional_rank_at_fourteen : ∀ d ∈ [g2Datum, f4Datum, e6Datum, e7Datum, e8Datum],
    d.cartan.size + (table d).card = 14 → d.cartan.size ≤ 2 := by native_decide

include b in
/-- A simple complex Killing algebra of dimension fourteen has Cartan rank at most two. -/
theorem dim14_cartan_finrank_le_two (hdim : finrank ℂ L = 14) : finrank ℂ H ≤ 2 := by
  have hlim := three_cartan_finrank_le H
  have hpar := killing_dimension_parity H
  rw [hdim] at hlim hpar
  by_contra! hlarge
  have hr : finrank ℂ H = 4 := by omega
  rcases simple_lie_classical_or_exceptional_census H b with hcl | ⟨d, hd, s, _, e, _⟩
  · have hnon (t : Fin 4) (n : ℕ) (e : b.support ≃ Fin n)
        (hm : b.cartanMatrix.reindex e e = canon t n) : False := by
      have hnr : finrank ℂ H = n :=
        (finrank_eq_card_basis (b.toCoweightBasis.reindex e)).trans (Fintype.card_fin _)
      obtain rfl : n = 4 := hnr.symm.trans hr
      obtain ⟨hc, hne⟩ := rank_four_classical_dimensions t
      let s := (indices t 4).trans e.symm
      have h (i j : Index (datum t 4)) : b.cartanMatrix (s i) (s j) = matrix (datum t 4) i j := by
        rw [matrix_eq]
        exact congrFun (congrFun hm (indices t 4 i)) (indices t 4 j)
      obtain ⟨f, _⟩ := exists_census_root_equiv b s hc h
      have hd := dimension_of_equiv H b s f
      exact hne ((congrArg (· + (table (datum t 4)).card) (rank_eq t 4).symm).trans
        (hd.symm.trans hdim))
    rcases hcl with ⟨n,e,h⟩ | ⟨n,e,h⟩ | ⟨n,e,h⟩ | ⟨n,e,h⟩
    · exact hnon 0 n e h
    · exact hnon 1 n e h
    · exact hnon 2 n e h
    · exact hnon 3 n e h
  · have hsz : finrank ℂ H = d.cartan.size :=
      (finrank_eq_card_basis (b.toCoweightBasis.reindex s.symm)).trans (Fintype.card_fin _)
    have he := dimension_of_equiv H b s e
    have hmem : d ∈ [g2Datum, f4Datum, e6Datum, e7Datum, e8Datum] := by simpa using hd
    have hc := exceptional_rank_at_fourteen d hmem (he.symm.trans hdim)
    omega

end CubicAnomaly.Classification.ExceptionalF4Dimension
