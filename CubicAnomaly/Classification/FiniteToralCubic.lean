import CubicAnomaly.Classification.CartanCubic

/-!
# Cubic detection from an explicit toral and root spanning family

The familiar Cartan argument needs only commuting toral vectors, nonzero
root weights, and the fact that opposite roots bracket into the toral span.
This version isolates those finite, directly checkable hypotheses. It does
not require a classification theorem or a nondegenerate Killing form.
-/

namespace CubicAnomaly.Classification.FiniteToralCubic

open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanCubic

variable {K L τ σ : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

omit [CharZero K] in
private theorem cyclic
    (c : TrilinearForm (R := K) (L := L) (S := K)) (hs : IsSymmetric c)
    (x y z : L) : c x y z = c z x y := by
  rw [hs.2, hs.1]

/-- An explicit toral element is in the full mixed radical if its toral
insertions vanish. The hypotheses are all relations among a spanning family. -/
theorem toral_mem_radical_of_spanning
    (h : τ → L) (e : σ → L) (w : σ → τ → K)
    (hspan : Submodule.span K (Set.range h ∪ Set.range e) = ⊤)
    (hhh : ∀ i j, ⁅h i, h j⁆ = 0)
    (hhe : ∀ i r, ⁅h i, e r⁆ = w r i • e r)
    (hw : ∀ r, ∃ i, w r i ≠ 0)
    (hopp : ∀ r s, (∀ i, w r i + w s i = 0) →
      ⁅e r, e s⁆ ∈ Submodule.span K (Set.range h))
    (c : TrilinearForm (R := K) (L := L) (S := K))
    (hc : IsInvariant c) (hs : IsSymmetric c)
    (a : τ) (ha : ∀ i j, c (h a) (h i) (h j) = 0) :
    h a ∈ radical c hc := by
  classical
  have htoral (i : τ) {v : L} (hv : v ∈ Submodule.span K (Set.range h)) :
      c (h a) (h i) v = 0 := by
    have hle : Submodule.span K (Set.range h) ≤ LinearMap.ker (c (h a) (h i)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact ha i j
    exact hle hv
  have hmixed (i : τ) (r : σ) : c (h a) (h i) (e r) = 0 := by
    obtain ⟨j, hj⟩ := hw r
    have hh := hc (h j) (h a) (h i) (e r)
    rw [hhh, hhh, hhe] at hh
    simp only [map_zero, LinearMap.zero_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, zero_add] at hh
    exact (mul_eq_zero.mp hh).resolve_left hj
  have hroots (r s : σ) : c (h a) (e r) (e s) = 0 := by
    by_cases hsum : ∀ i, w r i + w s i = 0
    · have hbr := hopp r s hsum
      have rel (i : τ) :
          w r i * c (h a) (e r) (e s) + w r a * c (h i) (e r) (e s) = 0 := by
        have hh := hc (e r) (h i) (e s) (h a)
        have hri : ⁅e r, h i⁆ = -(w r i) • e r := by
          rw [← lie_skew, hhe, neg_smul]
        have hra : ⁅e r, h a⁆ = -(w r a) • e r := by
          rw [← lie_skew, hhe, neg_smul]
        have hmid : c (h i) ⁅e r, e s⁆ (h a) = 0 := by
          rw [cyclic c hs]
          exact htoral i hbr
        rw [hri, hra, hmid] at hh
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, add_zero] at hh
        rw [cyclic c hs (e r) (e s) (h a), hs.2 (h i) (e s) (e r)] at hh
        linear_combination -hh
      by_cases hra : w r a = 0
      · obtain ⟨i, hi⟩ := hw r
        have hh := rel i
        rw [hra, zero_mul, add_zero] at hh
        exact (mul_eq_zero.mp hh).resolve_left hi
      · have hh : (2 : K) * (w r a * c (h a) (e r) (e s)) = 0 := by
          linear_combination rel a
        exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))).resolve_left hra
    · push_neg at hsum
      obtain ⟨i, hi⟩ := hsum
      have hh := hc (h i) (h a) (e r) (e s)
      rw [hhh, hhe, hhe] at hh
      simp only [map_zero, LinearMap.zero_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, zero_add] at hh
      have hh' : (w r i + w s i) * c (h a) (e r) (e s) = 0 := by
        linear_combination hh
      exact (mul_eq_zero.mp hh').resolve_left hi
  have hgenerators : ∀ y ∈ Set.range h ∪ Set.range e,
      ∀ z ∈ Set.range h ∪ Set.range e, c (h a) y z = 0 := by
    rintro y (⟨i, rfl⟩ | ⟨r, rfl⟩) z (⟨j, rfl⟩ | ⟨s, rfl⟩)
    · exact ha i j
    · exact hmixed i s
    · rw [hs.2]
      exact hmixed j r
    · exact hroots r s
  have houter : Submodule.span K (Set.range h ∪ Set.range e) ≤
      LinearMap.ker (c (h a)) := by
    apply Submodule.span_le.mpr
    intro y hy
    apply LinearMap.ext
    intro z
    have hinner : Submodule.span K (Set.range h ∪ Set.range e) ≤
        LinearMap.ker (c (h a) y) := Submodule.span_le.mpr (hgenerators y hy)
    exact hinner (hspan.symm ▸ Submodule.mem_top)
  change c (h a) = 0
  apply LinearMap.ext
  intro y
  exact houter (hspan.symm ▸ Submodule.mem_top)

end CubicAnomaly.Classification.FiniteToralCubic
