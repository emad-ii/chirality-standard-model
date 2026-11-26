import CubicAnomaly.Classification.ClassicalConstituentChamber
import CubicAnomaly.Classification.WeylComponentObstruction

/-!
# Diagram symmetry forced by a complex quotient

A reversing Weyl word permutes the nodes and preserves their Cartan
matrix. If all nodes are fixed, its action on the coroot basis is
negation. A pair of inequivalent duals therefore gives a nontrivial
diagram symmetry. In every rank this excludes both marked paths B
and C, whose directed double edge fixes its endpoint and then the
entire path.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentDiagram

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ClassicalConstituentWeyl ClassicalConstituentChamber WeylDualityObstruction
open Structural WeylComponentObstruction
open scoped TensorProduct

private theorem typeB_rigid {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hc : ∀ i j, CartanMatrix.B n (σ i) (σ j) = CartanMatrix.B n i j) : ∀ i, σ i = i := by
  rcases n with _ | _ | k
  · exact fun i => Fin.elim0 i
  · intro i; apply Fin.ext; have := (σ i).isLt; have := i.isLt; omega
  let u : Fin (k+2) := ⟨k, by omega⟩
  let v : Fin (k+2) := ⟨k+1, by omega⟩
  have marked (i j : Fin (k+2)) : CartanMatrix.B (k+2) i j = -2 ↔ i = u ∧ j = v := by
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, u, v]
    split_ifs <;> simp_all <;> omega
  obtain ⟨hu,hv⟩ := (marked (σ u) (σ v)).mp ((hc u v).trans ((marked u v).mpr ⟨rfl,rfl⟩))
  have step (m : ℕ) : ∀ i : Fin (k+2), k+1-i.val = m → σ i = i := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i hm
      by_cases hi : i.val = k
      · have he : i = u := Fin.ext hi
        simpa [he] using hu
      by_cases hi' : i.val = k+1
      · have he : i = v := Fin.ext hi'
        simpa [he] using hv
      have hlt : i.val < k := by omega
      let j : Fin (k+2) := ⟨i.val+1, by omega⟩
      let l : Fin (k+2) := ⟨i.val+2, by omega⟩
      have hj : σ j = j := ih _ (show k+1-j.val < m by dsimp [j]; omega) j rfl
      have hl : σ l = l := ih _ (show k+1-l.val < m by dsimp [l]; omega) l rfl
      have hneq : (σ i).val ≠ l.val := by
        intro he
        have h := σ.injective ((Fin.ext he).trans hl.symm)
        have h := congrArg Fin.val h
        dsimp [l] at h
        omega
      have h := hc i j
      rw [hj] at h
      apply Fin.ext
      simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, j] at h
      change (σ i).val ≠ i.val+2 at hneq
      split_ifs at h <;> omega
  exact fun i => step _ i rfl


section Cartan

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

private theorem cartan_eq_applyWord (w : List H.root) (x : H) :
    cartanWord H w x = applyWord H w x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => exact ih _

/-- Without Weyl negation there is an actual nonidentity automorphism
of the based Cartan matrix. -/
theorem exists_nontrivial_diagram_symmetry
    (hn : ¬ ∃ w : List H.root, ∀ z : H, applyWord H w z = -z) :
    ∃ δ : Equiv.Perm b.support, (∃ i, δ i ≠ i) ∧
      ∀ i j, b.cartanMatrix (δ i) (δ j) = b.cartanMatrix i j := by
  obtain ⟨w,hw⟩ := exists_reversing_word H b
  obtain ⟨δ,hd⟩ := exists_opposition_nodes H b w hw
  refine ⟨δ, ?_, fun i j => ?_⟩
  · by_contra! hh
    apply hn
    refine ⟨w, fun z => ?_⟩
    rw [← cartan_eq_applyWord]
    rw [← b.toCoweightBasis.sum_repr z]
    simp only [map_sum, map_smul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h := (hd i).2
    rw [hh] at h
    rw [b.toCoweightBasis_apply]
    change _ • cartanWord H w (coroot i.val.val) = _
    rw [h, smul_neg]
    rfl
  · have p (i j : b.support) : ((b.cartanMatrix i j : ℤ) : ℂ) = i.val.val (coroot j.val.val) :=
      b.algebraMap_cartanMatrixIn_apply ℤ i j
    apply (Int.cast_injective (α := ℂ))
    rw [p, p, (hd i).1, (hd j).2]
    change -((i.val.val : Dual ℂ H) (-coroot j.val.val)) = _
    rw [map_neg, neg_neg]
    rfl

/-- Neither marked classical path admits Weyl opposition on a Cartan
without a negating Weyl word. This includes all ranks. -/
theorem not_type_B_or_C
    (hn : ¬ ∃ w : List H.root, ∀ z : H, applyWord H w z = -z) {n : ℕ}
    (e : b.support ≃ Fin n) :
    Matrix.reindex e e b.cartanMatrix ≠ CartanMatrix.B n ∧
      Matrix.reindex e e b.cartanMatrix ≠ CartanMatrix.C n := by
  obtain ⟨δ, ⟨i, hi⟩, hd⟩ := exists_nontrivial_diagram_symmetry H b hn
  let σ := e.symm.trans (δ.trans e)
  let A := Matrix.reindex e e b.cartanMatrix
  have hA (j k : Fin n) : A (σ j) (σ k) = A j k := by
    change b.cartanMatrix (e.symm (e (δ (e.symm j)))) (e.symm (e (δ (e.symm k)))) = _
    simpa only [Equiv.symm_apply_apply] using hd (e.symm j) (e.symm k)
  have rigid (hb : ∀ j k, CartanMatrix.B n (σ j) (σ k) = CartanMatrix.B n j k) : False := by
    have hf := typeB_rigid σ hb (e i)
    apply hi
    apply e.injective
    simpa [σ] using hf
  constructor <;> intro he
  · exact rigid (fun j k => by simpa only [A,he] using hA j k)
  · apply rigid
    intro j k
    have hh := hA k j
    simp only [A,he, ← CartanMatrix.B_transpose, Matrix.transpose_apply] at hh
    exact hh

end Cartan

end CubicAnomaly.Classification.ClassicalConstituentDiagram
