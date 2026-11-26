import CubicAnomaly.Classification.RootClassificationExceptional
import CubicAnomaly.Classification.Selection

/-!
# Reflection invariance of the exceptional assignment tests

Root-coordinate and character reflections are dual. They give an explicit
bijection at every grade, carry zero-root annihilators to annihilators, and
carry cubic kernels to cubic kernels by a change of variables in all three
slots of the actual coordinate sum.
-/

namespace CubicAnomaly.Classification.RootClassificationExceptional
open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.Selection
open Matrix

variable {d : RootDatum}

def reflectRow (d : RootDatum) (i : Index d) (v : Vector ℤ d.cartan.size) :=
  let c := ∑ j, v.get j * matrix d j i
  Vector.ofFn fun j => v.get j - if j = i then c else 0

def reflectDual {R : Type*} [CommRing R] (d : RootDatum) (i : Index d) (x : Index d → R) :=
  fun j => x j - (matrix d j i : R) * x i

def linearValue {R : Type*} [CommRing R] (v : Vector ℤ d.cartan.size) (x : Index d → R) : R :=
  ∑ j, (v.get j : R) * x j

private theorem reflect_pairing {R : Type*} [CommRing R] (i : Index d)
    (v : Vector ℤ d.cartan.size) (x : Index d → R) :
    linearValue (reflectRow d i v) x = linearValue v (reflectDual d i x) := by
  simp [linearValue, reflectRow, reflectDual, Vector.get, sub_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_mul, Int.cast_ite, ite_mul, mul_assoc]

private theorem reflectDual_involutive {R : Type*} [CommRing R] (i : Index d)
    (h : matrix d i i = 2) : Function.Involutive (reflectDual (R := R) d i) := by
  intro x
  funext j
  simp [reflectDual, h]
  ring

private theorem reflectRow_involutive (i : Index d) (h : matrix d i i = 2) :
    Function.Involutive (reflectRow d i) := by
  intro v
  apply Vector.ext
  intro j hj
  let t : Index d := ⟨j, hj⟩
  have hc := reflect_pairing i (reflectRow d i v) (Pi.single t (1 : ℤ))
  rw [reflect_pairing i v, reflectDual_involutive i h] at hc
  simpa [linearValue, Pi.single_apply, mul_ite] using hc

private theorem reflect_mem {d : RootDatum} (hd : IsExceptionalCensusDatum d)
    (i : Index d) (v : Vector ℤ d.cartan.size) (hv : v ∈ table d) :
    reflectRow d i v ∈ table d := by
  have ht : Certified d := by
    obtain ⟨hG,hF,h₆,h₇,h₈⟩ := exceptional_root_tables_certified
    rcases hd with rfl|rfl|rfl|rfl|rfl
    · exact hG
    · exact hF
    · exact h₆
    · exact h₇
    · exact h₈
  exact ht.2.2.2.2.1 v hv i

private theorem matrix_diag {d : RootDatum} (hd : IsExceptionalCensusDatum d)
    (i : Index d) : matrix d i i = 2 := by
  rcases hd with rfl|rfl|rfl|rfl|rfl <;> decide +revert

def gradeReflectEquiv (hd : IsExceptionalCensusDatum d) (i : Index d)
    (a : Index d → ZMod 3) (k : ZMod 3) :
    ↥(gradeTable d a k) ≃ ↥(gradeTable d (reflectDual d i a) k) := by
  let w := reflectRow d i
  have hm (x : Index d → ZMod 3) (v : Vector ℤ d.cartan.size) (hv : v ∈ gradeTable d x k) :
      w v ∈ gradeTable d (reflectDual d i x) k := by
    obtain ⟨hvt, hvx⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨reflect_mem hd i v hvt, ?_⟩
    change linearValue (reflectRow d i v) (reflectDual d i x) = k
    rwa [reflect_pairing, reflectDual_involutive i (matrix_diag hd i)]
  exact { toFun := fun v => ⟨w v.val, hm _ v.val v.property⟩
          invFun := fun v => ⟨w v.val, by
            have hv := hm _ v.val v.property
            rwa [reflectDual_involutive i (matrix_diag hd i)] at hv⟩
          left_inv := fun v => Subtype.ext (reflectRow_involutive i (matrix_diag hd i) v.val)
          right_inv := fun v => Subtype.ext (reflectRow_involutive i (matrix_diag hd i) v.val) }

private def scalarCubic (a : Index d → ZMod 3) (x y z : Index d → ℚ) : ℚ :=
  ∑ v : ↥(gradeTable d a 1), linearValue v.val x * linearValue v.val y * linearValue v.val z

private theorem scalarCubic_flip (a : Index d → ZMod 3) (x y z : Index d → ℚ) :
    scalarCubic a x y z = scalarCubic a x z y := by
  apply Finset.sum_congr rfl
  intro v _
  ring

private theorem scalarCubic_expand (a : Index d → ZMod 3) (x y z : Index d → ℚ) :
    scalarCubic a x y z = ∑ i, z i * scalarCubic a x y (Pi.single i 1) := by
  unfold scalarCubic
  have hs (v : ↥(gradeTable d a 1)) (i : Index d) :
      linearValue v.val (Pi.single i (1 : ℚ)) = (v.val.get i : ℚ) := by
    simp [linearValue, Pi.single_apply, mul_ite]
  simp only [hs, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  unfold linearValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem entry_eq_unit (a : Index d → ZMod 3) (x : Index d → ℚ) (i j : Index d) :
    ((censusCubicMatrix d a 1).map (Int.cast : ℤ → ℚ) *ᵥ x) (i,j) =
      scalarCubic a x (Pi.single i 1) (Pi.single j 1) := by
  have hs (v : ↥(gradeTable d a 1)) (i : Index d) :
      linearValue v.val (Pi.single i (1 : ℚ)) = (v.val.get i : ℚ) := by
    simp [linearValue, Pi.single_apply, mul_ite]
  simp only [censusCubicMatrix, Matrix.mulVec, dotProduct, map_apply, Int.cast_sum,
    Int.cast_mul, Finset.sum_mul, scalarCubic, hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [linearValue, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem cubic_kernel_iff (a : Index d → ZMod 3) (x : Index d → ℚ) :
    (censusCubicMatrix d a 1).map (Int.cast : ℤ → ℚ) *ᵥ x = 0 ↔
    ∀ y z, scalarCubic a x y z = 0 := by
  constructor
  · intro h y z
    rw [scalarCubic_expand]
    apply Finset.sum_eq_zero
    intro i _
    rw [scalarCubic_flip, scalarCubic_expand]
    suffices ∀ j, scalarCubic a x (Pi.single i 1) (Pi.single j 1) = 0 by simp [this]
    exact fun j => (entry_eq_unit a x i j).symm.trans (congrFun h (i,j))
  · intro h
    funext ⟨i,j⟩
    rw [entry_eq_unit, h]
    rfl

private theorem scalarCubic_reflect (hd : IsExceptionalCensusDatum d) (i : Index d)
    (a : Index d → ZMod 3) (x y z : Index d → ℚ) :
    scalarCubic (reflectDual d i a) (reflectDual d i x) y z =
      scalarCubic a x (reflectDual d i y) (reflectDual d i z) := by
  unfold scalarCubic
  rw [← (gradeReflectEquiv hd i a 1).sum_comp]
  apply Finset.sum_congr rfl
  intro v _
  change linearValue (reflectRow d i v.val) (reflectDual d i x) *
    linearValue (reflectRow d i v.val) y * linearValue (reflectRow d i v.val) z = _
  rw [reflect_pairing, reflect_pairing, reflect_pairing, reflectDual_involutive i (matrix_diag hd i)]

/-- The three necessary conditions tested by the finite toral sieve. -/
def Admissible (d : RootDatum) (a : Index d → ZMod 3) : Prop :=
  a ≠ 0 ∧
  (∀ w : Vector ℤ d.cartan.size, (∀ v ∈ gradeTable d a 0, ∑ i, v.get i * w.get i = 0) →
    ∀ i, w.get i = 0) ∧
  ∃ x : Index d → ℚ, x ≠ 0 ∧ ((censusCubicMatrix d a 1).map (Int.cast : ℤ → ℚ)) *ᵥ x = 0

/-- Reflection of a character preserves full zero-root rank and transports
the nonzero rational cubic kernel by the dual reflection. -/
theorem reflect_admissible (hd : IsExceptionalCensusDatum d) (i : Index d)
    {a : Index d → ZMod 3} (ha : Admissible d a) : Admissible d (reflectDual d i a) := by
  obtain ⟨ha, hsep, x, hx, hAx⟩ := ha
  have hdiag := matrix_diag hd i
  have hz {R : Type} [CommRing R] (f : Index d → R) (hf : f ≠ 0) :
      reflectDual d i f ≠ 0 := by
    intro h
    apply hf
    rw [← reflectDual_involutive i hdiag f, h]
    ext
    simp [reflectDual]
  refine ⟨hz a ha, ?_, reflectDual d i x, hz x hx, ?_⟩
  · intro w hw j
    let u := Vector.ofFn (reflectDual d i w.get)
    have hu : ∀ j, u.get j = 0 := hsep u (by
      intro v hv
      have hh := hw _ ((gradeReflectEquiv hd i a 0) ⟨v, hv⟩).property
      change linearValue (reflectRow d i v) w.get = 0 at hh
      rw [reflect_pairing] at hh
      simpa [u, Vector.get, linearValue] using hh)
    have hu' : reflectDual d i w.get = 0 := funext (fun j => by simpa [u, Vector.get] using hu j)
    have hw' : w.get = 0 := by
      rw [← reflectDual_involutive i hdiag w.get, hu']
      ext
      simp [reflectDual]
    exact congrFun hw' j
  · apply (cubic_kernel_iff _ _).mpr
    intro y z
    rw [scalarCubic_reflect hd]
    exact (cubic_kernel_iff _ _).mp hAx _ _

/-- The root counts in every character grade are invariant under all
simple reflections. -/
theorem reflect_grade_card (hd : IsExceptionalCensusDatum d) (i : Index d)
    (a : Index d → ZMod 3) (k : ZMod 3) :
    (gradeTable d a k).card = (gradeTable d (reflectDual d i a) k).card := by
  simpa using Fintype.card_congr (gradeReflectEquiv hd i a k)

end CubicAnomaly.Classification.RootClassificationExceptional
