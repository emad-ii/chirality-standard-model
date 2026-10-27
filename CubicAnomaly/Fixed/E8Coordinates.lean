import CubicAnomaly.Classification.ExceptionalRoots
import Mathlib.Data.Matrix.Cartan
import Mathlib.Data.Vector.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Exact certificates for the fixed exceptional root coordinates

The root index type in this file consists of the actual integer coordinate
vectors reconstructed by `Exceptional.roots e8Datum`.  The finite checks prove
reflection closure and norm two.  Their conclusions are then used to build a
`RootPairing` over `ℂ`, rather than a record of numerical root signatures.

This is a construction of the fixed root system.  It does not assert that an
arbitrary compact Lie pair is classified by these coordinates.
-/

namespace CubicAnomaly.Fixed.E8RootPairing

open CubicAnomaly.Classification.Exceptional
open scoped BigOperators

/-- Coordinate evaluation for the array-backed vectors used by the certificate. -/
@[simp] theorem coordinate_vector_get_ofFn (f : Fin 8 → ℤ) (i : Fin 8) :
    (Vector.ofFn f).get i = f i :=
  Vector.getElem_ofFn i.isLt

/-- Materialized integer vectors for efficient, exact finite verification. -/
def coordinateVectors : Finset (Vector ℤ 8) :=
  ((roots e8Datum).toList.map fun r => Vector.ofFn fun i : Fin 8 => r[i.val]!).toFinset

/-- The actual coordinate functions of the independently reconstructed roots. -/
def coordinateRoots : Finset (Fin 8 → ℤ) := coordinateVectors.image Vector.get

/-- Integer scalar product in the fixed simple-root basis. -/
def innerZ (x y : Fin 8 → ℤ) : ℤ :=
  ∑ i, ∑ j, x i * CartanMatrix.E₈ i j * y j

/-- Reflection in a norm-two integer root. -/
def reflectZ (x y : Fin 8 → ℤ) : Fin 8 → ℤ :=
  let coefficient := innerZ y x
  let coordinates : Vector ℤ 8 := Vector.ofFn fun i => y i - coefficient * x i
  coordinates.get

theorem reflectZ_apply (x y : Fin 8 → ℤ) (i : Fin 8) :
    reflectZ x y i = y i - innerZ y x * x i := by
  simp [reflectZ]

theorem reflectZ_eq (x y : Fin 8 → ℤ) :
    reflectZ x y = y - innerZ y x • x := by
  ext i
  simp [reflectZ_apply]

/-- The authored census uses precisely the standard `E₈` Cartan matrix. -/
theorem cartan_coordinates_eq :
    (fun i j : Fin 8 => (e8Datum.cartan[i.val]!)[j.val]!) = CartanMatrix.E₈ := by
  decide

/-- Materialized reflection, used only to make the finite certificate economical. -/
def reflectVector (x y : Vector ℤ 8) : Vector ℤ 8 :=
  let coefficient := innerZ y.get x.get
  Vector.ofFn fun i => y[i] - coefficient * x[i]

/-- One finite certificate for the reconstructed roots and every root reflection. -/
theorem coordinate_certificate :
    coordinateVectors.card = 240 ∧
    (∀ x ∈ coordinateVectors, innerZ x.get x.get = 2) ∧
    (∀ x ∈ coordinateVectors, ∀ y ∈ coordinateVectors,
      reflectVector x y ∈ coordinateVectors) ∧
    (∀ i : Fin 8, Vector.ofFn (Pi.single i (1 : ℤ)) ∈ coordinateVectors) ∧
    (∀ x ∈ coordinateVectors,
      (∀ i : Fin 8, 0 ≤ x[i]) ∨ (∀ i : Fin 8, x[i] ≤ 0)) := by
  native_decide

private theorem vector_get_injective : Function.Injective (Vector.get (α := ℤ) (n := 8)) := by
  intro x y h
  apply Vector.ext
  intro i hi
  exact congrFun h ⟨i, hi⟩

/-- The fixed integer root set has 240 distinct members. -/
theorem coordinateRoots_card : coordinateRoots.card = 240 := by
  rw [coordinateRoots, Finset.card_image_of_injective _ vector_get_injective]
  exact coordinate_certificate.1

/-- Each reconstructed integer root has squared length two. -/
theorem coordinateRoots_norm_two :
    ∀ x ∈ coordinateRoots, innerZ x x = 2 := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  exact coordinate_certificate.2.1 v hv

/-- Closure under every root reflection, rather than only the simple generators. -/
theorem coordinateRoots_reflection_closed :
    ∀ x ∈ coordinateRoots, ∀ y ∈ coordinateRoots,
      reflectZ x y ∈ coordinateRoots := by
  intro x hx y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr
    ⟨reflectVector v w, coordinate_certificate.2.2.1 v hv w hw, rfl⟩

/-- All eight simple coordinate vectors occur in the reconstructed set. -/
theorem simpleRoots_mem :
    ∀ i : Fin 8, Pi.single i (1 : ℤ) ∈ coordinateRoots := by
  intro i
  exact Finset.mem_image.mpr ⟨Vector.ofFn (Pi.single i 1),
    coordinate_certificate.2.2.2.1 i, by ext j; simp⟩

/-- Every root is positive or negative in the explicit simple coordinate basis. -/
theorem coordinateRoots_sign :
    ∀ x ∈ coordinateRoots, (∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0) := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  exact coordinate_certificate.2.2.2.2 v hv

/-- An explicit integral inverse of the fixed Cartan matrix. -/
def cartanInverse : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
     5, 8, 10, 15, 12, 9, 6, 3;
     7, 10, 14, 20, 16, 12, 8, 4;
     10, 15, 20, 30, 24, 18, 12, 6;
     8, 12, 16, 24, 20, 15, 10, 5;
     6, 9, 12, 18, 15, 12, 8, 4;
     4, 6, 8, 12, 10, 8, 6, 3;
     2, 3, 4, 6, 5, 4, 3, 2]

theorem cartan_mul_inverse : CartanMatrix.E₈ * cartanInverse = 1 := by
  decide

theorem cartan_det_ne_zero : CartanMatrix.E₈.det ≠ 0 := by
  intro h
  have hm := congrArg Matrix.det cartan_mul_inverse
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hm
  exact zero_ne_one hm

/-- The two-colouring signs of the explicit `E₈` Dynkin tree. -/
def diagramSigns : Fin 8 → ℤ := ![1, -1, -1, 1, -1, 1, -1, 1]

/-- Exact inverse for the unsigned Cartan matrix used in Geck's construction. -/
def unsignedCartanInverse : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => diagramSigns i * cartanInverse i j * diagramSigns j

theorem unsigned_cartan_mul_inverse :
    (4 - CartanMatrix.E₈) * unsignedCartanInverse = 1 := by
  decide

theorem unsigned_cartan_det_ne_zero : (4 - CartanMatrix.E₈).det ≠ 0 := by
  intro h
  have hm := congrArg Matrix.det unsigned_cartan_mul_inverse
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hm
  exact zero_ne_one hm

end CubicAnomaly.Fixed.E8RootPairing
