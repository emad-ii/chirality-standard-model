import CubicAnomaly.Classification.ExceptionalRoots
import CubicAnomaly.Fixed.E8FullCubicData

/-!
# The six-dimensional E₆ root lattice and its bracket

Start with the reflection closure of the six simple roots of the E₆ Cartan
matrix. In the lattice construction, the bracket of two nonopposite root
vectors is zero unless their sum is a root. Its sign on a root sum is the
bimultiplicative sign given by a lower triangular half of the Cartan form.
For opposite roots the bracket is minus the corresponding coroot.
-/

namespace CubicAnomaly.Fixed.E6Lattice

open CubicAnomaly.Classification.Exceptional

abbrev Vector6 := Vector ℤ 6
abbrev Index := Fin 6 ⊕ Fin 72

/-- The positive simple roots are the even-indexed reflection seeds. -/
def simpleRootIndex (a : Fin 6) : Fin 72 := ⟨2 * a.val, by omega⟩

/-- Simple-root coordinates of the independently generated E₆ roots. -/
def root (i : Fin 72) : Vector6 :=
  Vector.ofFn fun j => ((roots e6Datum)[i.val]!)[j.val]!

private def pairing (v : Vector6) (i : Fin 6) : ℤ :=
  ∑ j : Fin 6, v[j] * CartanMatrix.E₆ j i

private def epsilon (v w : Vector6) : ℤ :=
  let t := ∑ i : Fin 6, v[i] * (w[i] +
    ∑ j : Fin 6, if j < i then CartanMatrix.E₆ i j * w[j] else 0)
  if t % 2 = 0 then 1 else -1

/-- Structure constants in the six simple coroots and seventy-two root vectors.
No ambient algebra or grading occurs in this formula. -/
def products : Index → Index → List (Index × ℤ)
  | .inl _, .inl _ => []
  | .inl i, .inr r => [(.inr r, pairing (root r) i)]
  | .inr r, .inl i => [(.inr r, -pairing (root r) i)]
  | .inr r, .inr s =>
    let v := root r
    let w := root s
    if w = Vector.ofFn (fun i => -v[i]) then
      (List.finRange 6).map fun i => (.inl i, -v[i])
    else
      match (List.finRange 72).find? (fun i => root i == Vector.ofFn (fun j => v[j] + w[j])) with
      | some i => [(.inr i, epsilon v w)]
      | none => []

end CubicAnomaly.Fixed.E6Lattice

namespace CubicAnomaly.Fixed.E8RadicalIdentificationData

open CubicAnomaly.Fixed E8BracketData E8GradingData E8FullCubicData
open CubicAnomaly.Classification.Exceptional

/-- Inclusion of the six-dimensional coordinate lattice into the first six
simple coordinates of the exceptional eight-dimensional lattice. -/
def includeRoot (v : E6Lattice.Vector6) : RootVector :=
  Vector.ofFn fun i => if hi : i.val < 6 then v.get ⟨i.val, hi⟩ else 0

def label : E6Lattice.Index → DataIndex
  | .inl i => .inl (e6SimpleIndex i)
  | .inr r => .inr (includeRoot (E6Lattice.root r))

def sign : E6Lattice.Index → ℤ
  | .inl i => diagramSign (e6SimpleIndex i)
  | .inr r => rootSign (includeRoot (E6Lattice.root r))

def signedImage (xs : List (E6Lattice.Index × ℤ)) : Sparse :=
  xs.map fun p => (label p.1, p.2 * sign p.1)

/-- The reflection enumeration exactly fills the 72 root slots, and its
signed coordinates are independent coordinates of the actual cubic radical. -/
theorem e6_lattice_embedding_certificate :
    (roots e6Datum).size = 72 ∧
      (∀ v ∈ (roots e6Datum).toList, v.size = 6) ∧
      (∀ i j : Fin 6, (e6Datum.cartan[i.val]!)[j.val]! = CartanMatrix.E₆ i j) ∧
      Function.Injective label ∧
      ∀ i, label i ∈ e6Labels ∧ sign i ≠ 0 := by
  native_decide

/-- The six positive simple generators map to the corresponding ambient simple roots. -/
theorem e6_lattice_simple_root_certificate : ∀ a : Fin 6,
    includeRoot (E6Lattice.root (E6Lattice.simpleRootIndex a)) =
      simpleVector (e6SimpleIndex a) := by
  native_decide

/-- The lattice cocycle and the fixed exceptional bracket agree on every
ordered basis pair after the signed inclusion. -/
theorem e6_lattice_bracket_certificate :
    ∀ i j, sparseEq (signedImage (E6Lattice.products i j))
      (scale (sign i * sign j) (bracket (label i) (label j))) = true := by
  native_decide

end CubicAnomaly.Fixed.E8RadicalIdentificationData
