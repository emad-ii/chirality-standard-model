import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Relation

/-!
# Connectivity of a Cartan matrix

In the finite Cartan classification, indecomposability says that any index
can reach every other along nonzero entries. For a Cartan matrix the support
is symmetric, so these paths are precisely those of its Dynkin diagram.
-/

namespace Matrix

/-- Path formulation of matrix indecomposability. -/
def IsIndecomposable {ι R : Type*} [Zero R] (M : Matrix ι ι R) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun u v => M u v ≠ 0) i j

lemma isIndecomposable_iff_reflTransGen {ι R : Type*} [Zero R] {M : Matrix ι ι R} :
    M.IsIndecomposable ↔ ∀ i j, Relation.ReflTransGen (fun u v => M u v ≠ 0) i j :=
  Iff.rfl

end Matrix
