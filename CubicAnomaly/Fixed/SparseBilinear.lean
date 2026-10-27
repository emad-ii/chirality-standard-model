import CubicAnomaly.Fixed.SparseRealization
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Lie.Matrix

/-!
# From sparse bilinear data to actual matrix intertwiners

Only generator derivation identities are needed. This file realizes a finite
table on an actual vector space, extends the checked basis identities by
bilinearity, and turns derivations into matrix-commutator equivariance.
-/

namespace CubicAnomaly.Fixed.SparseBilinear

open CubicAnomaly.Fixed.SparseRealization
open Matrix

variable {D I K : Type*} [Fintype I] [DecidableEq I] [Field K]

noncomputable section

def bilinear (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D) : (I → K) →ₗ[K] (I → K) →ₗ[K] I → K :=
  (Pi.basisFun K I).constr K fun i =>
    (Pi.basisFun K I).constr K fun j => realize basis (table (label i) (label j))

theorem sparse_bilinear_basis (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D) (i j : I) :
    bilinear label basis table (Pi.single i 1) (Pi.single j 1) =
      realize basis (table (label i) (label j)) := by
  rw [← Pi.basisFun_apply K I i, ← Pi.basisFun_apply K I j]
  simp [bilinear]

theorem sparse_bilinear_label (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D)
    (hbasis : ∀ i, basis (label i) = Pi.single i 1) (i j : I) :
    bilinear label basis table (basis (label i)) (basis (label j)) =
      realize basis (table (label i) (label j)) := by
  rw [hbasis, hbasis, sparse_bilinear_basis]

theorem sparse_bilinear_realize_left (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D)
    (hbasis : ∀ i, basis (label i) = Pi.single i 1)
    (xs : Sparse D) (hx : ∀ p ∈ xs, ∃ i, label i = p.1) (j : I) :
    bilinear label basis table (realize basis xs) (basis (label j)) =
      realize basis (linearExtend (fun d => table d (label j)) xs) := by
  apply sparse_realize_action basis
    ((bilinear label basis table).flip (basis (label j))).toAddMonoidHom
  intro p hp
  obtain ⟨i, hi⟩ := hx p hp
  change bilinear label basis table (basis p.1) (basis (label j)) = _
  rw [← hi, sparse_bilinear_label label basis table hbasis]

theorem sparse_bilinear_realize_right (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D)
    (hbasis : ∀ i, basis (label i) = Pi.single i 1)
    (xs : Sparse D) (hx : ∀ p ∈ xs, ∃ j, label j = p.1) (i : I) :
    bilinear label basis table (basis (label i)) (realize basis xs) =
      realize basis (linearExtend (table (label i)) xs) := by
  apply sparse_realize_action basis
    (bilinear label basis table (basis (label i))).toAddMonoidHom
  intro p hp
  obtain ⟨j, hj⟩ := hx p hp
  change bilinear label basis table (basis (label i)) (basis p.1) = _
  rw [← hj, sparse_bilinear_label label basis table hbasis]

theorem sparse_bilinear_realize_both (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D)
    (hbasis : ∀ i, basis (label i) = Pi.single i 1)
    (xs ys : Sparse D)
    (hx : ∀ p ∈ xs, ∃ i, label i = p.1)
    (hy : ∀ p ∈ ys, ∃ j, label j = p.1) :
    bilinear label basis table (realize basis xs) (realize basis ys) =
      realize basis (linearExtend (fun d => linearExtend (table d) ys) xs) := by
  apply sparse_realize_action basis
    ((bilinear label basis table).flip (realize basis ys)).toAddMonoidHom
  intro p hp
  obtain ⟨i, hi⟩ := hx p hp
  change bilinear label basis table (basis p.1) (realize basis ys) = _
  rw [← hi]
  exact sparse_bilinear_realize_right label basis table hbasis ys hy i

theorem sparse_bilinear_derivation (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D)
    (hbasis : ∀ i, basis (label i) = Pi.single i 1)
    (A : Module.End K (I → K)) (g : D → Sparse D)
    (haction : ∀ i, A (basis (label i)) = realize basis (g (label i)))
    (htable : ∀ i j p, p ∈ table (label i) (label j) → ∃ k, label k = p.1)
    (hgen : ∀ i p, p ∈ g (label i) → ∃ k, label k = p.1)
    (hderivation : ∀ i j,
      realize basis (linearExtend g (table (label i) (label j))) =
        realize basis (linearExtend (fun d => table d (label j)) (g (label i)) ++
          linearExtend (table (label i)) (g (label j))))
    (v w : I → K) :
    A (bilinear label basis table v w) =
      bilinear label basis table (A v) w + bilinear label basis table v (A w) := by
  let B := bilinear label basis table
  have h : B.compr₂ A = B.comp A + B.compl₂ A := by
    apply (Pi.basisFun K I).ext
    intro i
    apply (Pi.basisFun K I).ext
    intro j
    simp only [Pi.basisFun_apply]
    change A (B (Pi.single i 1) (Pi.single j 1)) =
      B (A (Pi.single i 1)) (Pi.single j 1) +
        B (Pi.single i 1) (A (Pi.single j 1))
    rw [← hbasis i, ← hbasis j]
    change A (bilinear label basis table (basis (label i)) (basis (label j))) = _
    rw [sparse_bilinear_label label basis table hbasis]
    have hact : A (realize basis (table (label i) (label j))) =
        realize basis (linearExtend g (table (label i) (label j))) :=
      sparse_realize_action basis A.toAddMonoidHom g _ (by
      intro p hp
      obtain ⟨k, hk⟩ := htable i j p hp
      rw [← hk]
      exact haction k)
    rw [hact, hderivation i j, sparse_realize_append, haction i, haction j]
    dsimp only [B]
    rw [sparse_bilinear_realize_left label basis table hbasis _ (hgen i) j,
      sparse_bilinear_realize_right label basis table hbasis _ (hgen j) i]
  exact LinearMap.congr_fun₂ h v w

def matrixMap (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D) : (I → K) →ₗ[K] Matrix I I K :=
  LinearMap.toMatrix'.toLinearMap.comp (bilinear label basis table)

theorem sparse_matrixMap_mulVec (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D) (v w : I → K) :
    matrixMap label basis table v *ᵥ w = bilinear label basis table v w := by
  exact LinearMap.toMatrix'_mulVec _ _

theorem sparse_matrixMap_image (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D)
    (hbasis : ∀ i, basis (label i) = Pi.single i 1)
    (G : Matrix I I K) (g : D → Sparse D)
    (haction : ∀ i, G *ᵥ basis (label i) = realize basis (g (label i)))
    (d : D) (hd : ∃ i, label i = d) (c : ℤ)
    (himage : ∀ j, realize basis (table d (label j)) =
      c • realize basis (g (label j))) :
    matrixMap label basis table (basis d) = c • G := by
  obtain ⟨i, rfl⟩ := hd
  apply Matrix.toLin'.injective
  apply (Pi.basisFun K I).ext
  intro j
  simp only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.smul_mulVec]
  rw [sparse_matrixMap_mulVec, ← hbasis j,
    sparse_bilinear_label label basis table hbasis, himage j, haction j]

theorem sparse_matrixMap_equivariance (label : I → D) (basis : D → I → K)
    (table : D → D → Sparse D) (G : Matrix I I K)
    (hderivation : ∀ v w,
      G *ᵥ bilinear label basis table v w =
        bilinear label basis table (G *ᵥ v) w +
          bilinear label basis table v (G *ᵥ w)) (v : I → K) :
    matrixMap label basis table (G *ᵥ v) = ⁅G, matrixMap label basis table v⁆ := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  simp only [Matrix.toLin'_apply, Ring.lie_def, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, sparse_matrixMap_mulVec]
  exact eq_sub_iff_add_eq.mpr (hderivation v w).symm

end

end CubicAnomaly.Fixed.SparseBilinear
