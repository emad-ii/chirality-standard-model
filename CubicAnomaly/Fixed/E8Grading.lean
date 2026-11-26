import CubicAnomaly.Fixed.E8GradingData
import CubicAnomaly.Fixed.E8SparseModel
import CubicAnomaly.Fixed.E8Adjoint

/-!
# Homogeneous spaces in the actual fixed exceptional module

The order-three grading is realized as literal support subspaces of the
existing Geck coordinate space. Their dimensions are obtained by an actual
basis equivalence with the checked finite labels. Sparse bracket grading
extends to arbitrary vectors by bilinearity.
-/

namespace CubicAnomaly.Fixed.E8Grading

open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Geck
open scoped BigOperators

noncomputable section

/-- The actual zero/root coordinate index has the degree of its integer label. -/
def indexGrade (i : Index) : ZMod 3 := grade (dataIndex i)

/-- The literal coordinate subspace supported in one degree. -/
def gradeSpace (a : ZMod 3) : Submodule ℂ DefiningSpace where
  carrier := {v | ∀ i, indexGrade i ≠ a → v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

/-- Restriction to the homogeneous coordinates is an actual linear equivalence. -/
def gradeCoordinateEquiv (a : ZMod 3) :
    gradeSpace a ≃ₗ[ℂ] ({i : Index // indexGrade i = a} → ℂ) := by
  classical
  exact {
    toFun := fun x i => x.val i.val
    invFun := fun x => ⟨fun i => if hi : indexGrade i = a then x ⟨i, hi⟩ else 0,
      by intro i hi; simp [hi]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext i
      by_cases hi : indexGrade i = a
      · simp [hi]
      · simp [hi, x.property i hi]
    right_inv := by
      intro x
      funext i
      simp [i.property]
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The actual homogeneous indices match precisely the checked finite labels. -/
def gradeIndexEquiv (a : ZMod 3) :
    {i : Index // indexGrade i = a} ≃ {d : DataIndex // d ∈ gradeLabels a} := by
  classical
  refine Equiv.ofBijective
    (fun i => ⟨dataIndex i.val, (e8_mem_gradeLabels a _).mpr
      ⟨e8_dataIndex_mem_basisList i.val, i.property⟩⟩) ⟨?_, ?_⟩
  · intro i j hij
    apply Subtype.ext
    apply e8_dataIndex_injective
    exact congrArg Subtype.val hij
  · intro d
    obtain ⟨hd, hg⟩ := (e8_mem_gradeLabels a d.val).mp d.property
    obtain ⟨i, hi⟩ := (e8_mem_basisList_iff d.val).mp hd
    refine ⟨⟨i, ?_⟩, ?_⟩
    · change grade (dataIndex i) = a
      rwa [hi]
    · apply Subtype.ext
      exact hi

theorem e8_gradeSpace_finrank (a : ZMod 3) :
    Module.finrank ℂ (gradeSpace a) = (gradeLabels a).card := by
  classical
  rw [(gradeCoordinateEquiv a).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_congr (gradeIndexEquiv a), Fintype.card_coe]

/-- The dimensions belong to actual subspaces, not just a formal root census. -/
theorem e8_gradeSpace_dimensions :
    Module.finrank ℂ (gradeSpace 0) = 86 ∧
    Module.finrank ℂ (gradeSpace 1) = 81 ∧
    Module.finrank ℂ (gradeSpace 2) = 81 := by
  simpa only [e8_gradeSpace_finrank] using e8_grading_card_certificate

theorem e8_basisVector_homogeneous (d : DataIndex) :
    basisVector d ∈ gradeSpace (grade d) := by
  intro i hi
  change (if dataIndex i = d then (1 : ℂ) else 0) = 0
  exact if_neg (fun h => hi (congrArg grade h))

theorem e8_realize_homogeneous (xs : Sparse) (a : ZMod 3)
    (hxs : ∀ p ∈ xs, grade p.1 = a) : realize xs ∈ gradeSpace a := by
  induction xs with
  | nil => exact (gradeSpace a).zero_mem
  | cons p xs ih =>
    change p.2 • basisVector p.1 + realize xs ∈ gradeSpace a
    apply (gradeSpace a).add_mem
    · have hp : basisVector p.1 ∈ gradeSpace a := by
        rw [← hxs p (List.mem_cons_self)]
        exact e8_basisVector_homogeneous p.1
      exact zsmul_mem hp p.2
    · exact ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))

/-- Literal coordinate projection to a homogeneous piece. -/
def gradeProjection (a : ZMod 3) : DefiningSpace →ₗ[ℂ] DefiningSpace where
  toFun v i := if indexGrade i = a then v i else 0
  map_add' := by
    intro x y
    funext i
    by_cases hi : indexGrade i = a <;> simp [hi]
  map_smul' := by
    intro c x
    funext i
    by_cases hi : indexGrade i = a <;> simp [hi]

theorem e8_gradeProjection_homogeneous (a : ZMod 3) (v : DefiningSpace) :
    gradeProjection a v ∈ gradeSpace a := by
  intro i hi
  exact if_neg hi

/-- Every actual vector is the sum of its three homogeneous components. -/
theorem e8_grade_decomposition (v : DefiningSpace) :
    v = gradeProjection 0 v + gradeProjection 1 v + gradeProjection 2 v := by
  funext i
  have hc : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  rcases hc (indexGrade i) with hi | hi | hi <;>
    simp [gradeProjection, hi, h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12]

theorem e8_gradeSpace_disjoint (a b : ZMod 3) (hab : a ≠ b) :
    Disjoint (gradeSpace a) (gradeSpace b) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  funext i
  by_cases hi : indexGrade i = a
  · exact hy i (fun hb => hab (hi.symm.trans hb))
  · exact hx i hi

private theorem basis_expansion (v : DefiningSpace) :
    v = ∑ i : Index, v i • basisVector (dataIndex i) := by
  classical
  simp only [e8_basisVector_dataIndex]
  exact pi_eq_sum_univ' v

/-- A literal sparse basis formula propagates grading to all vectors. -/
theorem e8_bilinear_map_graded
    (β : DefiningSpace →ₗ[ℂ] DefiningSpace →ₗ[ℂ] DefiningSpace)
    (hβ : ∀ i j : Index,
      β (basisVector (dataIndex i)) (basisVector (dataIndex j)) =
        realize (bracket (dataIndex i) (dataIndex j)))
    (a b : ZMod 3) (x y : DefiningSpace)
    (hx : x ∈ gradeSpace a) (hy : y ∈ gradeSpace b) :
    β x y ∈ gradeSpace (a + b) := by
  classical
  rw [basis_expansion x, basis_expansion y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply (gradeSpace (a + b)).sum_mem
  intro i _
  by_cases hi : indexGrade i = b
  · apply (gradeSpace (a + b)).smul_mem
    apply (gradeSpace (a + b)).sum_mem
    intro j _
    by_cases hj : indexGrade j = a
    · apply (gradeSpace (a + b)).smul_mem
      rw [hβ j i]
      apply e8_realize_homogeneous
      intro p hp
      have hh := e8_sparse_bracket_graded (dataIndex j) (dataIndex i) p hp
      exact hh.trans (congrArg₂ (· + ·) hj hi)
    · rw [hx j hj, zero_smul]
      exact (gradeSpace (a + b)).zero_mem
  · rw [hy i hi, zero_smul]
    exact (gradeSpace (a + b)).zero_mem

section Transport

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- An actual linear identification transfers the concrete homogeneous spaces. -/
def transferredGrade (e : DefiningSpace ≃ₗ[ℂ] L) (a : ZMod 3) : Submodule ℂ L :=
  (gradeSpace a).map e.toLinearMap

theorem e8_transferred_grade_finrank (e : DefiningSpace ≃ₗ[ℂ] L) (a : ZMod 3) :
    Module.finrank ℂ (transferredGrade e a) = (gradeLabels a).card := by
  rw [transferredGrade, e.finrank_map_eq, e8_gradeSpace_finrank]

variable (e : DefiningSpace ≃ₗ[ℂ] L)
  (β : DefiningSpace →ₗ[ℂ] DefiningSpace →ₗ[ℂ] DefiningSpace)
  (hβ : ∀ i j : Index,
    β (basisVector (dataIndex i)) (basisVector (dataIndex j)) =
      realize (bracket (dataIndex i) (dataIndex j)))
  (hlie : ∀ x y, e (β x y) = ⁅e x, e y⁆)

include β hβ hlie

/-- A proved basis bracket formula gives actual bracket closure after identification. -/
theorem e8_transferred_bracket_graded (a b : ZMod 3) (x y : L)
    (hx : x ∈ transferredGrade e a) (hy : y ∈ transferredGrade e b) :
    ⁅x, y⁆ ∈ transferredGrade e (a + b) := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨β v w, e8_bilinear_map_graded β hβ a b v w hv hw, hlie v w⟩

/-- The degree-zero piece is a Lie subalgebra once the actual bracket is identified. -/
def transferredZeroSubalgebra : LieSubalgebra ℂ L where
  toSubmodule := transferredGrade e 0
  lie_mem' := by
    intro x y hx hy
    simpa only [add_zero] using e8_transferred_bracket_graded e β hβ hlie 0 0 x y hx hy

/-- Every homogeneous piece is an actual module for the degree-zero subalgebra. -/
def transferredGradeModule (a : ZMod 3) :
    LieSubmodule ℂ (transferredZeroSubalgebra e β hβ hlie) L where
  toSubmodule := transferredGrade e a
  lie_mem := by
    intro x y hy
    change ⁅x.val, y⁆ ∈ transferredGrade e a
    simpa only [zero_add] using
      e8_transferred_bracket_graded e β hβ hlie 0 a x.val y x.property hy

end Transport

section ActualAlgebra

open CubicAnomaly.Fixed.E8Adjoint

private theorem actual_basis_bracket (i j : Index) :
    candidateBracket (basisVector (dataIndex i)) (basisVector (dataIndex j)) =
      realize (bracket (dataIndex i) (dataIndex j)) :=
  e8_candidateBracket_labels _ _ (e8_dataIndex_mem_basisList i)
    (e8_dataIndex_mem_basisList j)

/-- The actual homogeneous matrix subspace under the proved adjoint identification. -/
def actualGrade (a : ZMod 3) : Submodule ℂ E8Geck.lieAlgebra :=
  transferredGrade adjointEquiv.toLinearEquiv a

/-- The actual degree-zero Lie subalgebra of the generated matrix algebra. -/
def zeroSubalgebra : LieSubalgebra ℂ E8Geck.lieAlgebra :=
  transferredZeroSubalgebra adjointEquiv.toLinearEquiv candidateBracket
    actual_basis_bracket e8_adjointEquiv_bracket

/-- Each homogeneous matrix piece is an actual module for the degree-zero algebra. -/
def gradeModule (a : ZMod 3) : LieSubmodule ℂ zeroSubalgebra E8Geck.lieAlgebra :=
  transferredGradeModule adjointEquiv.toLinearEquiv candidateBracket
    actual_basis_bracket e8_adjointEquiv_bracket a

theorem e8_actual_bracket_graded (a b : ZMod 3) (x y : E8Geck.lieAlgebra)
    (hx : x ∈ actualGrade a) (hy : y ∈ actualGrade b) :
    ⁅x, y⁆ ∈ actualGrade (a + b) :=
  e8_transferred_bracket_graded adjointEquiv.toLinearEquiv candidateBracket
    actual_basis_bracket e8_adjointEquiv_bracket a b x y hx hy

theorem e8_zeroSubalgebra_finrank : Module.finrank ℂ zeroSubalgebra = 86 := by
  change Module.finrank ℂ (transferredGrade adjointEquiv.toLinearEquiv 0) = 86
  rw [e8_transferred_grade_finrank]
  exact e8_grading_card_certificate.1

theorem e8_gradeModule_finrank (a : ZMod 3) :
    Module.finrank ℂ (gradeModule a) = (gradeLabels a).card :=
  e8_transferred_grade_finrank adjointEquiv.toLinearEquiv a

/-- The two complementary pieces are 81-dimensional actual Lie modules. -/
theorem e8_complementary_module_dimensions :
    Module.finrank ℂ (gradeModule 1) = 81 ∧
    Module.finrank ℂ (gradeModule 2) = 81 := by
  simpa only [e8_gradeModule_finrank] using e8_grading_card_certificate.2

theorem e8_grade_module_invariant (a : ZMod 3) (x : zeroSubalgebra)
    (y : E8Geck.lieAlgebra) (hy : y ∈ actualGrade a) :
    ⁅x.val, y⁆ ∈ actualGrade a :=
  (gradeModule a).lie_mem hy

/-- Every element of the actual matrix Lie algebra is the sum of its three grades. -/
theorem e8_actual_grade_decomposition (x : E8Geck.lieAlgebra) :
    ∃ x₀ ∈ actualGrade 0, ∃ x₁ ∈ actualGrade 1, ∃ x₂ ∈ actualGrade 2,
      x = x₀ + x₁ + x₂ := by
  let e := adjointEquiv.toLinearEquiv
  let v := e.symm x
  refine ⟨e (gradeProjection 0 v), ⟨_, e8_gradeProjection_homogeneous 0 v, rfl⟩,
    e (gradeProjection 1 v), ⟨_, e8_gradeProjection_homogeneous 1 v, rfl⟩,
    e (gradeProjection 2 v), ⟨_, e8_gradeProjection_homogeneous 2 v, rfl⟩, ?_⟩
  have h := congrArg e (e8_grade_decomposition v)
  simpa only [map_add, v, e.apply_symm_apply] using h

end ActualAlgebra

end

end CubicAnomaly.Fixed.E8Grading
