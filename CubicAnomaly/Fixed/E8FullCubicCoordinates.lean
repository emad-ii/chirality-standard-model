import CubicAnomaly.Fixed.E8Matter
import CubicAnomaly.Fixed.E8FullCubicData

/-!
# The cubic of the entire degree-zero exceptional algebra

The representation in this file is the inherited action of every element
of the actual eighty-six-dimensional zero subalgebra on its degree-one
module. The root and toral coordinates are the already constructed E8
adjoint coordinates, not a separately postulated representation.
-/

namespace CubicAnomaly.Fixed.E8FullCubic

open Matrix
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8BracketBinding
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8Adjoint
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8Grading
open CubicAnomaly.Fixed.E8FullCubicData
open CubicAnomaly.Fixed.E8MatterMatching
open CubicAnomaly.Fixed.E8Matter
open CubicAnomaly.Fixed.E8ClassicalEmbedding
open CubicAnomaly.Fixed.MatterFamilyAnomaly
open CubicAnomaly.Fixed.FamilyAnomaly
open CubicAnomaly.Fixed.TensorAnomaly
open scoped BigOperators

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
set_option Elab.async false

/-- The action of the full degree-zero algebra in the proved matter coordinates. -/
def fullMatrixRepresentation :
    zeroSubalgebra →ₗ⁅ℂ⁆ Matrix (Fin 27 × Fin 3) (Fin 27 × Fin 3) ℂ :=
  lieEquivMatrix'.toLieHom.comp
    (actualCoordinates.lieConj.toLieHom.comp
      (LieModule.toEnd ℂ zeroSubalgebra ActualMatter))

/-- Restricting the full action recovers the previously matched representation. -/
theorem e8_full_matrix_representation_restrict :
    fullMatrixRepresentation.comp gaugeFamilyZeroEmbedding = actualMatrixRepresentation := rfl

/-- The full mixed-insertion radical, with both other slots ranging over all of g₀. -/
def fullRadical : LieIdeal ℂ zeroSubalgebra :=
  complexTraceRadical fullMatrixRepresentation

/-- The existing adjoint identification restricts to each homogeneous space. -/
def gradeActualEquiv (a : ZMod 3) : gradeSpace a ≃ₗ[ℂ] gradeModule a :=
  adjointEquiv.toLinearEquiv.submoduleMap (gradeSpace a)

/-- The zero-space restriction, with its actual Lie-subalgebra codomain. -/
def zeroActualEquiv : gradeSpace 0 ≃ₗ[ℂ] zeroSubalgebra :=
  adjointEquiv.toLinearEquiv.submoduleMap (gradeSpace 0)

abbrev GradeLabel (a : ZMod 3) := {d : DataIndex // d ∈ gradeLabels a}

/-- Coordinates indexed by the checked labels of a homogeneous component. -/
def gradeLabelCoordinates (a : ZMod 3) : gradeModule a ≃ₗ[ℂ] (GradeLabel a → ℂ) :=
  (gradeActualEquiv a).symm.trans ((gradeCoordinateEquiv a).trans
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (gradeIndexEquiv a)))

def zeroLabelCoordinates : zeroSubalgebra ≃ₗ[ℂ] (GradeLabel 0 → ℂ) :=
  zeroActualEquiv.symm.trans ((gradeCoordinateEquiv 0).trans
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (gradeIndexEquiv 0)))

/-- The actual homogeneous root/toral basis, with literal finite labels. -/
def gradeBasis (a : ZMod 3) : Module.Basis (GradeLabel a) ℂ (gradeModule a) :=
  (Pi.basisFun ℂ (GradeLabel a)).map (gradeLabelCoordinates a).symm

def zeroBasis : Module.Basis (GradeLabel 0) ℂ zeroSubalgebra :=
  (Pi.basisFun ℂ (GradeLabel 0)).map zeroLabelCoordinates.symm

private theorem gradeBasis_val (a : ZMod 3) (d : GradeLabel a) :
    (gradeBasis a d).val = adjointEquiv (basisVector d.val) := by
  classical
  have hgd : grade d.val = a := ((e8_mem_gradeLabels a d.val).mp d.property).2
  let v : gradeSpace a := ⟨basisVector d.val, by
    simpa only [hgd] using e8_basisVector_homogeneous d.val⟩
  have hh : gradeBasis a d = gradeActualEquiv a v := by
    apply (gradeLabelCoordinates a).injective
    simp only [gradeBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
      Pi.basisFun_apply]
    simp only [gradeLabelCoordinates, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
    funext b
    change (Pi.single d (1 : ℂ) : GradeLabel a → ℂ) b =
      basisVector d.val ((gradeIndexEquiv a).symm b).val
    have hb : dataIndex ((gradeIndexEquiv a).symm b).val = b.val :=
      congrArg Subtype.val ((gradeIndexEquiv a).apply_symm_apply b)
    have he : b = d ↔ b.val = d.val :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    simp only [basisVector, hb, Pi.single_apply, he]
  exact congrArg Subtype.val hh

private theorem zeroBasis_val (d : GradeLabel 0) :
    (zeroBasis d).val = adjointEquiv (basisVector d.val) :=
  gradeBasis_val 0 d

private theorem cartanLabel_mem (i : Fin 8) : Sum.inl i ∈ gradeLabels 0 := by
  simp [e8_mem_gradeLabels, basisList, grade]

private theorem rootLabel_mem {v : RootVector} (hv : v ∈ zeroRoots) :
    Sum.inr v ∈ gradeLabels 0 := by
  obtain ⟨hv, hg⟩ := Finset.mem_filter.mp hv
  exact (e8_mem_gradeLabels 0 _).mpr
    ⟨by simpa [basisList] using hv, hg⟩

/-- Simple coroots in the actual degree-zero algebra. -/
def cartan (i : Fin 8) : zeroSubalgebra :=
  (diagramSign i : ℂ) • zeroBasis ⟨.inl i, cartanLabel_mem i⟩

/-- All degree-zero root vectors in the actual algebra. -/
def rootVector (v : {v : RootVector // v ∈ zeroRoots}) : zeroSubalgebra :=
  zeroBasis ⟨.inr v.val, rootLabel_mem v.property⟩

private theorem diagramSign_sq_complex (i : Fin 8) :
    (diagramSign i : ℂ) * (diagramSign i : ℂ) = 1 := by
  exact_mod_cast bracket_data_diagram_sign_sq i

private theorem diagramSign_ne_zero (i : Fin 8) : (diagramSign i : ℂ) ≠ 0 := by
  intro hi
  have hh := diagramSign_sq_complex i
  simp [hi] at hh

/-- These toral vectors are exactly the original simple Geck h matrices. -/
theorem e8_full_cartan_matrix (i : Fin 8) :
    (cartan i).val.val = RootPairing.GeckConstruction.h (E8RootPairing.simpleIndex i) := by
  change (diagramSign i : ℂ) • (zeroBasis ⟨.inl i, cartanLabel_mem i⟩).val.val = _
  rw [zeroBasis_val, e8_adjointEquiv_val, e8_h_bracketMatrixMap_image,
    Int.cast_smul_eq_zsmul, ← SemigroupAction.mul_smul,
    bracket_data_diagram_sign_sq, one_smul]

/-- Every simple coroot in the actual zero algebra is nonzero. -/
theorem e8_full_cartan_ne_zero (i : Fin 8) : cartan i ≠ 0 :=
  smul_ne_zero (diagramSign_ne_zero i) (zeroBasis.ne_zero ⟨.inl i, cartanLabel_mem i⟩)

private theorem realize_singleton_complex (d : DataIndex) (n : ℤ) :
    realize (E8BracketData.singleton d n) = (n : ℂ) • basisVector d := by
  rw [e8_realize_singleton, Int.cast_smul_eq_zsmul]

private theorem zero_grade_bracket (d : GradeLabel 0) (a : ZMod 3) (f : GradeLabel a) :
    (⁅zeroBasis d, gradeBasis a f⁆ : gradeModule a).val =
      adjointEquiv (realize (bracket d.val f.val)) := by
  change ⁅(zeroBasis d).val, (gradeBasis a f).val⁆ = _
  rw [zeroBasis_val, gradeBasis_val, ← e8_adjointEquiv_bracket,
    e8_candidateBracket_labels _ _
      ((e8_mem_gradeLabels 0 d.val).mp d.property).1
      ((e8_mem_gradeLabels a f.val).mp f.property).1]

/-- Every displayed homogeneous basis vector is an eigenvector of the actual coroot action. -/
theorem e8_full_cartan_basis_action (i : Fin 8) (a : ZMod 3) (d : GradeLabel a) :
    ⁅cartan i, gradeBasis a d⁆ = (labelWeight d.val i : ℂ) • gradeBasis a d := by
  unfold cartan
  rw [smul_lie]
  apply Subtype.ext
  change (diagramSign i : ℂ) • (⁅zeroBasis ⟨.inl i, cartanLabel_mem i⟩,
    gradeBasis a d⁆ : gradeModule a).val =
      (labelWeight d.val i : ℂ) • (gradeBasis a d).val
  simp only [zero_grade_bracket, gradeBasis_val]
  rcases d with ⟨d, hd⟩
  cases d with
  | inl j => simp [bracket, labelWeight, realize, SparseRealization.realize]
  | inr v =>
    rw [bracket, realize_singleton_complex, map_smul, smul_smul]
    simp only [labelWeight, Int.cast_mul]
    rw [← mul_assoc, diagramSign_sq_complex, one_mul]

/-- The eight actual coroots commute. -/
theorem e8_full_cartan_commute (i j : Fin 8) : ⁅cartan i, cartan j⁆ = 0 := by
  change ⁅cartan i, (diagramSign j : ℂ) •
    gradeBasis 0 ⟨.inl j, cartanLabel_mem j⟩⁆ = 0
  rw [lie_smul, e8_full_cartan_basis_action]
  simp [labelWeight]

/-- Every degree-zero root has its literal integral Cartan weight. -/
theorem e8_full_cartan_root_action (i : Fin 8)
    (v : {v : RootVector // v ∈ zeroRoots}) :
    ⁅cartan i, rootVector v⁆ = (pairSimple v.val i : ℂ) • rootVector v :=
  e8_full_cartan_basis_action i 0 ⟨.inr v.val, rootLabel_mem v.property⟩

private theorem zero_basis_in_toral_root_span (d : GradeLabel 0) :
    zeroBasis d ∈ Submodule.span ℂ (Set.range cartan ∪ Set.range rootVector) := by
  rcases d with ⟨d, hd⟩
  cases d with
  | inl i =>
    apply (Submodule.smul_mem_iff _ (diagramSign_ne_zero i)).mp
    exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  | inr v =>
    have hparts := (e8_mem_gradeLabels 0 (.inr v)).mp hd
    have hv : v ∈ zeroRoots := by
      apply Finset.mem_filter.mpr
      exact ⟨by simpa [basisList] using hparts.1, hparts.2⟩
    exact Submodule.subset_span (Or.inr ⟨⟨v, hv⟩, rfl⟩)

/-- The actual coroot and root vectors span the entire degree-zero algebra. -/
theorem e8_full_toral_root_span :
    Submodule.span ℂ (Set.range cartan ∪ Set.range rootVector) = ⊤ := by
  apply le_antisymm le_top
  rw [← zeroBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  exact zero_basis_in_toral_root_span d

private theorem toral_basis_mem (i : Fin 8) :
    zeroBasis ⟨.inl i, cartanLabel_mem i⟩ ∈ Submodule.span ℂ (Set.range cartan) := by
  apply (Submodule.smul_mem_iff _ (diagramSign_ne_zero i)).mp
  exact Submodule.subset_span ⟨i, rfl⟩

private theorem toral_sparse_realization (xs : List (Fin 8)) (c : Fin 8 → ℤ) :
    ∃ x : zeroSubalgebra, x ∈ Submodule.span ℂ (Set.range cartan) ∧
      x.val = adjointEquiv (realize (xs.map fun i => (.inl i, c i))) := by
  induction xs with
  | nil => exact ⟨0, Submodule.zero_mem _, by simp [realize, SparseRealization.realize]⟩
  | cons i xs ih =>
    obtain ⟨x, hx, hval⟩ := ih
    refine ⟨(c i : ℂ) • zeroBasis ⟨.inl i, cartanLabel_mem i⟩ + x,
      (Submodule.span ℂ (Set.range cartan)).add_mem
        ((Submodule.span ℂ (Set.range cartan)).smul_mem _ (toral_basis_mem i)) hx, ?_⟩
    have hr : realize ((.inl i, c i) :: xs.map fun j => (.inl j, c j)) =
        (c i : ℂ) • basisVector (.inl i) + realize (xs.map fun j => (.inl j, c j)) := by
      simp only [realize, SparseRealization.realize, List.map_cons, List.sum_cons,
        Int.cast_smul_eq_zsmul]
    change (c i : ℂ) • (zeroBasis ⟨.inl i, cartanLabel_mem i⟩).val + x.val = _
    rw [List.map_cons, hr, map_add, map_smul, zeroBasis_val, hval]

/-- Opposite zero-root weights bracket into the actual toral span. -/
theorem e8_full_opposite_root_bracket
    (v w : {v : RootVector // v ∈ zeroRoots})
    (hw : ∀ i : Fin 8, (pairSimple v.val i : ℂ) + (pairSimple w.val i : ℂ) = 0) :
    ⁅rootVector v, rootVector w⁆ ∈ Submodule.span ℂ (Set.range cartan) := by
  have hw' : ∀ i : Fin 8, pairSimple v.val i + pairSimple w.val i = 0 := by
    intro i
    exact_mod_cast hw i
  have hneg := e8_zero_root_weight_certificate.2 v.val v.property w.val w.property hw'
  let c : Fin 8 → ℤ := fun i =>
    -rootSign v.val * rootSign (negateVector v.val) * v.val[i] * diagramSign i
  obtain ⟨x, hx, hval⟩ := toral_sparse_realization (List.finRange 8) c
  have heq : ⁅rootVector v, rootVector w⁆ = x := by
    apply Subtype.ext
    change (⁅zeroBasis ⟨.inr v.val, rootLabel_mem v.property⟩,
      gradeBasis 0 ⟨.inr w.val, rootLabel_mem w.property⟩⁆ : gradeModule 0).val = x.val
    rw [zero_grade_bracket, hval]
    simp only [bracket, hneg, if_pos, c]
  simpa only [heq] using hx

end

end CubicAnomaly.Fixed.E8FullCubic
