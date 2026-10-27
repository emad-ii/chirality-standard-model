import CubicAnomaly.Fixed.E8FullCubicTrace
import CubicAnomaly.Classification.FiniteToralCubic

/-! The full mixed cubic radical of the actual degree-zero algebra. -/

namespace CubicAnomaly.Fixed.E8FullCubic

open Matrix
open CubicAnomaly.Classification.CubicRadical
open CubicAnomaly.Classification.CartanTrace
open CubicAnomaly.Classification.FiniteToralCubic
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
set_option maxHeartbeats 200000
set_option Elab.async false

/-- Six actual coroots annihilate all mixed insertions from the entire zero algebra. -/
theorem e8_full_radical_cartan (a : Fin 6) : cartan (e6SimpleIndex a) ∈ fullRadical := by
  have hweight : ∀ v : {v : RootVector // v ∈ zeroRoots},
      ∃ i : Fin 8, (pairSimple v.val i : ℂ) ≠ 0 := by
    intro v
    obtain ⟨i, hi⟩ := e8_zero_root_weight_certificate.1 v.val v.property
    exact ⟨i, by exact_mod_cast hi⟩
  apply toral_mem_radical_of_spanning cartan rootVector
    (fun v i => (pairSimple v.val i : ℂ)) e8_full_toral_root_span
    e8_full_cartan_commute e8_full_cartan_root_action hweight
    e8_full_opposite_root_bracket
    (complexTraceCubicForm fullMatrixRepresentation.toLinearMap)
    (complex_trace_cubic_invariant fullMatrixRepresentation)
    (complex_trace_cubic_symmetric fullMatrixRepresentation.toLinearMap)
    (e6SimpleIndex a)
  intro i j
  change matrixTraceCubic (fullMatrixRepresentation (cartan (e6SimpleIndex a)))
    (fullMatrixRepresentation (cartan i)) (fullMatrixRepresentation (cartan j)) = 0
  rw [e8_full_cubic_cartan_tensor, e8_full_cubic_cartan_certificate]
  simp

/-- The actual full mixed radical is nonzero. -/
theorem e8_full_radical_ne_bot : fullRadical ≠ ⊥ := by
  intro hbot
  have hm := e8_full_radical_cartan (0 : Fin 6)
  rw [hbot, LieSubmodule.mem_bot] at hm
  exact e8_full_cartan_ne_zero _ hm

private theorem diagramSign_ne_zero (i : Fin 8) : (diagramSign i : ℂ) ≠ 0 := by
  have hh : (diagramSign i : ℂ) * (diagramSign i : ℂ) = 1 := by
    exact_mod_cast bracket_data_diagram_sign_sq i
  intro hi
  simp [hi] at hh

abbrev E6Label := {d : DataIndex // d ∈ e6Labels}

private def e6ToZeroLabel : E6Label → GradeLabel 0 :=
  Set.inclusion (s := (e6Labels : Set DataIndex))
    (t := (gradeLabels 0 : Set DataIndex)) e8_full_cubic_support_certificate.2.1

/-- The explicit seventy-eight-dimensional span inside the actual zero algebra. -/
def e6Span : Submodule ℂ zeroSubalgebra :=
  Submodule.span ℂ (Set.range fun d : E6Label => zeroBasis (e6ToZeroLabel d))

/-- Its dimension follows from independence of the actual adjoint coordinates. -/
theorem e8_e6Span_finrank : Module.finrank ℂ e6Span = 78 := by
  classical
  have hi : Function.Injective e6ToZeroLabel :=
    Set.inclusion_injective (s := (e6Labels : Set DataIndex))
      (t := (gradeLabels 0 : Set DataIndex)) e8_full_cubic_support_certificate.2.1
  have hli := zeroBasis.linearIndependent.comp e6ToZeroLabel hi
  change Module.finrank ℂ (Submodule.span ℂ
    (Set.range (zeroBasis ∘ e6ToZeroLabel))) = 78
  rw [finrank_span_eq_card hli]
  exact (Fintype.card_of_subtype e6Labels (fun _ => Iff.rfl)).trans
    e8_full_cubic_support_certificate.1

private theorem e6_root_mem_zero {v : RootVector} (hv : v ∈ e6Roots) : v ∈ zeroRoots := by
  rw [e8_zero_root_decomposition_certificate.2.2.1]
  exact Finset.mem_union_left _ hv

/-- All seventy-two root directions are in the full radical by ideal closure
under the six already detected coroots. -/
theorem e8_full_radical_e6_root (v : RootVector) (hv : v ∈ e6Roots) :
    rootVector ⟨v, e6_root_mem_zero hv⟩ ∈ fullRadical := by
  obtain ⟨a, ha⟩ := e8_full_cubic_support_certificate.2.2 v hv
  have hh := lie_mem_left ℂ zeroSubalgebra fullRadical
    (cartan (e6SimpleIndex a)) (rootVector ⟨v, e6_root_mem_zero hv⟩)
    (e8_full_radical_cartan a)
  rw [e8_full_cartan_root_action] at hh
  exact (fullRadical.toSubmodule.smul_mem_iff (by exact_mod_cast ha)).mp hh

/-- The displayed seventy-eight coordinates all belong to the full radical. -/
theorem e8_e6Span_le_fullRadical : e6Span ≤ fullRadical.toSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨d, hd⟩, rfl⟩
  obtain ⟨hdroot, hd6⟩ := Finset.mem_filter.mp hd
  cases d with
  | inl i =>
    have hi : i.val < 6 := of_decide_eq_true hd6
    let a : Fin 6 := ⟨i.val, hi⟩
    have ha : e6SimpleIndex a = i := Fin.ext rfl
    have hm := e8_full_radical_cartan a
    rw [ha] at hm
    exact (fullRadical.toSubmodule.smul_mem_iff (diagramSign_ne_zero i)).mp hm
  | inr v =>
    have hv : v ∈ e6Roots := by
      apply Finset.mem_filter.mpr
      exact ⟨by simpa [basisList] using hdroot, of_decide_eq_true hd6⟩
    exact e8_full_radical_e6_root v hv

private theorem family_zero_embedding (F : FamilyLie) :
    gaugeFamilyZeroEmbedding (0, F) = E8A2.sl3ZeroEmbedding F := by
  apply Subtype.ext
  change E8A4.sl5Embedding (gaugeSl5Embedding 0) + E8A2.sl3Embedding F = _
  simp only [map_zero, zero_add]
  rfl

/-- The family subspace of the actual zero algebra. -/
def familySpace : Submodule ℂ zeroSubalgebra :=
  LinearMap.range E8A2.sl3ZeroEmbedding.toLinearMap

/-- Full radical membership has trivial intersection with the faithful family algebra. -/
theorem e8_full_radical_disjoint_family : Disjoint fullRadical.toSubmodule familySpace := by
  rw [Submodule.disjoint_def]
  intro x hx hf
  obtain ⟨F, rfl⟩ := hf
  have hrep (a : GaugeFamilyAlgebra) :
      fullMatrixRepresentation (gaugeFamilyZeroEmbedding a) = actualMatrixRepresentation a :=
    congrArg (fun r : GaugeFamilyAlgebra →ₗ⁅ℂ⁆ Matrix (Fin 27 × Fin 3) (Fin 27 × Fin 3) ℂ =>
      r a) e8_full_matrix_representation_restrict
  have hrestricted : ((0, F) : GaugeFamilyAlgebra) ∈
      complexTraceRadical actualMatrixRepresentation := by
    apply (mem_radical_iff (L := GaugeFamilyAlgebra)
      (complexTraceCubicForm actualMatrixRepresentation.toLinearMap)
      (complex_trace_cubic_invariant actualMatrixRepresentation)
      ((0, F) : GaugeFamilyAlgebra)).mpr
    intro y z
    change matrixTraceCubic (actualMatrixRepresentation (0, F))
      (actualMatrixRepresentation y) (actualMatrixRepresentation z) = 0
    have hh := (mem_radical_iff
      (complexTraceCubicForm fullMatrixRepresentation.toLinearMap)
      (complex_trace_cubic_invariant fullMatrixRepresentation)
      (E8A2.sl3ZeroEmbedding F)).mp hx
      (gaugeFamilyZeroEmbedding y) (gaugeFamilyZeroEmbedding z)
    change matrixTraceCubic (fullMatrixRepresentation (E8A2.sl3ZeroEmbedding F))
      (fullMatrixRepresentation (gaugeFamilyZeroEmbedding y))
      (fullMatrixRepresentation (gaugeFamilyZeroEmbedding z)) = 0 at hh
    rw [← family_zero_embedding] at hh
    simpa only [hrep] using hh
  rw [e8_actual_matter_radical_eq_gauge_ideal] at hrestricted
  have hF : F = 0 := hrestricted
  simp only [hF, map_zero]

private theorem family_finrank : Module.finrank ℂ FamilyLie = 8 := by
  let t : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin 3) ℂ ℂ
  have ht : Function.Surjective t := by
    intro z
    exact ⟨Matrix.single 0 0 z, by simp [t, Matrix.trace_single_eq_same]⟩
  have hh := t.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr ht, finrank_top] at hh
  norm_num only [Module.finrank_self, Module.finrank_matrix, Fintype.card_fin,
    mul_one, Nat.reduceMul] at hh
  change 1 + Module.finrank ℂ FamilyLie = 9 at hh
  omega

/-- The actual family factor supplies the complementary eight dimensions. -/
theorem e8_familySpace_finrank : Module.finrank ℂ familySpace = 8 := by
  rw [familySpace, LinearMap.finrank_range_of_inj E8A2.e8_a2_sl3ZeroEmbedding_injective]
  exact family_finrank

/-- The full mixed cubic radical has exactly seventy-eight complex dimensions. -/
theorem e8_full_radical_finrank : Module.finrank ℂ fullRadical = 78 := by
  have hlo := Submodule.finrank_mono e8_e6Span_le_fullRadical
  rw [e8_e6Span_finrank] at hlo
  change 78 ≤ Module.finrank ℂ fullRadical at hlo
  have hhi := Submodule.finrank_add_finrank_le_of_disjoint e8_full_radical_disjoint_family
  rw [e8_familySpace_finrank, e8_zeroSubalgebra_finrank] at hhi
  change Module.finrank ℂ fullRadical + 8 ≤ 86 at hhi
  omega

/-- The full radical is exactly the displayed six-toral-plus-seventy-two-root span. -/
theorem e8_full_radical_eq_e6Span : fullRadical.toSubmodule = e6Span := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq e8_e6Span_le_fullRadical
  rw [e8_e6Span_finrank]
  change 78 = Module.finrank ℂ fullRadical
  exact e8_full_radical_finrank.symm

/-- The full radical is a proper ideal of the entire zero algebra. -/
theorem e8_full_radical_ne_top : fullRadical ≠ ⊤ := by
  intro ht
  have hh := e8_full_radical_finrank
  rw [ht] at hh
  have he : Module.finrank ℂ (⊤ : LieIdeal ℂ zeroSubalgebra) = 86 := by
    change Module.finrank ℂ (⊤ : Submodule ℂ zeroSubalgebra) = 86
    rw [finrank_top, e8_zeroSubalgebra_finrank]
  omega

end

end CubicAnomaly.Fixed.E8FullCubic
