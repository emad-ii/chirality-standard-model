import CubicAnomaly.Fixed.E8Coordinates
import CubicAnomaly.Fixed.E8BracketData
import CubicAnomaly.Fixed.SparseRealization
import Std.Data.HashMap.Lemmas

/-!
# Semantic binding of the sparse exceptional witnesses

The materialized table is proved equal to the previously reconstructed root
set. Boolean checks are then extracted as quantified coefficient and support
identities, ready for realization in the actual Geck module.
-/

namespace CubicAnomaly.Fixed.E8BracketBinding

open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8RootPairing

/-- The literal sum-label Boolean comparison agrees with equality. -/
instance dataIndexLawfulBEq : LawfulBEq DataIndex where
  eq_of_beq := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hab : (a == b) = true := h
        exact congrArg Sum.inl (eq_of_beq hab)
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b =>
        have hab : (a == b) = true := h
        exact congrArg Sum.inr (eq_of_beq hab)
  rfl := by
    intro a
    cases a with
    | inl a =>
      change (a == a) = true
      exact beq_self_eq_true a
    | inr a =>
      change (a == a) = true
      exact beq_self_eq_true a

theorem bracket_data_root_binding : rootList.toFinset = coordinateVectors := by
  native_decide

theorem bracket_data_isRoot_iff_list (v : RootVector) :
    isRoot v = true ↔ v ∈ rootList := by
  simp [isRoot, signMap, rootList, Std.HashMap.contains_ofList]

theorem bracket_data_root_mem_iff (v : RootVector) :
    v ∈ rootList ↔ v ∈ coordinateVectors := by
  rw [← bracket_data_root_binding]
  simp

theorem bracket_data_isRoot_iff (v : RootVector) :
    isRoot v = true ↔ v ∈ coordinateVectors :=
  (bracket_data_isRoot_iff_list v).trans (bracket_data_root_mem_iff v)

theorem bracket_vector_get_mem_iff (v : RootVector) :
    v ∈ coordinateVectors ↔ v.get ∈ coordinateRoots := by
  constructor
  · intro hv
    exact Finset.mem_image_of_mem _ hv
  · intro hv
    obtain ⟨w, hw, h⟩ := Finset.mem_image.mp hv
    have hvec : w = v := by
      apply Vector.ext
      intro i hi
      exact congrFun h ⟨i, hi⟩
    simpa [hvec] using hw

theorem bracket_data_isRoot_iff_coordinates (v : RootVector) :
    isRoot v = true ↔ v.get ∈ coordinateRoots :=
  (bracket_data_isRoot_iff v).trans (bracket_vector_get_mem_iff v)

theorem bracket_data_simple_mem_basis (i : Fin 8) :
    (.inr (simpleVector i) : DataIndex) ∈ basisList := by
  have hs := bracket_data_sign_certificate
  simp only [signCheck, Bool.and_eq_true, List.all_eq_true, and_assoc] at hs
  have h := hs.2 i (List.mem_finRange i)
  have hm : simpleVector i ∈ rootList := by
    simpa only [List.contains_iff_mem] using h.1
  simp [basisList, hm]

theorem bracket_data_negative_simple_mem_basis (i : Fin 8) :
    (.inr (negateVector (simpleVector i)) : DataIndex) ∈ basisList := by
  have hs := bracket_data_sign_certificate
  simp only [signCheck, Bool.and_eq_true, List.all_eq_true, and_assoc] at hs
  have h := hs.2 i (List.mem_finRange i)
  have hm : negateVector (simpleVector i) ∈ rootList := by
    simpa only [List.contains_iff_mem] using h.2.1
  simp [basisList, hm]

theorem bracket_data_sparse_coefficients (v w : Sparse)
    (h : sparseEq v w = true) : ∀ i, coefficient v i = coefficient w i := by
  apply SparseRealization.sparse_coefficients_eq_of_support
  intro p hp
  have hh := List.all_eq_true.mp h p hp
  simpa using hh

theorem bracket_data_supported (x y : DataIndex)
    (hx : x ∈ basisList) (hy : y ∈ basisList) :
    ∀ p ∈ bracket x y, p.1 ∈ basisList := by
  have h := bracket_data_support_certificate
  simp only [supportCheck, Bool.and_eq_true, List.all_eq_true, and_assoc] at h
  have hxy := h.1 x hx y hy
  simpa only [supported, List.all_eq_true, List.contains_iff_mem] using hxy

theorem bracket_data_generators_supported (i : Fin 8) (x : DataIndex)
    (hx : x ∈ basisList) :
    (∀ p ∈ genH i x, p.1 ∈ basisList) ∧
    (∀ p ∈ genE i x, p.1 ∈ basisList) ∧
    (∀ p ∈ genF i x, p.1 ∈ basisList) := by
  have h := bracket_data_support_certificate
  simp only [supportCheck, Bool.and_eq_true, List.all_eq_true, and_assoc] at h
  have hx' := h.2 i (List.mem_finRange i) x hx
  simpa only [supported, List.all_eq_true, Bool.and_eq_true,
    List.contains_iff_mem, and_assoc] using hx'

theorem bracket_data_generator_images (i : Fin 8) (x : DataIndex)
    (hx : x ∈ basisList) :
    sparseEq (bracket (.inl i) x) (scale (diagramSign i) (genH i x)) = true ∧
    sparseEq (bracket (.inr (simpleVector i)) x) (scale (-diagramSign i) (genE i x)) = true ∧
    sparseEq (bracket (.inr (negateVector (simpleVector i))) x)
      (scale (diagramSign i) (genF i x)) = true := by
  have h := bracket_data_generator_image_certificate
  simp only [generatorImageCheck, List.all_eq_true, Bool.and_eq_true, and_assoc] at h
  exact h i (List.mem_finRange i) x hx

theorem bracket_data_generator_derivations (i : Fin 8) (x y : DataIndex)
    (hx : x ∈ basisList) (hy : y ∈ basisList) :
    derivationCheck (genH i) x y = true ∧
    derivationCheck (genE i) x y = true ∧
    derivationCheck (genF i) x y = true := by
  have h := bracket_data_generator_derivation_certificate
  simp only [generatorDerivationCheck, List.all_eq_true, Bool.and_eq_true, and_assoc] at h
  exact h i (List.mem_finRange i) x hx y hy

theorem bracket_data_diagram_sign (i : Fin 8) : diagramSign i = diagramSigns i := by
  fin_cases i <;> decide

theorem bracket_data_diagram_sign_sq (i : Fin 8) : diagramSign i * diagramSign i = 1 := by
  fin_cases i <;> decide

end CubicAnomaly.Fixed.E8BracketBinding
