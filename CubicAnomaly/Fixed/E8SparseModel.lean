import CubicAnomaly.Fixed.E8BracketBinding
import CubicAnomaly.Fixed.E8Base
import CubicAnomaly.Fixed.SparseRealization

/-!
# Realization of sparse exceptional data in the actual Geck module
-/

namespace CubicAnomaly.Fixed.E8SparseModel

open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8BracketBinding
open CubicAnomaly.Fixed.E8RootPairing

local notation "Index" => simpleBase.support ⊕ Root
local notation "DefiningSpace" => (simpleBase.support ⊕ Root) → ℂ

noncomputable section

/-- Integer labels of the actual zero/root basis. -/
def dataIndex : Index → DataIndex
  | .inl i => .inl (simpleIndexEquiv.symm i)
  | .inr r => .inr (Vector.ofFn r.val)

theorem e8_dataIndex_injective : Function.Injective dataIndex := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          apply congrArg Sum.inl
          exact simpleIndexEquiv.symm.injective (Sum.inl.inj h)
      | inr j => cases h
  | inr i =>
      cases j with
      | inl j => cases h
      | inr j =>
          apply congrArg Sum.inr
          apply Subtype.ext
          have hv := Sum.inr.inj h
          funext k
          simpa using congrArg (fun v : RootVector => v[k]) hv

theorem e8_dataIndex_mem_basisList (i : Index) : dataIndex i ∈ basisList := by
  cases i with
  | inl i => simp [dataIndex, basisList]
  | inr r =>
      have hv : Vector.ofFn r.val ∈ rootList := by
        rw [bracket_data_root_mem_iff, bracket_vector_get_mem_iff]
        have hg : (Vector.ofFn r.val).get = r.val := by
          funext j
          simp [Vector.get]
        rw [hg]
        exact r.property
      simp [dataIndex, basisList, hv]

theorem e8_mem_basisList_iff (d : DataIndex) :
    d ∈ basisList ↔ ∃ i : Index, dataIndex i = d := by
  constructor
  · intro hd
    cases d with
    | inl i =>
        refine ⟨Sum.inl (simpleIndexEquiv i), ?_⟩
        simp [dataIndex]
    | inr v =>
        have hv : v ∈ rootList := by simpa [basisList] using hd
        have hr : v.get ∈ coordinateRoots :=
          (bracket_vector_get_mem_iff v).mp ((bracket_data_root_mem_iff v).mp hv)
        refine ⟨Sum.inr ⟨v.get, hr⟩, ?_⟩
        change Sum.inr (Vector.ofFn v.get) = Sum.inr v
        congr 1
        ext i hi
        simp [Vector.get]
  · rintro ⟨i, rfl⟩
    exact e8_dataIndex_mem_basisList i

/-- A sparse data label denotes its actual standard basis vector, or zero
when the label lies outside the checked finite domain. -/
def basisVector (d : DataIndex) : DefiningSpace :=
  fun i => if dataIndex i = d then 1 else 0

theorem e8_basisVector_dataIndex (i : Index) :
    basisVector (dataIndex i) = Pi.single i (1 : ℂ) := by
  classical
  ext j
  simp [basisVector, Pi.single_apply, e8_dataIndex_injective.eq_iff, eq_comm]

/-- Exact integer sparse lists realized in the existing complex Geck space. -/
def realize (xs : Sparse) : DefiningSpace :=
  SparseRealization.realize basisVector xs

theorem e8_realize_apply (xs : Sparse) (i : Index) :
    realize xs i = (coefficient xs (dataIndex i) : ℂ) := by
  induction xs with
  | nil => simp [realize, SparseRealization.realize, coefficient]
  | cons p xs ih =>
      change p.2 • basisVector p.1 i + realize xs i =
        (((if p.1 = dataIndex i then p.2 else 0) + coefficient xs (dataIndex i) : ℤ) : ℂ)
      rw [ih, Int.cast_add]
      by_cases h : p.1 = dataIndex i
      · simp [basisVector, h]
      · simp [basisVector, h, Ne.symm h]

theorem e8_realize_singleton (d : DataIndex) (c : ℤ) :
    realize (singleton d c) = c • basisVector d := by
  simp [realize, SparseRealization.realize, E8BracketData.singleton]

theorem e8_realize_scale (c : ℤ) (xs : Sparse) :
    realize (scale c xs) = c • realize xs :=
  SparseRealization.sparse_realize_scale basisVector c xs

theorem e8_realize_append (xs ys : Sparse) :
    realize (xs ++ ys) = realize xs + realize ys :=
  SparseRealization.sparse_realize_append basisVector xs ys

theorem e8_realize_eq_of_sparseEq (xs ys : Sparse) (h : sparseEq xs ys = true) :
    realize xs = realize ys := by
  apply SparseRealization.sparse_realize_eq_of_coefficients basisVector
  apply SparseRealization.sparse_coefficients_eq_of_support
  intro p hp
  have hh := (List.all_eq_true.mp h) p hp
  exact eq_of_beq hh

end

end CubicAnomaly.Fixed.E8SparseModel
