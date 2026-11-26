import CubicAnomaly.Fixed.E8GradingData

/-!
# Finite data for the full degree-zero cubic

These checks concern the literal root labels of the fixed construction.
The semantic file binds their weights to the actual inherited adjoint action.
-/

namespace CubicAnomaly.Fixed.E8FullCubicData

open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8GradingData
open scoped BigOperators

/-- The weight of a data label under an actual simple coroot. -/
def labelWeight : DataIndex → Fin 8 → ℤ
  | .inl _, _ => 0
  | .inr v, i => pairSimple v i

/-- The integral Cartan restriction of the cubic on the eighty-one roots. -/
def cartanTensor (i j k : Fin 8) : ℤ :=
  ∑ d ∈ gradeLabels 1, labelWeight d i * labelWeight d j * labelWeight d k

/-- Six toral directions annihilate every pair of Cartan insertions. -/
theorem e8_full_cubic_cartan_certificate :
    ∀ (a : Fin 6) (i j : Fin 8), cartanTensor (e6SimpleIndex a) i j = 0 := by
  native_decide

/-- The remaining two toral directions have a nondegenerate contraction map. -/
theorem e8_full_cubic_family_tensor_certificate :
    cartanTensor 6 6 6 = 6 ∧ cartanTensor 6 6 7 = -9 ∧
      cartanTensor 6 7 7 = 9 ∧ cartanTensor 7 7 7 = 0 := by
  native_decide

/-- Every degree-zero root has nonzero weight, and opposite weights come
from literal opposite roots. These are the hypotheses used by toral detection. -/
theorem e8_zero_root_weight_certificate :
    (∀ v ∈ zeroRoots, ∃ i : Fin 8, pairSimple v i ≠ 0) ∧
      (∀ v ∈ zeroRoots, ∀ w ∈ zeroRoots,
        (∀ i : Fin 8, pairSimple v i + pairSimple w i = 0) → w = negateVector v) := by
  native_decide

/-- The explicit seventy-eight coordinates: six toral coordinates and
the seventy-two roots supported on those six simple coordinates. -/
def isE6Label : DataIndex → Bool
  | .inl i => decide (i.val < 6)
  | .inr v => decide (v[6] = 0 ∧ v[7] = 0)

def e6Labels : Finset DataIndex :=
  basisList.toFinset.filter fun d => isE6Label d = true

/-- The proposed radical has exactly seventy-eight valid degree-zero labels,
and each of its root directions is detected by one of its six coroots. -/
theorem e8_full_cubic_support_certificate :
    e6Labels.card = 78 ∧ e6Labels ⊆ gradeLabels 0 ∧
      (∀ v ∈ e6Roots, ∃ i : Fin 6, pairSimple v (e6SimpleIndex i) ≠ 0) := by
  native_decide

end CubicAnomaly.Fixed.E8FullCubicData
