import CubicAnomaly.Fixed.E8FullCubicData
import CubicAnomaly.Fixed.E8A2Data

/-! The mixed bracket on the six coroot and 72 root directions of the
radical, tested against the nine projected family matrix units. -/

namespace CubicAnomaly.Fixed.E8RadicalFamily

open E8BracketData E8FullCubicData E8A2Data E8A4Data

theorem e8_radical_family_unit_certificate :
    ∀ d ∈ e6Labels, ∀ i j : Fin 3,
      sparseEq (sparseBracket (E8BracketData.singleton d 1) (familyUnitData i j)) [] = true := by
  native_decide

end CubicAnomaly.Fixed.E8RadicalFamily
