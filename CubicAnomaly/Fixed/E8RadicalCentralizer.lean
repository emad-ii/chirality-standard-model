import CubicAnomaly.Fixed.E8RadicalFamily
import CubicAnomaly.Fixed.E8CanonicalPair

/-! The mutual centralizers in the actual degree-zero Lie algebra and the
inclusion of the selected gauge subalgebra in the full cubic radical. -/

namespace CubicAnomaly.Fixed.E8RadicalFamily

open E8Grading E8FullCubic E8CompactPair E8CanonicalPair E8ClassicalEmbedding
open MatterLieAlgebra CubicAnomaly.Classification.Complexification
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 800000

private theorem exists_radical_add_family (z : zeroSubalgebra) :
    ∃ (a : fullRadical) (F : E8A2.sl3), a.val + E8A2.sl3ZeroEmbedding F = z := by
  obtain ⟨⟨a, F⟩, h⟩ := radicalFamilyEquiv.surjective z
  exact ⟨a, F, h⟩

private theorem zero_of_commutes (z : zeroSubalgebra)
    (hR : ∀ r : fullRadical, ⁅z, r.val⁆ = 0)
    (hF : ∀ F : E8A2.sl3, ⁅z, E8A2.sl3ZeroEmbedding F⁆ = 0) : z = 0 := by
  letI : LieAlgebra.IsSemisimple ℝ compactZero :=
    e8_canonical_pair_structural_conclusions.2.2.2.1
  letI : LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] compactZero) :=
    compact_complexification_isKilling compactZeroForm (LieAlgebra.center_eq_bot ℝ compactZero)
  letI : LieAlgebra.IsKilling ℂ zeroSubalgebra := zeroComplexificationEquiv.isKilling
  have hz : z ∈ LieAlgebra.center ℂ zeroSubalgebra := by
    intro y
    obtain ⟨r, F, rfl⟩ := exists_radical_add_family y
    rw [← lie_skew, lie_add, hR, hF, add_zero, neg_zero]
  rwa [LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] at hz

private theorem family_commutes_radical (F : E8A2.sl3) (r : fullRadical) :
    ⁅E8A2.sl3ZeroEmbedding F, r.val⁆ = 0 := by
  rw [← lie_skew, e8_radical_family_commute, neg_zero]

/-- The centralizer of the full cubic radical is exactly the embedded family algebra. -/
theorem e8_centralizes_radical_iff (z : zeroSubalgebra) :
    (∀ r : fullRadical, ⁅z, r.val⁆ = 0) ↔ z ∈ familySpace := by
  constructor
  · intro h
    obtain ⟨a, F, rfl⟩ := exists_radical_add_family z
    have ha := zero_of_commutes a.val (fun r => by
      simpa only [add_lie, family_commutes_radical,
        add_zero] using h r) (e8_radical_family_commute a)
    rw [ha, zero_add]
    exact ⟨F, rfl⟩
  · rintro ⟨F, rfl⟩
    exact family_commutes_radical F

/-- The centralizer of the embedded family algebra is exactly the full cubic radical. -/
theorem e8_centralizes_family_iff (z : zeroSubalgebra) :
    (∀ F : E8A2.sl3, ⁅z, E8A2.sl3ZeroEmbedding F⁆ = 0) ↔ z ∈ fullRadical := by
  constructor
  · intro h
    obtain ⟨a, F, rfl⟩ := exists_radical_add_family z
    have hF := zero_of_commutes _ (family_commutes_radical F) (fun G => by
      simpa only [add_lie, e8_radical_family_commute,
        zero_add] using h G)
    rw [hF, add_zero]
    exact a.property
  · exact fun h => e8_radical_family_commute ⟨z, h⟩

/-- Every gauge insertion vanishes even when the other two cubic insertions
range over the whole degree-zero algebra. -/
theorem e8_standardModel_mem_fullRadical (x : StandardModelAlgebra) :
    gaugeFamilyZeroEmbedding (x, 0) ∈ fullRadical := by
  apply (e8_centralizes_family_iff _).mp
  intro F
  apply Subtype.ext
  change ⁅E8A4.sl5Embedding (gaugeSl5Embedding x) + E8A2.sl3Embedding 0,
    E8A2.sl3Embedding F⁆ = 0
  rw [map_zero, add_zero]
  exact e8_a4_a2_matrices_commute _ _

end

end CubicAnomaly.Fixed.E8RadicalFamily
