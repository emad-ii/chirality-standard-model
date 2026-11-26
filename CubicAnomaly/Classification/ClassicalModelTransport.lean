import CubicAnomaly.Classification.CompactPairTransport
import CubicAnomaly.Classification.UnitaryNoGo
import CubicAnomaly.Classification.ClassicalConstituentSymplecticExclusion

/-! The special unitary and compact symplectic exclusions hold for all
real Lie algebras admitting the respective classical realization. -/

namespace CubicAnomaly.Classification.ClassicalModelTransport

open Structural HermitianRealization UnitaryGeometry SymplecticGeometry CompactPairTransport

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

include ha hp

/-- A special-unitary realization of the ambient algebra forces the
original pair's full cubic radical to vanish. -/
theorem special_unitary_model_radical_eq_bot (f : g ≃ₗ⁅ℝ⁆ specialUnitaryAlgebra W) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊥ := by
  by_contra hr
  obtain ⟨C, l, c, _, hla, hlp, hlr⟩ := transport_pair_hypotheses f B h e ha hp hr
  exact hlr (UnitaryNoGo.all_rank_special_unitary_cubic_radical_eq_bot l C hla hlp c)

/-- A compact symplectic realization of the ambient algebra forces the
original pair's full cubic radical to vanish. -/
theorem symplectic_model_radical_eq_bot (Q : QuaternionicStructure W) (f : g ≃ₗ⁅ℝ⁆ symplecticAlgebra Q) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊥ := by
  by_contra hr
  obtain ⟨C, l, c, _, hla, hlp, hlr⟩ := transport_pair_hypotheses f B h e ha hp hr
  exact hlr (ClassicalConstituentSymplecticExclusion.all_rank_symplectic_cubic_radical_eq_bot Q l C hla hlp c)

end CubicAnomaly.Classification.ClassicalModelTransport
