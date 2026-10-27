import CubicAnomaly.Fixed.E8Compact
import CubicAnomaly.Fixed.E8Adjoint
import CubicAnomaly.Classification.SimpleIdealStructure

/-!
# Dimension and simplicity of the actual compact exceptional algebra

Dimension and simplicity are transferred through the proved
tensor-complexification equivalence. Neither is supplied as a compact-form
hypothesis.
-/

namespace CubicAnomaly.Fixed.E8Structure

open CubicAnomaly.Fixed.E8Compact
open scoped TensorProduct

/-- Real dimension agrees with complex dimension under the actual complexification. -/
theorem e8_compact_dimension_eq :
    Module.finrank ℝ compactRealAlgebra = Module.finrank ℂ E8Geck.lieAlgebra := by
  have h := complexificationEquiv.toLinearEquiv.finrank_eq
  simpa only [Module.finrank_baseChange] using h

/-- The constructed compact real Lie algebra itself has dimension 248. -/
theorem e8_compact_finrank : Module.finrank ℝ compactRealAlgebra = 248 :=
  e8_compact_dimension_eq.trans E8Adjoint.e8_lieAlgebra_finrank

private theorem simple_of_fixed_equiv {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (e : L ≃ₗ⁅ℂ⁆ E8Geck.lieAlgebra) : LieAlgebra.IsSimple ℂ L := by
  letI := E8Adjoint.e8_lieAlgebra_isSimple
  constructor
  · intro I
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (I.map e.toLieHom) with hb | ht
    · exact Or.inl (LieIdeal.bot_of_map_eq_bot (f := e.toLieHom) e.injective hb)
    · right
      apply top_unique
      intro x _
      have hx : e x ∈ I.map e.toLieHom := by rw [ht]; trivial
      obtain ⟨y, hy⟩ := LieIdeal.mem_map_of_surjective (f := e.toLieHom) e.surjective hx
      have hxy : (y : L) = x := e.injective hy
      exact hxy ▸ y.property
  · intro hab
    exact LieAlgebra.IsSimple.non_abelian ℂ
      ((lie_abelian_iff_equiv_lie_abelian e).mp hab)

/-- The constructed compact real algebra is simple, by descent from its actual complexification. -/
theorem e8_compact_isSimple : LieAlgebra.IsSimple ℝ compactRealAlgebra := by
  letI : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] compactRealAlgebra) :=
    simple_of_fixed_equiv complexificationEquiv
  exact CubicAnomaly.Classification.SimpleIdealStructure.simple_of_complexification_simple

end CubicAnomaly.Fixed.E8Structure
