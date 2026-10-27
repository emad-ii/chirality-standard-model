import CubicAnomaly.Classification.FlipOddObstruction
import CubicAnomaly.Classification.TensorUnitary
import CubicAnomaly.Classification.TraceReshuffle

/-!
# The trace-skew line obstruction for actual compact defining actions

Canonical trace reshuffling sends equivariant trace-skew operators on
`End(W)` to equivariant operators on `W ⊗ W` that anticommute with the
actual tensor flip. The tensor commutant of a complexified unitary action
is adjoint-closed. Its odd operators cannot form a nonzero complex line.

Every action and operator here is actual. No irreducibility,
semisimplicity, highest-weight data, or classification witness is assumed.
-/

namespace CubicAnomaly.Classification.UnitaryTraceSkewObstruction

open Module LieModule
open CubicAnomaly.Classification.FlipOddObstruction
open CubicAnomaly.Classification.TensorUnitary
open CubicAnomaly.Classification.TraceReshuffle
open scoped TensorProduct

noncomputable section

section ComplexifiedAction

variable {l W : Type*} [LieRing l] [LieAlgebra ℝ l]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [LieRingModule (ℂ ⊗[ℝ] l) W] [LieModule ℂ (ℂ ⊗[ℝ] l) W]

/-- For an actual complexified action with skew-Hermitian real
generators, its equivariant trace-skew operators on the defining
endomorphism space cannot form a nonzero complex line. -/
theorem complexified_trace_skew_not_line
    (hskew : ∀ x : l, (toEnd ℂ (ℂ ⊗[ℝ] l) W (1 ⊗ₜ[ℝ] x)).adjoint =
      -toEnd ℂ (ℂ ⊗[ℝ] l) W (1 ⊗ₜ[ℝ] x))
    (D₀ : Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] l⁆ Module.End ℂ W) (hD₀ : D₀ ≠ 0)
    (hsk : ∀ A B : Module.End ℂ W,
      LinearMap.trace ℂ W (D₀ A * B) = -LinearMap.trace ℂ W (A * D₀ B))
    (hline : ∀ D : Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] l⁆ Module.End ℂ W,
      (∀ A B : Module.End ℂ W,
        LinearMap.trace ℂ W (D A * B) = -LinearMap.trace ℂ W (A * D B)) →
      ∃ c : ℂ, D = c • D₀) : False := by
  obtain ⟨T, hT, hodd, hoddline⟩ := exists_flip_odd_line_of_trace_skew_line D₀ hD₀ hsk hline
  let C := equivariantOperatorAlgebra (K := ℂ) (L := ℂ ⊗[ℝ] l) (U := W ⊗[ℂ] W)
  have hTmap : T.toLinearMap ≠ 0 := by
    intro hz
    apply hT
    apply LieModuleHom.ext
    intro z
    exact LinearMap.congr_fun hz z
  apply adjoint_closed_flip_odd_not_line C
    (complexified_tensor_equivariant_adjoint_mem hskew)
    (TensorProduct.comm ℂ W W).toLinearMap
    (tensor_flip_mem (L := ℂ ⊗[ℝ] l)) tensor_flip_adjoint tensor_flip_sq
    T.toLinearMap (equivariant_hom_mem T) hTmap hodd
  intro S hS hSodd
  obtain ⟨c, hc⟩ := hoddline (equivariantOperatorHom S hS) hSodd
  exact ⟨c, congrArg LieModuleHom.toLinearMap hc⟩

end ComplexifiedAction

section DefiningAction

variable {l W : Type*} [LieRing l] [LieAlgebra ℝ l]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- The trace-skew line obstruction for the exact scalar-extended
defining representation. Real skew-Hermitian preservation supplies all
adjoint-closure hypotheses; no structural classification is an input. -/
theorem complexified_defining_trace_skew_not_line
    (ρ : l →ₗ⁅ℝ⁆ Module.End ℂ W) (hρ : ∀ x : l, (ρ x).adjoint = -ρ x) :
    letI := ComplexDefining.complexifiedDefiningAction ρ
    letI := ComplexDefining.complexified_defining_lieModule ρ
    ∀ D₀ : Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] l⁆ Module.End ℂ W, D₀ ≠ 0 →
      (∀ A B : Module.End ℂ W,
        LinearMap.trace ℂ W (D₀ A * B) = -LinearMap.trace ℂ W (A * D₀ B)) →
      (∀ D : Module.End ℂ W →ₗ⁅ℂ,ℂ ⊗[ℝ] l⁆ Module.End ℂ W,
        (∀ A B : Module.End ℂ W,
          LinearMap.trace ℂ W (D A * B) = -LinearMap.trace ℂ W (A * D B)) →
        ∃ c : ℂ, D = c • D₀) → False := by
  letI := ComplexDefining.complexifiedDefiningAction ρ
  letI := ComplexDefining.complexified_defining_lieModule ρ
  exact complexified_trace_skew_not_line (complexified_defining_real_action_skew ρ hρ)

end DefiningAction

end

end CubicAnomaly.Classification.UnitaryTraceSkewObstruction
