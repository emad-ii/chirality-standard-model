import CubicAnomaly.Classification.CanonicalHalf
import CubicAnomaly.Classification.CompactGeometry

/-! A real Lie-pair equivalence preserving the oriented half conjugates the
two canonical Hermitian matrix representations, even with different chosen
compact forms and coordinates. -/

namespace CubicAnomaly.Classification.CanonicalHalfTransport

open Structural Complexification HermitianRealization CompactGeometry AnomalyComplexification
open CanonicalHalf Matrix
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

private noncomputable def ambientCoordinates (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) Complex.I
      ≃ₗ[ℂ] (Fin (hermitianHalfOfCommutant B h e).dimension → ℂ) :=
  (ambientHalfEquiv (orthogonalComplement B h) (commutantComplexStructure e)
    Complex.I).symm.toLinearEquiv.trans (canonicalPositiveHalfEquiv B h e)

private theorem ambient_coordinates_action (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (x : ℂ ⊗[ℝ] h)
    (z : ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) Complex.I) :
    ambientCoordinates B h e ⁅x, z⁆ =
      complexHermitianRepresentation (hermitianHalfOfCommutant B h e) x *ᵥ ambientCoordinates B h e z := by
  let E := (ambientHalfEquiv (orthogonalComplement B h) (commutantComplexStructure e) Complex.I).symm
  change canonicalPositiveHalfEquiv B h e (E ⁅x, z⁆) = _ *ᵥ canonicalPositiveHalfEquiv B h e (E z)
  exact (congrArg (canonicalPositiveHalfEquiv B h e) (E.map_lie x z)).trans
    (canonicalPositiveHalfEquiv_intertwines B h e x (E z))

variable {k : Type*} [LieRing k] [LieAlgebra ℝ k] [Module.Finite ℝ k]

/-- Transport the entire canonical positive-half action under the original
real pair map. The second equivalence changes only the matrix coordinates. -/
theorem exists_positive_matrix_equiv (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (C : CompactForm k) (l : LieSubalgebra ℝ k)
    (c : lieCommutant (L := l) (M := orthogonalComplement C l) ≃ₐ[ℝ] ℂ)
    (f : g ≃ₗ⁅ℝ⁆ k) (hf : h.map f.toLieHom = l)
    (hpos : (ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e)
      Complex.I).toSubmodule.map (f.toLinearMap.baseChange ℂ) =
      (ambientComplexifiedHalf (orthogonalComplement C l) (commutantComplexStructure c) Complex.I).toSubmodule) :
    ∃ (θ : h ≃ₗ⁅ℝ⁆ l) (R : (Fin (hermitianHalfOfCommutant B h e).dimension → ℂ) ≃ₗ[ℂ]
        (Fin (hermitianHalfOfCommutant C l c).dimension → ℂ)), ∀ (x : h) v,
      R (complexHermitianRepresentation (hermitianHalfOfCommutant B h e) (1 ⊗ₜ[ℝ] x) *ᵥ v) =
      complexHermitianRepresentation (hermitianHalfOfCommutant C l c) (1 ⊗ₜ[ℝ] θ x) *ᵥ R v := by
  let θ := f.ofSubalgebras h l hf
  let P := ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) Complex.I
  let Q := ambientComplexifiedHalf (orthogonalComplement C l) (commutantComplexStructure c) Complex.I
  let E : P ≃ₗ[ℂ] Q := (LinearEquiv.baseChange ℝ ℂ g k f.toLinearEquiv).ofSubmodules P.toSubmodule Q.toSubmodule hpos
  have map_act (x : h) (z : P) : E ⁅(1 ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] h), z⁆ =
      ⁅(1 ⊗ₜ[ℝ] θ x : ℂ ⊗[ℝ] l), E z⁆ := by
    apply Subtype.ext
    have hincl := complexifiedLieHom_inclusion_action h (1 ⊗ₜ[ℝ] x) z.val
    have hincl' := complexifiedLieHom_inclusion_action l (1 ⊗ₜ[ℝ] θ x) (E z).val
    change f.toLinearMap.baseChange ℂ ⁅(1 ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] h), z.val⁆ =
      ⁅(1 ⊗ₜ[ℝ] θ x : ℂ ⊗[ℝ] l), (E z).val⁆
    rw [← hincl, ← hincl']
    exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) f.toLieHom).map_lie _ _
  let p := ambientCoordinates B h e
  let q := ambientCoordinates C l c
  refine ⟨θ, p.symm.trans (E.trans q), ?_⟩
  intro x v
  obtain ⟨z, rfl⟩ := p.surjective v
  change q (E (p.symm (_ *ᵥ p z))) = _ *ᵥ q (E (p.symm (p z)))
  rw [← ambient_coordinates_action B h e, p.symm_apply_apply, p.symm_apply_apply, map_act,
    ambient_coordinates_action C l c]

end CubicAnomaly.Classification.CanonicalHalfTransport
