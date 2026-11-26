import CubicAnomaly.Classification.ClassicalConstituentForkReduction
import CubicAnomaly.Classification.ClassicalConstituentDDiagonal
import CubicAnomaly.Classification.ClassicalOrthogonalCartanFamilies
import CubicAnomaly.Classification.TypeAOrthogonalExclusion

/-!
# Exclusion of the compact orthogonal ambient algebra

For a nonzero cubic radical the simple isotropy has a complex-type
quotient half and hence lacks a negating Weyl word. Its Cartan matrix
has type A, D or E₆. The type-A cubic trace, the proper-path obstruction
and the singleton inverse-column identities exclude every case.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentOrthogonalExclusion

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open Structural ComplexDuality HermitianRealization OrthogonalDefining OrthogonalComplexification
open ClassicalModuleBridge ClassicalSimplicity AllRankComplex CompactOperatorModel
open ClassicalConstituentForkReduction ClassicalConstituentDDiagonal OrthogonalMinusculeExclusion
open ClassicalOrthogonalCartanFamilies WeylComponentObstruction TypeAOrthogonalExclusion
open scoped TensorProduct Classical

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- A compact orthogonal pair with nonzero cubic radical cannot have
E₆ isotropy or D isotropy of rank at least five. -/
theorem no_orthogonal_fork (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)] (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra]
    (b : (rootSystem H).Base) (hfork : ForkType b.cartanMatrix) : False := by
  letI : FiniteDimensional ℂ (ℂ ⊗[ℝ] h) := inferInstance
  letI : IsSimple ℂ (ℂ ⊗[ℝ] h) := all_rank_orthogonal_complexified_isotropy_simple B h heff hp e hr
  letI := all_rank_orthogonal_defining_complex_irreducible B h heff hp e hr
  letI := orthogonal_complexified_defining_faithful h
  let β := orthogonalExtendedForm (W := W)
  have hnd : β.Nondegenerate := by
    apply complexified_bilinForm_nondegenerate (innerₗ W)
    constructor <;> intro u hu <;> exact inner_self_eq_zero.mp (hu u)
  have hsym : β.IsSymm := by
    apply LinearMap.BilinForm.isSymm_iff.mpr
    exact LinearMap.BilinForm.IsSymm.baseChange ℂ (B₂ := innerₗ W) ⟨fun u w => real_inner_comm w u⟩
  obtain ⟨χ,v,j,d,γ,hv,hd,hl,hγ⟩ := fork_model_singleton B h hp e H b β (orthogonalModel h) hnd
    (orthogonal_complexified_defining_form_invariant h) hsym hfork
  rcases hfork with ⟨n,hn,s,hD⟩|⟨s,hE⟩
  · obtain ⟨j,rfl⟩ := s.surjective j
    have labs (i : Fin n) : χ (coroot (s i).val.val) = if i=j then (d:ℂ) else 0 := by simpa using hl (s i)
    obtain ⟨hj,rfl⟩ := D_diagonal H b hn s j d hd χ labs γ hγ hD
    exact no_typeD_vector h hp H b hv (by omega) s hD (fun i => by
      simpa only [Fin.ext_iff,hj,Nat.cast_one] using labs i)
  · exact E6_singleton_impossible H b s hE j d hd χ (fun k => by
      by_cases hk : k = j <;> simpa [hk] using hl k) γ hγ


set_option maxHeartbeats 1800000 in
/-- For every effective proper compact orthogonal pair with complex
quotient commutant, the full cubic radical of its canonical half is zero. -/
theorem all_rank_orthogonal_cubic_radical_eq_bot (B : CompactForm (orthogonalAlgebra W))
    (h : LieSubalgebra ℝ (orthogonalAlgebra W)) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊥ := by
  by_contra hr
  letI : IsKilling ℂ (ℂ ⊗[ℝ] h) := (all_rank_complex_structural_reduction B h heff hp e hr).2.2.2.1
  letI : IsSimple ℂ (ℂ ⊗[ℝ] h) := all_rank_orthogonal_complexified_isotropy_simple B h heff hp e hr
  obtain ⟨x,hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℂ (ℂ ⊗[ℝ] h)
  let H := LieSubalgebra.engel ℂ x
  letI : H.IsCartanSubalgebra := hx
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  have hfamily := orthogonal_cartan_families H b (compact_isotropy_no_weyl_negation B h hp e H b)
  rcases hfamily with ⟨n,_,s,hA⟩|hfork
  · exact compact_orthogonal_no_type_A B h heff hp e hr H b s.symm (by ext i j; exact hA i j)
  exact no_orthogonal_fork B h heff hp e hr H b hfork

end CubicAnomaly.Classification.ClassicalConstituentOrthogonalExclusion
