import CubicAnomaly.Fixed.E8RadicalFamilyData
import CubicAnomaly.Fixed.E8FullCubic

/-! The full degree-zero algebra is the Lie direct product of the full
mixed cubic radical and the embedded family algebra. -/

namespace CubicAnomaly.Fixed.E8RadicalFamily

open E8Grading E8GradingData E8FullCubic E8FullCubicData E8BracketData
open E8Adjoint E8SparseModel E8A2Data TensorAnomaly

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

private theorem label_commutes_unit (d : E6Label) (i j : Fin 3) :
    ⁅(zeroBasis (e6ToZeroLabel d)).val, E8A2.unitImage i j⁆ = 0 := by
  have hd : d.val ∈ basisList := (e8_mem_gradeLabels 0 d.val).mp
    (e8_full_cubic_support_certificate.2.1 d.property) |>.1
  have hf : ∀ p ∈ familyUnitData i j, p.1 ∈ basisList := by
    simpa only [supported, List.all_eq_true, List.contains_iff_mem] using
      (e8_a2_unit_support_certificate i j).1
  have hc := e8_realize_eq_of_sparseEq _ _
    (e8_radical_family_unit_certificate d.val d.property i j)
  have hb := e8_candidateBracket_realize (E8BracketData.singleton d.val 1)
    (familyUnitData i j) (by simpa [E8BracketData.singleton] using hd) hf
  rw [e8_realize_singleton, one_smul] at hb
  have hz : candidateBracket (basisVector d.val) (realize (familyUnitData i j)) = 0 :=
    hb.trans hc
  rw [e8_full_zeroBasis_val]
  change ⁅adjointEquiv (basisVector d.val), adjointEquiv (E8A2.unitVector i j)⁆ = 0
  rw [← e8_adjointEquiv_bracket]
  simp [E8A2.unitVector, hz]

private theorem label_commutes_matrix (d : E6Label) (A : E8A2.Matrix3) :
    ⁅(zeroBasis (e6ToZeroLabel d)).val, E8A2.gl3Hom A⁆ = 0 := by
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A B ha hb => simp [lie_add, ha, hb]
  | h_std_basis i j t =>
    rw [show Matrix.single i j t = t • Matrix.single i j (1 : ℂ) by simp,
      map_smul, lie_smul, E8A2.e8_a2_gl3Hom_unit, label_commutes_unit, smul_zero]

/-- Every element of the cubic radical commutes with the actual family embedding. -/
theorem e8_radical_family_commute (x : fullRadical) (F : E8A2.sl3) :
    ⁅x.val, E8A2.sl3ZeroEmbedding F⁆ = 0 := by
  have hx : x.val ∈ e6Span := e8_full_radical_eq_e6Span ▸ x.property
  refine Submodule.span_induction
    (p := fun z _ => ⁅z, E8A2.sl3ZeroEmbedding F⁆ = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨d, rfl⟩
    exact Subtype.ext (label_commutes_matrix d F.val)
  · exact zero_lie _
  · intro a b _ _ ha hb
    simp [add_lie, ha, hb]
  · intro c a _ ha
    simp [smul_lie, ha]

theorem e8_radical_isCompl_family : IsCompl fullRadical.toSubmodule familySpace := by
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).mpr e8_full_radical_disjoint_family
  change Module.finrank ℂ zeroSubalgebra ≤ Module.finrank ℂ fullRadical +
    Module.finrank ℂ familySpace
  rw [e8_zeroSubalgebra_finrank, e8_full_radical_finrank, e8_familySpace_finrank]

private def idealProductEquiv {L K : Type*} [LieRing L] [LieAlgebra ℂ L]
    [LieRing K] [LieAlgebra ℂ K] (I : LieIdeal ℂ L) (f : K →ₗ⁅ℂ⁆ L)
    (hinj : Function.Injective f) (hcomp : IsCompl I.toSubmodule f.toLinearMap.range)
    (hcomm : ∀ (x : I) (y : K), ⁅x.val, f y⁆ = 0) :
    ProductLie I K ≃ₗ⁅ℂ⁆ L := by
  let e := ((LinearEquiv.refl ℂ I).prodCongr (LinearEquiv.ofInjective f.toLinearMap hinj)).trans
    (Submodule.prodEquivOfIsCompl I.toSubmodule f.toLinearMap.range hcomp)
  exact { e with
    map_lie' := by
      intro x y
      have hrev : ⁅f x.2, y.1.val⁆ = 0 := by rw [← lie_skew, hcomm, neg_zero]
      change ⁅x.1.val, y.1.val⁆ + f ⁅x.2, y.2⁆ =
        ⁅x.1.val + f x.2, y.1.val + f y.2⁆
      simp only [LieHom.map_lie, add_lie, lie_add, hcomm, hrev, zero_add, add_zero] }

/-- Addition identifies the actual cubic radical and the family copy of
sl₃ with the entire degree-zero Lie algebra. -/
def radicalFamilyEquiv : ProductLie fullRadical E8A2.sl3 ≃ₗ⁅ℂ⁆ zeroSubalgebra :=
  idealProductEquiv fullRadical E8A2.sl3ZeroEmbedding E8A2.e8_a2_sl3ZeroEmbedding_injective
    e8_radical_isCompl_family e8_radical_family_commute

theorem e8_radicalFamilyEquiv_apply (x : fullRadical) (F : E8A2.sl3) :
    radicalFamilyEquiv (x, F) = x.val + E8A2.sl3ZeroEmbedding F := rfl

end

end CubicAnomaly.Fixed.E8RadicalFamily
