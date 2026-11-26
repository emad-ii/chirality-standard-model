import CubicAnomaly.Fixed.E8RadicalIdentificationSimple
import CubicAnomaly.Fixed.E8LocalCompactFamily
import CubicAnomaly.Fixed.E8LocalHighestWeight

/-!
# The compact isotropy and its action on the canonical half

The two real ideals add to the entire compact isotropy. In its local and
family coordinates the original Hermitian generator acts by the first
factor on each local 27 and by the defining three-dimensional action on
the family labels.
-/

namespace CubicAnomaly.Fixed.E8CompactIsotropy

open CubicAnomaly.Classification.UnitaryGeometry
open E8Grading E8FullCubic E8CompactPair E8CompactFactors E8CanonicalPair
open E8MatterMatching E8LocalMatter E8LocalCompactFamily E8RadicalFamily TensorAnomaly
open MatterSpectrum
open scoped TensorProduct Matrix

noncomputable section

abbrev Su3 := specialUnitaryAlgebra (EuclideanSpace ℂ (Fin 3))

/-- The 78-dimensional real radical is a compact simple real form of E₆. -/
theorem e8_compact_radical_isSimple : LieAlgebra.IsSimple ℝ compactRadical := by
  letI := E6Lattice.e6_lattice_isSimple
  letI : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] compactRadical) :=
    E8Structure.simple_of_complex_lie_equiv compactRadicalComplexEquiv
  exact CubicAnomaly.Classification.SimpleIdealStructure.simple_of_complexification_simple

private def idealProduct {L K : Type*} [LieRing L] [LieAlgebra ℝ L]
    [LieRing K] [LieAlgebra ℝ K] (I J : LieIdeal ℝ L) (e : K ≃ₗ⁅ℝ⁆ J)
    (hcomp : IsCompl I.toSubmodule J.toSubmodule)
    (hcomm : ∀ (r : I) (s : J), ⁅r.val, s.val⁆ = 0) :
    ProductLie I K ≃ₗ⁅ℝ⁆ L := by
  let p := ((LinearEquiv.refl ℝ I).prodCongr e.toLinearEquiv).trans
    (Submodule.prodEquivOfIsCompl I.toSubmodule J.toSubmodule hcomp)
  exact { p with
    map_lie' := by
      intro x y
      have hrev : ⁅(e x.2).val, y.1.val⁆ = 0 := by rw [← lie_skew, hcomm, neg_zero]
      change ⁅x.1.val, y.1.val⁆ + (e ⁅x.2,y.2⁆).val =
        ⁅x.1.val + (e x.2).val, y.1.val + (e y.2).val⁆
      simp only [e.map_lie, add_lie, lie_add, hcomm, hrev, zero_add, add_zero]
      rfl }

/-- Addition of the actual compact radical and the standard special-unitary
family factor gives the paper's original compact isotropy algebra. -/
def compactIsotropyEquiv : ProductLie compactRadical Su3 ≃ₗ⁅ℝ⁆ compactZero :=
  idealProduct compactRadical compactFamily compactFamilySu3Equiv.symm
    e8_compact_factors_isCompl e8_compact_factors_commute

theorem e8_compact_isotropy_apply (r : compactRadical) (s : Su3) :
    compactIsotropyEquiv (r, s) = r.val + (compactFamilySu3Equiv.symm s).val := rfl

/-- Coordinates on the canonical half indexed by the three copies of the
actual fundamental E₆ matter module. -/
def canonicalCopies : Matter81 ≃ₗ[ℂ] (Fin canonicalHalf.dimension → ℂ) :=
  actualMatterEquiv.trans canonicalMatterCoordinates

/-- The defining family matrix written in the signed matter coordinates. -/
def familyMatrix (s : Su3) : E8A2.sl3 :=
  compactFamilyComplexEquiv (1 ⊗ₜ[ℝ] compactFamilySu3Equiv.symm s)

/-- The actual compact radical generator in the independent E₆ algebra. -/
def localGenerator (r : compactRadical) : E6Lattice.Algebra :=
  compactRadicalComplexEquiv (1 ⊗ₜ[ℝ] r)

private theorem radical_embedding (r : compactRadical) :
    (E6Lattice.radicalLieEquiv (localGenerator r)).val = compactZeroToComplex r.val := by
  calc
    _ = idealComplexification compactRadical (1 ⊗ₜ[ℝ] r) :=
      congrArg Subtype.val (E6Lattice.radicalLieEquiv.apply_symm_apply _)
    _ = compactZeroToComplex r.val :=
      (e8_zeroComplexificationEquiv_tmul 1 r.val).trans (one_smul _ _)

private theorem both_embeddings (r : compactRadical) (s : Su3) :
    radicalFamilyEquiv (E6Lattice.radicalLieEquiv (localGenerator r), familyMatrix s) =
      compactZeroToComplex (compactIsotropyEquiv (r,s)) := by
  exact ((e8_radicalFamilyEquiv_apply _ _).trans
    (congrArg₂ (· + ·) (radical_embedding r)
      (e8_compact_family_embedding (compactFamilySu3Equiv.symm s)))).trans
    (map_add compactZeroToComplex _ _).symm

/-- Under the compact product equivalence every generator of the original
canonical half acts by the irreducible E₆ local action and the defining
family action. The factor of `I` follows the manuscript's Hermitian convention. -/
theorem e8_compact_isotropy_canonical_action (r : compactRadical) (s : Su3) (v : Matter81) :
    canonicalCopies (fun i =>
      ⁅localGenerator r, v i⁆ + ∑ j, (familyMatrix s).val i j • v j) =
    Complex.I • (canonicalHalf.generators (compactIsotropyEquiv (r,s)) *ᵥ canonicalCopies v) := by
  let R := E6Lattice.radicalLieEquiv (localGenerator r)
  let F := familyMatrix s
  let x := compactIsotropyEquiv (r,s)
  have hh : actualMatterEquiv.symm ⁅x, actualMatterEquiv v⁆ =
      (fun i => localRepresentation R (v i) + ∑ j, F.val i j • v j) := by
    change actualMatterEquiv.symm ⁅compactZeroToComplex x, actualMatterEquiv v⁆ = _
    exact (congrArg (fun y : zeroSubalgebra => actualMatterEquiv.symm ⁅y, actualMatterEquiv v⁆)
      (both_embeddings r s).symm).trans (funext (e8_local_family_action R F v))
  have hv := (actualMatterEquiv.symm_apply_eq.mp hh).symm
  exact (congrArg canonicalMatterCoordinates hv).trans
    (e8_canonical_matter_action x (actualMatterEquiv v))

end

end CubicAnomaly.Fixed.E8CompactIsotropy
