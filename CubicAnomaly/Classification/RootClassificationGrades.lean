import CubicAnomaly.Classification.RootClassificationExceptional
import CubicAnomaly.Classification.Selection
import CubicAnomaly.Classification.RootCharacterCoordinates
import Mathlib.LinearAlgebra.Basis.Submodule

/-!
# Exceptional census coordinates for actual Cartan roots and their grades

The simple roots form an integral basis of the actual function-valued root
lattice. For a Cartan matrix identified with an authored exceptional matrix,
every actual root and every root-lattice character is accounted for by the
census coordinates. Its grade is the ordinary coordinate dot product.
-/

namespace CubicAnomaly.Classification.RootClassificationExceptional

open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.Selection
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.ToralCharacter
open CubicAnomaly.Classification.RootCharacterCoordinates
open CubicAnomaly.Classification.RootLatticeBasis
open CubicAnomaly.Classification.CommonCartan
open LieAlgebra LieModule Module LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

private theorem simple_span_eq :
    Submodule.span ℤ (Set.range b.toWeightBasis) = (rootSystem H).rootSpan ℤ := by
  rw [RootPairing.rootSpan, ← b.span_int_root_support, Set.image_eq_range]
  exact congrArg (fun f : b.support → Module.Dual K H => Submodule.span ℤ (Set.range f))
    (funext b.toWeightBasis_apply)

/-- The integral basis of the actual lattice given by the actual simple roots. -/
noncomputable def simpleLatticeBasis : Basis b.support ℤ (rootLattice H) :=
  (b.toWeightBasis.restrictScalars ℤ).map
    ((LinearEquiv.ofEq _ _ (simple_span_eq H b)).trans (rootSpanEquivRootLattice H))

@[simp] theorem simpleLatticeBasis_apply (i : b.support) :
    simpleLatticeBasis H b i = rootLatticeElement H i.val := by
  apply Subtype.ext
  change ⇑(((b.toWeightBasis.restrictScalars ℤ) i : Module.Dual K H)) = _
  rw [Module.Basis.restrictScalars_apply, b.toWeightBasis_apply]
  rfl

variable {d : RootDatum} (s : Index d ≃ b.support)

/-- All assignments to the indexed simple roots extend uniquely to characters
of the actual root lattice. -/
noncomputable def simpleCharacterEquiv :
    (rootLattice H →+ ZMod 3) ≃ (Index d → ZMod 3) :=
  rootCharacterBasisEquiv H ((simpleLatticeBasis H b).reindex s.symm)

@[simp] theorem simpleCharacterEquiv_apply (χ : rootLattice H →+ ZMod 3) (i : Index d) :
    simpleCharacterEquiv H b s χ i = χ (rootLatticeElement H (s i).val) := by
  simp [simpleCharacterEquiv, rootCharacterBasisEquiv]

private theorem rootLatticeElement_eq_census_sum
    {α : H.root} {v : Vector ℤ d.cartan.size}
    (hv : (rootSystem H).root α = realize b s v) :
    rootLatticeElement H α = ∑ i, v[i] • rootLatticeElement H (s i).val := by
  apply Subtype.ext
  funext t
  have ht := congrArg (fun f : Module.Dual K H => f t) hv
  simpa [realize, rootLatticeElement, Finset.sum_apply] using ht

private theorem certified_of_exceptional (hd : IsExceptionalCensusDatum d) : Certified d := by
  obtain ⟨hG, hF, h₆, h₇, h₈⟩ := exceptional_root_tables_certified
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact hG
  · exact hF
  · exact h₆
  · exact h₇
  · exact h₈

/-- For any of the five identified simple Cartan matrices, there is a single
bijection from the enumerated coordinates to actual Lie roots which works
simultaneously for all characters and grades. -/
theorem actual_exceptional_root_grade_equiv
    (hd : IsExceptionalCensusDatum d)
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j) :
    ∃ e : ↥(table d) ≃ H.root,
      (∀ v, (rootSystem H).root (e v) = realize b s v.val) ∧
      ∀ (χ : rootLattice H →+ ZMod 3) (v : ↥(table d)) (k : ZMod 3),
        ((e v).val : H → K) ∈ containedRoots H (rootCharacterGrade H χ k) ↔
          ∑ i, ((v.val[i] : ℤ) : ZMod 3) * simpleCharacterEquiv H b s χ i = k := by
  obtain ⟨e, he⟩ := exists_census_root_equiv b s (certified_of_exceptional hd) h
  refine ⟨e, he, fun χ v k => ?_⟩
  rw [root_mem_character_grade_iff, rootLatticeElement_eq_census_sum H b s (he v)]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, simpleCharacterEquiv_apply]

end CubicAnomaly.Classification.RootClassificationExceptional
