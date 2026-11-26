import CubicAnomaly.Fixed.E8RadicalIdentificationData
import CubicAnomaly.Fixed.E8FullCubic

/-!
# The cubic radical is the E₆ root-lattice Lie algebra

The source of the equivalence has the six-coordinate E₆ roots and the
standard lattice bracket. A signed inclusion preserves that bracket on all
basis pairs. Bilinearity gives bracket preservation on arbitrary vectors.
Independence and dimension give an equivalence with the full cubic radical.
-/

namespace CubicAnomaly.Fixed.E6Lattice

noncomputable section

/-- The complex coordinate space of the root-lattice construction. -/
def Algebra := Index → ℂ

instance : AddCommGroup Algebra := inferInstanceAs (AddCommGroup (Index → ℂ))
instance : Module ℂ Algebra := inferInstanceAs (Module ℂ (Index → ℂ))

/-- The lattice bracket, extended from its integral structure constants. -/
def latticeBracket (x y : Algebra) : Algebra :=
  ∑ i : Index, ∑ j : Index, (x i * y j) •
    ((products i j).map (fun p => p.2 • (Pi.single p.1 (1 : ℂ) : Index → ℂ))).sum

end

end CubicAnomaly.Fixed.E6Lattice

namespace CubicAnomaly.Fixed.E8RadicalIdentification

open CubicAnomaly.Fixed
open E8BracketData E8SparseModel E8Adjoint E8Grading E8GradingData
open E8FullCubicData E8FullCubic E8RadicalIdentificationData

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 650000

private def toRadicalLabel (i : E6Lattice.Index) : E6Label :=
  ⟨label i, (e6_lattice_embedding_certificate.2.2.2.2 i).1⟩

private def toZeroLabel (i : E6Lattice.Index) : GradeLabel 0 :=
  e6ToZeroLabel (toRadicalLabel i)

private theorem label_mem (i : E6Lattice.Index) : label i ∈ basisList :=
  ((e8_mem_gradeLabels 0 _).mp (toZeroLabel i).property).1

private def image (i : E6Lattice.Index) : fullRadical :=
  ⟨(sign i : ℂ) • zeroBasis (toZeroLabel i),
    fullRadical.smul_mem _ (e8_e6Span_le_fullRadical
      (Submodule.subset_span ⟨toRadicalLabel i, rfl⟩))⟩

private theorem image_independent : LinearIndependent ℂ image := by
  have hi : Function.Injective toZeroLabel := fun i j h =>
    e6_lattice_embedding_certificate.2.2.2.1 (congrArg Subtype.val h)
  have hs (i : E6Lattice.Index) : (sign i : ℂ) ≠ 0 := by
    exact_mod_cast (e6_lattice_embedding_certificate.2.2.2.2 i).2
  apply LinearIndependent.of_comp fullRadical.toSubmodule.subtype
  exact (zeroBasis.linearIndependent.comp toZeroLabel hi).units_smul
    (fun i => Units.mk0 (sign i : ℂ) (hs i))

/-- The signed coordinate embedding as a complex linear equivalence onto the
entire actual radical. -/
def latticeEquiv : E6Lattice.Algebra ≃ₗ[ℂ] fullRadical :=
  (Fintype.linearCombination ℂ image).linearEquivOfInjective
    image_independent.fintypeLinearCombination_injective (by
      rw [Module.finrank_fintype_fun_eq_card, e8_full_radical_finrank]
      decide)

private theorem latticeEquiv_single (i : E6Lattice.Index) :
    latticeEquiv (Pi.single i (1 : ℂ)) = image i := by
  change Fintype.linearCombination ℂ image (Pi.single i (1 : ℂ)) = image i
  simp

private theorem image_val (i : E6Lattice.Index) :
    (image i).val.val = (sign i : ℂ) • adjointEquiv (basisVector (label i)) := by
  change (sign i : ℂ) • (zeroBasis (toZeroLabel i)).val = _
  rw [e8_full_zeroBasis_val]
  rfl

private theorem signed_list_image (xs : List (E6Lattice.Index × ℤ)) :
    (latticeEquiv ((xs.map (fun p => p.2 •
      (Pi.single p.1 (1 : ℂ) : E6Lattice.Index → ℂ))).sum)).val.val =
    adjointEquiv (realize (signedImage xs)) := by
  induction xs with
  | nil =>
    change (latticeEquiv 0).val.val = adjointEquiv 0
    simp
  | cons p xs ih =>
    rcases p with ⟨i, n⟩
    let v : E6Lattice.Algebra := Pi.single i (1 : ℂ)
    let t : E6Lattice.Algebra :=
      (xs.map fun p => p.2 • (Pi.single p.1 (1 : ℂ) : E6Lattice.Index → ℂ)).sum
    change (latticeEquiv (n • v + t)).val.val =
      adjointEquiv ((n * sign i) • basisVector (label i) + realize (signedImage xs))
    conv_lhs => rw [map_add latticeEquiv, map_zsmul latticeEquiv]
    conv_rhs => rw [map_add adjointEquiv, map_zsmul adjointEquiv]
    change n • (latticeEquiv (Pi.single i (1 : ℂ))).val.val + _ =
      (n * sign i) • adjointEquiv (basisVector (label i)) + _
    apply congrArg₂ (· + ·) _ ih
    calc
      n • (latticeEquiv (Pi.single i (1 : ℂ))).val.val =
          n • (image i).val.val :=
        congrArg (fun z : fullRadical => n • z.val.val) (latticeEquiv_single i)
      _ = n • ((sign i : ℂ) • adjointEquiv (basisVector (label i))) :=
        congrArg (n • ·) (image_val i)
      _ = _ := by rw [Int.cast_smul_eq_zsmul, mul_smul]

private theorem basis_bracket (i j : E6Lattice.Index) :
    latticeEquiv (((E6Lattice.products i j).map (fun p =>
      p.2 • (Pi.single p.1 (1 : ℂ) : E6Lattice.Index → ℂ))).sum) =
    ⁅image i, image j⁆ := by
  apply Subtype.ext
  apply Subtype.ext
  change (latticeEquiv _).val.val = ⁅(image i).val.val, (image j).val.val⁆
  rw [signed_list_image, image_val, image_val, smul_lie, lie_smul, smul_smul,
    ← e8_adjointEquiv_bracket, e8_candidateBracket_labels _ _ (label_mem i) (label_mem j)]
  have h := e8_realize_eq_of_sparseEq _ _ (e6_lattice_bracket_certificate i j)
  rw [h, e8_realize_scale, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_mul]

/-- The independently specified E₆ lattice bracket is the commutator on the
actual cubic radical under the signed coordinate change. -/
theorem e8_latticeEquiv_bracket (x y : E6Lattice.Algebra) :
    latticeEquiv (E6Lattice.latticeBracket x y) = ⁅latticeEquiv x, latticeEquiv y⁆ := by
  change latticeEquiv (∑ i : E6Lattice.Index, ∑ j : E6Lattice.Index,
    (x i * y j) • _) = ⁅∑ i, x i • image i, ∑ j, y j • image j⁆
  rw [sum_lie_sum]
  simp only [map_sum, map_smul, basis_bracket, smul_lie, lie_smul, smul_smul, mul_comm]

end

end CubicAnomaly.Fixed.E8RadicalIdentification

namespace CubicAnomaly.Fixed.E6Lattice

open CubicAnomaly.Fixed.E8RadicalIdentification

noncomputable section

instance : LieRing Algebra where
  bracket := latticeBracket
  add_lie x y z := latticeEquiv.injective (by
    simp only [e8_latticeEquiv_bracket, map_add, add_lie])
  lie_add x y z := latticeEquiv.injective (by
    simp only [e8_latticeEquiv_bracket, map_add, lie_add])
  lie_self x := latticeEquiv.injective (by
    simp only [e8_latticeEquiv_bracket, map_zero, lie_self])
  leibniz_lie x y z := latticeEquiv.injective (by
    simp only [e8_latticeEquiv_bracket, map_add]
    exact leibniz_lie _ _ _)

instance : LieAlgebra ℂ Algebra where
  lie_smul c x y := latticeEquiv.injective (by
    change latticeEquiv (latticeBracket x (c • y)) = latticeEquiv (c • latticeBracket x y)
    simp only [e8_latticeEquiv_bracket, map_smul, lie_smul])

/-- The split complex E₆ lattice Lie algebra is isomorphic to the full cubic
radical of the constructed degree-zero exceptional algebra. -/
def radicalLieEquiv : Algebra ≃ₗ⁅ℂ⁆ E8FullCubic.fullRadical where
  __ := latticeEquiv
  map_lie' := fun {x y} => e8_latticeEquiv_bracket x y

/-- Images of the simple coroots and the positive simple-root vectors in the
actual zero algebra. The root-vector signs record the specified Geck basis. -/
theorem e6_lattice_simple_images (a : Fin 6) :
    (radicalLieEquiv (Pi.single (.inl a) (1 : ℂ))).val =
      E8FullCubic.cartan (E8GradingData.e6SimpleIndex a) ∧
    ∀ h : E8BracketData.simpleVector (E8GradingData.e6SimpleIndex a) ∈ E8GradingData.zeroRoots,
      (radicalLieEquiv (Pi.single (.inr (simpleRootIndex a)) (1 : ℂ))).val =
        (E8RadicalIdentificationData.sign (.inr (simpleRootIndex a)) : ℂ) •
          E8FullCubic.rootVector ⟨_, h⟩ := by
  constructor
  · exact congrArg Subtype.val (latticeEquiv_single (.inl a))
  · intro h
    rw [show radicalLieEquiv (Pi.single (.inr (simpleRootIndex a)) (1 : ℂ)) =
        image (.inr (simpleRootIndex a)) from latticeEquiv_single _]
    apply congrArg ((E8RadicalIdentificationData.sign (.inr (simpleRootIndex a)) : ℂ) • ·)
    apply congrArg E8FullCubic.zeroBasis
    apply Subtype.ext
    exact congrArg Sum.inr (E8RadicalIdentificationData.e6_lattice_simple_root_certificate a)

end

end CubicAnomaly.Fixed.E6Lattice
