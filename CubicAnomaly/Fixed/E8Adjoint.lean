import CubicAnomaly.Fixed.E8GeneratorMatching
import CubicAnomaly.Fixed.SparseBilinear
import CubicAnomaly.Fixed.AdjointRecognition
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-!
# The actual 248-dimensional exceptional adjoint algebra

The integer table defines a bilinear operation on the already constructed
Geck module. Its checked generator derivation identities produce an actual
equivariant matrix map. Irreducibility and the generator images identify its
image with the entire generated algebra. In particular, the dimension below
is the dimension of the actual Lie algebra, not only its defining module.

No independent Jacobi assumption or root-system classification is used.
-/

namespace CubicAnomaly.Fixed.E8Adjoint

open Matrix
open CubicAnomaly.Fixed.E8RootPairing
open CubicAnomaly.Fixed.E8Geck
open CubicAnomaly.Fixed.E8BracketData
open CubicAnomaly.Fixed.E8BracketBinding
open CubicAnomaly.Fixed.E8SparseModel
open CubicAnomaly.Fixed.E8GeneratorMatching
open RootPairing.GeckConstruction

noncomputable section

/-- The candidate operation is extended from the checked integer table on
the actual defining basis. -/
def candidateBracket : DefiningSpace →ₗ[ℂ] DefiningSpace →ₗ[ℂ] DefiningSpace :=
  SparseBilinear.bilinear dataIndex basisVector bracket

/-- Left multiplication by the candidate operation, as actual matrices. -/
def bracketMatrixMap : DefiningSpace →ₗ[ℂ] Matrix Index Index ℂ :=
  SparseBilinear.matrixMap dataIndex basisVector bracket

theorem e8_candidateBracket_basis (i j : Index) :
    candidateBracket (Pi.single i 1) (Pi.single j 1) =
      realize (bracket (dataIndex i) (dataIndex j)) :=
  SparseBilinear.sparse_bilinear_basis dataIndex basisVector bracket i j

theorem e8_candidateBracket_labels (x y : DataIndex)
    (hx : x ∈ basisList) (hy : y ∈ basisList) :
    candidateBracket (basisVector x) (basisVector y) = realize (bracket x y) := by
  obtain ⟨i, rfl⟩ := (e8_mem_basisList_iff x).mp hx
  obtain ⟨j, rfl⟩ := (e8_mem_basisList_iff y).mp hy
  exact SparseBilinear.sparse_bilinear_label dataIndex basisVector bracket
    e8_basisVector_dataIndex i j

theorem e8_bracketMatrixMap_mulVec (v w : DefiningSpace) :
    bracketMatrixMap v *ᵥ w = candidateBracket v w :=
  SparseBilinear.sparse_matrixMap_mulVec dataIndex basisVector bracket v w

theorem e8_candidateBracket_realize (xs ys : Sparse)
    (hx : ∀ p ∈ xs, p.1 ∈ basisList) (hy : ∀ p ∈ ys, p.1 ∈ basisList) :
    candidateBracket (realize xs) (realize ys) =
      realize (applySparse (fun x => applySparse (bracket x) ys) xs) := by
  exact SparseBilinear.sparse_bilinear_realize_both dataIndex basisVector bracket
    e8_basisVector_dataIndex xs ys
    (fun p hp => (e8_mem_basisList_iff p.1).mp (hx p hp))
    (fun p hp => (e8_mem_basisList_iff p.1).mp (hy p hp))

private theorem generator_equivariance
    (G : Matrix Index Index ℂ) (g : DataIndex → Sparse)
    (haction : ∀ k, G *ᵥ Pi.single k (1 : ℂ) = realize (g (dataIndex k)))
    (hsupport : ∀ x ∈ basisList, ∀ p ∈ g x, p.1 ∈ basisList)
    (hderivation : ∀ x ∈ basisList, ∀ y ∈ basisList,
      derivationCheck g x y = true) (v : DefiningSpace) :
    bracketMatrixMap (G *ᵥ v) = ⁅G, bracketMatrixMap v⁆ := by
  apply SparseBilinear.sparse_matrixMap_equivariance dataIndex basisVector bracket G
  intro v w
  apply SparseBilinear.sparse_bilinear_derivation dataIndex basisVector bracket
    e8_basisVector_dataIndex (Matrix.toLin' G) g
  · intro k
    simpa only [e8_basisVector_dataIndex, Matrix.toLin'_apply] using haction k
  · intro i j p hp
    apply (e8_mem_basisList_iff p.1).mp
    exact bracket_data_supported _ _ (e8_dataIndex_mem_basisList i)
      (e8_dataIndex_mem_basisList j) p hp
  · intro i p hp
    exact (e8_mem_basisList_iff p.1).mp
      (hsupport _ (e8_dataIndex_mem_basisList i) p hp)
  · intro i j
    exact e8_realize_eq_of_sparseEq _ _
      (hderivation _ (e8_dataIndex_mem_basisList i) _ (e8_dataIndex_mem_basisList j))

theorem e8_h_bracketMatrixMap_equivariance (i : Fin 8) (v : DefiningSpace) :
    bracketMatrixMap (h (simpleIndex i) *ᵥ v) =
      ⁅h (simpleIndex i), bracketMatrixMap v⁆ :=
  generator_equivariance _ (genH i) (geck_h_realize_basis i)
    (fun x hx => (bracket_data_generators_supported i x hx).1)
    (fun x hx y hy => (bracket_data_generator_derivations i x y hx hy).1) v

theorem e8_e_bracketMatrixMap_equivariance (i : Fin 8) (v : DefiningSpace) :
    bracketMatrixMap (e (simpleIndex i) *ᵥ v) =
      ⁅e (simpleIndex i), bracketMatrixMap v⁆ :=
  generator_equivariance _ (genE i) (geck_e_realize_basis i)
    (fun x hx => (bracket_data_generators_supported i x hx).2.1)
    (fun x hx y hy => (bracket_data_generator_derivations i x y hx hy).2.1) v

theorem e8_f_bracketMatrixMap_equivariance (i : Fin 8) (v : DefiningSpace) :
    bracketMatrixMap (f (simpleIndex i) *ᵥ v) =
      ⁅f (simpleIndex i), bracketMatrixMap v⁆ :=
  generator_equivariance _ (genF i) (geck_f_realize_basis i)
    (fun x hx => (bracket_data_generators_supported i x hx).2.2)
    (fun x hx y hy => (bracket_data_generator_derivations i x y hx hy).2.2) v

private theorem generator_image
    (G : Matrix Index Index ℂ) (g : DataIndex → Sparse)
    (haction : ∀ k, G *ᵥ Pi.single k (1 : ℂ) = realize (g (dataIndex k)))
    (d : DataIndex) (hd : d ∈ basisList) (c : ℤ)
    (himage : ∀ x ∈ basisList, sparseEq (bracket d x) (scale c (g x)) = true) :
    bracketMatrixMap (basisVector d) = c • G := by
  refine SparseBilinear.sparse_matrixMap_image dataIndex basisVector bracket
    e8_basisVector_dataIndex G g ?_ d ((e8_mem_basisList_iff d).mp hd) c ?_
  · intro k
    simpa only [e8_basisVector_dataIndex] using haction k
  · intro k
    exact (e8_realize_eq_of_sparseEq _ _
      (himage _ (e8_dataIndex_mem_basisList k))).trans (e8_realize_scale _ _)

theorem e8_h_bracketMatrixMap_image (i : Fin 8) :
    bracketMatrixMap (basisVector (.inl i)) = diagramSign i • h (simpleIndex i) :=
  generator_image _ (genH i) (geck_h_realize_basis i) (.inl i)
    (by simp [basisList]) (diagramSign i)
    (fun x hx => (bracket_data_generator_images i x hx).1)

theorem e8_e_bracketMatrixMap_image (i : Fin 8) :
    bracketMatrixMap (basisVector (.inr (simpleVector i))) =
      (-diagramSign i) • e (simpleIndex i) :=
  generator_image _ (genE i) (geck_e_realize_basis i) (.inr (simpleVector i))
    (bracket_data_simple_mem_basis i) (-diagramSign i)
    (fun x hx => (bracket_data_generator_images i x hx).2.1)

theorem e8_f_bracketMatrixMap_image (i : Fin 8) :
    bracketMatrixMap (basisVector (.inr (negateVector (simpleVector i)))) =
      diagramSign i • f (simpleIndex i) :=
  generator_image _ (genF i) (geck_f_realize_basis i)
    (.inr (negateVector (simpleVector i))) (bracket_data_negative_simple_mem_basis i)
    (diagramSign i) (fun x hx => (bracket_data_generator_images i x hx).2.2)

private def generatorSet : Set (Matrix Index Index ℂ) :=
  Set.range (h (b := base)) ∪ Set.range (e (b := base)) ∪ Set.range (f (b := base))

private theorem generatorSet_equivariance :
    ∀ G ∈ generatorSet, ∀ v : DefiningSpace,
      bracketMatrixMap ⁅G, v⁆ = ⁅G, bracketMatrixMap v⁆ := by
  rintro G ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) v
  · obtain ⟨j, rfl⟩ := simpleIndex_bijective.2 i
    exact e8_h_bracketMatrixMap_equivariance j v
  · obtain ⟨j, rfl⟩ := simpleIndex_bijective.2 i
    exact e8_e_bracketMatrixMap_equivariance j v
  · obtain ⟨j, rfl⟩ := simpleIndex_bijective.2 i
    exact e8_f_bracketMatrixMap_equivariance j v

private theorem generatorSet_in_range : generatorSet ⊆ Set.range bracketMatrixMap := by
  rintro G ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · obtain ⟨j, rfl⟩ := simpleIndex_bijective.2 i
    refine ⟨diagramSign j • basisVector (.inl j), ?_⟩
    rw [map_zsmul, e8_h_bracketMatrixMap_image, ← SemigroupAction.mul_smul,
      bracket_data_diagram_sign_sq, one_smul]
  · obtain ⟨j, rfl⟩ := simpleIndex_bijective.2 i
    refine ⟨(-diagramSign j) • basisVector (.inr (simpleVector j)), ?_⟩
    rw [map_zsmul, e8_e_bracketMatrixMap_image, ← SemigroupAction.mul_smul, neg_mul_neg,
      bracket_data_diagram_sign_sq, one_smul]
  · obtain ⟨j, rfl⟩ := simpleIndex_bijective.2 i
    refine ⟨diagramSign j • basisVector (.inr (negateVector (simpleVector j))), ?_⟩
    rw [map_zsmul, e8_f_bracketMatrixMap_image, ← SemigroupAction.mul_smul,
      bracket_data_diagram_sign_sq, one_smul]

private def witness : DefiningSpace := basisVector (.inl 0)

private theorem witness_image : bracketMatrixMap witness = h (simpleIndex 0) := by
  simpa [witness, diagramSign] using e8_h_bracketMatrixMap_image 0

private theorem witness_image_ne_zero : bracketMatrixMap witness ≠ 0 := by
  rw [witness_image]
  exact (isSl2Triple (simpleIndex 0)).h_ne_zero

private theorem witness_image_mem :
    bracketMatrixMap witness ∈ LieSubalgebra.lieSpan ℂ (Matrix Index Index ℂ) generatorSet := by
  rw [witness_image]
  exact cartan_generator_mem (simpleIndex 0)

local instance : LieModule.IsIrreducible ℂ
    (LieSubalgebra.lieSpan ℂ (Matrix Index Index ℂ) generatorSet) DefiningSpace :=
  defining_space_irreducible

/-- The actual defining module is the actual adjoint module of the generated
exceptional matrix algebra. -/
def adjointEquiv : DefiningSpace ≃ₗ⁅ℂ, E8Geck.lieAlgebra⁆ E8Geck.lieAlgebra :=
  AdjointRecognition.generatedAdjointEquiv generatorSet bracketMatrixMap
    generatorSet_equivariance witness witness_image_ne_zero witness_image_mem generatorSet_in_range

theorem e8_adjointEquiv_val (v : DefiningSpace) :
    (adjointEquiv v : Matrix Index Index ℂ) = bracketMatrixMap v := rfl

/-- The generated Lie algebra itself has dimension 248. -/
theorem e8_lieAlgebra_finrank : Module.finrank ℂ E8Geck.lieAlgebra = 248 :=
  adjointEquiv.toLinearEquiv.finrank_eq.symm.trans defining_space_finrank

theorem e8_bracketMatrixMap_injective : Function.Injective bracketMatrixMap := by
  intro v w h
  apply adjointEquiv.injective
  exact Subtype.ext h

theorem e8_bracketMatrixMap_mem (v : DefiningSpace) :
    bracketMatrixMap v ∈ E8Geck.lieAlgebra := (adjointEquiv v).property

theorem e8_bracketMatrixMap_range :
    bracketMatrixMap.range = E8Geck.lieAlgebra.toSubmodule :=
  (AdjointRecognition.generated_adjoint_recognition generatorSet bracketMatrixMap
    generatorSet_equivariance witness witness_image_ne_zero witness_image_mem
    generatorSet_in_range).2

/-- The checked operation agrees with the actual matrix commutator under the
proved adjoint identification. -/
theorem e8_candidateBracket_commutator (v w : DefiningSpace) :
    bracketMatrixMap (candidateBracket v w) = ⁅bracketMatrixMap v, bracketMatrixMap w⁆ := by
  have he := AdjointRecognition.generated_intertwiner_equivariance generatorSet
    bracketMatrixMap generatorSet_equivariance (adjointEquiv v) w
  change bracketMatrixMap ((adjointEquiv v : Matrix Index Index ℂ) *ᵥ w) =
    ⁅(adjointEquiv v : Matrix Index Index ℂ), bracketMatrixMap w⁆ at he
  simpa only [e8_adjointEquiv_val, e8_bracketMatrixMap_mulVec] using he

theorem e8_adjointEquiv_bracket (v w : DefiningSpace) :
    adjointEquiv (candidateBracket v w) = ⁅adjointEquiv v, adjointEquiv w⁆ := by
  apply Subtype.ext
  exact e8_candidateBracket_commutator v w

theorem e8_adjoint_irreducible :
    LieModule.IsIrreducible ℂ E8Geck.lieAlgebra E8Geck.lieAlgebra := by
  letI : LieModule.IsIrreducible ℂ E8Geck.lieAlgebra DefiningSpace :=
    defining_space_irreducible
  exact (LieSubmodule.orderIsoMapComap adjointEquiv).symm.isSimpleOrder

/-- Simplicity follows from the actual adjoint identification and one
nonzero simple-root `sl₂` commutator. -/
theorem e8_lieAlgebra_isSimple : LieAlgebra.IsSimple ℂ E8Geck.lieAlgebra := by
  letI := e8_adjoint_irreducible
  refine { eq_bot_or_eq_top := IsSimpleOrder.eq_bot_or_eq_top, non_abelian := ?_ }
  intro ha
  have hz := ha.trivial
    (⟨e (simpleIndex 0), raising_generator_mem (simpleIndex 0)⟩ : E8Geck.lieAlgebra)
    (⟨f (simpleIndex 0), lowering_generator_mem (simpleIndex 0)⟩ : E8Geck.lieAlgebra)
  have hm : ⁅e (simpleIndex 0), f (simpleIndex 0)⁆ = (0 : Matrix Index Index ℂ) :=
    congrArg Subtype.val hz
  rw [lie_e_f_same] at hm
  exact (isSl2Triple (simpleIndex 0)).h_ne_zero hm

end

end CubicAnomaly.Fixed.E8Adjoint
