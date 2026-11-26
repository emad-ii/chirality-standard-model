import CubicAnomaly.Classification.RootClassificationGrades
import CubicAnomaly.Classification.IntrinsicAnomaly
import CubicAnomaly.Classification.FullRankRoots

/-!
# The original cubic radical in exceptional census coordinates

The census lists, reduced to a specified character grade, give the exact
integer matrix of the actual root cubic in the Cartan basis dual to the
identified simple roots. This yields a rational kernel test for the
original compact pair using only the authored roots and character values.
-/

namespace CubicAnomaly.Classification.RootClassificationExceptional

open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.Selection
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.ToralCharacter
open CubicAnomaly.Classification.RootCharacterCoordinates
open CubicAnomaly.Classification.RootLatticeBasis
open CubicAnomaly.Classification.FullRankRoots
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.CoordinateCubic
open CubicAnomaly.Classification.RootSupportDimension
open CubicAnomaly.Classification.RootSupportTrace
open CubicAnomaly.Classification.RootCubicKernel
open LieAlgebra LieModule Module LieAlgebra.IsKilling Matrix

variable {d : RootDatum}

section Lie

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base) (s : Index d ≃ b.support)

/-- Cartan basis dual to the indexed simple roots. -/
noncomputable def simpleCartanBasis : Basis (Index d) K H :=
  (b.toWeightBasis.reindex s.symm).dualBasis.map (Module.evalEquiv K H).symm

/-- Evaluation in the dual simple-root basis reads the specified coordinate. -/
theorem realize_apply_simpleCartanBasis (v : Vector ℤ d.cartan.size) (i : Index d) :
    realize b s v (simpleCartanBasis H b s i) = (v.get i : K) := by
  let B := b.toWeightBasis.reindex s.symm
  have hv : realize b s v = B.equivFun.symm (fun j => (v.get j : K)) := by
    simp [B, realize, Basis.equivFun_symm_apply, Int.cast_smul_eq_zsmul, Vector.get]
  change realize b s v ((B.dualBasis.map (Module.evalEquiv K H).symm) i) = _
  simp only [Basis.map_apply, Module.apply_evalEquiv_symm_apply, Basis.dualBasis_apply]
  change B.equivFun (realize b s v) i = _
  rw [hv, B.equivFun.apply_symm_apply]

/-- Each graded census table indexes precisely the supported actual root functions. -/
theorem exists_grade_support_equiv
    (hd : IsExceptionalCensusDatum d)
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j)
    (χ : rootLattice H →+ ZMod 3) (k : ZMod 3) :
    ∃ f : ↥(gradeTable d (simpleCharacterEquiv H b s χ) k) ≃
        containedRoots H (rootCharacterGrade H χ k),
      ∀ v, (f v).val = ⇑(realize b s v.val) := by
  obtain ⟨e, he, hgrade⟩ := actual_exceptional_root_grade_equiv H b s hd h
  let S := gradeTable d (simpleCharacterEquiv H b s χ) k
  let T := containedRoots H (rootCharacterGrade H χ k)
  let lift (v : ↥S) : ↥(table d) := ⟨v.val, (Finset.mem_filter.mp v.property).1⟩
  let f (v : ↥S) : T := ⟨(e (lift v)).val,
    (hgrade χ (lift v) k).mpr (Finset.mem_filter.mp v.property).2⟩
  have hval (v : ↥S) : (f v).val = ⇑(realize b s v.val) := congrArg DFunLike.coe (he (lift v))
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hval⟩
  · intro u v huv
    have huv' : ⇑(realize b s u.val) = ⇑(realize b s v.val) :=
      (hval u).symm.trans ((congrArg Subtype.val huv).trans (hval v))
    exact Subtype.ext (realize_injective b s (DFunLike.coe_injective huv'))
  · intro w
    let α : H.root := ⟨Weight.mk w.val w.property.2.1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.property.1⟩⟩
    let v := e.symm α
    have hev : e v = α := e.apply_symm_apply _
    have hv : v.val ∈ S := Finset.mem_filter.mpr ⟨v.property,
      (hgrade χ v k).mp (by rw [hev]; exact w.property)⟩
    refine ⟨⟨v.val, hv⟩, Subtype.ext ?_⟩
    change ((e v).val : H → K) = w.val
    rw [hev]
    rfl

/-- On the common Cartan the actual root-cubic matrix is exactly the scalar
extension of the matrix formed by the enumerated exceptional coordinates. -/
theorem actual_cubic_matrix_eq_census (hd : IsExceptionalCensusDatum d)
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j)
    (χ : rootLattice H →+ ZMod 3) (k : ZMod 3) :
    actualRootCubicMatrix H (rootCharacterGrade H χ k) (simpleCartanBasis H b s) =
      (censusCubicMatrix d (simpleCharacterEquiv H b s χ) k).map (Int.castRingHom K) := by
  classical
  obtain ⟨f, hf⟩ := exists_grade_support_equiv H b s hd h χ k
  ext jk i
  letI := (containedRoots_finite H (rootCharacterGrade H χ k)).fintype
  let c (w : containedRoots H (rootCharacterGrade H χ k)) : K :=
    w.val (simpleCartanBasis H b s i) * w.val (simpleCartanBasis H b s jk.1) *
      w.val (simpleCartanBasis H b s jk.2)
  change ∑ w, c w = _
  rw [← f.sum_comp c]
  simp [c, hf, realize_apply_simpleCartanBasis, censusCubicMatrix]

/-- Full span of the actual zero roots excludes every nonzero integral
functional annihilating the zero-grade census vectors. -/
theorem zero_grade_separates_census_coordinates
    (hd : IsExceptionalCensusDatum d)
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j)
    (χ : rootLattice H →+ ZMod 3) (S : LieSubalgebra K L)
    (hzero : S.toSubmodule = rootCharacterGrade H χ 0)
    (hspan : Submodule.span K (containedRootForms H S) = ⊤)
    (w : Vector ℤ d.cartan.size)
    (hw : ∀ v ∈ gradeTable d (simpleCharacterEquiv H b s χ) 0,
      ∑ i, v.get i * w.get i = 0) : ∀ i, w.get i = 0 := by
  classical
  let B := simpleCartanBasis H b s
  let x := B.equivFun.symm (fun i => (w.get i : K))
  obtain ⟨f, hf⟩ := exists_grade_support_equiv H b s hd h χ 0
  have hkill : ∀ φ ∈ containedRootForms H S, φ x = 0 := by
    rintro φ ⟨α, hα, rfl⟩
    have hg : ((α.val : H → K)) ∈ containedRoots H (rootCharacterGrade H χ 0) :=
      ⟨(Finset.mem_filter.mp α.property).2, α.val.genWeightSpace_ne_bot, hzero ▸ hα⟩
    obtain ⟨v, hv⟩ := f.surjective ⟨_, hg⟩
    have hfun : ⇑(realize b s v.val) = (α.val : H → K) :=
      (hf v).symm.trans (congrArg Subtype.val hv)
    change (α.val : H → K) x = 0
    rw [← hfun]
    have heval := congrArg (fun z : ℤ => (z : K)) (hw v.val v.property)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_zero] at heval
    simpa [x, B, Basis.equivFun_symm_apply, realize_apply_simpleCartanBasis, mul_comm] using heval
  have hker : Submodule.span K (containedRootForms H S) ≤
      LinearMap.ker (Module.Dual.eval K H x) := Submodule.span_le.mpr hkill
  rw [hspan] at hker
  have hx : x = 0 := Module.evalEquiv K H |>.injective <| by
    ext φ
    simpa only [map_zero, LinearMap.zero_apply] using
      (hker (by trivial : φ ∈ (⊤ : Submodule K (Dual K H))) : φ x = 0)
  have hcoord := congrArg B.equivFun hx
  simp only [x, B.equivFun.apply_symm_apply, map_zero] at hcoord
  exact fun i => Int.cast_eq_zero.mp (congrFun hcoord i)

end Lie

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.HermitianRealization
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.RationalKernel
open scoped TensorProduct

/-- For an identified exceptional common Cartan and its grade-one half, the
original canonical mixed radical is nonzero exactly when the authored census
coordinate matrix has a nonzero rational kernel vector. -/
theorem canonical_anomaly_iff_census_kernel
    {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥) [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra] (hH : H ≤ complexifiedSubalgebra h)
    (b : (rootSystem H).Base) (s : Index d ≃ b.support) (hd : IsExceptionalCensusDatum d)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = matrix d i j)
    (χ : rootLattice H →+ ZMod 3)
    (hone : rootCharacterGrade H χ 1 =
      (ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e)
        Complex.I).toSubmodule) :
    (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥ ↔
      ∃ v : Index d → ℚ, v ≠ 0 ∧
        ((censusCubicMatrix d (simpleCharacterEquiv H b s χ) 1).map (Int.cast : ℤ → ℚ)) *ᵥ v = 0 := by
  rw [canonical_anomaly_iff_actual_root_kernel B h heff hproper e hcenter H hH
    (simpleCartanBasis H b s), ← hone, actual_cubic_matrix_eq_census H b s hd hC]
  exact integer_matrix_complex_kernel_iff_rational _

end CubicAnomaly.Classification.RootClassificationExceptional
