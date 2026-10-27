import CubicAnomaly.Classification.EqualRank
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Actual root-lattice characters for the toral census

A three-class root decomposition of exact order three yields an additive
character from the actual integer root lattice to `ZMod 3`.  Its root-space
components agree with the geometric cyclic grading.  Thus the passage to a
toral character, the object enumerated by the finite census, does not require
an authored root table or a separately assumed grading assignment.
-/

namespace CubicAnomaly.Classification.ToralCharacter

open LieAlgebra LieModule
open CubicAnomaly.Classification.RootGrading

variable {K L A : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H] [AddCommGroup A]

/-- Three-class support on roots puts the entire integer root lattice in the
range of the actual cyclic order-three embedding. -/
theorem root_lattice_degree_mem_cyclic_range
    (degree : (H → K) →+ A) (c : A) (hc : addOrderOf c = 3)
    (hsupport : ∀ α : H → K, rootSpace H α ≠ ⊥ →
      degree α = 0 ∨ degree α = c ∨ degree α = -c)
    (x : rootLattice H) : degree x ∈ (orderThreeClass c hc).range := by
  have hle : rootLattice H ≤ (orderThreeClass c hc).range.comap degree := by
    apply (AddSubgroup.closure_le _).mpr
    intro α hα
    change degree α ∈ (orderThreeClass c hc).range
    rcases hsupport α hα.2 with hz | hp | hn
    · exact ⟨0, by simpa only [map_zero] using hz.symm⟩
    · exact ⟨1, by simpa only [orderThreeClass_one] using hp.symm⟩
    · exact ⟨-1, by simpa only [map_neg, orderThreeClass_one] using hn.symm⟩
  exact hle x.property

/-- The actual additive character on the ambient integer root lattice. -/
noncomputable def rootLatticeCharacter
    (degree : (H → K) →+ A) (c : A) (hc : addOrderOf c = 3)
    (hsupport : ∀ α : H → K, rootSpace H α ≠ ⊥ →
      degree α = 0 ∨ degree α = c ∨ degree α = -c) : rootLattice H →+ ZMod 3 :=
  (AddMonoidHom.ofInjective (orderThreeClass_injective c hc)).symm.toAddMonoidHom.comp
    ((degree.comp (rootLattice H).subtype).codRestrict (orderThreeClass c hc).range
      (root_lattice_degree_mem_cyclic_range H degree c hc hsupport))

/-- Composing the character with the cyclic embedding recovers the actual
root-lattice quotient degree. -/
theorem root_lattice_character_evaluation
    (degree : (H → K) →+ A) (c : A) (hc : addOrderOf c = 3)
    (hsupport : ∀ α : H → K, rootSpace H α ≠ ⊥ →
      degree α = 0 ∨ degree α = c ∨ degree α = -c)
    (x : rootLattice H) :
    orderThreeClass c hc (rootLatticeCharacter H degree c hc hsupport x) = degree x := by
  exact AddMonoidHom.apply_ofInjective_symm (orderThreeClass_injective c hc) _

/-- Character values and the original quotient degree carry exactly the same
information on the integer root lattice. -/
theorem root_lattice_character_eq_iff
    (degree : (H → K) →+ A) (c : A) (hc : addOrderOf c = 3)
    (hsupport : ∀ α : H → K, rootSpace H α ≠ ⊥ →
      degree α = 0 ∨ degree α = c ∨ degree α = -c)
    (x : rootLattice H) (i : ZMod 3) :
    rootLatticeCharacter H degree c hc hsupport x = i ↔
      degree x = orderThreeClass c hc i := by
  rw [← root_lattice_character_evaluation H degree c hc hsupport x]
  exact (orderThreeClass_injective c hc).eq_iff.symm

/-- Root-space components determined by a character of the actual root lattice.
The zero weight is included, so grade zero contains the Cartan itself. -/
noncomputable def rootCharacterGrade (character : rootLattice H →+ ZMod 3)
    (i : ZMod 3) : Submodule K L :=
  ⨆ α : Weight K H L,
    ⨆ (_ : character ⟨α, root_mem_rootLattice H α.genWeightSpace_ne_bot⟩ = i),
      (rootSpace H α).toSubmodule

/-- The root-lattice character produces exactly the original geometric grades. -/
theorem root_character_grade_eq
    (degree : (H → K) →+ A) (c : A) (hc : addOrderOf c = 3)
    (hsupport : ∀ α : H → K, rootSpace H α ≠ ⊥ →
      degree α = 0 ∨ degree α = c ∨ degree α = -c) (i : ZMod 3) :
    rootCharacterGrade H (rootLatticeCharacter H degree c hc hsupport) i =
      orderThreeGrade H degree c hc i := by
  apply le_antisymm
  · refine iSup_le fun α => iSup_le fun hα => ?_
    have heq := (root_lattice_character_eq_iff H degree c hc hsupport
      ⟨α, root_mem_rootLattice H α.genWeightSpace_ne_bot⟩ i).mp hα
    simpa only [orderThreeGrade, heq] using genWeightSpace_le_weightGrade H (M := L) degree α
  · unfold orderThreeGrade weightGrade
    refine iSup_le fun α => iSup_le fun hα => ?_
    by_cases hαne : rootSpace H α = ⊥
    · simp only [hαne, LieSubmodule.bot_toSubmodule, bot_le]
    let a : Weight K H L := ⟨α, hαne⟩
    have ha : rootLatticeCharacter H degree c hc hsupport
        ⟨a, root_mem_rootLattice H a.genWeightSpace_ne_bot⟩ = i :=
      (root_lattice_character_eq_iff H degree c hc hsupport _ i).mpr hα
    exact le_iSup_of_le a (le_iSup_of_le ha le_rfl)

/-- Properness of the zero algebra makes the constructed character nonzero. -/
theorem root_lattice_character_ne_zero [FiniteDimensional K L]
    [IsTriangularizable K H L]
    (degree : (H → K) →+ A) (c : A) (hc : addOrderOf c = 3)
    (hsupport : ∀ α : H → K, rootSpace H α ≠ ⊥ →
      degree α = 0 ∨ degree α = c ∨ degree α = -c)
    (hproper : weightGrade H L degree 0 ≠ ⊤) :
    rootLatticeCharacter H degree c hc hsupport ≠ 0 := by
  intro hzero
  apply hproper
  apply weightGrade_zero_eq_top H degree
  intro α hα
  have h := root_lattice_character_evaluation H degree c hc hsupport
    ⟨α, root_mem_rootLattice H hα⟩
  simpa only [hzero, AddMonoidHom.zero_apply, map_zero] using h.symm

section Coordinates

variable {ι : Type*}

/-- Arbitrary values on an actual integer basis extend to a root-lattice character. -/
noncomputable def characterOfBasisValues (b : Module.Basis ι ℤ (rootLattice H))
    (values : ι → ZMod 3) : rootLattice H →+ ZMod 3 :=
  (b.constr ℤ values).toAddMonoidHom

/-- The constructed character has exactly the assigned basis values. -/
theorem character_of_basis_values_apply (b : Module.Basis ι ℤ (rootLattice H))
    (values : ι → ZMod 3) (i : ι) : characterOfBasisValues H b values (b i) = values i := by
  simp [characterOfBasisValues]

/-- Every character is precisely the dot product of its basis values with
the actual integer root coordinates, reduced modulo three. -/
theorem root_character_basis_formula [Fintype ι]
    (b : Module.Basis ι ℤ (rootLattice H)) (character : rootLattice H →+ ZMod 3)
    (x : rootLattice H) :
    character x = ∑ i, (b.repr x i : ZMod 3) * character (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_zsmul, zsmul_eq_mul]

/-- Agreement on an actual integer root-lattice basis determines a character. -/
theorem root_character_eq_of_basis_values
    (b : Module.Basis ι ℤ (rootLattice H)) (f g : rootLattice H →+ ZMod 3)
    (hfg : ∀ i, f (b i) = g (b i)) : f = g := by
  have hlin : f.toIntLinearMap = g.toIntLinearMap := b.ext hfg
  exact DFunLike.ext _ _ (fun x => congrArg (fun t : rootLattice H →ₗ[ℤ] ZMod 3 => t x) hlin)

/-- Basis assignments parametrize all actual root-lattice characters exactly. -/
noncomputable def rootCharacterBasisEquiv (b : Module.Basis ι ℤ (rootLattice H)) :
    (rootLattice H →+ ZMod 3) ≃ (ι → ZMod 3) where
  toFun character i := character (b i)
  invFun := characterOfBasisValues H b
  left_inv _character := root_character_eq_of_basis_values H b _ _
    (fun i => character_of_basis_values_apply H b _ i)
  right_inv values := funext (character_of_basis_values_apply H b values)

/-- The nontrivial toral characters are exactly the nonzero basis assignments. -/
theorem root_character_ne_zero_iff_basis_value
    (b : Module.Basis ι ℤ (rootLattice H)) (character : rootLattice H →+ ZMod 3) :
    character ≠ 0 ↔ ∃ i, character (b i) ≠ 0 := by
  constructor
  · intro hne
    by_contra h
    push_neg at h
    exact hne (root_character_eq_of_basis_values H b character 0 h)
  · rintro ⟨i, hi⟩ hzero
    exact hi (by simp only [hzero, AddMonoidHom.zero_apply])

/-- A rank-`r` actual root lattice has exactly `3^r` characters to `ZMod 3`. -/
theorem card_root_lattice_characters [Fintype ι]
    (b : Module.Basis ι ℤ (rootLattice H)) :
    Nat.card (rootLattice H →+ ZMod 3) = 3 ^ Fintype.card ι := by
  classical
  rw [Nat.card_congr (rootCharacterBasisEquiv H b), Nat.card_eq_fintype_card,
    Fintype.card_fun, ZMod.card]

end Coordinates

section CompactPair

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.Complexification
open CubicAnomaly.Classification.CompactGeometry
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Classification.HermitianRealization
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

/-- The original compact-pair hypotheses and an actual common Cartan produce
a nonzero character on the actual integer root lattice.  Its root-space grades
are exactly the isotropy and the two actual complex halves.

This is the intrinsic toral-character input to a finite root-coordinate
census.  No root-coordinate identification or finite candidate is an input.
-/
theorem compact_common_cartan_root_character
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g)) [H.IsCartanSubalgebra]
    (hH : H ≤ complexifiedSubalgebra h) :
    let q := orthogonalComplement B h
    let J := commutantComplexStructure e
    ∃ character : rootLattice H →+ ZMod 3,
      character ≠ 0 ∧
      DirectSum.IsInternal (rootCharacterGrade H character) ∧
      rootCharacterGrade H character 0 = h.toSubmodule.baseChange ℂ ∧
      rootCharacterGrade H character 1 =
        (ambientComplexifiedHalf q J Complex.I).toSubmodule ∧
      rootCharacterGrade H character (-1) =
        (ambientComplexifiedHalf q J (-Complex.I)).toSubmodule ∧
      ∀ (i j : ZMod 3) (x y : ℂ ⊗[ℝ] g),
        x ∈ rootCharacterGrade H character i →
        y ∈ rootCharacterGrade H character j →
        ⁅x, y⁆ ∈ rootCharacterGrade H character (i + j) := by
  let q := orthogonalComplement B h
  let J := commutantComplexStructure e
  let P := ambientComplexifiedHalf q J Complex.I
  let Q := ambientComplexifiedHalf q J (-Complex.I)
  let degree := QuotientAddGroup.mk'
    (AddSubgroup.closure (containedRoots H (h.toSubmodule.baseChange ℂ)))
  obtain ⟨c, horder, hInternal, hzero, hpos, hneg, hbracket⟩ :=
    EqualRank.compact_common_cartan_cyclic_grading B h heff hproper e hradical H hH
  have hPQ : P.toSubmodule ⊔ Q.toSubmodule = q.toSubmodule.baseChange ℂ :=
    congrArg LieSubmodule.toSubmodule
      (ambient_complex_halves_sup q J (commutant_complex_structure_square e))
  have hspan : h.toSubmodule.baseChange ℂ ⊔ (P.toSubmodule ⊔ Q.toSubmodule) = ⊤ := by
    rw [hPQ]
    exact (compact_pair_complexification_isCompl B h).sup_eq_top
  have hS : h.toSubmodule.baseChange ℂ ≤ weightGrade H (ℂ ⊗[ℝ] g) degree 0 := by
    simpa only [orderThreeGrade, map_zero] using hzero.ge
  have hP : P.toSubmodule ≤ weightGrade H (ℂ ⊗[ℝ] g) degree c := by
    simpa only [orderThreeGrade, orderThreeClass_one] using hpos.ge
  have hQ : Q.toSubmodule ≤ weightGrade H (ℂ ⊗[ℝ] g) degree (-c) := by
    simpa only [orderThreeGrade, map_neg, orderThreeClass_one] using hneg.ge
  have hsupport := EqualRank.three_class_support_of_homogeneous_span H degree c
    (h.toSubmodule.baseChange ℂ) P.toSubmodule Q.toSubmodule hspan hS hP hQ
  have hgradeproper : weightGrade H (ℂ ⊗[ℝ] g) degree 0 ≠ ⊤ := by
    intro htop
    have hz : weightGrade H (ℂ ⊗[ℝ] g) degree 0 = h.toSubmodule.baseChange ℂ := by
      simpa only [orderThreeGrade, map_zero] using hzero
    have hbase : h.toSubmodule.baseChange ℂ = ⊤ := hz.symm.trans htop
    apply hproper
    apply top_unique
    intro x _
    apply (complexification_real_mem_baseChange_iff g h.toSubmodule x).mp
    rw [hbase]
    trivial
  let character := rootLatticeCharacter H degree c horder hsupport
  have hgrades : rootCharacterGrade H character = orderThreeGrade H degree c horder := by
    funext i
    exact root_character_grade_eq H degree c horder hsupport i
  refine ⟨character, root_lattice_character_ne_zero H degree c horder hsupport hgradeproper,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgrades]
    exact hInternal
  · rw [hgrades]
    exact hzero
  · rw [hgrades]
    exact hpos
  · rw [hgrades]
    exact hneg
  · rw [hgrades]
    exact hbracket

end CompactPair

end CubicAnomaly.Classification.ToralCharacter
