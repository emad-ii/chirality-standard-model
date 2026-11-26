import CubicAnomaly.Classification.RootClassificationOrbit
import CubicAnomaly.Fixed.E8Base
import CubicAnomaly.Fixed.E8RadicalIdentificationData

/-!
# Root components and joint weights of the equal-rank survivor

Transport to the numbered E8 roots preserves the Cartan pairings and
normalizes the surviving character by an actual Weyl word. Thus the
zero-grade roots and the Dynkin labels of every grade-one root can be
read in a common simple system for E6 and A2.
-/

namespace CubicAnomaly.Classification.RootClassificationSubsystem

open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.RootClassificationExceptional
open CubicAnomaly.Classification.RootClassificationOrbit
open CubicAnomaly.Classification.RootCharacterCoordinates
open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.ToralCharacter
open CubicAnomaly.Classification.CommonCartan
open CubicAnomaly.Fixed
open CubicAnomaly.Fixed.E8GradingData
open CubicAnomaly.Fixed.E8BracketData
open LieAlgebra LieModule Module LieAlgebra.IsKilling

private noncomputable def fixedIndex : ↥(table e8Datum) ≃ E8RootPairing.Root := by
  let g (v : ↥(table e8Datum)) : E8RootPairing.Root :=
    ⟨v.val.get, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
  apply Equiv.ofBijective g
  constructor
  · intro x y h
    exact Subtype.ext (Vector.ext fun i hi => congrFun (congrArg Subtype.val h) ⟨i, hi⟩)
  · intro r
    obtain ⟨v, hv, hvr⟩ := Finset.mem_image.mp r.property
    exact ⟨⟨v,hv⟩, Subtype.ext hvr⟩

private theorem fixed_pair (x y : ↥(table e8Datum)) :
    E8RootPairing.rootPairing.pairing (fixedIndex x) (fixedIndex y) =
      (rootPair x.val y.val : ℂ) := E8RootPairing.rootPairing_pairing _ _

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  (b : (rootSystem H).Base) (s : Index e8Datum ≃ b.support)

private theorem root_pairing_chart (f : ↥(table e8Datum) ≃ H.root)
    (hf : ∀ v, (rootSystem H).root (f v) = realize b s v.val) (x y : ↥(table e8Datum)) :
    (rootSystem H).pairing (f x) (f y) = (rootPair x.val y.val : ℂ) := by
  let P := rootSystem H
  let Q := E8RootPairing.rootPairing
  let B := b.toWeightBasis.reindex s.symm
  let T := B.equivFun
  let g := f.symm.trans fixedIndex
  have hg (α : H.root) : T (P.root α) = Q.root (g α) := by
    obtain ⟨v, rfl⟩ := f.surjective α
    have hr : P.root (f v) = B.equivFun.symm (fun j => (v.val.get j : ℂ)) := by
      rw [show P.root (f v) = realize b s v.val from hf v]
      simp [B, realize, Basis.equivFun_symm_apply, Int.cast_smul_eq_zsmul, Vector.get]
    rw [hr]
    change B.equivFun (B.equivFun.symm _) = Q.root (fixedIndex (f.symm (f v)))
    rw [B.equivFun.apply_symm_apply, f.symm_apply_apply]
    rfl
  let E := RootPairing.Equiv.mk' P Q T g hg
  have Hmap := RootPairing.Hom.weight_coweight_transpose_apply P Q (Q.coroot (g (f y))) E.toHom
  have hz := congrArg (fun ℓ : Module.Dual ℂ (Module.Dual ℂ H) => ℓ (P.root (f x))) Hmap
  have hc := RootPairing.Hom.coroot_coweightMap_apply P Q (g (f y)) E.toHom
  change E.coweightMap (Q.coroot (g (f y))) = P.coroot (g.symm (g (f y))) at hc
  rw [g.symm_apply_apply] at hc
  change Q.toLinearMap (T (P.root (f x))) (Q.coroot (g (f y))) =
    P.toLinearMap (P.root (f x)) (E.coweightMap (Q.coroot (g (f y)))) at hz
  rw [hg, hc] at hz
  have gx (v : ↥(table e8Datum)) : g (f v) = fixedIndex v := by simp [g]
  rw [gx, gx] at hz
  exact hz.symm.trans (fixed_pair x y)

private theorem root_word_pair (w : List (Fin 8)) (x y : H.root) :
    (rootSystem H).pairing (rootWord H b s w x) (rootWord H b s w y) =
      (rootSystem H).pairing x y := by
  induction w generalizing x y with
  | nil => rfl
  | cons i w ih =>
    change (rootSystem H).pairing (rootWord H b s w _) (rootWord H b s w _) = _
    rw [ih, (rootSystem H).pairing_reflectionPerm]
    simp

/-- A single index equivalence identifies all grades of the actual
surviving character with the canonical E8 grades and preserves every
root-coroot pairing. -/
theorem normalized_survivor_root_chart
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j)
    (χ : rootLattice H →+ ZMod 3)
    (hc : (gradeTable e8Datum (simpleCharacterEquiv H b s χ) 0).card = 78) :
    ∃ f : ↥(table e8Datum) ≃ H.root,
      (∀ v w, (rootSystem H).pairing (f v) (f w) = (rootPair v.val w.val : ℂ)) ∧
      ∀ v k, ((f v).val : H → ℂ) ∈ containedRoots H (rootCharacterGrade H χ k) ↔
        (v.val.get (6 : Fin 8) : ZMod 3) = k := by
  let χ₀ := (simpleCharacterEquiv H b s).symm canonical
  obtain ⟨w, hw⟩ := e8_actual_character_weyl_word H b s h χ hc
  have he8 : Selection.IsExceptionalCensusDatum e8Datum := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨g, hg, hgrade⟩ := actual_exceptional_root_grade_equiv H b s he8 h
  let f := g.trans (rootWord H b s w).symm
  have hinv (v : ↥(table e8Datum)) : rootWord H b s w (f v) = g v := Equiv.apply_symm_apply _ _
  refine ⟨f, fun v t => ?_, fun v k => ?_⟩
  · rw [← root_word_pair H b s w (f v) (f t), hinv, hinv, root_pairing_chart H b s g hg]
  · have hc₀ := hgrade χ₀ v k
    rw [root_mem_character_grade_iff] at hc₀ ⊢
    rw [hw, AddMonoidHom.comp_apply]
    change χ₀ ((latticeWord H b s w) (rootLatticeElement H (f v))) = k ↔ _
    rw [lattice_word_on_root, hinv]
    rw [show (simpleCharacterEquiv H b s) χ₀ = canonical from Equiv.apply_symm_apply _ _] at hc₀
    simpa [canonical, Pi.single_apply, mul_ite] using hc₀

/-- Simple roots of the degree-zero subsystem. The two A2 roots are ordered
with the negative highest E8 root first. -/
def subsystemSimple : Fin 6 ⊕ Fin 2 → RootVector
  | .inl i => simpleVector (e6SimpleIndex i)
  | .inr j => if j = 0 then a2Second else a2First

private theorem simple_mem_table : ∀ i, subsystemSimple i ∈ table e8Datum := by native_decide

def subsystemIndex (i : Fin 6 ⊕ Fin 2) : ↥(table e8Datum) :=
  ⟨subsystemSimple i, simple_mem_table i⟩

/-- The integral Dynkin labels for E6 and A2 of a root in the common E8 Cartan. -/
def jointWeight (v : RootVector) : Vector ℤ 6 × Vector ℤ 2 :=
  (Vector.ofFn fun i => rootPair v (subsystemSimple (.inl i)),
   Vector.ofFn fun j => rootPair v (subsystemSimple (.inr j)))

def oneRoots := (table e8Datum).filter fun v => (v.get (6 : Fin 8) : ZMod 3) = 1

def localWeights : Finset (Vector ℤ 6) := oneRoots.image fun v => (jointWeight v).1

def familyWeights : Finset (Vector ℤ 2) := {#v[1,0], #v[-1,1], #v[0,-1]}

/-- The zero roots are precisely the independently generated E6 roots and the
six roots of A2. Their simple Cartan matrix is block diagonal. -/
theorem subsystem_root_certificate :
    (table e8Datum).filter (fun v => (v.get (6 : Fin 8) : ZMod 3) = 0) =
      (Finset.univ.image (fun i : Fin 72 => E8RadicalIdentificationData.includeRoot
        (E6Lattice.root i))) ∪ a2Roots ∧
    (∀ i j, rootPair (subsystemSimple i) (subsystemSimple j) =
      Matrix.fromBlocks CartanMatrix.E₆ 0 0 (CartanMatrix.A 2) i j) := by native_decide

/-- Every grade-one root has a different joint label. All 27 by 3 choices
occur, and the unique dominant E6 label is the first fundamental weight. -/
theorem subsystem_weight_certificate :
    oneRoots.image jointWeight = localWeights.product familyWeights ∧
    localWeights.card = 27 ∧
    (localWeights.filter (fun v => ∀ i, 0 ≤ v.get i)) = {#v[1,0,0,0,0,0]} ∧
    ∀ v ∈ oneRoots, ∀ w ∈ oneRoots, jointWeight v = jointWeight w → v = w := by
  have cert : oneRoots.image jointWeight = localWeights.product familyWeights ∧
      localWeights.card = 27 ∧
      (localWeights.filter (fun v => ∀ i, 0 ≤ v.get i)) = {#v[1,0,0,0,0,0]} ∧
      (oneRoots.image jointWeight).card = oneRoots.card := by native_decide
  exact ⟨cert.1, cert.2.1, cert.2.2.1,
    fun _ hv _ hw h => Finset.injOn_of_card_image_eq cert.2.2.2 hv hw h⟩

private theorem joint_fiber (l : Vector ℤ 6) (hl : l ∈ localWeights)
    (p : Vector ℤ 2) (hp : p ∈ familyWeights) :
    ∃! v : ↥(table e8Datum), (v.val.get (6 : Fin 8) : ZMod 3) = 1 ∧ jointWeight v.val = (l,p) := by
  have hz : (l,p) ∈ oneRoots.image jointWeight := by
    rw [subsystem_weight_certificate.1]
    exact Finset.mem_product.mpr ⟨hl,hp⟩
  obtain ⟨v,hv,hvp⟩ := Finset.mem_image.mp hz
  obtain ⟨hv',hg⟩ := Finset.mem_filter.mp hv
  refine ⟨⟨v,hv'⟩, ⟨hg,hvp⟩, ?_⟩
  intro w hw
  exact Subtype.ext (subsystem_weight_certificate.2.2.2 _ (Finset.mem_filter.mpr ⟨w.property,hw.1⟩)
    _ hv (hw.2.trans hvp.symm))

/-- For the actual survivor choose zero-grade coroot labels with E6 + A2 Cartan
matrix. For each of the 27 local and three family weights there is exactly
one grade-one root with those actual Cartan eigenvalues. -/
theorem survivor_cartan_and_joint_weights
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j)
    (χ : rootLattice H →+ ZMod 3)
    (hc : (gradeTable e8Datum (simpleCharacterEquiv H b s χ) 0).card = 78) :
    ∃ z : Fin 6 ⊕ Fin 2 → H.root,
      (∀ i, ((z i).val : H → ℂ) ∈ containedRoots H (rootCharacterGrade H χ 0)) ∧
      (∀ i j, (rootSystem H).pairing (z i) (z j) =
        (Matrix.fromBlocks CartanMatrix.E₆ 0 0 (CartanMatrix.A 2) i j : ℤ)) ∧
      ∀ l ∈ localWeights, ∀ p ∈ familyWeights, ∃! α : H.root,
        (α.val : H → ℂ) ∈ containedRoots H (rootCharacterGrade H χ 1) ∧
        (∀ i, (rootSystem H).pairing α (z (.inl i)) = (l.get i : ℂ)) ∧
        ∀ j, (rootSystem H).pairing α (z (.inr j)) = (p.get j : ℂ) := by
  obtain ⟨f, hpair, hg⟩ := normalized_survivor_root_chart H b s h χ hc
  refine ⟨fun i => f (subsystemIndex i), ?_, ?_, ?_⟩
  · have hz : ∀ i, ((subsystemSimple i).get 6 : ZMod 3) = 0 := by native_decide
    exact fun i => (hg _ _).mpr (hz i)
  · exact fun i j => (hpair _ _).trans (congrArg (fun n : ℤ => (n : ℂ))
      (subsystem_root_certificate.2 i j))
  · intro l hl p hp
    obtain ⟨v,hv,huniq⟩ := joint_fiber l hl p hp
    obtain ⟨hdeg, hwt⟩ := hv
    refine ⟨f v, ⟨(hg v 1).mpr hdeg, fun i => ?_, fun j => ?_⟩, ?_⟩
    · rw [hpair]
      simpa [jointWeight, Vector.get] using congrArg (fun w : Vector ℤ 6 × Vector ℤ 2 => (w.1.get i : ℂ)) hwt
    · rw [hpair]
      simpa [jointWeight, Vector.get] using congrArg (fun w : Vector ℤ 6 × Vector ℤ 2 => (w.2.get j : ℂ)) hwt
    · rintro α ⟨hdeg', hloc, hfam⟩
      obtain ⟨w, rfl⟩ := f.surjective α
      apply congrArg f
      apply huniq w
      refine ⟨(hg w 1).mp hdeg', Prod.ext ?_ ?_⟩
      · apply Vector.ext
        intro i hi
        have hh := (hpair w (subsystemIndex (.inl ⟨i,hi⟩))).symm.trans (hloc ⟨i,hi⟩)
        simp [jointWeight]
        exact_mod_cast hh
      · apply Vector.ext
        intro j hj
        have hh := (hpair w (subsystemIndex (.inr ⟨j,hj⟩))).symm.trans (hfam ⟨j,hj⟩)
        simp [jointWeight]
        exact_mod_cast hh

end CubicAnomaly.Classification.RootClassificationSubsystem
