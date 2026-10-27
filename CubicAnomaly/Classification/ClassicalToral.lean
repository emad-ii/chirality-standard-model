import CubicAnomaly.Classification.Classical
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-!
# Classical order-three gradings in every rank

Every root in the standard A/B/C/D coordinate realizations has one of the
shapes represented below.  Lifting coordinate grades in `ZMod 3` to
`{-1,0,1}` makes its pairing with every such root lie in `[-2,2]`.  A zero
grade therefore means an exactly zero integer pairing.  For a nontrivial
grading the zero-grade root span is a proper subspace of the ambient root
span.  This argument has no rank bound and needs no finite census.

The statements concern explicit root-coordinate systems.  Relating these
systems to compact Lie algebras and identifying a zero-grade span with the
semisimple rank of a toral centralizer are separate structural bridges.
-/

namespace CubicAnomaly.Classification.Classical

/-- Signed coordinate shapes containing every classical root. -/
inductive ClassicalRootShape (n : ℕ) where
  | single (i : Fin n) (positive : Bool)
  | double (i : Fin n) (positive : Bool)
  | pair (i j : Fin n) (distinct : i ≠ j) (positiveI positiveJ : Bool)

private def rootSign (positive : Bool) : ℤ := if positive then 1 else -1

/-- Evaluation of a root on coordinate values over any ring. -/
def ClassicalRootShape.evaluate {n : ℕ} {R : Type*} [Ring R]
    (root : ClassicalRootShape n) (x : Fin n → R) : R :=
  match root with
  | .single i s => (rootSign s : R) * x i
  | .double i s => 2 * (rootSign s : R) * x i
  | .pair i j _ s t => (rootSign s : R) * x i + (rootSign t : R) * x j

/-- The coordinate vector of a signed classical root. -/
def ClassicalRootShape.vector {n : ℕ} {R : Type*} [Ring R]
    (root : ClassicalRootShape n) : Fin n → R :=
  fun j => root.evaluate (fun i => if j = i then 1 else 0)

/-- The canonical representative `-1`, `0` or `1` of a residue modulo three. -/
def ternaryLift (x : ZMod 3) : ℤ := if x = 0 then 0 else if x = 1 then 1 else -1

private theorem ternaryLift_cast (x : ZMod 3) : (ternaryLift x : ZMod 3) = x := by
  fin_cases x <;> decide

private theorem ternaryLift_bounds (x : ZMod 3) : -1 ≤ ternaryLift x ∧ ternaryLift x ≤ 1 := by
  unfold ternaryLift
  split_ifs <;> norm_num

private theorem root_evaluate_cast {n : ℕ} (root : ClassicalRootShape n) (x : Fin n → ℤ) :
    ((root.evaluate x : ℤ) : ZMod 3) = root.evaluate (fun i => (x i : ZMod 3)) := by
  cases root <;> simp [ClassicalRootShape.evaluate, Int.cast_add, Int.cast_mul]

/-- Every classical root has lifted pairing between minus two and two. -/
theorem classical_root_ternary_bounds {n : ℕ} (a : Fin n → ZMod 3)
    (root : ClassicalRootShape n) :
    -2 ≤ root.evaluate (fun i => ternaryLift (a i)) ∧
      root.evaluate (fun i => ternaryLift (a i)) ≤ 2 := by
  cases root with
  | single i s =>
    have hi := ternaryLift_bounds (a i)
    cases s <;> simp [ClassicalRootShape.evaluate, rootSign] <;> omega
  | double i s =>
    have hi := ternaryLift_bounds (a i)
    cases s <;> simp [ClassicalRootShape.evaluate, rootSign] <;> omega
  | pair i j _ s t =>
    have hi := ternaryLift_bounds (a i)
    have hj := ternaryLift_bounds (a j)
    cases s <;> cases t <;> simp [ClassicalRootShape.evaluate, rootSign] <;> omega

/-- A zero grade is an actual zero lifted pairing, uniformly in rank. -/
theorem classical_zero_grade_lift_zero {n : ℕ} (a : Fin n → ZMod 3)
    (root : ClassicalRootShape n) (hgrade : root.evaluate a = 0) :
    root.evaluate (fun i => ternaryLift (a i)) = 0 := by
  have hcast : ((root.evaluate (fun i => ternaryLift (a i)) : ℤ) : ZMod 3) = 0 := by
    rw [root_evaluate_cast]
    simpa only [ternaryLift_cast] using hgrade
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hcast
  have hb := classical_root_ternary_bounds a root
  norm_num at hk
  omega

/-- The rational linear functional determined by the ternary coordinate lifts. -/
def ternaryLiftFunctional {n : ℕ} (a : Fin n → ZMod 3) : (Fin n → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ j : Fin n, (ternaryLift (a j) : ℚ) * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem ternaryLiftFunctional_root {n : ℕ} (a : Fin n → ZMod 3)
    (root : ClassicalRootShape n) :
    ternaryLiftFunctional a (root.vector (R := ℚ)) =
      (root.evaluate (fun i => ternaryLift (a i)) : ℤ) := by
  cases root <;>
    simp [ternaryLiftFunctional, ClassicalRootShape.vector, ClassicalRootShape.evaluate,
      mul_ite, mul_add, Finset.sum_add_distrib] <;> ring

/-- The rational span of an arbitrary collection of classical coordinate roots. -/
def classicalRootSpan {n : ℕ} (roots : Set (ClassicalRootShape n)) :
    Submodule ℚ (Fin n → ℚ) :=
  Submodule.span ℚ (ClassicalRootShape.vector (R := ℚ) '' roots)

/-- The roots of grade zero in a given collection. -/
def classicalZeroGradeRoots {n : ℕ} (roots : Set (ClassicalRootShape n))
    (a : Fin n → ZMod 3) : Set (ClassicalRootShape n) :=
  {root | root ∈ roots ∧ root.evaluate a = 0}

/-- All zero-grade roots lie in the kernel of one common rational functional. -/
theorem classical_zero_grade_span_le_ker {n : ℕ} (roots : Set (ClassicalRootShape n))
    (a : Fin n → ZMod 3) :
    classicalRootSpan (classicalZeroGradeRoots roots a) ≤ (ternaryLiftFunctional a).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨root, ⟨_, hgrade⟩, rfl⟩
  change ternaryLiftFunctional a (root.vector (R := ℚ)) = 0
  rw [ternaryLiftFunctional_root, classical_zero_grade_lift_zero a root hgrade]
  norm_num

/-- A nontrivial classical order-three grading strictly decreases the
zero-grade root span, for every natural rank. -/
theorem classical_order_three_span_drop {n : ℕ} (roots : Set (ClassicalRootShape n))
    (a : Fin n → ZMod 3) (hnontrivial : ∃ root ∈ roots, root.evaluate a ≠ 0) :
    classicalRootSpan (classicalZeroGradeRoots roots a) < classicalRootSpan roots := by
  have hle : classicalRootSpan (classicalZeroGradeRoots roots a) ≤ classicalRootSpan roots := by
    apply Submodule.span_mono
    rintro _ ⟨root, ⟨hroot, _⟩, rfl⟩
    exact ⟨root, hroot, rfl⟩
  apply lt_of_le_not_ge hle
  intro hreverse
  obtain ⟨root, hroot, hgrade⟩ := hnontrivial
  have hm : root.vector (R := ℚ) ∈ classicalRootSpan roots :=
    Submodule.subset_span ⟨root, hroot, rfl⟩
  have hk := classical_zero_grade_span_le_ker roots a (hreverse hm)
  change ternaryLiftFunctional a (root.vector (R := ℚ)) = 0 at hk
  rw [ternaryLiftFunctional_root] at hk
  have hz : root.evaluate (fun i => ternaryLift (a i)) = 0 := by exact_mod_cast hk
  have hc := congrArg (fun z : ℤ => (z : ZMod 3)) hz
  change ((root.evaluate (fun i => ternaryLift (a i)) : ℤ) : ZMod 3) = 0 at hc
  rw [root_evaluate_cast] at hc
  exact hgrade (by simpa only [ternaryLift_cast, Int.cast_zero] using hc)

/-- The zero-grade subsystem has strictly smaller rational rank. -/
theorem classical_order_three_rank_drop {n : ℕ} (roots : Set (ClassicalRootShape n))
    (a : Fin n → ZMod 3) (hnontrivial : ∃ root ∈ roots, root.evaluate a ≠ 0) :
    Module.finrank ℚ (classicalRootSpan (classicalZeroGradeRoots roots a)) <
      Module.finrank ℚ (classicalRootSpan roots) :=
  Submodule.finrank_lt_finrank_of_lt (classical_order_three_span_drop roots a hnontrivial)

/-- Twice a standard integral coordinate vector. -/
def doubledCoordinate {n : ℕ} (i : Fin n) : Fin n → ℤ :=
  fun j => if j = i then 2 else 0

/-- Integral lattices containing all `2e_i` have coordinate representatives
for every grading modulo three.  This is the root-lattice extension needed
for types C and D; division by two is multiplication by two in `ZMod 3`. -/
theorem lattice_order_three_coordinate_extension {n : ℕ}
    (L : Submodule ℤ (Fin n → ℤ))
    (hL : ∀ i : Fin n, doubledCoordinate i ∈ L)
    (f : L →ₗ[ℤ] ZMod 3) :
    ∃ a : Fin n → ZMod 3, ∀ x : L,
      f x = ∑ i : Fin n, (((x : Fin n → ℤ) i : ℤ) : ZMod 3) * a i := by
  let v : Fin n → L := fun i => ⟨doubledCoordinate i, hL i⟩
  refine ⟨fun i => 2 * f (v i), ?_⟩
  intro x
  have heq : (2 : ℤ) • x = ∑ i : Fin n, (x : Fin n → ℤ) i • v i := by
    apply Subtype.ext
    funext j
    simp [v, doubledCoordinate, Finset.sum_apply, mul_ite]
    ring
  have hf := congrArg f heq
  simp only [map_smul, map_sum, zsmul_eq_mul, Int.cast_ofNat] at hf
  have htwo : (2 : ZMod 3) * 2 = 1 := by decide
  calc
    f x = 2 * (2 * f x) := by rw [← mul_assoc, htwo, one_mul]
    _ = 2 * ∑ i : Fin n, (((x : Fin n → ℤ) i : ℤ) : ZMod 3) * f (v i) := by rw [hf]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem root_vector_cast {n : ℕ} (root : ClassicalRootShape n) (j : Fin n) :
    ((root.vector (R := ℤ) j : ℤ) : ZMod 3) = root.vector (R := ZMod 3) j := by
  simp only [ClassicalRootShape.vector, root_evaluate_cast]
  congr 1
  funext i
  split_ifs <;> norm_num

private theorem root_vector_dot {n : ℕ} {R : Type*} [CommRing R]
    (root : ClassicalRootShape n) (a : Fin n → R) :
    (∑ i : Fin n, root.vector (R := R) i * a i) = root.evaluate a := by
  cases root <;>
    simp [ClassicalRootShape.vector, ClassicalRootShape.evaluate, mul_ite,
      ite_mul, add_mul, Finset.sum_add_distrib]

/-- Every integral root-lattice grading is represented by coordinate grades
as soon as the lattice contains the doubled coordinate basis. -/
theorem root_lattice_order_three_coordinate_extension {n : ℕ}
    (L : Submodule ℤ (Fin n → ℤ))
    (hL : ∀ i : Fin n, doubledCoordinate i ∈ L)
    (f : L →ₗ[ℤ] ZMod 3) :
    ∃ a : Fin n → ZMod 3, ∀ (root : ClassicalRootShape n)
      (hroot : root.vector (R := ℤ) ∈ L), f ⟨root.vector, hroot⟩ = root.evaluate a := by
  obtain ⟨a, ha⟩ := lattice_order_three_coordinate_extension L hL f
  refine ⟨a, ?_⟩
  intro root hroot
  rw [ha]
  simp only [root_vector_cast]
  exact root_vector_dot root a

/-- The integer lattice generated by a collection of coordinate roots. -/
def classicalRootLattice {n : ℕ} (roots : Set (ClassicalRootShape n)) :
    Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (ClassicalRootShape.vector (R := ℤ) '' roots)

/-- The usual D-type roots `±e_i ±e_j`. -/
def typeDRootShapes (n : ℕ) : Set (ClassicalRootShape n) :=
  {root | match root with | .pair .. => True | _ => False}

/-- The usual C-type roots `±2e_i` and `±e_i ±e_j`. -/
def typeCRootShapes (n : ℕ) : Set (ClassicalRootShape n) :=
  {root | match root with | .single .. => False | _ => True}

/-- The C root lattice contains all doubled standard coordinates. -/
theorem typeC_root_lattice_contains_doubled {n : ℕ} (i : Fin n) :
    doubledCoordinate i ∈ classicalRootLattice (typeCRootShapes n) := by
  have heq : doubledCoordinate i =
      (ClassicalRootShape.double i true).vector (R := ℤ) := by
    funext j
    simp [doubledCoordinate, ClassicalRootShape.vector, ClassicalRootShape.evaluate,
      rootSign, mul_ite]
  rw [heq]
  exact Submodule.subset_span ⟨.double i true, trivial, rfl⟩

/-- The D root lattice also contains all doubled coordinates: add
`e_i+e_j` and `e_i-e_j`, choosing any `j ≠ i`. -/
theorem typeD_root_lattice_contains_doubled (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    doubledCoordinate i ∈ classicalRootLattice (typeDRootShapes n) := by
  have hex : ∃ j : Fin n, i ≠ j := by
    by_cases hi : i.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have hv := congrArg Fin.val h
      change i.val = 1 at hv
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      exact hi (congrArg Fin.val h)
  obtain ⟨j, hij⟩ := hex
  have heq : doubledCoordinate i =
      (ClassicalRootShape.pair i j hij true true).vector (R := ℤ) +
        (ClassicalRootShape.pair i j hij true false).vector (R := ℤ) := by
    funext k
    simp [doubledCoordinate, ClassicalRootShape.vector, ClassicalRootShape.evaluate,
      rootSign]
    split_ifs <;> ring
  rw [heq]
  exact Submodule.add_mem _
    (Submodule.subset_span ⟨.pair i j hij true true, trivial, rfl⟩)
    (Submodule.subset_span ⟨.pair i j hij true false, trivial, rfl⟩)

/-- The usual B-type roots `±e_i` and `±e_i ±e_j`. -/
def typeBRootShapes (n : ℕ) : Set (ClassicalRootShape n) :=
  {root | match root with | .double .. => False | _ => True}

/-- The usual A-type roots `e_i-e_j`, including both signs. -/
def typeARootShapes (n : ℕ) : Set (ClassicalRootShape n) :=
  {root | match root with | .pair _ _ _ s t => s ≠ t | _ => False}

/-- The B root lattice contains all doubled coordinate vectors. -/
theorem typeB_root_lattice_contains_doubled {n : ℕ} (i : Fin n) :
    doubledCoordinate i ∈ classicalRootLattice (typeBRootShapes n) := by
  have heq : doubledCoordinate i =
      (2 : ℤ) • (ClassicalRootShape.single i true).vector (R := ℤ) := by
    funext j
    simp [doubledCoordinate, ClassicalRootShape.vector, ClassicalRootShape.evaluate,
      rootSign, mul_ite]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.single i true, trivial, rfl⟩)

/-- Zero-grade roots for a grading defined on the root lattice itself. -/
def classicalLatticeZeroRoots {n : ℕ} (roots : Set (ClassicalRootShape n))
    (f : classicalRootLattice roots →ₗ[ℤ] ZMod 3) : Set (ClassicalRootShape n) :=
  {root | ∃ hroot : root ∈ roots,
    f ⟨root.vector, Submodule.subset_span ⟨root, hroot, rfl⟩⟩ = 0}

private theorem root_lattice_nontrivial_generator {n : ℕ}
    (roots : Set (ClassicalRootShape n))
    (f : classicalRootLattice roots →ₗ[ℤ] ZMod 3) (hf : f ≠ 0) :
    ∃ (root : ClassicalRootShape n) (hroot : root ∈ roots),
      f ⟨root.vector, Submodule.subset_span ⟨root, hroot, rfl⟩⟩ ≠ 0 := by
  by_contra! h
  apply hf
  apply (Submodule.linearMap_eq_iff_of_eq_span f 0 rfl).2
  rintro ⟨_, ⟨root, hroot, rfl⟩⟩
  exact h root hroot

private theorem lattice_rank_drop_of_coordinate_extension {n : ℕ}
    (roots : Set (ClassicalRootShape n))
    (f : classicalRootLattice roots →ₗ[ℤ] ZMod 3) (hf : f ≠ 0)
    (hcoord : ∃ a : Fin n → ZMod 3, ∀ (root : ClassicalRootShape n)
      (hm : root.vector (R := ℤ) ∈ classicalRootLattice roots),
        f ⟨root.vector, hm⟩ = root.evaluate a) :
    Module.finrank ℚ (classicalRootSpan (classicalLatticeZeroRoots roots f)) <
      Module.finrank ℚ (classicalRootSpan roots) := by
  obtain ⟨a, ha⟩ := hcoord
  have hset : classicalLatticeZeroRoots roots f = classicalZeroGradeRoots roots a := by
    ext root
    constructor
    · rintro ⟨hroot, hzero⟩
      refine ⟨hroot, ?_⟩
      rw [ha] at hzero
      exact hzero
    · rintro ⟨hroot, hzero⟩
      refine ⟨hroot, ?_⟩
      rw [ha]
      exact hzero
  rw [hset]
  apply classical_order_three_rank_drop
  obtain ⟨root, hroot, hne⟩ := root_lattice_nontrivial_generator roots f hf
  refine ⟨root, hroot, ?_⟩
  rwa [ha] at hne

/-- A direct rank-drop theorem for any nonzero grading of a root lattice
containing the doubled coordinate basis. -/
theorem classical_lattice_order_three_rank_drop {n : ℕ}
    (roots : Set (ClassicalRootShape n))
    (hdouble : ∀ i : Fin n, doubledCoordinate i ∈ classicalRootLattice roots)
    (f : classicalRootLattice roots →ₗ[ℤ] ZMod 3) (hf : f ≠ 0) :
    Module.finrank ℚ (classicalRootSpan (classicalLatticeZeroRoots roots f)) <
      Module.finrank ℚ (classicalRootSpan roots) :=
  lattice_rank_drop_of_coordinate_extension roots f hf
    (root_lattice_order_three_coordinate_extension _ hdouble f)

/-- Every nontrivial order-three B root-lattice grading drops rank. -/
theorem typeB_order_three_rank_drop (n : ℕ)
    (f : classicalRootLattice (typeBRootShapes n) →ₗ[ℤ] ZMod 3) (hf : f ≠ 0) :
    Module.finrank ℚ (classicalRootSpan (classicalLatticeZeroRoots (typeBRootShapes n) f)) <
      Module.finrank ℚ (classicalRootSpan (typeBRootShapes n)) :=
  classical_lattice_order_three_rank_drop _ typeB_root_lattice_contains_doubled f hf

/-- Every nontrivial order-three C root-lattice grading drops rank. -/
theorem typeC_order_three_rank_drop (n : ℕ)
    (f : classicalRootLattice (typeCRootShapes n) →ₗ[ℤ] ZMod 3) (hf : f ≠ 0) :
    Module.finrank ℚ (classicalRootSpan (classicalLatticeZeroRoots (typeCRootShapes n) f)) <
      Module.finrank ℚ (classicalRootSpan (typeCRootShapes n)) :=
  classical_lattice_order_three_rank_drop _ typeC_root_lattice_contains_doubled f hf

/-- Every nontrivial order-three D root-lattice grading drops rank. -/
theorem typeD_order_three_rank_drop (n : ℕ) (hn : 2 ≤ n)
    (f : classicalRootLattice (typeDRootShapes n) →ₗ[ℤ] ZMod 3) (hf : f ≠ 0) :
    Module.finrank ℚ (classicalRootSpan (classicalLatticeZeroRoots (typeDRootShapes n) f)) <
      Module.finrank ℚ (classicalRootSpan (typeDRootShapes n)) :=
  classical_lattice_order_three_rank_drop _ (typeD_root_lattice_contains_doubled n hn) f hf

/-- A standard integral coordinate difference. -/
def differenceCoordinate {n : ℕ} (i p : Fin n) : Fin n → ℤ :=
  fun j => (if j = i then 1 else 0) - (if j = p then 1 else 0)

/-- The sum of integral coordinates, whose kernel contains the A root lattice. -/
def integerCoordinateSum (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ∑ j : Fin n, x j
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- Every A root has coordinate sum zero, as does its entire root lattice. -/
theorem typeA_root_lattice_sum_zero (n : ℕ) :
    classicalRootLattice (typeARootShapes n) ≤ (integerCoordinateSum n).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨root, hroot, rfl⟩
  change (∑ j : Fin n, root.vector (R := ℤ) j) = 0
  cases root with
  | single i s => exact False.elim hroot
  | double i s => exact False.elim hroot
  | pair i j _ s t =>
    cases s <;> cases t <;>
      simp_all [typeARootShapes, ClassicalRootShape.vector, ClassicalRootShape.evaluate,
        rootSign, Finset.sum_add_distrib]

/-- All coordinate differences belong to the A root lattice. -/
theorem typeA_root_lattice_contains_difference {n : ℕ} (i p : Fin n) :
    differenceCoordinate i p ∈ classicalRootLattice (typeARootShapes n) := by
  by_cases hip : i = p
  · subst i
    have hz : differenceCoordinate p p = 0 := by
      funext j
      exact sub_self _
    rw [hz]
    exact Submodule.zero_mem _
  · have heq : differenceCoordinate i p =
        (ClassicalRootShape.pair i p hip true false).vector (R := ℤ) := by
      funext j
      by_cases hjp : j = p <;>
        simp [differenceCoordinate, ClassicalRootShape.vector, ClassicalRootShape.evaluate,
          rootSign, sub_eq_add_neg, hjp]
    rw [heq]
    exact Submodule.subset_span ⟨.pair i p hip true false, by change true ≠ false; decide, rfl⟩

/-- Root-lattice coordinate extension for the sum-zero lattice, using the
basis `e_i-e_p` instead of doubled coordinates. -/
theorem sum_zero_lattice_coordinate_extension {n : ℕ} (p : Fin n)
    (L : Submodule ℤ (Fin n → ℤ))
    (hsum : L ≤ (integerCoordinateSum n).ker)
    (hdiff : ∀ i : Fin n, differenceCoordinate i p ∈ L)
    (f : L →ₗ[ℤ] ZMod 3) :
    ∃ a : Fin n → ZMod 3, ∀ x : L,
      f x = ∑ i : Fin n, (((x : Fin n → ℤ) i : ℤ) : ZMod 3) * a i := by
  let v : Fin n → L := fun i => ⟨differenceCoordinate i p, hdiff i⟩
  refine ⟨fun i => f (v i), ?_⟩
  intro x
  have hxsum : (∑ i : Fin n, (x : Fin n → ℤ) i) = 0 := hsum x.property
  have heq : x = ∑ i : Fin n, (x : Fin n → ℤ) i • v i := by
    apply Subtype.ext
    funext j
    simp [v, differenceCoordinate, Finset.sum_apply, mul_sub, mul_ite,
      Finset.sum_sub_distrib, hxsum]
  have hf := congrArg f heq
  simpa only [map_sum, map_smul, zsmul_eq_mul] using hf

/-- Every nontrivial order-three A root-lattice grading drops rank.  The
coordinate realization has `n` coordinates, so its root system is `A_(n-1)`. -/
theorem typeA_order_three_rank_drop (n : ℕ) (hn : 1 ≤ n)
    (f : classicalRootLattice (typeARootShapes n) →ₗ[ℤ] ZMod 3) (hf : f ≠ 0) :
    Module.finrank ℚ (classicalRootSpan (classicalLatticeZeroRoots (typeARootShapes n) f)) <
      Module.finrank ℚ (classicalRootSpan (typeARootShapes n)) := by
  apply lattice_rank_drop_of_coordinate_extension _ f hf
  let p : Fin n := ⟨0, by omega⟩
  obtain ⟨a, ha⟩ := sum_zero_lattice_coordinate_extension p
    (classicalRootLattice (typeARootShapes n)) (typeA_root_lattice_sum_zero n)
    (fun i => typeA_root_lattice_contains_difference i p) f
  refine ⟨a, ?_⟩
  intro root hroot
  rw [ha]
  simp only [root_vector_cast]
  exact root_vector_dot root a

end CubicAnomaly.Classification.Classical
