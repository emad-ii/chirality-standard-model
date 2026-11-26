import CubicAnomaly.Classification.RootClassificationGrades
import Std.Data.HashMap.Basic

/-!
# The Weyl orbit of the selected E₈ character

A simple reflection acts on the eight simple-root character values by the
transpose of its integral root-coordinate action. A bounded breadth-first
search from the seventh coordinate constructs words in these reflections.
The certificate checks the word itself on every assignment whose zero
root set has the selected cardinality. Its soundness requires no
assumption about completeness of the search.
-/

namespace CubicAnomaly.Classification.RootClassificationOrbit

open CubicAnomaly.Classification.Exceptional
open CubicAnomaly.Classification.RootClassificationExceptional

open CubicAnomaly.Classification.RootGrading
open CubicAnomaly.Classification.RootCharacterCoordinates
open CubicAnomaly.Classification.RootLatticeBasis
open LieAlgebra LieModule Module LieAlgebra.IsKilling

abbrev Assignment := Fin 8 → ZMod 3

/-- The character used by the constructed exceptional three-grading. -/
def canonical : Assignment := Pi.single 6 1

/-- Pullback of a character along the `i`-th simple reflection. -/
def reflect (i : Fin 8) (a : Assignment) : Assignment :=
  fun j => a j - (matrix e8Datum j i : ZMod 3) * a i

private abbrev Key := Vector (Fin 3) 8

private def key (a : Assignment) : Key := Vector.ofFn a

private def wordState : List (Fin 8) → Key → Key
  | [], a => a
  | i :: w, a => key (reflect i (wordState w a).get)

/-- Pullback along a word with its head reflection applied last to the
assignment. Each intermediate vector is materialized once. -/
def wordAction (w : List (Fin 8)) (a : Assignment) : Assignment :=
  (wordState w (key a)).get

private theorem wordAction_nil (a : Assignment) : wordAction [] a = a := by
  funext i
  simp [wordAction, wordState, key, Vector.get]

private theorem wordAction_cons (i : Fin 8) (w : List (Fin 8)) (a : Assignment) :
    wordAction (i :: w) a = reflect i (wordAction w a) := by
  funext j
  simp [wordAction, wordState, key, Vector.get]

private def encode (v : Key) : ℕ := v.toArray.foldl (fun a x => 3 * a + x.val) 0

private abbrev Paths := Std.HashMap ℕ (List (Fin 8))

private def search : Paths := Id.run do
  let seed := key canonical
  let mut paths : Paths := ({} : Paths).insert (encode seed) []
  let mut queue : Array Key := #[seed]
  let mut cursor := 0
  for _ in [:3 ^ 8] do
    if h : cursor < queue.size then
      let v := queue[cursor]
      let word := paths.getD (encode v) []
      cursor := cursor + 1
      for i in List.finRange 8 do
        let u := key (reflect i v.get)
        if !paths.contains (encode u) then
          paths := paths.insert (encode u) (i :: word)
          queue := queue.push u
    else
      break
  return paths

private def wordFor (paths : Paths) (a : Assignment) : List (Fin 8) :=
  paths.getD (encode (key a)) []

/-- Compute the grade cardinality against the precomputed census table.
The returned words are checked independently by reflection. -/
@[noinline] private def checked (paths : Paths) (roots : Finset (Vector ℤ 8)) : Bool :=
  decide (∀ a : Assignment,
    (roots.filter (fun v => ∑ i, (v.get i : ZMod 3) * a i = 0)).card = 78 →
      wordAction (wordFor paths a) canonical = a)

private theorem orbit_certificate : checked search (table e8Datum) = true := by native_decide

/-- Every assignment with the surviving zero-root count is Weyl-conjugate to
the actual grading coordinate, including its orientation. -/
theorem e8_assignment_weyl_word (a : Assignment) (h : (gradeTable e8Datum a 0).card = 78) :
    ∃ w : List (Fin 8), wordAction w canonical = a :=
  ⟨wordFor search a, (of_decide_eq_true orbit_certificate : ∀ a : Assignment,
    ((table e8Datum).filter (fun v => ∑ i, (v.get i : ZMod 3) * a i = 0)).card = 78 →
      wordAction (wordFor search a) canonical = a) a h⟩


/-- The canonical simple assignment evaluates exactly the seventh coordinate
of every integral vector, as in the fixed exceptional construction. -/
theorem e8_canonical_residue (v : Vector ℤ 8) :
    (∑ i, (v.get i : ZMod 3) * canonical i) = (v.get 6 : ZMod 3) := by
  simp [canonical, Pi.single_apply, mul_ite]

private def spanReflection {K M N ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) (i : ι) :
    P.rootSpan ℤ ≃ₗ[ℤ] P.rootSpan ℤ := by
  let e := (P.reflection i).restrictScalars ℤ
  apply e.ofSubmodules
  rw [RootPairing.rootSpan, Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℤ)
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨P.reflectionPerm i j, P.root_reflectionPerm i j⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨k, rfl⟩ := (P.reflectionPerm i).surjective j
    exact ⟨k, (P.root_reflectionPerm i k).symm⟩

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The actual Weyl reflection restricted to the actual integral root lattice. -/
noncomputable def latticeReflection (i : H.root) : rootLattice H ≃ₗ[ℤ] rootLattice H :=
  (rootSpanEquivRootLattice H).symm.trans ((spanReflection (rootSystem H) i).trans
    (rootSpanEquivRootLattice H))

theorem lattice_reflection_on_root (i j : H.root) :
    latticeReflection H i (rootLatticeElement H j) =
      rootLatticeElement H ((rootSystem H).reflectionPerm i j) := by
  have h (k : H.root) : rootSpanEquivRootLattice H ((rootSystem H).rootSpanMem ℤ k) =
      rootLatticeElement H k := rfl
  rw [← h j, ← h ((rootSystem H).reflectionPerm i j)]
  unfold latticeReflection
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  apply Subtype.ext
  exact ((rootSystem H).root_reflectionPerm i j).symm

variable (b : (rootSystem H).Base) (s : Index e8Datum ≃ b.support)

private theorem reflect_basis (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j)
    (i j : Fin 8) :
    latticeReflection H (s i) (rootLatticeElement H (s j)) =
      rootLatticeElement H (s j) - matrix e8Datum j i • rootLatticeElement H (s i) := by
  rw [lattice_reflection_on_root H]
  apply Subtype.ext
  funext y
  have he := congrArg (fun f : Dual K H => f y)
    (((rootSystem H).root_reflectionPerm (s i) (s j)).trans
      ((rootSystem H).reflection_apply_root (s i) (s j)))
  have hc := b.algebraMap_cartanMatrixIn_apply ℤ (s j) (s i)
  change ((b.cartanMatrix (s j) (s i) : ℤ) : K) = _ at hc
  rw [h] at hc
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, ← hc,
    Int.cast_smul_eq_zsmul] using he

private theorem reflect_character
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j)
    (χ : rootLattice H →+ ZMod 3) (i : Fin 8) :
    simpleCharacterEquiv H b s (χ.comp (latticeReflection H (s i)).toAddMonoidHom) =
      reflect i (simpleCharacterEquiv H b s χ) := by
  funext j
  simp only [simpleCharacterEquiv_apply, reflect, AddMonoidHom.comp_apply]
  change χ (latticeReflection H (s i) (rootLatticeElement H (s j))) =
    χ (rootLatticeElement H (s j)) - (matrix e8Datum j i : ZMod 3) * χ (rootLatticeElement H (s i))
  rw [reflect_basis H b s h, map_sub, map_zsmul, zsmul_eq_mul]

/-- Composition of the actual simple reflections on the integral root lattice. -/
noncomputable def latticeWord : List (Fin 8) → rootLattice H ≃ₗ[ℤ] rootLattice H
  | [] => LinearEquiv.refl ℤ _
  | i :: w => (latticeReflection H (s i)).trans (latticeWord w)

/-- The same word as a permutation of the actual roots. -/
noncomputable def rootWord : List (Fin 8) → Equiv.Perm H.root
  | [] => Equiv.refl _
  | i :: w => ((rootSystem H).reflectionPerm (s i)).trans (rootWord w)

theorem lattice_word_on_root (w : List (Fin 8)) (j : H.root) :
    latticeWord H b s w (rootLatticeElement H j) =
      rootLatticeElement H (rootWord H b s w j) := by
  induction w generalizing j with
  | nil => rfl
  | cons i w ih =>
    change latticeWord H b s w (latticeReflection H (s i) (rootLatticeElement H j)) = _
    exact (congrArg (latticeWord H b s w) (lattice_reflection_on_root H (s i) j)).trans (ih _)

private theorem word_character (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j)
    (χ : rootLattice H →+ ZMod 3) (w : List (Fin 8)) :
    simpleCharacterEquiv H b s (χ.comp (latticeWord H b s w).toAddMonoidHom) =
      wordAction w (simpleCharacterEquiv H b s χ) := by
  induction w with
  | nil => rw [wordAction_nil]; rfl
  | cons i w ih =>
    rw [wordAction_cons, ← ih]
    exact reflect_character H b s h (χ.comp (latticeWord H b s w).toAddMonoidHom) i

/-- Every surviving character on the actual integral root lattice is the
pullback of the seventh simple-coordinate character by a product of actual
simple Weyl reflections. The orientation is included in the orbit. -/
theorem e8_actual_character_weyl_word
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = matrix e8Datum i j)
    (χ : rootLattice H →+ ZMod 3)
    (hc : (gradeTable e8Datum (simpleCharacterEquiv H b s χ) 0).card = 78) :
    ∃ w : List (Fin 8), χ = ((simpleCharacterEquiv H b s).symm canonical).comp
      (latticeWord H b s w).toAddMonoidHom := by
  obtain ⟨w, hw⟩ := e8_assignment_weyl_word _ hc
  refine ⟨w, (simpleCharacterEquiv H b s).injective ?_⟩
  rw [word_character H b s h, Equiv.apply_symm_apply, hw]

end CubicAnomaly.Classification.RootClassificationOrbit
