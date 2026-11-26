import CubicAnomaly.Fixed.E8RadicalIdentification
import CubicAnomaly.Fixed.E8RadicalIdentificationSimpleData

/-!
# Simplicity of the E₆ lattice algebra

The squared adjoint of a root vector isolates its opposite-root coordinate.
Composing with root-raising and lowering operators, and taking six linear
combinations for the Cartan coordinates, extracts any coordinate of a vector
into the first root line. That line in turn generates every root and coroot.
-/

namespace CubicAnomaly.Fixed.E6Lattice

open SparseRealization
noncomputable section

private def b (i : Index) : Algebra := Pi.single i (1 : ℂ)

private theorem expand_coords (x : Algebra) : ∑ i, x i • b i = x := by
  change ∑ i, x i • (Pi.single i (1 : ℂ) : Index → ℂ) = x
  funext j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]

private theorem bracket_b (i j : Index) : ⁅b i, b j⁆ = realize b (products i j) := by
  change (∑ k : Index, ∑ l : Index,
    ((Pi.single i (1 : ℂ) : Index → ℂ) k * (Pi.single j (1 : ℂ) : Index → ℂ) l) •
      realize b (products k l)) = _
  simp [Pi.single_apply, mul_ite, ite_smul]

private def wordOp : Word → Module.End ℂ Algebra
  | [] => LinearMap.id
  | r :: w => (wordOp w).comp (LieAlgebra.ad ℂ Algebra (b (.inr r)))

private def wordsOp : List (ℤ × Word) → Module.End ℂ Algebra
  | [] => 0
  | (n, w) :: ws => (n : ℂ) • wordOp w + wordsOp ws

private theorem root_action (r : Fin 72) (xs : Expansion) :
    ⁅b (.inr r), realize b xs⁆ = realize b (applyRoot r xs) :=
  sparse_realize_action b (LieAlgebra.ad ℂ Algebra (b (.inr r))).toAddMonoidHom
    (products (.inr r)) xs (fun p _ => bracket_b _ p.1)

private theorem word_action (w : Word) (xs : Expansion) :
    wordOp w (realize b xs) = realize b (applyWord w xs) := by
  induction w generalizing xs with
  | nil => rfl
  | cons r w ih =>
    change wordOp w ⁅b (.inr r), realize b xs⁆ = realize b (applyWord w (applyRoot r xs))
    rw [root_action, ih]

private theorem words_action (ws : List (ℤ × Word)) (xs : Expansion) :
    wordsOp ws (realize b xs) = realize b (applyWords ws xs) := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    rcases p with ⟨n, w⟩
    change (n : ℂ) • wordOp w (realize b xs) + wordsOp ws (realize b xs) =
      realize b (scale n (applyWord w xs) ++ applyWords ws xs)
    rw [word_action, ih, sparse_realize_append, sparse_realize_scale, Int.cast_smul_eq_zsmul]

private theorem realize_equal {xs ys : Expansion} (h : equal xs ys = true) :
    realize b xs = realize b ys := by
  apply sparse_realize_eq_of_coefficients
  apply sparse_coefficients_eq_of_support
  intro p hp
  exact eq_of_beq ((List.all_eq_true.mp h) p hp)

private theorem singleton_realize (i : Index) (n : ℤ) :
    realize b [(i, n)] = (n : ℂ) • b i := by
  simp [realize, Int.cast_smul_eq_zsmul]

private theorem extract_basis (i j : Index) :
    wordsOp (coordinateWords i) (b j) =
      (if i = j then (coordinateCoeff i : ℂ) else 0) • b firstRoot := by
  have h := (words_action (coordinateWords i) [(j, 1)]).trans
    (realize_equal (e6_adjoint_words_certificate.2.2 i |>.2 j))
  by_cases hij : i = j <;> simpa [hij, singleton_realize] using h

private theorem extract_coordinate (i : Index) (v : Algebra) :
    wordsOp (coordinateWords i) v = (v i * coordinateCoeff i) • b firstRoot := by
  conv_lhs => rw [← expand_coords v, map_sum]
  simp [map_smul, extract_basis, ite_smul, smul_ite, smul_smul]

private theorem generate_basis (i : Index) :
    wordOp (generateWord i) (b firstRoot) = (generateCoeff i : ℂ) • b i := by
  have h := (word_action (generateWord i) [(firstRoot, 1)]).trans
    (realize_equal ((e6_adjoint_words_certificate.2.1 i).2))
  simpa only [singleton_realize, Int.cast_one, one_smul] using h

private theorem word_mem (I : LieIdeal ℂ Algebra) (w : Word) {x : Algebra} (hx : x ∈ I) :
    wordOp w x ∈ I := by
  induction w generalizing x with
  | nil => exact hx
  | cons r w ih =>
    exact ih (I.lie_mem (x := b (.inr r)) hx)

private theorem words_mem (I : LieIdeal ℂ Algebra) (ws : List (ℤ × Word))
    {x : Algebra} (hx : x ∈ I) : wordsOp ws x ∈ I := by
  induction ws with
  | nil => exact I.zero_mem
  | cons p ws ih => exact I.add_mem (I.smul_mem _ (word_mem I p.2 hx)) ih

/-- Every nonzero ideal of the independently constructed E₆ algebra contains
all seventy-eight basis vectors, and the bracket is nonabelian. -/
theorem e6_lattice_isSimple : LieAlgebra.IsSimple ℂ Algebra := by
  constructor
  · intro I
    by_cases hI : I = ⊥
    · exact Or.inl hI
    right
    obtain ⟨x, hx, hx0⟩ := I.toSubmodule.ne_bot_iff.mp
      ((LieSubmodule.toSubmodule_eq_bot I).not.mpr hI)
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx0 (funext h)
    have extracted := words_mem I (coordinateWords i) hx
    rw [extract_coordinate] at extracted
    have ci : (coordinateCoeff i : ℂ) ≠ 0 := by
      exact_mod_cast (e6_adjoint_words_certificate.2.2 i).1
    have hb := (I.toSubmodule.smul_mem_iff (mul_ne_zero hi ci)).mp extracted
    apply top_unique
    intro v _
    rw [← expand_coords v]
    apply I.toSubmodule.sum_mem
    intro j _
    have generated := word_mem I (generateWord j) hb
    rw [generate_basis] at generated
    have cj : (generateCoeff j : ℂ) ≠ 0 := by
      exact_mod_cast (e6_adjoint_words_certificate.2.1 j).1
    exact I.smul_mem _ ((I.toSubmodule.smul_mem_iff cj).mp generated)
  · intro ha
    have hz := ha.trivial (b (.inl 0)) (b firstRoot)
    rw [bracket_b, e6_adjoint_words_certificate.1, singleton_realize] at hz
    have hh := congrArg (fun v : Algebra => v firstRoot) hz
    change (2 : ℂ) * (Pi.single firstRoot (1 : ℂ) : Index → ℂ) firstRoot = 0 at hh
    norm_num at hh

end

end CubicAnomaly.Fixed.E6Lattice
