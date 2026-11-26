import CubicAnomaly.Classification.WeylDualityObstruction
import CubicAnomaly.Classification.ClassicalConstituentOpposition
import CubicAnomaly.Classification.CorootComponents
import CubicAnomaly.Classification.ComplexDuality

/-!
# Weyl opposition in the actual semisimple isotropy

Connected components of the matrix of the simple roots have orthogonal
simple coroots. Their Coxeter words therefore act independently. If every
component admits negation, composing the component words negates the
whole Cartan and makes its irreducible modules self-dual.
-/

namespace CubicAnomaly.Classification.WeylComponentObstruction

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open WeylDualityObstruction CorootComponents CartanCoroot

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

/-- Connectivity in the Dynkin diagram of the actual Cartan. -/
def componentSetoid : Setoid b.support where
  r := Relation.ReflTransGen fun i j => b.cartanMatrix i j ≠ 0
  iseqv := ⟨fun _ => .refl, fun {_ _} hij => Relation.ReflTransGen.symmetric (r := fun i j : b.support => b.cartanMatrix i j ≠ 0)
    (fun {_ _} h hz => h (b.cartanMatrix_apply_eq_zero_iff_symm.mp hz)) hij, fun h₁ h₂ => h₁.trans h₂⟩

abbrev Component := Quotient (componentSetoid H b)

def component (i : b.support) : Component H b := Quotient.mk _ i

abbrev Nodes (c : Component H b) := {i : b.support // component H b i = c}

noncomputable def componentMatrix (c : Component H b) : Matrix (Nodes H b c) (Nodes H b c) ℤ :=
  b.cartanMatrix.submatrix Subtype.val Subtype.val

private theorem same_component_of_edge {i j : b.support} (h : b.cartanMatrix i j ≠ 0) :
    component H b i = component H b j := Quotient.sound (Relation.ReflTransGen.single h)

private theorem component_indec (c : Component H b) : (componentMatrix H b c).IsIndecomposable := by
  rintro ⟨i,hi⟩ ⟨j,hj⟩
  have path : Relation.ReflTransGen (fun x y => b.cartanMatrix x y ≠ 0) i j :=
    Quotient.exact (hi.trans hj.symm)
  induction path with
  | refl => exact .refl
  | @tail v j hv hvj ih =>
    have hv' : component H b v = c := (same_component_of_edge H b hvj).trans hj
    exact (ih hv').tail (show componentMatrix H b c ⟨v,hv'⟩ ⟨j,hj⟩ ≠ 0 from hvj)

private theorem word_append (v w : List H.root) (x : H) :
    applyWord H (v ++ w) x = applyWord H w (applyWord H v x) := by
  induction v generalizing x with
  | nil => rfl
  | cons i v ih => exact ih ((rootSystem H).coreflection i x)

private theorem word_fixes_outside {c : Component H b} (i : b.support)
    (hi : component H b i ≠ c) (w : List (Nodes H b c)) :
    applyWord H (w.map fun j => j.val.val) (b.toCoweightBasis i) = b.toCoweightBasis i := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    have hz : b.cartanMatrix j.val i = 0 := by
      by_contra hn
      exact hi ((same_component_of_edge H b hn).symm.trans j.property)
    have hp := b.algebraMap_cartanMatrixIn_apply ℤ j.val i
    change ((b.cartanMatrix j.val i : ℤ) : ℂ) = _ at hp
    rw [hz, Int.cast_zero] at hp
    change applyWord H _ ((rootSystem H).coreflection j.val.val (b.toCoweightBasis i)) = _
    rw [b.toCoweightBasis_apply, RootPairing.coreflection_apply_coroot, ← hp, zero_smul, sub_zero]
    simpa only [b.toCoweightBasis_apply] using ih

open scoped Classical in
private theorem component_word (c : Component H b) (hcard : finrank ℂ H ≤ 8)
    (ht : ¬ NoncentralType (componentMatrix H b c)) :
    ∃ w : List H.root, ∀ i : b.support, applyWord H w (b.toCoweightBasis i) =
      if component H b i = c then -b.toCoweightBasis i else b.toCoweightBasis i := by
  classical
  letI : Fintype (Nodes H b c) := Fintype.ofFinite _
  have hbound : Fintype.card (Nodes H b c) ≤ 8 := by
    rw [finrank_eq_card_basis b.toCoweightBasis] at hcard
    exact (Fintype.card_le_of_injective _ Subtype.val_injective).trans hcard
  have hc := (DynkinClassification.actual_finite_cartan b).submatrix
    (f := (Subtype.val : Nodes H b c → b.support)) Subtype.val_injective
  obtain ⟨m,e,k,hk⟩ := (small_cartan_opposition hc (component_indec H b c) hbound).resolve_left ht
  let w := (coxeterWord m k).map e.symm
  refine ⟨w.map fun j => j.val.val, fun i => ?_⟩
  split_ifs with hi
  · have hz := coxeter_negates_indexed_coroots H b (fun j => (e.symm j).val) k
      (C := (componentMatrix H b c).reindex e e) (fun _ _ => rfl) hk (e ⟨i,hi⟩)
    simpa [w, List.map_map, Function.comp_def] using hz
  · exact word_fixes_outside H b i hi w

private theorem component_words_cover (hcard : finrank ℂ H ≤ 8)
    (ht : ∀ c, ¬ NoncentralType (componentMatrix H b c)) :
    ∃ w : List H.root, ∀ x : H, applyWord H w x = -x := by
  classical
  have part (S : Finset (Component H b)) :
      ∃ w : List H.root, ∀ i : b.support, applyWord H w (b.toCoweightBasis i) =
        if component H b i ∈ S then -b.toCoweightBasis i else b.toCoweightBasis i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨[], fun _ => by simp [applyWord]⟩
    | @insert c S hn ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨v, hv⟩ := component_word H b c hcard (ht c)
      refine ⟨w ++ v, fun i => ?_⟩
      rw [word_append, hw]
      by_cases h1 : component H b i = c
      · simp [h1, hn, hv, -RootPairing.Base.toCoweightBasis_apply]
      · by_cases h2 : component H b i ∈ S <;> simp [h1, h2, hv, -RootPairing.Base.toCoweightBasis_apply]
  obtain ⟨w, hw⟩ := part (Finset.univ.image (component H b))
  refine ⟨w, fun z => ?_⟩
  have hz (i : b.support) : applyWord H w (b.toCoweightBasis i) = -b.toCoweightBasis i := by
    simpa [Finset.mem_image_of_mem _ (Finset.mem_univ i)] using hw i
  rw [← b.toCoweightBasis.sum_repr z]
  simp only [map_sum, map_smul, hz, smul_neg, Finset.sum_neg_distrib]

/-- Some connected simple-root block of the semisimple Cartan is A (rank at
least two), odd D, or E6 whenever actual Weyl negation fails. -/
theorem exists_noncentral_component (hcard : finrank ℂ H ≤ 8)
    (hn : ¬ ∃ w : List H.root, ∀ x : H, applyWord H w x = -x) :
    ∃ c, NoncentralType (componentMatrix H b c) := by
  by_contra! ht
  exact hn (component_words_cover H b hcard ht)

/-- The simple Lie ideal generated by any coroot in the selected component. -/
noncomputable def componentIdeal (c : Component H b) : LieIdeal ℂ L := corootIdeal H c.out.val

theorem componentIdeal_isSimple (c : Component H b) : IsSimple ℂ (componentIdeal H b c) :=
  corootIdeal_isSimple H c.out.val

private theorem corootConnected_of_path {i j : b.support}
    (hp : Relation.ReflTransGen (fun x y => b.cartanMatrix x y ≠ 0) i j) :
    CorootConnected H i.val j.val := by
  induction hp with
  | refl => exact .refl _
  | @tail j k _ hj ih =>
    apply Relation.EqvGen.trans _ _ _ ih
    apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    intro hz
    have he := b.algebraMap_cartanMatrixIn_apply ℤ j k
    change ((b.cartanMatrix j k : ℤ) : ℂ) = j.val.val (coroot k.val.val) at he
    exact hj (Int.cast_eq_zero.mp (he.trans hz))

/-- Every simple coroot of this Dynkin block generates the same actual simple ideal. -/
theorem componentIdeal_eq_corootIdeal (c : Component H b) (i : Nodes H b c) :
    componentIdeal H b c = corootIdeal H i.val.val := by
  apply corootIdeal_eq_of_connected
  exact corootConnected_of_path H b (Quotient.exact ((Quotient.out_eq c).trans i.property.symm))

private theorem cartanWord_eq (w : List H.root) (x : H) :
    ClassicalConstituentWeyl.cartanWord H w x = applyWord H w x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => exact ih ((rootSystem H).coreflection i x)

section Compact

open Complexification ComplexDuality Structural
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  (B : CompactForm g) (h : LieSubalgebra ℝ g) (hp : h ≠ ⊤)
  (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
  [IsKilling ℂ (ℂ ⊗[ℝ] h)] (J : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [J.IsCartanSubalgebra]
  (d : (rootSystem J).Base)

include hp e d in
/-- The actual canonical half of a compact complex-type complement obstructs
Weyl negation on its isotropy Cartan without any simplicity hypothesis. -/
theorem compact_isotropy_no_weyl_negation :
    ¬ ∃ w : List J.root, ∀ z : J, applyWord J w z = -z := by
  rintro ⟨w,hw⟩
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  obtain ⟨-, hV, -, ⟨D⟩, hne⟩ := compact_complement_complex_type_decomposition B h hp e
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) V := hV
  obtain ⟨T⟩ := ClassicalConstituentOpposition.irreducible_self_dual_of_neg_word (M := V)
    J d w (fun z => (cartanWord_eq J w z).trans (hw z))
  exact hne ⟨T.trans D.symm⟩

include hp e in
/-- Every compact complex-type isotropy of rank at most eight has a connected
simple factor of one of the three noncentral opposition types. -/
theorem compact_isotropy_noncentral_component (hcard : finrank ℂ J ≤ 8) :
    ∃ c, NoncentralType (componentMatrix J d c) :=
  exists_noncentral_component J d hcard (compact_isotropy_no_weyl_negation B h hp e J d)

end Compact

end CubicAnomaly.Classification.WeylComponentObstruction
