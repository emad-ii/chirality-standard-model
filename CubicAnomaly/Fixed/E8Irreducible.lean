import CubicAnomaly.Fixed.E8Base

/-!
# Irreducibility of the constructed fixed root system

The proof works on actual invariant complex subspaces.  A nonzero vector
has a nonzero pairing with a simple root, reflection extracts that root,
and the explicit connected eight-node Cartan diagram propagates membership
to the whole simple-root basis.
-/

namespace CubicAnomaly.Fixed.E8RootPairing

theorem form_simpleRoots (i j : Fin 8) :
    form (rootVector (simpleRoot i)) (rootVector (simpleRoot j)) =
      (CartanMatrix.E₈ i j : ℂ) := by
  rw [rootVector_simpleRoot, rootVector_simpleRoot, form_apply]
  simp [Pi.single_apply]

private theorem invariant_extract_root (U : Submodule ℂ Space)
    (hU : ∀ x, U ∈ Module.End.invtSubmodule (rootPairing.reflection x))
    (x : Root) (v : Space) (hv : v ∈ U) (hx : form v (rootVector x) ≠ 0) :
    rootVector x ∈ U := by
  have hr : rootPairing.reflection x v ∈ U :=
    (Module.End.mem_invtSubmodule _).mp (hU x) hv
  have hm := U.sub_mem hv hr
  rw [rootPairing.reflection_apply, sub_sub_cancel] at hm
  exact (U.smul_mem_iff hx).mp hm

private theorem invariant_simple_step (U : Submodule ℂ Space)
    (hU : ∀ x, U ∈ Module.End.invtSubmodule (rootPairing.reflection x))
    (i j : Fin 8) (hij : CartanMatrix.E₈ i j ≠ 0)
    (hi : rootVector (simpleRoot i) ∈ U) :
    rootVector (simpleRoot j) ∈ U := by
  apply invariant_extract_root U hU (simpleRoot j) _ hi
  rw [form_simpleRoots]
  exact_mod_cast hij

private theorem invariant_simple_center (U : Submodule ℂ Space)
    (hU : ∀ x, U ∈ Module.End.invtSubmodule (rootPairing.reflection x))
    (i : Fin 8) (hi : rootVector (simpleRoot i) ∈ U) :
    rootVector (simpleRoot 3) ∈ U := by
  have step := invariant_simple_step U hU
  fin_cases i
  · exact step 2 3 (by decide) (step 0 2 (by decide) hi)
  · exact step 1 3 (by decide) hi
  · exact step 2 3 (by decide) hi
  · exact hi
  · exact step 4 3 (by decide) hi
  · exact step 4 3 (by decide) (step 5 4 (by decide) hi)
  · exact step 4 3 (by decide) (step 5 4 (by decide) (step 6 5 (by decide) hi))
  · exact step 4 3 (by decide) (step 5 4 (by decide)
      (step 6 5 (by decide) (step 7 6 (by decide) hi)))

private theorem invariant_center_all_simple (U : Submodule ℂ Space)
    (hU : ∀ x, U ∈ Module.End.invtSubmodule (rootPairing.reflection x))
    (hi : rootVector (simpleRoot 3) ∈ U) (j : Fin 8) :
    rootVector (simpleRoot j) ∈ U := by
  have step := invariant_simple_step U hU
  fin_cases j
  · exact step 2 0 (by decide) (step 3 2 (by decide) hi)
  · exact step 3 1 (by decide) hi
  · exact step 3 2 (by decide) hi
  · exact hi
  · exact step 3 4 (by decide) hi
  · exact step 4 5 (by decide) (step 3 4 (by decide) hi)
  · exact step 5 6 (by decide) (step 4 5 (by decide) (step 3 4 (by decide) hi))
  · exact step 6 7 (by decide) (step 5 6 (by decide)
      (step 4 5 (by decide) (step 3 4 (by decide) hi)))

/-- Actual reflection-invariant complex subspaces of the fixed root space are trivial. -/
theorem invariant_subspace_eq_top (U : Submodule ℂ Space)
    (hU : ∀ x, U ∈ Module.End.invtSubmodule (rootPairing.reflection x))
    (hU0 : U ≠ ⊥) : U = ⊤ := by
  obtain ⟨v, hv, hv0⟩ := U.ne_bot_iff.mp hU0
  obtain ⟨i, hi⟩ : ∃ i : Fin 8, form v (rootVector (simpleRoot i)) ≠ 0 := by
    by_contra! h
    have hz : form v = 0 := by
      apply LinearMap.ext_on (Pi.basisFun ℂ (Fin 8)).span_eq
      rintro _ ⟨i, rfl⟩
      simpa [rootVector_simpleRoot] using h i
    apply hv0
    exact form_nondegenerate.1 v (fun y => by rw [hz]; rfl)
  have hs := invariant_simple_center U hU i (invariant_extract_root U hU _ v hv hi)
  apply top_unique
  rw [← (Pi.basisFun ℂ (Fin 8)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  simpa [rootVector_simpleRoot] using invariant_center_all_simple U hU hs j

noncomputable instance : rootPairing.IsIrreducible :=
  RootPairing.IsIrreducible.mk' rootPairing invariant_subspace_eq_top

end CubicAnomaly.Fixed.E8RootPairing
