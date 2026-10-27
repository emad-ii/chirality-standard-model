import CubicAnomaly.Fixed.E8RootPairing

/-!
# The explicit simple coordinate base of the constructed E8 root system
-/

namespace CubicAnomaly.Fixed.E8RootPairing

open scoped BigOperators

theorem simpleRoot_injective : Function.Injective simpleRoot := by
  intro i j h
  apply (Pi.basisFun ℂ (Fin 8)).injective
  simpa [rootVector_simpleRoot] using congrArg rootVector h

/-- The eight named simple roots, as a finite subset of the actual root index. -/
def simpleSupport : Finset Root := Finset.univ.image simpleRoot

theorem simpleSupport_coe : (simpleSupport : Set Root) = Set.range simpleRoot := by
  ext x
  simp [simpleSupport]

theorem simpleSupport_independent :
    LinearIndepOn ℂ rootPairing.root (simpleSupport : Set Root) := by
  rw [simpleSupport_coe]
  apply (linearIndepOn_range_iff simpleRoot_injective rootPairing.root).mpr
  simpa [Function.comp_def, rootPairing_root, rootVector_simpleRoot] using
    Pi.linearIndependent_single_one (Fin 8) ℂ

theorem simpleSupport_image :
    rootPairing.root '' (simpleSupport : Set Root) =
      Set.range (fun i : Fin 8 => Pi.single i (1 : ℂ)) := by
  rw [simpleSupport_coe, ← Set.range_comp]
  simp only [Function.comp_def, rootPairing_root, rootVector_simpleRoot]

private theorem nonnegative_mem_simpleCone (z : Fin 8 → ℤ) (hz : ∀ i, 0 ≤ z i) :
    (fun i => (z i : ℂ)) ∈
      AddSubmonoid.closure (Set.range (fun i : Fin 8 => Pi.single i (1 : ℂ))) := by
  have hs : (fun i => (z i : ℂ)) = ∑ i : Fin 8, (z i).toNat • Pi.single i (1 : ℂ) := by
    ext j
    have hj : ((z j).toNat : ℂ) = (z j : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg (hz j)
    simp [Finset.sum_apply, Pi.single_apply, hj]
  rw [hs]
  apply AddSubmonoid.sum_mem
  intro i _
  have hg : Pi.single i (1 : ℂ) ∈ AddSubmonoid.closure
      (Set.range (fun j : Fin 8 => Pi.single j (1 : ℂ))) :=
    AddSubmonoid.subset_closure ⟨i, rfl⟩
  exact AddSubmonoid.nsmul_mem _ hg _

theorem root_mem_or_neg_mem_simpleCone (x : Root) :
    rootPairing.root x ∈ AddSubmonoid.closure
      (rootPairing.root '' (simpleSupport : Set Root)) ∨
    -rootPairing.root x ∈ AddSubmonoid.closure
      (rootPairing.root '' (simpleSupport : Set Root)) := by
  rw [simpleSupport_image]
  rcases coordinateRoots_sign x.val x.property with hx | hx
  · exact Or.inl (nonnegative_mem_simpleCone x.val hx)
  · right
    have h := nonnegative_mem_simpleCone (-x.val) (fun i => neg_nonneg.mpr (hx i))
    simpa [rootPairing_root, rootVector] using h

/-- The actual base formed by the eight standard simple coordinate roots. -/
noncomputable def simpleBase : rootPairing.Base where
  support := simpleSupport
  linearIndepOn_root := simpleSupport_independent
  linearIndepOn_coroot := simpleSupport_independent
  root_mem_or_neg_mem := root_mem_or_neg_mem_simpleCone
  coroot_mem_or_neg_mem := root_mem_or_neg_mem_simpleCone

/-- Indexing the actual simple base by the eight coordinate directions. -/
def simpleIndex (i : Fin 8) : simpleBase.support :=
  ⟨simpleRoot i, by simp [simpleBase, simpleSupport]⟩

theorem simpleIndex_bijective : Function.Bijective simpleIndex := by
  constructor
  · intro i j h
    exact simpleRoot_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
    exact ⟨i, Subtype.ext hi⟩

/-- The explicit index equivalence for the base. -/
noncomputable def simpleIndexEquiv : Fin 8 ≃ simpleBase.support :=
  Equiv.ofBijective simpleIndex simpleIndex_bijective

theorem simpleBase_cartanMatrix (i j : Fin 8) :
    simpleBase.cartanMatrix (simpleIndex i) (simpleIndex j) = CartanMatrix.E₈ i j := by
  apply Int.cast_injective (α := ℂ)
  change algebraMap ℤ ℂ (rootPairing.pairingIn ℤ (simpleRoot i) (simpleRoot j)) = _
  rw [rootPairing.algebraMap_pairingIn]
  rw [rootPairing_pairing]
  congr 1
  simp [simpleRoot, innerZ, Pi.single_apply]

theorem simpleBase_unsigned_cartan_det_ne_zero :
    (4 - simpleBase.cartanMatrix).det ≠ 0 := by
  have h : (4 - simpleBase.cartanMatrix).submatrix simpleIndexEquiv simpleIndexEquiv =
      4 - CartanMatrix.E₈ := by
    ext i j
    simp [Matrix.submatrix_apply, simpleIndexEquiv, simpleBase_cartanMatrix,
      Matrix.ofNat_apply, simpleIndex_bijective.1.eq_iff]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_submatrix_equiv_self] at hd
  rw [hd]
  exact unsigned_cartan_det_ne_zero

end CubicAnomaly.Fixed.E8RootPairing
