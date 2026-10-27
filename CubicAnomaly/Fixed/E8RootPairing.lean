import CubicAnomaly.Fixed.E8Coordinates
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic

/-!
# An actual complex root pairing from the checked E8 coordinates

The root index type consists of the reconstructed integer vectors.  The
finite certificates in `E8Coordinates` are transported to a genuine complex
root pairing, with reducedness, crystallographic pairings, and full span.
-/

namespace CubicAnomaly.Fixed.E8RootPairing

open scoped BigOperators

/-- The finite index type consists of actual coordinate roots. -/
abbrev Root := {x : Fin 8 → ℤ // x ∈ coordinateRoots}

/-- The ambient complex root space. -/
abbrev Space := Fin 8 → ℂ

/-- A root regarded as a vector in the complex root space. -/
def rootVector (x : Root) : Space := fun i => (x.val i : ℂ)

/-- The standard symmetric Cartan matrix, with complex coefficients. -/
def gram : Matrix (Fin 8) (Fin 8) ℂ := CartanMatrix.E₈.map (Int.castRingHom ℂ)

/-- The actual bilinear Cartan form. -/
noncomputable def form : Space →ₗ[ℂ] Space →ₗ[ℂ] ℂ := gram.toBilin'

theorem form_apply (x y : Space) :
    form x y = ∑ i, ∑ j, x i * (CartanMatrix.E₈ i j : ℂ) * y j := by
  simp [form, gram, Matrix.toBilin'_apply, mul_assoc]

theorem form_rootVectors (x y : Root) :
    form (rootVector x) (rootVector y) = (innerZ x.val y.val : ℂ) := by
  simp [form_apply, rootVector, innerZ, Int.cast_sum, Int.cast_mul]

theorem rootVector_injective : Function.Injective rootVector := by
  intro x y h
  apply Subtype.ext
  funext i
  exact Int.cast_injective (congrFun h i : (x.val i : ℂ) = (y.val i : ℂ))

theorem form_symmetric : form.IsSymm := by
  constructor
  intro x y
  change form x y = form y x
  rw [form_apply, form_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [CartanMatrix.E₈_isSymm.apply i j]
  ring

theorem form_nondegenerate : form.Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  change (CartanMatrix.E₈.map fun z => (z : ℂ)).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast cartan_det_ne_zero

noncomputable instance : form.IsPerfPair :=
  LinearMap.IsPerfPair.of_bijective form
    (LinearMap.BilinForm.toDual form form_nondegenerate).bijective

theorem innerZ_sub_left (x y z : Fin 8 → ℤ) :
    innerZ (x - y) z = innerZ x z - innerZ y z := by
  simp [innerZ, sub_mul, Finset.sum_sub_distrib]

theorem innerZ_smul_left (n : ℤ) (x y : Fin 8 → ℤ) :
    innerZ (n • x) y = n * innerZ x y := by
  simp [innerZ, Finset.mul_sum, mul_assoc]

theorem reflectZ_involutive (x : Fin 8 → ℤ) (hx : innerZ x x = 2) :
    Function.Involutive (reflectZ x) := by
  intro y
  simp only [reflectZ_eq]
  rw [innerZ_sub_left, innerZ_smul_left, hx]
  module

/-- The reflection permutation on the actual finite coordinate roots. -/
def reflectionPerm (x : Root) : Equiv.Perm Root where
  toFun y := ⟨reflectZ x.val y.val,
    coordinateRoots_reflection_closed x.val x.property y.val y.property⟩
  invFun y := ⟨reflectZ x.val y.val,
    coordinateRoots_reflection_closed x.val x.property y.val y.property⟩
  left_inv y := Subtype.ext (reflectZ_involutive x.val
    (coordinateRoots_norm_two x.val x.property) y.val)
  right_inv y := Subtype.ext (reflectZ_involutive x.val
    (coordinateRoots_norm_two x.val x.property) y.val)

/-- The actual complex root pairing carried by the reconstructed `E₈` roots. -/
noncomputable def rootPairing : RootPairing Root ℂ Space Space where
  toLinearMap := form
  root := ⟨rootVector, rootVector_injective⟩
  coroot := ⟨rootVector, rootVector_injective⟩
  root_coroot_two x := by
    change form (rootVector x) (rootVector x) = 2
    rw [form_rootVectors, coordinateRoots_norm_two x.val x.property]
    norm_num
  reflectionPerm := reflectionPerm
  reflectionPerm_root x y := by
    change rootVector y - form (rootVector y) (rootVector x) • rootVector x =
      rootVector (reflectionPerm x y)
    ext i
    simp [rootVector, reflectionPerm, reflectZ_apply, form_rootVectors]
  reflectionPerm_coroot x y := by
    change rootVector y - form (rootVector x) (rootVector y) • rootVector x =
      rootVector (reflectionPerm x y)
    rw [show form (rootVector x) (rootVector y) = form (rootVector y) (rootVector x)
      from form_symmetric.eq _ _]
    ext i
    simp [rootVector, reflectionPerm, reflectZ_apply, form_rootVectors]

theorem rootPairing_root (x : Root) : rootPairing.root x = rootVector x := rfl

theorem rootPairing_coroot (x : Root) : rootPairing.coroot x = rootVector x := rfl

theorem rootPairing_pairing (x y : Root) :
    rootPairing.pairing x y = (innerZ x.val y.val : ℂ) :=
  form_rootVectors x y

/-- The simple roots as actual members of the fixed root index type. -/
def simpleRoot (i : Fin 8) : Root := ⟨Pi.single i 1, simpleRoots_mem i⟩

theorem rootVector_simpleRoot (i : Fin 8) :
    rootVector (simpleRoot i) = Pi.single i 1 := by
  ext j
  by_cases h : j = i <;> simp [rootVector, simpleRoot, Pi.single_apply, h]

theorem span_rootVector_eq_top :
    Submodule.span ℂ (Set.range rootVector) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℂ (Fin 8)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨simpleRoot i, by simpa using rootVector_simpleRoot i⟩

noncomputable instance : rootPairing.IsRootSystem where
  span_root_eq_top := span_rootVector_eq_top
  span_coroot_eq_top := span_rootVector_eq_top

noncomputable instance : rootPairing.IsCrystallographic where
  exists_value x y := ⟨innerZ x.val y.val, (rootPairing_pairing x y).symm⟩

/-- Equal norm two rules out proportional roots other than the two orientations. -/
noncomputable instance : rootPairing.IsReduced where
  eq_or_eq_neg x y h := by
    rw [LinearIndependent.pair_iff' (rootPairing.ne_zero x)] at h
    push_neg at h
    obtain ⟨a, ha⟩ := h
    have haa : a * a = 1 := by
      have hn := rootPairing.root_coroot_two y
      change form (rootPairing.root y) (rootPairing.root y) = 2 at hn
      rw [← ha] at hn
      have hxx : form (rootPairing.root x) (rootPairing.root x) = 2 :=
        rootPairing.root_coroot_two x
      simp only [map_smul, LinearMap.smul_apply, hxx, smul_eq_mul] at hn
      linear_combination hn / 2
    have hasign : a = 1 ∨ a = -1 := by
      have hz : (a - 1) * (a + 1) = 0 := by linear_combination haa
      rcases mul_eq_zero.mp hz with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hasign with rfl | rfl
    · exact Or.inl (by simpa using ha)
    · exact Or.inr (by simpa using congrArg Neg.neg ha)

end CubicAnomaly.Fixed.E8RootPairing
