import CubicAnomaly.Classification.CanonicalHalf
import CubicAnomaly.Classification.CompactGeometry

/-! A real Lie-pair equivalence preserving the oriented half conjugates the
two canonical Hermitian matrix representations, even with different chosen
compact forms and coordinates. -/

namespace CubicAnomaly.Classification.CanonicalHalfTransport

open Structural Complexification HermitianRealization CompactGeometry AnomalyComplexification
open CanonicalHalf Matrix
open scoped TensorProduct

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

private noncomputable def ambientCoordinates (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) Complex.I
      ≃ₗ[ℂ] (Fin (hermitianHalfOfCommutant B h e).dimension → ℂ) :=
  (ambientHalfEquiv (orthogonalComplement B h) (commutantComplexStructure e)
    Complex.I).symm.toLinearEquiv.trans (canonicalPositiveHalfEquiv B h e)

private theorem ambient_coordinates_action (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (x : ℂ ⊗[ℝ] h)
    (z : ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) Complex.I) :
    ambientCoordinates B h e ⁅x, z⁆ =
      complexHermitianRepresentation (hermitianHalfOfCommutant B h e) x *ᵥ ambientCoordinates B h e z := by
  let E := (ambientHalfEquiv (orthogonalComplement B h) (commutantComplexStructure e) Complex.I).symm
  change canonicalPositiveHalfEquiv B h e (E ⁅x, z⁆) = _ *ᵥ canonicalPositiveHalfEquiv B h e (E z)
  exact (congrArg (canonicalPositiveHalfEquiv B h e) (E.map_lie x z)).trans
    (canonicalPositiveHalfEquiv_intertwines B h e x (E z))

variable {k : Type*} [LieRing k] [LieAlgebra ℝ k] [Module.Finite ℝ k]

/-- Transport the entire canonical positive-half action under the original
real pair map. The second equivalence changes only the matrix coordinates. -/
theorem positive_matrix_equiv_for_restriction (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (C : CompactForm k) (l : LieSubalgebra ℝ k)
    (c : lieCommutant (L := l) (M := orthogonalComplement C l) ≃ₐ[ℝ] ℂ)
    (f : g ≃ₗ⁅ℝ⁆ k) (hf : h.map f.toLieHom = l)
    (hpos : (ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e)
      Complex.I).toSubmodule.map (f.toLinearMap.baseChange ℂ) =
      (ambientComplexifiedHalf (orthogonalComplement C l) (commutantComplexStructure c) Complex.I).toSubmodule) :
    ∃ (R : (Fin (hermitianHalfOfCommutant B h e).dimension → ℂ) ≃ₗ[ℂ]
        (Fin (hermitianHalfOfCommutant C l c).dimension → ℂ)), ∀ (x : h) v,
      R (complexHermitianRepresentation (hermitianHalfOfCommutant B h e) (1 ⊗ₜ[ℝ] x) *ᵥ v) =
      complexHermitianRepresentation (hermitianHalfOfCommutant C l c) (1 ⊗ₜ[ℝ] f.ofSubalgebras h l hf x) *ᵥ R v := by
  let θ := f.ofSubalgebras h l hf
  let P := ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) Complex.I
  let Q := ambientComplexifiedHalf (orthogonalComplement C l) (commutantComplexStructure c) Complex.I
  let E : P ≃ₗ[ℂ] Q := (LinearEquiv.baseChange ℝ ℂ g k f.toLinearEquiv).ofSubmodules P.toSubmodule Q.toSubmodule hpos
  have map_act (x : h) (z : P) : E ⁅(1 ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] h), z⁆ =
      ⁅(1 ⊗ₜ[ℝ] θ x : ℂ ⊗[ℝ] l), E z⁆ := by
    apply Subtype.ext
    have hincl := complexifiedLieHom_inclusion_action h (1 ⊗ₜ[ℝ] x) z.val
    have hincl' := complexifiedLieHom_inclusion_action l (1 ⊗ₜ[ℝ] θ x) (E z).val
    change f.toLinearMap.baseChange ℂ ⁅(1 ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] h), z.val⁆ =
      ⁅(1 ⊗ₜ[ℝ] θ x : ℂ ⊗[ℝ] l), (E z).val⁆
    rw [← hincl, ← hincl']
    exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) f.toLieHom).map_lie _ _
  let p := ambientCoordinates B h e
  let q := ambientCoordinates C l c
  refine ⟨p.symm.trans (E.trans q), ?_⟩
  intro x v
  obtain ⟨z, rfl⟩ := p.surjective v
  change q (E (p.symm (_ *ᵥ p z))) = _ *ᵥ q (E (p.symm (p z)))
  rw [← ambient_coordinates_action B h e, p.symm_apply_apply, p.symm_apply_apply, map_act,
    ambient_coordinates_action C l c]

/-- The canonical matrix representations agree under restriction of the pair map. -/
theorem exists_positive_matrix_equiv (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (C : CompactForm k) (l : LieSubalgebra ℝ k)
    (c : lieCommutant (L := l) (M := orthogonalComplement C l) ≃ₐ[ℝ] ℂ)
    (f : g ≃ₗ⁅ℝ⁆ k) (hf : h.map f.toLieHom = l)
    (hpos : (ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e)
      Complex.I).toSubmodule.map (f.toLinearMap.baseChange ℂ) =
      (ambientComplexifiedHalf (orthogonalComplement C l) (commutantComplexStructure c) Complex.I).toSubmodule) :
    ∃ (θ : h ≃ₗ⁅ℝ⁆ l) (R : (Fin (hermitianHalfOfCommutant B h e).dimension → ℂ) ≃ₗ[ℂ]
        (Fin (hermitianHalfOfCommutant C l c).dimension → ℂ)), ∀ (x : h) v,
      R (complexHermitianRepresentation (hermitianHalfOfCommutant B h e) (1 ⊗ₜ[ℝ] x) *ᵥ v) =
      complexHermitianRepresentation (hermitianHalfOfCommutant C l c) (1 ⊗ₜ[ℝ] θ x) *ᵥ R v := by
  obtain ⟨R, hR⟩ := positive_matrix_equiv_for_restriction B h e C l c f hf hpos
  exact ⟨f.ofSubalgebras h l hf, R, hR⟩

open AllRank CubicRadical

omit [Module.Finite ℝ g] [Module.Finite ℝ k] in
/-- An intertwiner preserves the mixed cubic on every triple of real isotropy elements. -/
theorem cubic_of_matched_real_actions {h : LieSubalgebra ℝ g} {l : LieSubalgebra ℝ k}
    {q : LieSubmodule ℝ h g} {p : LieSubmodule ℝ l k}
    (V : HermitianHalf h q) (W : HermitianHalf l p) (θ : h ≃ₗ⁅ℝ⁆ l)
    (R : (Fin V.dimension → ℂ) ≃ₗ[ℂ] (Fin W.dimension → ℂ))
    (hR : ∀ x : h, ∀ v, R (complexHermitianRepresentation V (1 ⊗ₜ[ℝ] x) *ᵥ v) =
      complexHermitianRepresentation W (1 ⊗ₜ[ℝ] (θ x)) *ᵥ R v) :
    ∀ x y z, matrixTraceCubic (V.generators x) (V.generators y) (V.generators z) =
      matrixTraceCubic (W.generators (θ x)) (W.generators (θ y)) (W.generators (θ z)) := by
  let M := Matrix.toLinAlgEquiv'.trans ((R.conjAlgEquiv ℂ).trans Matrix.toLinAlgEquiv'.symm)
  let a (x : h) := complexHermitianRepresentation V (1 ⊗ₜ[ℝ] x)
  let b (x : l) := complexHermitianRepresentation W (1 ⊗ₜ[ℝ] x)
  have heq (x : h) : M (a x) = b (θ x) := by
    apply Matrix.toLin'.injective
    change Matrix.toLin' (LinearMap.toMatrix' (R.conj (a x).toLin')) = _
    rw [Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    change R (a x *ᵥ R.symm v) = b (θ x) *ᵥ v
    simpa only [R.apply_symm_apply] using hR x (R.symm v)
  intro x y z
  apply mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero)
  rw [← hermitian_complex_cubic_real_inputs, ← hermitian_complex_cubic_real_inputs]
  change matrixTraceCubic (a x) (a y) (a z) = matrixTraceCubic (b (θ x)) (b (θ y)) (b (θ z))
  rw [← heq, ← heq, ← heq]
  unfold matrixTraceCubic
  simp only [← map_mul, ← map_add, Matrix.trace_map]

omit [Module.Finite ℝ g] [Module.Finite ℝ k] in
/-- The same isotropy equivalence identifies the full mixed cubic radicals. -/
theorem mem_radical_iff_of_matched_real_actions {h : LieSubalgebra ℝ g} {l : LieSubalgebra ℝ k}
    {q : LieSubmodule ℝ h g} {p : LieSubmodule ℝ l k}
    (V : HermitianHalf h q) (W : HermitianHalf l p) (θ : h ≃ₗ⁅ℝ⁆ l)
    (R : (Fin V.dimension → ℂ) ≃ₗ[ℂ] (Fin W.dimension → ℂ))
    (hR : ∀ x : h, ∀ v, R (complexHermitianRepresentation V (1 ⊗ₜ[ℝ] x) *ᵥ v) =
      complexHermitianRepresentation W (1 ⊗ₜ[ℝ] (θ x)) *ᵥ R v) (x : h) :
    x ∈ V.cubicRadical ↔ θ x ∈ W.cubicRadical := by
  rw [hermitian_half_cubic_radical_membership, hermitian_half_cubic_radical_membership]
  have same := cubic_of_matched_real_actions V W θ R hR
  constructor
  · intro hx y z
    obtain ⟨y, rfl⟩ := θ.surjective y
    obtain ⟨z, rfl⟩ := θ.surjective z
    exact (same x y z).symm.trans (hx y z)
  · intro hx y z
    rw [same, hx]

omit [Module.Finite ℝ g] [Module.Finite ℝ k] in
/-- An intertwiner of the actual actions transports the mixed cubic radical. -/
theorem radical_of_matched_real_actions {h : LieSubalgebra ℝ g} {l : LieSubalgebra ℝ k}
    {q : LieSubmodule ℝ h g} {p : LieSubmodule ℝ l k}
    (V : HermitianHalf h q) (W : HermitianHalf l p) (θ : h ≃ₗ⁅ℝ⁆ l)
    (R : (Fin V.dimension → ℂ) ≃ₗ[ℂ] (Fin W.dimension → ℂ))
    (hR : ∀ x : h, ∀ v, R (complexHermitianRepresentation V (1 ⊗ₜ[ℝ] x) *ᵥ v) =
      complexHermitianRepresentation W (1 ⊗ₜ[ℝ] (θ x)) *ᵥ R v)
    (hW : W.cubicRadical ≠ ⊥) : V.cubicRadical ≠ ⊥ := by
  have same := cubic_of_matched_real_actions V W θ R hR
  have hn : W.cubicRadical.toSubmodule ≠ ⊥ := fun hbot =>
    hW (LieSubmodule.toSubmodule_injective hbot)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let u := θ.symm v
  have hu : u ∈ V.cubicRadical := by
    apply (hermitian_half_cubic_radical_membership V u).mpr
    intro y z
    rw [same, show θ u = v from θ.apply_symm_apply _]
    exact (hermitian_half_cubic_radical_membership W v).mp hv _ _
  intro hb
  have hu0 : u = 0 := by simpa only [hb, LieSubmodule.mem_bot] using hu
  exact hv0 ((θ.apply_symm_apply v).symm.trans ((congrArg θ hu0).trans (map_zero θ)))


end CubicAnomaly.Classification.CanonicalHalfTransport
