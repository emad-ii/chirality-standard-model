import CubicAnomaly.Classification.CanonicalHalfTransport

/-! Transport of the compact form, isotropy, real commutant and its chosen
complex structure under a real Lie algebra equivalence. -/

namespace CubicAnomaly.Classification.CompactPairTransport

open Structural Complexification HermitianRealization
open scoped TensorProduct

noncomputable section

variable {g k : Type*} [LieRing g] [LieAlgebra ℝ g] [LieRing k] [LieAlgebra ℝ k]
    (f : g ≃ₗ⁅ℝ⁆ k) (B : CompactForm g) (h : LieSubalgebra ℝ g)

private def targetForm : CompactForm k where
  form := B.form.comp f.symm.toLinearMap f.symm.toLinearMap
  symmetric x y := B.symmetric _ _
  positive x hx := B.positive _ (fun he => hx (f.symm.injective (he.trans (map_zero f.symm).symm)))
  invariant x y z := by
    change B.form (f.symm ⁅x, y⁆) (f.symm z) = - B.form (f.symm y) (f.symm ⁅x, z⁆)
    rw [f.symm.map_lie, f.symm.map_lie, B.invariant]

private abbrev target := h.map f.toLieHom

private theorem target_mem (x : g) : f x ∈ target f h ↔ x ∈ h := by
  rw [LieSubalgebra.mem_map]
  exact ⟨fun ⟨y, hy, he⟩ => f.injective he ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

private theorem target_effective (ha : Effective h) : Effective (target f h) := by
  intro I hI
  have hz : I.comap f.toLieHom = ⊥ := ha _ (fun x hx => (target_mem f h x).mp (hI hx))
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨y, rfl⟩ := f.surjective x
  have hy : y ∈ I.comap f.toLieHom := hx
  rw [hz, LieSubmodule.mem_bot] at hy
  change f y = 0
  rw [hy, map_zero]

private theorem target_proper (hp : h ≠ ⊤) : target f h ≠ ⊤ := by
  intro he
  exact hp (top_unique fun x _ => (target_mem f h x).mp (he ▸ LieSubalgebra.mem_top _))

private theorem complement_image (x : g) :
    f x ∈ orthogonalComplement (targetForm f B) (target f h) ↔ x ∈ orthogonalComplement B h := by
  change (∀ z ∈ target f h, B.form (f.symm z) (f.symm (f x)) = 0) ↔ ∀ z ∈ h, B.form z x = 0
  simp only [f.symm_apply_apply]
  constructor
  · intro hx z hz
    simpa only [f.symm_apply_apply] using hx (f z) ((target_mem f h z).mpr hz)
  · intro hx z hz
    obtain ⟨w, rfl⟩ := f.surjective z
    change B.form (f.symm (f w)) x = 0
    rw [f.symm_apply_apply]
    exact hx w ((target_mem f h w).mp hz)

private def complementEquiv : orthogonalComplement B h ≃ₗ[ℝ]
    orthogonalComplement (targetForm f B) (target f h) where
  toFun x := ⟨f x.val, (complement_image f B h x.val).mpr x.property⟩
  invFun y := ⟨f.symm y.val, (complement_image f B h (f.symm y.val)).mp
    (by rw [f.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext (f.symm_apply_apply _)
  right_inv y := Subtype.ext (f.apply_symm_apply _)
  map_add' x y := Subtype.ext (map_add f _ _)
  map_smul' a x := Subtype.ext (map_smul f _ _)

private theorem equiv_act (x : h) (w : orthogonalComplement B h) :
    complementEquiv f B h ⁅x, w⁆ = ⁅(f.ofSubalgebras h (target f h) rfl) x, complementEquiv f B h w⁆ :=
  Subtype.ext (f.map_lie x.val w.val)

private def commutantEquiv : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ]
    lieCommutant (L := target f h) (M := orthogonalComplement (targetForm f B) (target f h)) := by
  let U := complementEquiv f B h
  let θ := f.ofSubalgebras h (target f h) rfl
  let D := U.conjAlgEquiv ℝ
  let S := lieCommutant (L := h) (M := orthogonalComplement B h)
  let T := lieCommutant (L := target f h) (M := orthogonalComplement (targetForm f B) (target f h))
  apply (D.subalgebraMap S).trans
  apply Subalgebra.equivOfEq _ T
  ext F
  constructor
  · rintro ⟨A, hA, rfl⟩ y v
    obtain ⟨x, rfl⟩ := θ.surjective y
    obtain ⟨w, rfl⟩ := U.surjective v
    change U (A (U.symm ⁅θ x, U w⁆)) = ⁅θ x, U (A (U.symm (U w)))⁆
    rw [← equiv_act f B h, U.symm_apply_apply, U.symm_apply_apply, hA x w, equiv_act f B h]
  · intro hF
    refine ⟨D.symm F, ?_, D.apply_symm_apply F⟩
    intro x w
    apply U.injective
    change U (U.symm (F (U ⁅x, w⁆))) = U ⁅x, U.symm (F (U w))⁆
    rw [U.apply_symm_apply, equiv_act f B h, equiv_act f B h, U.apply_symm_apply, hF]

variable (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)

private abbrev targetOrientation := (commutantEquiv f B h).symm.trans e

private theorem structure_equivariant (x : orthogonalComplement B h) :
    commutantComplexStructure (targetOrientation f B h e) (complementEquiv f B h x) =
    complementEquiv f B h (commutantComplexStructure e x) := by
  let U := complementEquiv f B h
  change U ((e.symm Complex.I).val (U.symm (U x))) = _
  rw [U.symm_apply_apply]
  rfl

private theorem half_image (a : ℂ) :
    ((ambientComplexifiedHalf (orthogonalComplement B h) (commutantComplexStructure e) a).toSubmodule.map
      (f.toLinearMap.baseChange ℂ)) =
    (ambientComplexifiedHalf (orthogonalComplement (targetForm f B) (target f h))
      (commutantComplexStructure (targetOrientation f B h e)) a).toSubmodule := by
  let P := orthogonalComplement B h
  let Q := orthogonalComplement (targetForm f B) (target f h)
  let U := LinearEquiv.baseChange ℝ ℂ P Q (complementEquiv f B h)
  let J := complexifiedEnd (commutantComplexStructure e)
  let J' := complexifiedEnd (commutantComplexStructure (targetOrientation f B h e))
  have hj (v : ℂ ⊗[ℝ] P) : J' (U v) = U (J v) := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul z v =>
      change z ⊗ₜ[ℝ] commutantComplexStructure _ (complementEquiv f B h v) =
        z ⊗ₜ[ℝ] complementEquiv f B h (commutantComplexStructure e v)
      rw [structure_equivariant]
    | add v w hv hw => simp only [map_add, hv, hw]
  have hv (v : ℂ ⊗[ℝ] P) : f.toLinearMap.baseChange ℂ (complexifiedHom P.incl v) =
      complexifiedHom Q.incl (U v) := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul z v => rfl
    | add v w h₁ h₂ => simp only [map_add, h₁, h₂]
  have he (v : ℂ ⊗[ℝ] P) : U v ∈ invariantEigenspace J' a ↔ v ∈ invariantEigenspace J a := by
    change J' (U v) - a • U v = 0 ↔ J v - a • v = 0
    rw [sub_eq_zero, sub_eq_zero, hj, ← U.map_smul, U.injective.eq_iff]
  ext x
  constructor
  · rintro ⟨_, ⟨v, hm, rfl⟩, rfl⟩
    exact ⟨U v, (he v).mpr hm, (hv v).symm⟩
  · rintro ⟨v, hm, rfl⟩
    obtain ⟨w, rfl⟩ := U.surjective v
    exact ⟨_, ⟨w, (he w).mp hm, rfl⟩, hv w⟩

variable [Module.Finite ℝ g] [Module.Finite ℝ k]

/-- A real Lie algebra equivalence transports every original hypothesis
to the image subalgebra, including the chosen matter orientation and the
nonzero radical of the full mixed anomaly. -/
theorem transport_pair_hypotheses (ha : Effective h) (hp : h ≠ ⊤)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥) :
    ∃ (C : CompactForm k) (l : LieSubalgebra ℝ k)
      (c : lieCommutant (L := l) (M := orthogonalComplement C l) ≃ₐ[ℝ] ℂ),
      h.map f.toLieHom = l ∧ Effective l ∧ l ≠ ⊤ ∧
      (hermitianHalfOfCommutant C l c).cubicRadical ≠ ⊥ := by
  let C := targetForm f B
  let l := target f h
  let c := targetOrientation f B h e
  refine ⟨C, l, c, rfl, target_effective f h ha, target_proper f h hp, ?_⟩
  obtain ⟨θ, R, hR⟩ := CanonicalHalfTransport.exists_positive_matrix_equiv B h e C l c f rfl
    (half_image f B h e Complex.I)
  apply CanonicalHalfTransport.radical_of_matched_real_actions _ _ θ.symm R.symm _ hr
  intro x v
  apply R.injective
  rw [R.apply_symm_apply, hR, θ.apply_symm_apply, R.apply_symm_apply]

end

end CubicAnomaly.Classification.CompactPairTransport
