import CubicAnomaly.Classification.CyclicBracket

/-!
# Involutions fixing a complex-type compact pair

The obstruction to a symmetric complement is independent of the chosen
invariant complement.  Transport through the actual quotient transfers the
complex structure, and positivity makes it skew for the restricted compact
form.  Consequently every involutive Lie automorphism fixing the isotropy
pointwise is the identity.  Preservation of a chosen positive form is not
an additional hypothesis.
-/

namespace CubicAnomaly.Classification.InvolutionObstruction

open CubicAnomaly.Classification.Structural
open CubicAnomaly.Classification.CyclicBracket
open CubicAnomaly.Classification.CompactKilling
open CubicAnomaly.Classification.HermitianRealization
open Submodule

noncomputable section

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- The fixed vectors of a Lie automorphism form an actual Lie subalgebra. -/
def automorphismFixedSubalgebra (σ : g ≃ₗ⁅ℝ⁆ g) : LieSubalgebra ℝ g where
  carrier := {x | σ x = x}
  zero_mem' := map_zero σ
  add_mem' := by
    intro x y (hx : σ x = x) (hy : σ y = y)
    change σ (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro a x (hx : σ x = x)
    change σ (a • x) = a • x
    rw [map_smul, hx]
  lie_mem' := by
    intro x y (hx : σ x = x) (hy : σ y = y)
    change σ ⁅x, y⁆ = ⁅x, y⁆
    rw [σ.map_lie, hx, hy]

/-- A nonidentity automorphism fixing a maximal proper subalgebra has
exactly that subalgebra as its fixed algebra. -/
theorem fixed_subalgebra_eq_of_maximal
    (h : LieSubalgebra ℝ g) (hmax : IsCoatom h)
    (σ : g ≃ₗ⁅ℝ⁆ g) (hσ : σ ≠ LieEquiv.refl)
    (hfix : ∀ x : h, σ x.val = x.val) : automorphismFixedSubalgebra σ = h := by
  have hle : h ≤ automorphismFixedSubalgebra σ := by
    intro x hx
    exact hfix ⟨x, hx⟩
  apply (hmax.le_iff_eq ?_).mp hle
  intro ht
  apply hσ
  ext x
  have hx : x ∈ automorphismFixedSubalgebra σ := by rw [ht]; trivial
  exact hx

/-- A centreless compact pair of complex type has no symmetric invariant
complement, including complements unrelated to the chosen orthogonal form. -/
theorem compact_complex_type_invariant_complement_nonsymmetric [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    (q : LieSubmodule ℝ h g) (hc : IsCompl h.toSubmodule q.toSubmodule) :
    ∃ x y : q, ⁅x.val, y.val⁆ ∉ h := by
  let q₀ := orthogonalComplement B h
  let hc₀ := compact_orthogonal_complement_isCompl B h
  let E : q ≃ₗ⁅ℝ,h⁆ q₀ :=
    (quotientComplementEquiv h q hc).symm.trans (quotientComplementEquiv h q₀ hc₀)
  have hq₀ : q₀ ≠ ⊥ := by
    intro hz
    have ht := hc₀.sup_eq_top
    have hz' : q₀.toSubmodule = ⊥ := congrArg LieSubmodule.toSubmodule hz
    rw [hz', sup_bot_eq] at ht
    exact hproper ((LieSubalgebra.toSubmodule_eq_top h).mp ht)
  letI : Nontrivial q₀ := (LieSubmodule.nontrivial_iff_ne_bot ℝ h g).mpr hq₀
  letI : LieModule.IsIrreducible ℝ h q₀ := compact_complex_commutant_irreducible B h q₀ e
  letI : LieModule.IsIrreducible ℝ h q :=
    (LieSubmodule.orderIsoMapComap E).isSimpleOrder_iff.mpr inferInstance
  let J₀ := commutantComplexStructure e
  have hJ₀ := commutant_complex_structure_square e
  let J : q →ₗ⁅ℝ,h⁆ q :=
    E.symm.toLieModuleHom.comp (J₀.comp E.toLieModuleHom)
  have hJ : ∀ x, J (J x) = -x := by
    intro x
    change E.symm (J₀ (E (E.symm (J₀ (E x))))) = -x
    rw [E.apply_symm_apply, hJ₀, map_neg, E.symm_apply_apply]
  let t : q₀ →ₗ⁅ℝ,h⁆ g := q.incl.comp E.symm.toLieModuleHom
  let Φ : LinearMap.BilinForm ℝ q₀ := B.form.compl₁₂ t.toLinearMap t.toLinearMap
  have hpos : ∀ x : q₀, x ≠ 0 → 0 < Φ x x := by
    intro x hx
    apply B.positive
    intro hz
    apply hx
    apply E.symm.injective
    exact Subtype.ext (by simpa only [map_zero] using hz)
  have hinv : Φ.lieInvariant h := by
    intro x y z
    change B.form (t ⁅x, y⁆) (t z) = -B.form (t y) (t ⁅x, z⁆)
    rw [t.map_lie, t.map_lie]
    exact B.invariant x.val (t y) (t z)
  have hskew₀ := complex_commutant_structure_skew Φ hpos hinv e
  have hskew : ∀ x y : q, B.form (J x) y = -B.form x (J y) := by
    intro x y
    have hs := hskew₀ (E x) (E y)
    change B.form (E.symm (J₀ (E x))) (E.symm (E y)) =
      -B.form (E.symm (E x)) (E.symm (J₀ (E y))) at hs
    simpa only [E.symm_apply_apply] using hs
  have hgcenter :=
    (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).2.2.1
  letI : LieAlgebra.IsKilling ℝ g := compact_centerless_isKilling B hgcenter
  by_contra hsymmetric
  push_neg at hsymmetric
  exact killing_symmetric_complex_complement_center_ne_bot B h q hc J hJ hskew
    hsymmetric hcenter

private def involutionNegativeSubmodule (h : LieSubalgebra ℝ g)
    (σ : g ≃ₗ⁅ℝ⁆ g) (hfix : ∀ x : h, σ x.val = x.val) : LieSubmodule ℝ h g where
  carrier := {x | σ x = -x}
  zero_mem' := by simp
  add_mem' := by
    intro x y (hx : σ x = -x) (hy : σ y = -y)
    change σ (x + y) = -(x + y)
    rw [map_add, hx, hy, neg_add]
  smul_mem' := by
    intro a x (hx : σ x = -x)
    change σ (a • x) = -(a • x)
    rw [map_smul, hx, smul_neg]
  lie_mem := by
    intro x y hy
    change σ ⁅x.val, y⁆ = -⁅x.val, y⁆
    rw [σ.map_lie, hfix, hy, lie_neg]

private theorem involution_eigenspaces_isCompl
    (h : LieSubalgebra ℝ g) (σ : g ≃ₗ⁅ℝ⁆ g)
    (hσ : Function.Involutive σ) (hfix : ∀ x : h, σ x.val = x.val)
    (hfixed : automorphismFixedSubalgebra σ = h) :
    IsCompl h.toSubmodule (involutionNegativeSubmodule h σ hfix).toSubmodule := by
  apply IsCompl.of_eq
  · apply le_antisymm _ bot_le
    rintro x ⟨hx, hneg⟩
    have hp : σ x = x := hfix ⟨x, hx⟩
    have hn : σ x = -x := hneg
    have htwo : (2 : ℝ) • x = 0 := by
      rw [two_smul, ← neg_eq_iff_add_eq_zero]
      exact hn.symm.trans hp
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · apply top_unique
    intro x _
    refine Submodule.mem_sup.mpr ⟨(1 / 2 : ℝ) • (x + σ x), ?_,
      (1 / 2 : ℝ) • (x - σ x), ?_, ?_⟩
    · rw [← hfixed]
      change σ ((1 / 2 : ℝ) • (x + σ x)) = (1 / 2 : ℝ) • (x + σ x)
      simp only [map_smul, map_add, hσ x, add_comm]
    · change σ ((1 / 2 : ℝ) • (x - σ x)) = -((1 / 2 : ℝ) • (x - σ x))
      simp only [map_smul, map_sub, hσ x, ← smul_neg, neg_sub]
    · have hadd : (x + σ x) + (x - σ x) = (2 : ℝ) • x := by
        rw [two_smul]
        abel
      rw [← smul_add, hadd, smul_smul]
      norm_num

/-- No nonidentity involutive Lie automorphism can fix the isotropy
pointwise in the original centreless compact complex-type domain. -/
theorem compact_complex_type_involution_eq_refl [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hcenter : LieAlgebra.center ℝ h = ⊥)
    (σ : g ≃ₗ⁅ℝ⁆ g) (hσ : Function.Involutive σ)
    (hfix : ∀ x : h, σ x.val = x.val) : σ = LieEquiv.refl := by
  by_contra hne
  have hmax := (compact_pair_reduction_to_semisimple_ambient B h heff hproper e).1
  have hfixed := fixed_subalgebra_eq_of_maximal h hmax σ hne hfix
  let q := involutionNegativeSubmodule h σ hfix
  have hc := involution_eigenspaces_isCompl h σ hσ hfix hfixed
  obtain ⟨x, y, hxy⟩ :=
    compact_complex_type_invariant_complement_nonsymmetric B h heff hproper e hcenter q hc
  apply hxy
  apply (show automorphismFixedSubalgebra σ ≤ h from le_of_eq hfixed)
  change σ ⁅x.val, y.val⁆ = ⁅x.val, y.val⁆
  have hx : σ x.val = -x.val := x.property
  have hy : σ y.val = -y.val := y.property
  rw [σ.map_lie, hx, hy, neg_lie, lie_neg, neg_neg]

/-- The full nonzero anomaly hypothesis excludes every nonidentity
involution fixing the isotropy, without an isometry assumption. -/
theorem all_rank_anomalous_involution_eq_refl [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hradical : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    (σ : g ≃ₗ⁅ℝ⁆ g) (hσ : Function.Involutive σ)
    (hfix : ∀ x : h, σ x.val = x.val) : σ = LieEquiv.refl := by
  letI : LieAlgebra.IsSemisimple ℝ h :=
    (all_rank_structural_reduction_of_commutant B h heff hproper e hradical).2.2.2.1
  exact compact_complex_type_involution_eq_refl B h heff hproper e
    (LieAlgebra.center_eq_bot ℝ h) σ hσ hfix

end

end CubicAnomaly.Classification.InvolutionObstruction
