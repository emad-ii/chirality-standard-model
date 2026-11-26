import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# The actual compact Standard Model group and its central cover

This module constructs `S(U(3) × U(2))` as a determinant kernel of actual
unitary matrix groups.  Its cover is the literal scalar-block map from
`SU(3) × SU(2) × U(1)`.  These constructions do not assume an exceptional
embedding or a representation branching statement.
-/

noncomputable section

namespace CubicAnomaly.Fixed.StandardModelGroup

abbrev Phase := unitary ℂ
abbrev Unitary (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ

/-- The determinant of an actual unitary matrix is an actual unit phase. -/
def determinant (n : ℕ) : Unitary n →* Phase where
  toFun A := ⟨Matrix.det A.val, Matrix.det_of_mem_unitary A.prop⟩
  map_one' := Subtype.ext Matrix.det_one
  map_mul' A B := Subtype.ext (Matrix.det_mul A.val B.val)

/-- Special unitary matrices, presented as the determinant kernel. -/
abbrev SpecialUnitary (n : ℕ) := (determinant n).ker

/-- The product of the two block determinants. -/
def blockDeterminant : (Unitary 3 × Unitary 2) →* Phase :=
  ((determinant 3).comp (MonoidHom.fst _ _)) *
    ((determinant 2).comp (MonoidHom.snd _ _))

/-- The concrete compact group `S(U(3) × U(2))`. -/
abbrev GaugeGroup := blockDeterminant.ker

/-- The product cover before its central kernel is divided out. -/
abbrev Cover := (SpecialUnitary 3 × SpecialUnitary 2) × Phase

/-- Scalar multiplication, with the scalar coercion fixed explicitly. -/
def scale (n : ℕ) (z : Phase) (A : Unitary n) : Unitary n :=
  ⟨(z : ℂ) • A.val, _root_.Unitary.smul_mem z A.prop⟩

private theorem scale_scale (n : ℕ) (z w : Phase) (A : Unitary n) :
    scale n z (scale n w A) = scale n (z * w) A :=
  Subtype.ext (smul_smul (z : ℂ) (w : ℂ) A.val)

private theorem scale_one (n : ℕ) (A : Unitary n) : scale n 1 A = A :=
  Subtype.ext (one_smul ℂ A.val)

/-- Multiplication of a special unitary matrix by a scalar phase. -/
def scalarBlock (n : ℕ) : (SpecialUnitary n × Phase) →* Unitary n where
  toFun p := scale n p.2 p.1.val
  map_one' := scale_one n 1
  map_mul' p q := Subtype.ext (by
    change ((p.2 : ℂ) * (q.2 : ℂ)) • (p.1.val.val * q.1.val.val) =
      ((p.2 : ℂ) • p.1.val.val) * ((q.2 : ℂ) • q.1.val.val)
    simp [smul_smul, mul_comm])

/-- Determinants of the literal scalar blocks. -/
theorem scalar_block_determinant (n : ℕ) (A : SpecialUnitary n) (z : Phase) :
    determinant n (scalarBlock n (A, z)) = z ^ n := by
  apply Subtype.ext
  have hA : Matrix.det A.val.val = 1 := congrArg Subtype.val A.prop
  simp [determinant, scalarBlock, scale, hA]

/-- Scaling any unitary matrix multiplies its determinant by the phase power. -/
theorem phase_scale_determinant (n : ℕ) (z : Phase) (A : Unitary n) :
    determinant n (scale n z A) = z ^ n * determinant n A := by
  apply Subtype.ext
  simp [determinant, scale]

/-- The colour and weak scalar exponents are the primitive pair `(-2, 3)`. -/
def coverBlocks : Cover →* (Unitary 3 × Unitary 2) where
  toFun p := (scalarBlock 3 (p.1.1, p.2 ^ (-2 : ℤ)),
    scalarBlock 2 (p.1.2, p.2 ^ (3 : ℤ)))
  map_one' := by
    change (scalarBlock 3 (1, 1 ^ (-2 : ℤ)), scalarBlock 2 (1, 1 ^ (3 : ℤ))) = 1
    simp only [one_zpow]
    exact Prod.ext (map_one (scalarBlock 3)) (map_one (scalarBlock 2))
  map_mul' p q := by
    change (scalarBlock 3 (p.1.1 * q.1.1, (p.2 * q.2) ^ (-2 : ℤ)),
      scalarBlock 2 (p.1.2 * q.1.2, (p.2 * q.2) ^ (3 : ℤ))) = _
    simp only [mul_zpow, ← Prod.mk_mul_mk, map_mul]

/-- The scalar exponents make the total determinant exactly one. -/
theorem cover_blocks_determinant (p : Cover) : blockDeterminant (coverBlocks p) = 1 := by
  change determinant 3 (scalarBlock 3 (p.1.1, p.2 ^ (-2 : ℤ))) *
    determinant 2 (scalarBlock 2 (p.1.2, p.2 ^ (3 : ℤ))) = 1
  rw [scalar_block_determinant, scalar_block_determinant]
  simp only [← zpow_natCast, ← zpow_mul, ← zpow_add]
  norm_num

/-- The actual scalar-block covering homomorphism. -/
def cover : Cover →* GaugeGroup := coverBlocks.codRestrict GaugeGroup cover_blocks_determinant

/-- A complex number of norm one is a unit phase. -/
private theorem phase_mem_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) : w ∈ unitary ℂ := by
  have h : w * star w = 1 := by
    change w * (starRingEnd ℂ) w = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    norm_num
  exact ⟨by simpa [mul_comm] using h, h⟩

/-- Every unit phase has an `n`th root which is itself a unit phase. -/
theorem phase_power_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun z : Phase => z ^ n) := by
  intro z
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) hn
  have hnorm : ‖w‖ ^ n = 1 := by
    rw [← norm_pow, hw, CStarRing.norm_coe_unitary]
  have hwnorm : ‖w‖ = 1 :=
    (pow_left_inj₀ (norm_nonneg w) zero_le_one hn.ne').mp (by simpa using hnorm)
  exact ⟨⟨w, phase_mem_of_norm_one hwnorm⟩, Subtype.ext hw⟩

/-- The concrete scalar-block map covers every determinant-one pair of blocks. -/
theorem standard_model_cover_surjective : Function.Surjective cover := by
  intro p
  obtain ⟨z, hz⟩ := phase_power_surjective 6 (by decide) (determinant 2 p.val.2)
  have hp : determinant 3 p.val.1 * determinant 2 p.val.2 = 1 := p.prop
  have hA : determinant 3 (scale 3 (z ^ (2 : ℤ)) p.val.1) = 1 := by
    rw [phase_scale_determinant, ← zpow_natCast, ← zpow_mul]
    change z ^ (6 : ℕ) * determinant 3 p.val.1 = 1
    exact (congrArg (fun w : Phase => w * determinant 3 p.val.1) hz).trans
      ((mul_comm _ _).trans hp)
  have hB : determinant 2 (scale 2 (z ^ (-3 : ℤ)) p.val.2) = 1 := by
    rw [phase_scale_determinant, ← zpow_natCast, ← zpow_mul]
    change (z ^ (6 : ℕ))⁻¹ * determinant 2 p.val.2 = 1
    rw [← hz]
    simp
  let A : SpecialUnitary 3 := ⟨scale 3 (z ^ (2 : ℤ)) p.val.1, hA⟩
  let B : SpecialUnitary 2 := ⟨scale 2 (z ^ (-3 : ℤ)) p.val.2, hB⟩
  refine ⟨((A, B), z), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change scale 3 (z ^ (-2 : ℤ)) (scale 3 (z ^ (2 : ℤ)) p.val.1) = p.val.1
    rw [scale_scale, ← zpow_add]
    norm_num [scale_one]
  · change scale 2 (z ^ (3 : ℤ)) (scale 2 (z ^ (-3 : ℤ)) p.val.2) = p.val.2
    rw [scale_scale, ← zpow_add]
    norm_num [scale_one]

/-- The quotient by the actual covering kernel is the actual compact gauge group. -/
def quotientCoverEquiv : Cover ⧸ cover.ker ≃* GaugeGroup :=
  QuotientGroup.quotientKerEquivOfSurjective cover standard_model_cover_surjective

/-- An exact description of the central kernel, with sixth-root phase parameter. -/
theorem standard_model_cover_kernel (p : Cover) :
    cover p = 1 ↔ p.2 ^ (6 : ℕ) = 1 ∧
      p.1.1.val = scale 3 (p.2 ^ (2 : ℤ)) 1 ∧
      p.1.2.val = scale 2 (p.2 ^ (-3 : ℤ)) 1 := by
  constructor
  · intro h
    have hraw : coverBlocks p = 1 := congrArg Subtype.val h
    have ha : scale 3 (p.2 ^ (-2 : ℤ)) p.1.1.val = 1 := congrArg Prod.fst hraw
    have hb : scale 2 (p.2 ^ (3 : ℤ)) p.1.2.val = 1 := congrArg Prod.snd hraw
    have hA : p.1.1.val = scale 3 (p.2 ^ (2 : ℤ)) 1 := by
      have hh := congrArg (scale 3 (p.2 ^ (2 : ℤ))) ha
      simpa only [scale_scale, ← zpow_add, show (2 : ℤ) + -2 = 0 from rfl,
        zpow_zero, scale_one] using hh
    have hB : p.1.2.val = scale 2 (p.2 ^ (-3 : ℤ)) 1 := by
      have hh := congrArg (scale 2 (p.2 ^ (-3 : ℤ))) hb
      simpa only [scale_scale, ← zpow_add, show (-3 : ℤ) + 3 = 0 from rfl,
        zpow_zero, scale_one] using hh
    refine ⟨?_, hA, hB⟩
    have hd := congrArg (determinant 3) hA
    rw [show determinant 3 p.1.1.val = 1 from p.1.1.prop,
      phase_scale_determinant, map_one, mul_one, ← zpow_natCast, ← zpow_mul] at hd
    simpa using hd.symm
  · rintro ⟨_, ha, hb⟩
    apply Subtype.ext
    apply Prod.ext
    · change scale 3 (p.2 ^ (-2 : ℤ)) p.1.1.val = 1
      rw [ha, scale_scale, ← zpow_add]
      norm_num [scale_one]
    · change scale 2 (p.2 ^ (3 : ℤ)) p.1.2.val = 1
      rw [hb, scale_scale, ← zpow_add]
      norm_num [scale_one]

/-- Projection of the actual covering kernel to the sixth roots of unity. -/
def kernelRootHom : cover.ker →* rootsOfUnity 6 ℂ where
  toFun p := ⟨_root_.Unitary.toUnits p.val.2, by
    rw [mem_rootsOfUnity, ← map_pow,
      ((standard_model_cover_kernel p.val).mp p.prop).1, map_one]⟩
  map_one' := Subtype.ext (map_one _root_.Unitary.toUnits)
  map_mul' p q := Subtype.ext (map_mul _root_.Unitary.toUnits p.val.2 q.val.2)

/-- A kernel element is completely determined by its phase. -/
theorem standard_model_kernel_root_injective : Function.Injective kernelRootHom := by
  intro p q h
  have hz : p.val.2 = q.val.2 :=
    _root_.Unitary.toUnits_injective (congrArg Subtype.val h)
  have hp := (standard_model_cover_kernel p.val).mp p.prop
  have hq := (standard_model_cover_kernel q.val).mp q.prop
  apply Subtype.ext
  refine Prod.ext (Prod.ext ?_ ?_) hz
  · apply Subtype.ext
    rw [hp.2.1, hq.2.1, hz]
  · apply Subtype.ext
    rw [hp.2.2, hq.2.2, hz]

/-- Every sixth root occurs as the phase of an actual kernel element. -/
theorem standard_model_kernel_root_surjective : Function.Surjective kernelRootHom := by
  intro u
  have hu : (u.val : ℂ) ^ (6 : ℕ) = 1 := (mem_rootsOfUnity' 6 u.val).mp u.prop
  have hn : ‖(u.val : ℂ)‖ ^ (6 : ℕ) = 1 := by rw [← norm_pow, hu, norm_one]
  have hnorm : ‖(u.val : ℂ)‖ = 1 :=
    (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (6 : ℕ) ≠ 0)).mp
      (by simpa using hn)
  let z : Phase := ⟨u.val, phase_mem_of_norm_one hnorm⟩
  have hz : z ^ (6 : ℕ) = 1 := Subtype.ext hu
  have hA : determinant 3 (scale 3 (z ^ (2 : ℤ)) 1) = 1 := by
    rw [phase_scale_determinant, map_one, mul_one, ← zpow_natCast, ← zpow_mul]
    exact hz
  have hB : determinant 2 (scale 2 (z ^ (-3 : ℤ)) 1) = 1 := by
    rw [phase_scale_determinant, map_one, mul_one, ← zpow_natCast, ← zpow_mul]
    change (z ^ (6 : ℕ))⁻¹ = 1
    rw [hz, inv_one]
  let A : SpecialUnitary 3 := ⟨scale 3 (z ^ (2 : ℤ)) 1, hA⟩
  let B : SpecialUnitary 2 := ⟨scale 2 (z ^ (-3 : ℤ)) 1, hB⟩
  let p : Cover := ((A, B), z)
  have hp : cover p = 1 := (standard_model_cover_kernel p).mpr ⟨hz, rfl, rfl⟩
  exact ⟨⟨p, hp⟩, Subtype.ext (Units.ext rfl)⟩

/-- The central kernel is the actual group of sixth roots of unity. -/
def kernelRootsEquiv : cover.ker ≃* rootsOfUnity 6 ℂ :=
  MulEquiv.ofBijective kernelRootHom
    ⟨standard_model_kernel_root_injective, standard_model_kernel_root_surjective⟩

/-- The actual covering kernel has exactly six elements. -/
theorem standard_model_kernel_card : Nat.card cover.ker = 6 := by
  rw [Nat.card_congr kernelRootsEquiv.toEquiv, Nat.card_eq_fintype_card,
    Complex.card_rootsOfUnity]

/-- The six-element kernel is cyclic. -/
theorem standard_model_kernel_cyclic : IsCyclic cover.ker :=
  isCyclic_of_injective kernelRootHom standard_model_kernel_root_injective

private theorem scalar_central (n : ℕ) (z : Phase) (A : Unitary n) :
    scale n z 1 * A = A * scale n z 1 := by
  apply Subtype.ext
  change ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * A.val =
    A.val * ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
  simp

/-- The literal six-element kernel lies in the centre of the product cover. -/
theorem standard_model_kernel_central : cover.ker ≤ Subgroup.center Cover := by
  intro p hp
  have h := (standard_model_cover_kernel p).mp hp
  rw [Subgroup.mem_center_iff]
  intro q
  refine Prod.ext (Prod.ext ?_ ?_) (mul_comm _ _)
  · apply Subtype.ext
    change q.1.1.val * p.1.1.val = p.1.1.val * q.1.1.val
    rw [h.2.1]
    exact (scalar_central 3 _ _).symm
  · apply Subtype.ext
    change q.1.2.val * p.1.2.val = p.1.2.val * q.1.2.val
    rw [h.2.2]
    exact (scalar_central 2 _ _).symm

/-- A power character is trivial on all sixth roots exactly at multiples of six. -/
theorem sixth_root_character_trivial_iff (n : ℤ) :
    (∀ u : rootsOfUnity 6 ℂ, u.val ^ n = 1) ↔ (6 : ℤ) ∣ n := by
  constructor
  · intro h
    have hζ := Complex.isPrimitiveRoot_exp 6 (by decide)
    let u : rootsOfUnity 6 ℂ := rootsOfUnity.mkOfPowEq _ hζ.pow_eq_one
    have hu : IsPrimitiveRoot u.val 6 := IsPrimitiveRoot.coe_units_iff.mp hζ
    exact (hu.zpow_eq_one_iff_dvd n).mp (h u)
  · rintro ⟨k, rfl⟩ u
    rw [zpow_mul]
    change (u.val ^ (6 : ℕ)) ^ k = 1
    rw [(mem_rootsOfUnity 6 u.val).mp u.prop, one_zpow]

/-- The scalar character of a kernel element with integer hypercharge `q`,
colour triality representative `t`, and weak parity representative `s`. -/
def centralChargeCharacter (q t s : ℤ) : cover.ker →* ℂˣ :=
  (zpowGroupHom (q + 2 * t - 3 * s)).comp
    ((rootsOfUnity 6 ℂ).subtype.comp kernelRootHom)

/-- The actual central kernel gives the Standard Model charge congruence. -/
theorem standard_model_charge_lattice (q t s : ℤ) :
    (∀ k : cover.ker, centralChargeCharacter q t s k = 1) ↔
      (6 : ℤ) ∣ q + 2 * t + 3 * s := by
  have hbase : (∀ k : cover.ker, centralChargeCharacter q t s k = 1) ↔
      (6 : ℤ) ∣ q + 2 * t - 3 * s := by
    rw [← sixth_root_character_trivial_iff]
    constructor
    · intro h u
      obtain ⟨k, hk⟩ := standard_model_kernel_root_surjective u
      have hh := h k
      change (kernelRootHom k).val ^ (q + 2 * t - 3 * s) = 1 at hh
      simpa only [hk] using hh
    · intro h k
      exact h (kernelRootHom k)
  rw [hbase]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + s, ?_⟩
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨k - s, ?_⟩
    linarith

/-- Actual group homomorphisms descend along the constructed surjection
exactly when they kill its kernel. -/
theorem standard_model_hom_descends_iff {G : Type*} [Group G] (ρ : Cover →* G) :
    (∃ φ : GaugeGroup →* G, φ.comp cover = ρ) ↔ cover.ker ≤ ρ.ker := by
  constructor
  · rintro ⟨φ, hφ⟩ p hp
    have heq := congrArg (fun f : Cover →* G => f p) hφ
    change φ (cover p) = ρ p at heq
    have hcover : cover p = 1 := hp
    rw [hcover, map_one] at heq
    exact heq.symm
  · intro h
    let φ : GaugeGroup →* G :=
      (QuotientGroup.lift cover.ker ρ h).comp quotientCoverEquiv.symm.toMonoidHom
    refine ⟨φ, ?_⟩
    apply MonoidHom.ext
    intro p
    change (QuotientGroup.lift cover.ker ρ h) (quotientCoverEquiv.symm (cover p)) = ρ p
    have hp : quotientCoverEquiv (QuotientGroup.mk p) = cover p := rfl
    rw [← hp, MulEquiv.symm_apply_apply]
    rfl

/-- For an actual representation whose scalar central action has charges
`(q,t,s)`, descent is equivalent to the derived charge-lattice congruence.
The scalar-action hypothesis states the character being tested; it does not
assume the congruence or the existence of a descended representation. -/
theorem standard_model_representation_descent_charge_iff
    {G : Type*} [Group G] (ρ : Cover →* G) (ι : ℂˣ →* G)
    (hι : Function.Injective ι) (q t s : ℤ)
    (hcentral : ∀ k : cover.ker, ρ k.val = ι (centralChargeCharacter q t s k)) :
    (∃ φ : GaugeGroup →* G, φ.comp cover = ρ) ↔
      (6 : ℤ) ∣ q + 2 * t + 3 * s := by
  rw [standard_model_hom_descends_iff, ← standard_model_charge_lattice]
  constructor
  · intro h k
    apply hι
    rw [map_one, ← hcentral]
    exact h k.prop
  · intro h k hk
    change ρ k = 1
    rw [hcentral ⟨k, hk⟩, h, map_one]

/-- The actual colour-plus-weak index set has five coordinates. -/
abbrev FiveIndex := Fin 3 ⊕ Fin 2

set_option maxRecDepth 2048 in
/-- The faithful block embedding in the actual special unitary matrix group
on the five-dimensional colour-plus-weak space. -/
def blockEmbedding : GaugeGroup →* Matrix.specialUnitaryGroup FiveIndex ℂ where
  toFun p := ⟨Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val, by
    constructor
    · change Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val ∈
        Matrix.unitaryGroup FiveIndex ℂ
      rw [Matrix.mem_unitaryGroup_iff]
      change Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val *
        (Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val).conjTranspose = 1
      rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      have hA : p.val.1.val * p.val.1.val.conjTranspose = 1 := p.val.1.prop.2
      have hB : p.val.2.val * p.val.2.val.conjTranspose = 1 := p.val.2.prop.2
      simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
        add_zero, zero_add, hA, hB, Matrix.fromBlocks_one]
    · change (Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val).det = 1
      rw [Matrix.det_fromBlocks_zero₂₁]
      have hp : determinant 3 p.val.1 * determinant 2 p.val.2 = 1 := p.prop
      exact congrArg Subtype.val hp⟩
  map_one' := Subtype.ext Matrix.fromBlocks_one
  map_mul' p q := Subtype.ext (by
    change Matrix.fromBlocks (p.val.1.val * q.val.1.val) 0 0
        (p.val.2.val * q.val.2.val) =
      Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val *
        Matrix.fromBlocks q.val.1.val 0 0 q.val.2.val
    simp [Matrix.fromBlocks_multiply])

/-- The displayed Standard Model action on the five coordinates is faithful. -/
theorem standard_model_block_embedding_injective : Function.Injective blockEmbedding := by
  intro p q h
  have hh := Matrix.fromBlocks_inj.mp (congrArg Subtype.val h)
  exact Subtype.ext (Prod.ext (Subtype.ext hh.1) (Subtype.ext hh.2.2.2))

/-- Restricting the cover to its circle factor gives the primitive
`diag(z⁻² I₃, z³ I₂)` subgroup inside the actual special unitary group. -/
theorem standard_model_circle_blocks (z : Phase) :
    (blockEmbedding (cover ((1, 1), z))).val =
      Matrix.fromBlocks ((z ^ (-2 : ℤ) : Phase).val • (1 : Matrix (Fin 3) (Fin 3) ℂ))
        0 0 ((z ^ (3 : ℤ) : Phase).val • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := rfl

/-- The central circle in the determinant-one block subgroup. -/
def centralCircle : Phase →* GaugeGroup := cover.comp {
  toFun z := ((1, 1), z)
  map_one' := rfl
  map_mul' z w := by simp
}

/-- The exponents `(-2,3)` traverse the central circle once: the circle
homomorphism is injective, so no smaller quotient is hidden in it. -/
theorem standard_model_central_circle_injective : Function.Injective centralCircle := by
  apply (injective_iff_map_eq_one centralCircle).mpr
  intro z hz
  have h := (standard_model_cover_kernel ((1, 1), z)).mp hz
  have htwo : z ^ (2 : ℤ) = 1 := by
    apply Subtype.ext
    have hh := congrArg (fun A : Unitary 3 => A.val 0 0) h.2.1
    simpa [scale] using hh.symm
  have hthree : z ^ (-3 : ℤ) = 1 := by
    apply Subtype.ext
    have hh := congrArg (fun A : Unitary 2 => A.val 0 0) h.2.2
    simpa [scale] using hh.symm
  calc
    z = (z ^ (2 : ℤ)) ^ (2 : ℤ) * z ^ (-3 : ℤ) := by
      rw [← zpow_mul, ← zpow_add]
      norm_num
    _ = 1 := by rw [htwo, hthree]; simp

end CubicAnomaly.Fixed.StandardModelGroup
