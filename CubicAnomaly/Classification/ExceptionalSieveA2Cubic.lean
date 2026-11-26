import CubicAnomaly.Classification.ExceptionalSieveWeightOrbit
import CubicAnomaly.Classification.ExceptionalSieveNormalization
import CubicAnomaly.Classification.AllRankComplex

/-! # A quadratic-index obstruction to a vanishing A₂ cubic

On a pair of Weyl-related integral labels the quadratic moment on one
coroot is congruent modulo four to twice the mixed cubic on two adjacent
coroots. This tests the actual mixed cubic via its quadratic trace index.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveA2Cubic

open LieAlgebra LieModule Module LieAlgebra.IsKilling ClassicalConstituentWeyl
open ExceptionalSieveWeightOrbit ExceptionalSieveWeights WeightCubic

private theorem paired_congruence {ι : Type*} [Fintype ι]
    (r : Equiv.Perm ι) (a b m : ι → ℤ) (ha : ∀ i, a (r i) = -a i)
    (hb : ∀ i, b (r i) = b i + a i) (hm : ∀ i, m (r i) = m i) :
    (4 : ℤ) ∣ (∑ i, m i * a i ^ 2) - 2 * ∑ i, m i * a i ^ 2 * b i := by
  classical
  let q i := m i * a i ^ 2 - 2 * (m i * a i ^ 2 * b i)
  let lo i := if a i < 0 then q i else 0
  have split : ∑ i, q i = ∑ i, if 0 < a i then q i + q (r i) else 0 := by
    calc
      _ = (∑ i, if 0 < a i then q i else 0) + ∑ i, lo i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rcases lt_trichotomy (a i) 0 with h | h | h <;> simp [q, lo, h, not_lt_of_ge h.le]
      _ = _ := by
        rw [← Equiv.sum_comp r lo, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : 0 < a i <;> simp [lo, ha, h]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  change 4 ∣ ∑ i, q i
  rw [split]
  apply Finset.dvd_sum
  intro i _
  split_ifs with hi
  · simp only [q, ha, hb, hm]
    rcases (a i).even_or_odd with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨2 * m i * t^2 * (1 - 2*t - 2*b i), ?_⟩
      rw [ht]
      ring
    · refine ⟨-(m i * (2*t+1)^2 * (t+b i)), ?_⟩
      rw [ht]
      ring
  · exact dvd_zero _

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

private noncomputable def reflected (α : H.root) (μ : Weight ℂ H M) : Weight ℂ H M := by
  let T := (rootSystem H).coreflection α
  let ν : H → ℂ := fun z => μ (T z)
  have eqd := multiplicity_of_weyl_word (M := M) H [α] μ ν (by
    intro z
    change μ ((rootSystem H).coreflection α ((rootSystem H).coreflection α z)) = μ z
    simp)
  refine ⟨ν, ?_⟩
  intro hz
  rw [hz] at eqd
  obtain ⟨v, hv, hv0⟩ := μ.exists_ne_zero
  haveI : Nontrivial (genWeightSpace M μ) := ⟨⟨⟨v,hv⟩, 0, fun hh => hv0 (congrArg Subtype.val hh)⟩⟩
  have hpos := finrank_pos (R := ℂ) (M := genWeightSpace M μ)
  have hbot : finrank ℂ (⊥ : LieSubmodule ℂ H M) = 0 := finrank_zero_of_subsingleton
  omega

private noncomputable def reflection (α : H.root) : Equiv.Perm (Weight ℂ H M) :=
  { toFun := reflected H α
    invFun := reflected H α
    left_inv := fun μ => Weight.ext fun h => by
      change μ ((rootSystem H).coreflection α ((rootSystem H).coreflection α h)) = μ h
      simp
    right_inv := fun μ => Weight.ext fun h => by
      change μ ((rootSystem H).coreflection α ((rootSystem H).coreflection α h)) = μ h
      simp }

/-- A vanishing mixed cubic on two adjacent coroots forces the quadratic
trace on the first one to be an integer multiple of four. -/
theorem four_dvd_trace_of_zero_cubic (α β : H.root) (hab : α.val (coroot β.val) = -1)
    (hc : ∑ χ : Weight ℂ H M, (finrank ℂ (genWeightSpace M χ) : ℂ) *
      (χ (coroot α.val) * χ (coroot α.val) * χ (coroot β.val)) = 0) :
    ∃ n : ℤ, traceForm ℂ L M (coroot α.val : L) (coroot α.val : L) = 4 * n := by
  classical
  let r := reflection (M := M) H α
  choose a ha using fun χ : Weight ℂ H M => weight_coroot_mem_integer_interval H χ α
  choose b hb using fun χ : Weight ℂ H M => weight_coroot_mem_integer_interval H χ β
  let m (χ : Weight ℂ H M) : ℤ := finrank ℂ (genWeightSpace M χ)
  have rA (χ) : a (r χ) = -a χ := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_neg, ← (ha _).1, ← (ha _).1]
    change χ ((rootSystem H).coreflection α ((rootSystem H).coroot α)) = -χ (coroot α.val)
    rw [RootPairing.coreflection_apply_self]
    exact map_neg (χ : Dual ℂ H) _
  have rB (χ) : b (r χ) = b χ + a χ := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_add, ← (hb _).1, ← (hb _).1, ← (ha _).1]
    change χ ((rootSystem H).coreflection α ((rootSystem H).coroot β)) = _
    rw [RootPairing.coreflection_apply_coroot]
    change (χ : Dual ℂ H) (coroot β.val - α.val (coroot β.val) • coroot α.val) = _
    rw [hab, neg_one_smul, sub_neg_eq_add, map_add]
    rfl
  have rM (χ) : m (r χ) = m χ := by
    apply congrArg Nat.cast
    apply (multiplicity_of_weyl_word (M := M) H [α] _ _ _).symm
    intro z
    change χ ((rootSystem H).coreflection α ((rootSystem H).coreflection α z)) = χ z
    simp
  have hc' : ∑ χ, m χ * a χ ^ 2 * b χ = 0 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    simpa only [m, Int.cast_natCast, sq, ← (ha _).1, ← (hb _).1, mul_assoc] using hc
  obtain ⟨n, hn⟩ := paired_congruence r a b m rA rB rM
  rw [hc', mul_zero, sub_zero] at hn
  refine ⟨n, ?_⟩
  change traceForm ℂ H M (coroot α.val) (coroot α.val) = _
  rw [LieModule.traceForm_eq_sum_finrank_nsmul_mul]
  have eqc := congrArg (Int.cast (R := ℂ)) hn
  push_cast at eqc
  simpa only [m, Int.cast_natCast, sq, nsmul_eq_mul, ← (ha _).1] using eqc


open ExceptionalSieveCatalog ExceptionalSieveNormalization Exceptional RootClassificationExceptional

/-- Neither 35-dimensional A₂ representation of highest labels (4,1) or
(1,4) has zero mixed Cartan cubic. The actual long-coroot trace equals
210, which is not divisible by four. -/
theorem a2_thirty_five_has_cubic [IsSimple ℂ L] [IsIrreducible ℂ L M]
    (b : (rootSystem H).Base) (s : Index (Factor.a 1).datum ≃ b.support)
    (hm : ∀ i j, b.cartanMatrix (s i) (s j) = matrix (Factor.a 1).datum i j)
    (χ : Dual ℂ H) (a : (Factor.a 1).Label)
    (ha : ∀ i, χ (coroot (s i).val.val) = (a (nodes (.a 1) i) : ℂ))
    (hrow : a = ![4,1] ∨ a = ![1,4]) (hd : finrank ℂ M = 35) {v : M} (hv : v ≠ 0)
    (hev : ∀ h : H, ⁅h,v⁆ = χ h • v)
    (hkill : ∀ α : H.root, b.IsPos α → ∀ z ∈ rootSpace H α.val, ⁅z,v⁆ = 0) :
    ∃ α β : H.root, ∑ μ : Weight ℂ H M, (finrank ℂ (genWeightSpace M μ) : ℂ) *
      (μ (coroot α.val) * μ (coroot α.val) * μ (coroot β.val)) ≠ 0 := by
  obtain ⟨i, hiκ, htr⟩ := actual_long_coroot_trace H b (.a 1) s hm χ a ha hv hev hkill
  obtain ⟨j, hj⟩ : ∃ j : Index (Factor.a 1).datum, matrix (Factor.a 1).datum i j = -1 := by
    have h : ∀ i : Index (Factor.a 1).datum, ∃ j, matrix (Factor.a 1).datum i j = -1 := by decide
    exact h i
  let α : H.root := (s i).val
  let β : H.root := (s j).val
  have hp : α.val (coroot β.val) = -1 := by
    have he := b.algebraMap_cartanMatrixIn_apply ℤ (s i) (s j)
    change ((b.cartanMatrix (s i) (s j) : ℤ) : ℂ) = α.val (coroot β.val) at he
    rw [← he, hm, hj]
    norm_num
  have hc : (Factor.a 1).casimir a = 24 := by
    have sum₂ (f : (Factor.a 1).Node → ℚ) : ∑ k, f k = f (0 : Fin 2) + f (1 : Fin 2) :=
      Fin.sum_univ_two f
    rcases hrow with rfl | rfl <;> norm_num [Factor.casimir, sum₂, Factor.gram, Factor.rank, Fin.isValue]
  change killingForm ℂ L (coroot α.val : L) (coroot α.val : L) +
    2 * traceForm ℂ L M (coroot α.val : L) (coroot α.val : L) = _ at htr
  rw [hiκ, hd, hc] at htr
  norm_num [show (Factor.a 1).algebraDim = 8 by decide, show (Factor.a 1).dualCoxeter = 3 by decide] at htr
  refine ⟨α, β, ?_⟩
  intro hz
  obtain ⟨n, hn⟩ := four_dvd_trace_of_zero_cubic H α β hp hz
  have h : (4 : ℂ) * n = 210 := by linear_combination htr / 2 - hn
  have hi : (4 : ℤ) * n = 210 := by exact_mod_cast h
  omega


open scoped TensorProduct
open Structural HermitianRealization Complexification AnomalyComplexification CartanTrace CanonicalAnomaly

/-- With simple complex isotropy, a nonzero full radical forces every
mixed Cartan cubic on the actual canonical positive half to vanish. -/
theorem compact_simple_cartan_cubic_zero {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsSimple ℂ (ℂ ⊗[ℝ] h)] [IsKilling ℂ (ℂ ⊗[ℝ] h)]
    (A : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [A.IsCartanSubalgebra] (x y z : A) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    ∑ μ : Weight ℂ A V, (finrank ℂ (genWeightSpace V μ) : ℂ) * (μ x * μ y * μ z) = 0 := by
  let ρ := complexHermitianRepresentation (hermitianHalfOfCommutant B h e)
  have hR : complexTraceRadical ρ ≠ ⊥ := (hermitian_complex_radical_ne_bot_iff _).mpr hr
  have htop := (IsSimple.eq_bot_or_eq_top (complexTraceRadical ρ)).resolve_left hR
  have hzero := (complex_trace_radical_ideal_iff_cartan A ρ ⊤).mp htop.ge x (LieSubmodule.mem_top _) y z
  simpa only [canonical_cubic_cartan_weight_sum, nsmul_eq_mul, ρ] using hzero

/-- For simple A₂ isotropy, the actual positive half cannot have dimension
35 and either of the two indicated highest weights under the anomaly hypothesis. -/
theorem compact_simple_a2_thirty_five_excluded {g : Type*} [LieRing g] [LieAlgebra ℝ g]
    [Module.Finite ℝ g] (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (heff : Effective h) (hproper : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hr : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [IsSimple ℂ (ℂ ⊗[ℝ] h)] [IsKilling ℂ (ℂ ⊗[ℝ] h)]
    (A : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [A.IsCartanSubalgebra] (b : (rootSystem A).Base)
    (s : Index (Factor.a 1).datum ≃ b.support)
    (hm : ∀ i j, b.cartanMatrix (s i) (s j) = matrix (Factor.a 1).datum i j)
    (χ : Dual ℂ A) (a : (Factor.a 1).Label)
    (ha : ∀ i, χ (coroot (s i).val.val) = (a (nodes (.a 1) i) : ℂ))
    (hrow : a = ![4,1] ∨ a = ![1,4]) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    ∀ v : V, v ≠ 0 → (∀ z : A, ⁅z,v⁆ = χ z • v) →
      (∀ α : A.root, b.IsPos α → ∀ z ∈ rootSpace A α.val, ⁅z,v⁆ = 0) → finrank ℂ V ≠ 35 := by
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  haveI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) V :=
    (AllRankComplex.all_rank_complex_structural_reduction B h heff hproper e hr).2.2.2.2.2.2.1
  dsimp only
  intro v hv hev hkill hd
  obtain ⟨α, β, hn⟩ := a2_thirty_five_has_cubic A b s hm χ a ha hrow hd hv hev hkill
  exact hn (compact_simple_cartan_cubic_zero B h e hr A _ _ _)

end CubicAnomaly.Classification.ExceptionalSieveA2Cubic
