import CubicAnomaly.Classification.ComplexDuality
import CubicAnomaly.Classification.ExceptionalSieveSimpleStrings
import CubicAnomaly.Classification.TensorEvaluation

/-!
# Faithfulness of the actual half and its nonzero factor labels

Real and imaginary parts prove faithfulness after complexification. An element
annihilating the positive half also annihilates its contragredient and hence
the whole complexified complement. A zero highest label would give a fixed
vector, forcing the entire irreducible constituent to be trivial.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveFaithful

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open Structural Complexification ComplexDuality TensorEvaluation
open scoped TensorProduct

private theorem complexification_faithful {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]
    [LieModule.IsFaithful ℝ L M] : LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M) := by
  apply (isFaithful_iff' ..).mpr
  intro x hx
  apply (complexification_zero_iff_parts L x).mpr
  have h (m : M) : 1 ⊗ₜ[ℝ] ⁅tensorRealPart L x,m⁆ + Complex.I ⊗ₜ[ℝ] ⁅tensorImagPart L x,m⁆ = 0 := by
    have hc := hx (1 ⊗ₜ[ℝ] m)
    rw [complexification_real_imag_decomposition L x] at hc
    simpa only [add_lie, LieAlgebra.ExtendScalars.bracket_tmul, mul_one] using hc
  constructor
  · apply (isFaithful_iff' ℝ L M).mp inferInstance
    intro m
    simpa [tensorRealPart] using congrArg (tensorRealPart M) (h m)
  · apply (isFaithful_iff' ℝ L M).mp inferInstance
    intro m
    simpa [tensorImagPart] using congrArg (tensorImagPart M) (h m)

/-- Each canonical positive half of a proper effective compact pair is a
faithful complex representation of its complexified isotropy. -/
theorem compact_half_faithful {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ) :
    LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h)
      (invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I) := by
  let q := orthogonalComplement B h
  letI : LieModule.IsFaithful ℝ h q :=
    effective_invariant_complement_faithful h q heff (compact_orthogonal_complement_isCompl B h).sup_eq_top
  letI : LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] q) := complexification_faithful
  let J := complexifiedEnd (commutantComplexStructure e)
  let V := invariantEigenspace J Complex.I
  let U := invariantEigenspace J (-Complex.I)
  obtain ⟨hc,_,_,⟨D⟩,_⟩ := compact_complement_complex_type_decomposition B h hp e
  apply (isFaithful_iff' ℂ (ℂ ⊗[ℝ] h) V).mpr
  intro x hx
  apply (isFaithful_iff' ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] q)).mp inferInstance
  intro m
  have hm : m ∈ V ⊔ U := by rw [hc.sup_eq_top]; trivial
  obtain ⟨v,hv,u,hu,rfl⟩ := (LieSubmodule.mem_sup V U m).mp hm
  have hz : ⁅x,(⟨u,hu⟩ : U)⁆ = 0 := by
    apply D.injective
    calc
      D ⁅x,(⟨u,hu⟩ : U)⁆ = ⁅x,D ⟨u,hu⟩⁆ := D.map_lie x _
      _ = 0 := by
        ext p
        change -(D ⟨u,hu⟩) ⁅x,p⁆ = 0
        rw [hx,map_zero,neg_zero]
      _ = D 0 := (map_zero D).symm
  rw [lie_add, show ⁅x,v⁆ = 0 from congrArg Subtype.val (hx ⟨v,hv⟩),
    show ⁅x,u⁆ = 0 from congrArg Subtype.val hz, add_zero]

/-- On a faithful irreducible representation of a nonzero Killing algebra,
some Dynkin label of every highest vector is nonzero. -/
theorem faithful_highest_label_ne_zero {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
    [Nontrivial L] [FiniteDimensional ℂ L] [IsKilling ℂ L] [AddCommGroup M] [Module ℂ M]
    [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
    [LieModule.IsFaithful ℂ L M] [IsIrreducible ℂ L M]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    {ι : Type*} (s : ι ≃ b.support) (a : ι → ℕ) (v : M) (hv : v ≠ 0)
    (hl : ∀ i, ⁅(coroot (s i).val.val : L),v⁆ = (a i : ℂ) • v)
    (hk : ∀ i : b.support, ∀ z ∈ rootSpace H i.val.val, ⁅z,v⁆ = 0) : a ≠ 0 := by
  intro ha
  obtain ⟨E,F,ht,hE,_,_,hg⟩ := ChevalleySimpleTriples.exists_simple_root_triples H b
  have htop (i : b.support) : (ht i).HasPrimitiveVectorWith v (0 : ℂ) := by
    obtain ⟨j,rfl⟩ := s.surjective i
    exact ⟨hv, by simpa [ha] using hl j, hk _ _ (hE _)⟩
  have hF (i : b.support) : ⁅F i,v⁆ = 0 := by
    simpa using (htop i).pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by simp)
  have hfixed (x : L) : ⁅x,v⁆ = 0 := by
    have hx : x ∈ LieSubalgebra.lieSpan ℂ L (Set.range E ∪ Set.range F) := hg ▸ trivial
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem z hz => rcases hz with ⟨i,rfl⟩ | ⟨i,rfl⟩; exact hk _ _ (hE _); exact hF _
    | zero => exact zero_lie v
    | add x y _ _ hx hy => simp [add_lie,hx,hy]
    | smul c x _ hx => simp [smul_lie,hx]
    | lie x y _ _ hx hy => simp [lie_lie,hx,hy]
  have hv' := (mem_maxTrivSubmodule ℂ L M v).mpr hfixed
  rcases IsSimpleOrder.eq_bot_or_eq_top (maxTrivSubmodule ℂ L M) with he | he
  · exact hv (by simpa [he] using hv')
  · obtain ⟨x,hx⟩ := exists_ne (0 : L)
    apply hx ((isFaithful_iff' ℂ L M).mp inferInstance x (fun m => ?_))
    exact (mem_maxTrivSubmodule ℂ L M m).mp (he ▸ LieSubmodule.mem_top m) x

end CubicAnomaly.Classification.ExceptionalSieveFaithful
