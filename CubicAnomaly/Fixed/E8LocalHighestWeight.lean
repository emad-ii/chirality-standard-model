import CubicAnomaly.Fixed.E8LocalMatter
import CubicAnomaly.Fixed.E8RadicalIdentification

/-!
# The highest weight of the local twenty-seven

The degree-one root with coordinates `(0,-1,-1,-2,-2,-2,-2,-1)` pairs
with the six simple coroots as `(1,0,0,0,0,0)`. Adding any positive
simple root of the local factor leaves the ambient root system. Its
homogeneous basis vector is therefore annihilated by the corresponding
raising operators. At least one of its three family coordinates is
nonzero, and the same relations hold on that local vector.
-/

namespace CubicAnomaly.Fixed.E8LocalHighestWeight

open E8BracketData E8BracketBinding E8GradingData E8FullCubic E8FullCubicData
open E8MatterMatching E8LocalMatter MatterSpectrum

noncomputable section

private def highestRoot : RootVector := #v[0, -1, -1, -2, -2, -2, -2, -1]

set_option maxRecDepth 4096 in
private theorem highestRoot_mem : highestRoot ∈ rootList := by decide

private theorem highestRoot_grade : grade (.inr highestRoot) = 1 := by decide

private theorem highestRoot_weight : ∀ a : Fin 6,
    pairSimple highestRoot (e6SimpleIndex a) = (if a = 0 then 1 else 0) := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem highestRoot_simple_bracket : ∀ a : Fin 6,
    bracket (.inr (simpleVector (e6SimpleIndex a))) (.inr highestRoot) = [] := by
  have hn : ∀ a : Fin 6, highestRoot ≠ negateVector (simpleVector (e6SimpleIndex a)) := by decide
  have hr : ∀ a : Fin 6, addVector (simpleVector (e6SimpleIndex a)) highestRoot ∉ rootList := by decide
  intro a
  simp only [bracket, if_neg (hn a), bracket_data_isRoot_iff_list, if_neg (hr a)]

private theorem simple_mem_e6 (a : Fin 6) : simpleVector (e6SimpleIndex a) ∈ e6Roots := by
  apply Finset.mem_filter.mpr
  constructor
  · have h := bracket_data_simple_mem_basis (e6SimpleIndex a)
    simpa [basisList] using h
  · have h : ∀ b : Fin 6, (simpleVector (e6SimpleIndex b))[6] = 0 ∧
        (simpleVector (e6SimpleIndex b))[7] = 0 := by decide
    exact h a

/-- The six simple coroots of the local ideal. -/
def localCartan (a : Fin 6) : fullRadical :=
  ⟨cartan (e6SimpleIndex a), e8_full_radical_cartan a⟩

/-- Positive simple-root vectors in the local ideal. -/
def localRaising (a : Fin 6) : fullRadical :=
  ⟨_, e8_full_radical_e6_root _ (simple_mem_e6 a)⟩

private def highestLabel : GradeLabel 1 :=
  ⟨.inr highestRoot, (e8_mem_gradeLabels 1 _).mpr
    ⟨by simpa [basisList] using highestRoot_mem, highestRoot_grade⟩⟩

private theorem highest_toral (a : Fin 6) :
    ⁅(localCartan a).val, gradeBasis 1 highestLabel⁆ =
      (if a = 0 then 1 else 0 : ℂ) • gradeBasis 1 highestLabel := by
  refine (e8_full_cartan_basis_action (e6SimpleIndex a) 1 highestLabel).trans ?_
  apply congrArg (fun c : ℂ => c • gradeBasis 1 highestLabel)
  change ((pairSimple highestRoot (e6SimpleIndex a) : ℤ) : ℂ) = _
  rw [highestRoot_weight]
  split <;> simp

private theorem highest_raising (a : Fin 6) :
    ⁅(localRaising a).val, gradeBasis 1 highestLabel⁆ = 0 := by
  apply Subtype.ext
  change (⁅zeroBasis _, gradeBasis 1 highestLabel⁆ : ActualMatter).val = 0
  rw [e8_full_zero_grade_bracket]
  change E8Adjoint.adjointEquiv (E8SparseModel.realize
    (bracket (.inr (simpleVector (e6SimpleIndex a))) (.inr highestRoot))) = 0
  rw [highestRoot_simple_bracket]
  exact map_zero E8Adjoint.adjointEquiv

/-- The irreducible local module has a highest-weight vector for the first
fundamental weight in the displayed ordering of the six simple roots. -/
theorem e8_local_matter_highest_weight :
    ∃ u : Matter27, u ≠ 0 ∧
      (∀ a : Fin 6, ⁅localCartan a, u⁆ = (if a = 0 then 1 else 0 : ℂ) • u) ∧
      ∀ a : Fin 6, ⁅localRaising a, u⁆ = 0 := by
  let w := gradeBasis 1 highestLabel
  let v := localCopiesEquiv.symm w
  have hn : v ≠ 0 := fun h => (gradeBasis 1).ne_zero highestLabel
    (localCopiesEquiv.symm.injective (h.trans (map_zero localCopiesEquiv.symm).symm))
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra! hz
    exact hn (funext hz)
  refine ⟨v i, hi, ?_, ?_⟩
  · intro a
    have h := (localCopiesEquiv.symm.map_lie (localCartan a) w).symm
    change ⁅localCartan a, v⁆ = localCopiesEquiv.symm ⁅(localCartan a).val, w⁆ at h
    have he := h.trans (congrArg localCopiesEquiv.symm (highest_toral a))
    exact congrFun (he.trans (map_smul localCopiesEquiv.symm _ _)) i
  · intro a
    have h := (localCopiesEquiv.symm.map_lie (localRaising a) w).symm
    change ⁅localRaising a, v⁆ = localCopiesEquiv.symm ⁅(localRaising a).val, w⁆ at h
    have he := h.trans (congrArg localCopiesEquiv.symm (highest_raising a))
    exact congrFun (he.trans (map_zero localCopiesEquiv.symm)) i

instance : LieRingModule E6Lattice.Algebra Matter27 :=
  LieRingModule.compLieHom Matter27 E6Lattice.radicalLieEquiv.toLieHom

instance : LieModule ℂ E6Lattice.Algebra Matter27 :=
  LieModule.compLieHom Matter27 E6Lattice.radicalLieEquiv.toLieHom

private theorem lattice_irreducible : LieModule.IsIrreducible ℂ E6Lattice.Algebra Matter27 := by
  haveI : Nontrivial Matter27 := Module.nontrivial_of_finrank_pos (R := ℂ)
    (by rw [matter27_finrank]; decide)
  letI := e8_local_matter_irreducible
  apply LieModule.IsIrreducible.mk
  intro U hU
  let W : LieSubmodule ℂ fullRadical Matter27 :=
    { U.toSubmodule with
      lie_mem := by
        intro x m hm
        obtain ⟨y, rfl⟩ := E6Lattice.radicalLieEquiv.surjective x
        exact U.lie_mem (x := y) hm }
  rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
  · exfalso
    apply hU
    exact (LieSubmodule.eq_bot_iff U).mpr ((LieSubmodule.eq_bot_iff W).mp h)
  · apply top_unique
    intro u _
    change u ∈ W
    rw [h]
    trivial

/-- The existing local matter space carries the irreducible fundamental 27
of the independent complex E₆ lattice algebra. Its nonzero highest vector
has Dynkin labels (1,0,0,0,0,0) for that model's own simple generators. -/
theorem e6_fundamental_matter :
    Module.finrank ℂ Matter27 = 27 ∧ LieModule.IsIrreducible ℂ E6Lattice.Algebra Matter27 ∧
      ∃ u : Matter27, u ≠ 0 ∧
        (∀ a : Fin 6, @Bracket.bracket E6Lattice.Algebra Matter27 _ (Pi.single (.inl a) (1 : ℂ)) u =
          (if a = 0 then 1 else 0 : ℂ) • u) ∧
        ∀ a : Fin 6, @Bracket.bracket E6Lattice.Algebra Matter27 _
          (Pi.single (.inr (E6Lattice.simpleRootIndex a)) (1 : ℂ)) u = 0 := by
  obtain ⟨u, hu, hc, hr⟩ := e8_local_matter_highest_weight
  refine ⟨matter27_finrank, lattice_irreducible, u, hu, ?_, ?_⟩
  · intro a
    have h : E6Lattice.radicalLieEquiv (Pi.single (.inl a) (1 : ℂ)) = localCartan a :=
      Subtype.ext (E6Lattice.e6_lattice_simple_images a).1
    exact (congrArg (fun x : fullRadical => ⁅x,u⁆) h).trans (hc a)
  · intro a
    let s : ℂ := E8RadicalIdentificationData.sign (.inr (E6Lattice.simpleRootIndex a))
    have h : E6Lattice.radicalLieEquiv
        (Pi.single (.inr (E6Lattice.simpleRootIndex a)) (1 : ℂ)) = s • localRaising a :=
      Subtype.ext ((E6Lattice.e6_lattice_simple_images a).2 _)
    change ⁅E6Lattice.radicalLieEquiv _, u⁆ = 0
    exact (congrArg (fun x : fullRadical => ⁅x,u⁆) h).trans
      ((smul_lie s (localRaising a) u).trans ((congrArg (s • ·) (hr a)).trans (smul_zero s)))

end

end CubicAnomaly.Fixed.E8LocalHighestWeight
