import CubicAnomaly.Classification.ClassicalConstituentPathExclusion
import CubicAnomaly.Classification.ClassicalConstituentOrthogonal
import CubicAnomaly.Classification.ClassicalConstituentDiagram
import CubicAnomaly.Classification.ClassicalConstituentDiagonal
import CubicAnomaly.Classification.ClassicalConstituentFork
import CubicAnomaly.Classification.ClassicalConstituentSupport
import CubicAnomaly.Classification.ExceptionalSieveFaithful

/-!
# Singleton support for D and E6 orthogonal isotropy

Every exchanged node in either diagram lies on one of the proper
straight paths. A positive exchanged label is at most two. The
commuting-node lowering excludes coefficient two, and the path
lowering excludes coefficient one. A fixed positive node has adjoint
first lowering, which uniquely determines that node.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentForkReduction

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open ClassicalConstituentWeights ClassicalConstituentHighest ClassicalConstituentOrthogonal
open ClassicalConstituentPathExclusion ClassicalConstituentFork ClassicalConstituentSupport
open ClassicalConstituentDiagram ClassicalConstituentDiagonal Structural CompactOperatorModel
open scoped TensorProduct Classical

/-- E₆ or D of rank at least five, with a chart on the actual simple
root indices. -/
def ForkType {ι : Type*} (C : Matrix ι ι ℤ) : Prop :=
  (∃ n, 5 ≤ n ∧ ∃ e : Fin n ≃ ι, ∀ i j, C (e i) (e j) = CartanMatrix.D n i j) ∨
    (∃ e : Fin 6 ≃ ι, ∀ i j, C (e i) (e j) = CartanMatrix.E₆ i j)

private theorem fork_geom {ι : Type*} {C : Matrix ι ι ℤ} (ht : ForkType C) :
    (∀ i j, C i j = C j i) ∧ ∀ (δ : Equiv.Perm ι) (_hd : ∀ i j, C (δ i) (δ j) = C i j)
      (i : ι), δ i ≠ i → ExchangedPath C i (δ i) := by
  have transport {m : ℕ} (D : Matrix (Fin m) (Fin m) ℤ) (e : Fin m ≃ ι)
      (he : ∀ i j, C (e i) (e j) = D i j) (hs : D.IsSymm)
      (hg : ∀ (σ : Equiv.Perm (Fin m)), (∀ i j, D (σ i) (σ j) = D i j) →
        ∀ i, σ i ≠ i → ExchangedPath D i (σ i)) :
      (∀ i j, C i j = C j i) ∧ ∀ (δ : Equiv.Perm ι) (_hd : ∀ i j, C (δ i) (δ j) = C i j)
        (i : ι), δ i ≠ i → ExchangedPath C i (δ i) := by
    constructor
    · intro i j
      obtain ⟨i,rfl⟩ := e.surjective i
      obtain ⟨j,rfl⟩ := e.surjective j
      rw [he,he]
      exact hs.apply _ _
    · intro δ hd i hn
      obtain ⟨i,rfl⟩ := e.surjective i
      let σ := e.trans (δ.trans e.symm)
      have act (k) : e (σ k) = δ (e k) := by simp [σ]
      have hσ (k l) : D (σ k) (σ l) = D k l := by rw [← he,← he,act,act,hd]
      have h := (hg σ hσ i (fun hh => hn ((act i).symm.trans (congrArg e hh)))).map e.toEmbedding he
      simpa only [Equiv.toEmbedding_apply,act] using h
  rcases ht with ⟨n,hn,e,he⟩|⟨e,he⟩
  · exact transport _ e he (CartanMatrix.D_isSymm n) (typeD_exchanged_path hn)
  · exact transport _ e he CartanMatrix.E₆_isSymm typeE6_exchanged_path

section Model

variable {g W : Type*} [LieRing g] [LieAlgebra ℝ g] [FiniteDimensional ℝ g]
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [IsKilling ℂ (ℂ ⊗[ℝ] h)] [IsSimple ℂ (ℂ ⊗[ℝ] h)]
    (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    [AddCommGroup W] [Module ℂ W] [LieRingModule (ℂ ⊗[ℝ] h) W] [LieModule ℂ (ℂ ⊗[ℝ] h) W]
    [FiniteDimensional ℂ W] [IsIrreducible ℂ (ℂ ⊗[ℝ] h) W] [LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) W]

noncomputable local instance (priority := high) : DecidableEq b.support := Classical.decEq _

include hp e in
set_option maxHeartbeats 1500000 in
/-- Over D or E₆ the compact orthogonal model has precisely one
supported node; its first lowering is an actual adjoint root. -/
theorem fork_model_singleton (β : LinearMap.BilinForm ℂ W) (A : Model h β)
    (hnd : β.Nondegenerate) (hi : β.lieInvariant (ℂ ⊗[ℝ] h)) (hsym : β.IsSymm)
    (ht : ForkType b.cartanMatrix) :
    ∃ (χ : Weight ℂ H W) (v : W) (j : b.support) (d : ℕ) (γ : H.root),
      IsHighestVector H b χ v ∧ 0 < d ∧
      (∀ k : b.support, χ (coroot k.val.val) = if k=j then (d : ℂ) else 0) ∧
      ∀ x, γ.val x = 2 * χ x - j.val.val x := by
  classical
  letI := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) W
  obtain ⟨χ,v,a,θ,w,δ,hv,_,⟨γ,hγ,_,_⟩,ha,_⟩ := orthogonal_model_opposition_support B h hp e H b β A hnd hi hsym
  obtain ⟨hs,hpaths⟩ := fork_geom ht
  have hd := cartan_preserved_of_dual_word H b w δ (fun i => (ha i).2.2.1)
  let l := fun i => (a i : ℕ)
  have hl (i : b.support) : χ (coroot i.val.val) = (l i : ℂ) := (ha i).1
  have fixed (i : b.support) (hpos : 1 ≤ l i) : δ i = i := by
    by_contra hn
    obtain ⟨ho,ho',n,s,k,hpath,hA,hends,hadj⟩ := hpaths δ hd i hn
    have hle : l i ≤ 2 := (ha i).2.2.2.2 hn
    have lδ : l (δ i) = l i := congrArg Fin.val (ha i).2.1
    have c (x y : b.support) : x.val.val (coroot y.val.val) = (b.cartanMatrix x y : ℂ) :=
      (b.algebraMap_cartanMatrixIn_apply ℤ x y).symm
    obtain hh|hh : l i = 1 ∨ l i = 2 := by omega
    · apply no_proper_path_unit_ends B h hp e H b β A hnd hi hsym hv hpath s hA hs l hl _ k hadj
      intro t ht
      rcases hends t ht with he|he <;> rw [he] <;> omega
    · exact no_two_orthogonal_labels_two B h hp e H b β A hnd hi hsym hv i (δ i) (fun hh => hn hh.symm)
        (by rw [c,ho,Int.cast_zero]) (by rw [c,ho',Int.cast_zero])
        (by rw [hl,hh]; norm_num) (by rw [hl,lδ,hh]; norm_num)
  letI := nontrivial_of_isIrreducible ℂ (ℂ ⊗[ℝ] h) (ℂ ⊗[ℝ] h)
  have hne := ExceptionalSieveFaithful.faithful_highest_label_ne_zero H b (Equiv.refl b.support) l v hv.1
    (fun i => (hv.2.1 _).trans (congrArg (· • v) (hl i)))
    (fun i => hv.2.2 _ (b.isPos_of_mem_support i.property))
  obtain ⟨j,hj⟩ : ∃ j, 0 < l j := by
    by_contra! hz
    exact hne (funext fun i => Nat.eq_zero_of_le_zero (hz i))
  have hf (i : b.support) (hi : 1 ≤ l i) : (fun x => 2 * χ x - i.val.val x) = θ :=
    ((ha i).2.2.2.1 hi).mpr (fixed i hi)
  refine ⟨χ,v,j,l j,γ,hv,hj,?_, fun x => congrFun (hγ.trans (hf j hj).symm) x⟩
  intro k
  rw [hl]
  split_ifs with he
  · rw [he]
  · suffices l k = 0 by simp [this]
    by_contra! hk
    apply he
    apply Subtype.ext
    apply Subtype.ext
    exact Weight.ext fun x => sub_right_inj.mp (congrFun ((hf k (by omega)).trans (hf j hj).symm) x)

end Model

private def e6inv3 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4,3,5,6,4,2; 3,6,6,9,6,3; 5,6,10,12,8,4; 6,9,12,18,12,6;
     4,6,8,12,10,5; 2,3,4,6,5,4]

/-- No singleton defining weight of type E₆ has an adjoint first lowering. -/
theorem E6_singleton_impossible {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] [IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (b : (rootSystem H).Base) (e : Fin 6 ≃ b.support)
    (he : ∀ i j, b.cartanMatrix (e i) (e j) = CartanMatrix.E₆ i j)
    (j : b.support) (d : ℕ) (hd : 0 < d) (χ : H → ℂ)
    (hl : ∀ k, χ (coroot k.val.val) = if k=j then (d : ℂ) else 0)
    (γ : H.root) (hg : ∀ x, γ.val x = 2 * χ x - j.val.val x) : False := by
  obtain ⟨j,rfl⟩ := e.surjective j
  have hs (i k : b.support) : b.cartanMatrix i k = b.cartanMatrix k i :=
    (fork_geom (Or.inr ⟨e,he⟩)).1 i k
  have q : ∀ j l : Fin 6, ∑ k, e6inv3 j k * CartanMatrix.E₆ k l = if l=j then 3 else 0 := by decide
  have pos : ∀ j : Fin 6, 4 ≤ e6inv3 j j := by decide
  have hh := singleton_inverse_column H b e j d hd χ (fun i => by simpa using hl (e i)) γ hg hs
    (e6inv3 j) 3 (fun l => by simp only [he]; exact q j l)
  nlinarith [pos j]

end CubicAnomaly.Classification.ClassicalConstituentForkReduction
