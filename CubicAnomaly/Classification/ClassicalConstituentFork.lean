import Mathlib.Data.Matrix.Cartan
import Mathlib.Tactic

/-!
# Automorphisms of the D and E6 diagrams

The branching node of D is determined by its three neighbours. In
rank at least five its unique non-leaf neighbour then determines the
whole long arm. Thus the only nodes an automorphism can exchange are
the two spin nodes.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentFork

private def edge (n i j : ℕ) : Prop :=
  (i+1 = j ∧ j+3 ≤ n) ∨ (j+1 = i ∧ i+3 ≤ n) ∨
  (i+3 = n ∧ n ≤ j+2) ∨ (j+3 = n ∧ n ≤ i+2)

private theorem edge_iff {n : ℕ} (hn : 5 ≤ n) (i j : Fin n) :
    edge n i.val j.val ↔ CartanMatrix.D n i j = -1 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,edge]
  split_ifs <;> (try norm_num) <;> omega

/-- An automorphism of a D diagram of rank at least five fixes every
node on its long arm, including the branching node. -/
theorem typeD_fixed_chain {n : ℕ} (hn : 5 ≤ n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, CartanMatrix.D n (σ i) (σ j) = CartanMatrix.D n i j) :
    ∀ i : Fin n, i.val+3 ≤ n → σ i = i := by
  have e (i j : Fin n) (hij : edge n i j) : edge n (σ i) (σ j) :=
    (edge_iff hn _ _).mpr ((hσ i j).trans ((edge_iff hn i j).mp hij))
  let c : Fin n := ⟨n-3,by omega⟩
  let t : Fin n := ⟨n-4,by omega⟩
  let t' : Fin n := ⟨n-5,by omega⟩
  let u : Fin n := ⟨n-2,by omega⟩
  let v : Fin n := ⟨n-1,by omega⟩
  have diff (i j : Fin n) (hij : i.val ≠ j.val) : (σ i).val ≠ (σ j).val :=
    fun he => hij (congrArg Fin.val (σ.injective (Fin.ext he)))
  have hc : σ c = c := by
    have et := e c t (by unfold edge; dsimp [c,t]; omega)
    have eu := e c u (by unfold edge; dsimp [c,u]; omega)
    have ev := e c v (by unfold edge; dsimp [c,v]; omega)
    have htu := diff t u (by dsimp [t,u]; omega)
    have htv := diff t v (by dsimp [t,v]; omega)
    have huv := diff u v (by dsimp [u,v]; omega)
    apply Fin.ext
    unfold edge at et eu ev
    change (σ c).val = n-3
    omega
  have ht : σ t = t := by
    have he := e c t (by unfold edge; dsimp [c,t]; omega)
    have he' := e t t' (by unfold edge; dsimp [t,t']; omega)
    have hne := diff c t' (by dsimp [c,t']; omega)
    rw [hc] at he hne
    unfold edge at he he'
    apply Fin.ext
    change (σ t).val = n-4
    change edge n (n-3) (σ t).val at he
    unfold edge at he
    change n-3 ≠ (σ t').val at hne
    omega
  have step (m : ℕ) : ∀ i : Fin n, i.val+3 ≤ n → n-3-i.val = m → σ i = i := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i hi hm
      by_cases he : i.val = n - 3
      · simpa [show i = c from Fin.ext he] using hc
      by_cases he' : i.val = n - 4
      · simpa [show i = t from Fin.ext he'] using ht
      let j : Fin n := ⟨i.val+1,by omega⟩
      let k : Fin n := ⟨i.val+2,by omega⟩
      have hj : σ j = j := ih _ (by dsimp [j]; omega) j (by dsimp [j]; omega) rfl
      have hk : σ k = k := ih _ (by dsimp [k]; omega) k (by dsimp [k]; omega) rfl
      have hne := diff i k (by dsimp [k]; omega)
      have had := e i j (by unfold edge; dsimp [j]; omega)
      rw [hj] at had
      rw [hk] at hne
      apply Fin.ext
      unfold edge at had
      dsimp [j,k] at had hne
      omega
  exact fun i hi => step _ i hi rfl

/-- On E₆ the only possible exchanged pairs consist of the outer
nodes 0,5 or the inner nodes 2,4. The squared Cartan matrix applied
to the constant vector distinguishes the four possible node orbits. -/
theorem typeE6_exchanged_pair (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ i j, CartanMatrix.E₆ (σ i) (σ j) = CartanMatrix.E₆ i j)
    (i : Fin 6) (hn : σ i ≠ i) :
    (i = 0 ∧ σ i = 5) ∨ (i = 5 ∧ σ i = 0) ∨ (i = 2 ∧ σ i = 4) ∨ (i = 4 ∧ σ i = 2) := by
  let a := fun i : Fin 6 => ∑ j, CartanMatrix.E₆ i j
  let v := fun i : Fin 6 => ∑ j, CartanMatrix.E₆ i j * a j
  have ha (i : Fin 6) : a (σ i) = a i := by
    unfold a
    rw [← Equiv.sum_comp σ (fun j => CartanMatrix.E₆ (σ i) j)]
    simp only [hσ]
  have hv (i : Fin 6) : v (σ i) = v i := by
    unfold v
    rw [← Equiv.sum_comp σ (fun j => CartanMatrix.E₆ (σ i) j * a j)]
    simp only [hσ,ha]
  have pairs : ∀ i j : Fin 6, v j = v i → j ≠ i →
      (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨ (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) := by
    dsimp only [v,a]
    decide
  exact pairs i _ (hv i) hn

/-- The two nodes are orthogonal ends of a proper straight path; the
negative column sum records an adjacent node outside the path. -/
def ExchangedPath {ι : Type*} (A : Matrix ι ι ℤ) (i j : ι) : Prop :=
  A i j = 0 ∧ A j i = 0 ∧
    ∃ (n : ℕ) (s : Fin n ↪ ι) (k : ι), (n = 3 ∨ n = 4 ∨ n = 5) ∧
      (∀ u v, A (s u) (s v) = CartanMatrix.A n u v) ∧
      (∀ t : Fin n, t.val = 0 ∨ t.val+1 = n → s t = i ∨ s t = j) ∧
      ((List.finRange n).map fun t => A (s t) k).sum < 0

private theorem ExchangedPath.symm {ι : Type*} {A : Matrix ι ι ℤ} {i j : ι} (h : ExchangedPath A i j) :
    ExchangedPath A j i := by
  obtain ⟨h₁,h₂,n,s,k,hn,hA,he,ho⟩ := h
  exact ⟨h₂,h₁,n,s,k,hn,hA,fun t ht => (he t ht).symm,ho⟩

theorem ExchangedPath.map {ι μ : Type*} {A : Matrix ι ι ℤ} {B : Matrix μ μ ℤ}
    (e : ι ↪ μ) (hc : ∀ i j, B (e i) (e j) = A i j) {i j : ι} (h : ExchangedPath A i j) :
    ExchangedPath B (e i) (e j) := by
  obtain ⟨h₁,h₂,n,s,k,hn,hA,he,ho⟩ := h
  refine ⟨(hc _ _).trans h₁,(hc _ _).trans h₂,n,s.trans e,e k,hn,fun u v => (hc _ _).trans (hA u v),?_,?_⟩
  · intro t ht
    exact (he t ht).imp (congrArg e) (congrArg e)
  · simpa only [Function.Embedding.trans_apply,hc] using ho

private def e6outer : Fin 5 ↪ Fin 6 := ⟨![0,2,3,4,5],by decide⟩
private def e6inner : Fin 3 ↪ Fin 6 := ⟨![2,3,4],by decide⟩

private theorem e6outer_path : ExchangedPath CartanMatrix.E₆ 0 5 :=
  ⟨by decide,by decide,5,e6outer,1,by decide,by decide,by decide,by decide⟩

private theorem e6inner_path : ExchangedPath CartanMatrix.E₆ 2 4 :=
  ⟨by decide,by decide,3,e6inner,1,by decide,by decide,by decide,by decide⟩

/-- Every nonfixed node of an E₆ diagram lies at one end of a proper
A₃ or A₅ path exchanged by the automorphism. -/
theorem typeE6_exchanged_path (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ i j, CartanMatrix.E₆ (σ i) (σ j) = CartanMatrix.E₆ i j)
    (i : Fin 6) (hn : σ i ≠ i) : ExchangedPath CartanMatrix.E₆ i (σ i) := by
  rcases typeE6_exchanged_pair σ hσ i hn with ⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩ <;> rw [h]
  · exact e6outer_path
  · exact e6outer_path.symm
  · exact e6inner_path
  · exact e6inner_path.symm

private theorem d_spin_path {n : ℕ} (hn : 5 ≤ n) :
    ExchangedPath (CartanMatrix.D n) (⟨n-2,by omega⟩ : Fin n) ⟨n-1,by omega⟩ := by
  classical
  let u : Fin n := ⟨n-2,by omega⟩
  let c : Fin n := ⟨n-3,by omega⟩
  let v : Fin n := ⟨n-1,by omega⟩
  let k : Fin n := ⟨n-4,by omega⟩
  let f : Fin 3 → Fin n := ![u,c,v]
  have inj : Function.Injective f := by
    intro i j h
    have he := congrArg Fin.val h
    fin_cases i <;> fin_cases j <;> dsimp [f,u,c,v] at he <;> first | rfl | omega
  let s : Fin 3 ↪ Fin n := ⟨f,inj⟩
  have entry (a b : Fin n) : CartanMatrix.D n a b =
      if a.val = b.val then 2 else if edge n a b then -1 else 0 := by
    have ha := a.isLt
    have hb := b.isLt
    classical
    simp only [CartanMatrix.D,Matrix.of_apply,edge,Fin.ext_iff]
    split_ifs <;> omega
  change ExchangedPath (CartanMatrix.D n) u v
  refine ⟨?_,?_,3,s,k,Or.inl rfl,?_,?_,?_⟩
  · rw [entry]; unfold edge; dsimp [u,v]; split_ifs <;> omega
  · rw [entry]; unfold edge; dsimp [u,v]; split_ifs <;> omega
  · intro i j
    rw [entry]
    fin_cases i <;> fin_cases j <;>
      norm_num [s,f,u,c,v,CartanMatrix.A,edge,Fin.ext_iff] <;> split_ifs <;> omega
  · intro t ht
    fin_cases t <;> first | exact Or.inl rfl | exact Or.inr rfl | norm_num at ht
  · change CartanMatrix.D n u k + (CartanMatrix.D n c k + (CartanMatrix.D n v k + 0)) < 0
    simp only [entry,edge,u,c,v,k]
    split_ifs <;> omega

/-- In every D diagram of rank at least five the nonfixed nodes of
a diagram automorphism are the ends of the proper spin-node A₃ path. -/
theorem typeD_exchanged_path {n : ℕ} (hn : 5 ≤ n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, CartanMatrix.D n (σ i) (σ j) = CartanMatrix.D n i j)
    (i : Fin n) (hi : σ i ≠ i) : ExchangedPath (CartanMatrix.D n) i (σ i) := by
  have fixed := typeD_fixed_chain hn σ hσ
  have hf : ¬i.val+3 ≤ n := fun h => hi (fixed i h)
  have hf' : ¬(σ i).val+3 ≤ n := fun h => hi (σ.injective (fixed (σ i) h))
  have hne : (σ i).val ≠ i.val := fun h => hi (Fin.ext h)
  have hai := i.isLt
  have hasi := (σ i).isLt
  obtain hh|hh : (i.val = n-2 ∧ (σ i).val = n-1) ∨ (i.val = n-1 ∧ (σ i).val = n-2) := by omega
  · simpa only [show i = (⟨n-2, by omega⟩ : Fin n) from Fin.ext hh.1,
      show σ (⟨n-2,by omega⟩ : Fin n) = ⟨n-1,by omega⟩ from (congrArg σ (Fin.ext hh.1)).symm.trans (Fin.ext hh.2)]
      using d_spin_path hn
  · simpa only [show i = (⟨n-1, by omega⟩ : Fin n) from Fin.ext hh.1,
      show σ (⟨n-1,by omega⟩ : Fin n) = ⟨n-2,by omega⟩ from (congrArg σ (Fin.ext hh.1)).symm.trans (Fin.ext hh.2)]
      using (d_spin_path hn).symm

end CubicAnomaly.Classification.ClassicalConstituentFork
