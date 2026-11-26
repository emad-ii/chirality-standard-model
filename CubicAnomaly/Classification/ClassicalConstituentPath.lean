import CubicAnomaly.Classification.ClassicalConstituentWeights
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Data.Matrix.Cartan

/-!
# Alternating-square highest vectors on a straight path

Words in lowering operators admit integral computations using the simple
Cartan matrix. Nonadjacent letters commute, and an unsupported node that
can reach the right end annihilates the highest vector. These reductions
are valid in the original module, including when the path lies in a
larger Dynkin diagram.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentPath

open LieAlgebra LieModule Module
open scoped TensorProduct

abbrev Word (n : ℕ) := List (Fin n)

private def letter (n : ℕ) (i : Fin n) : ℤ :=
  if i.val = 0 ∨ i.val + 1 = n then 1 else 0

private def entry {n : ℕ} (i j : Fin n) : ℤ :=
  if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

private def far {n : ℕ} (i j : Fin n) : Bool :=
  i.val + 1 < j.val || j.val + 1 < i.val

private def dead {n : ℕ} : Word n → Bool
  | [] => false
  | j :: w => (letter n j == 0 && w.all (far j)) || dead w

private def insertLetter {n : ℕ} (i : Fin n) : Word n → Word n
  | [] => [i]
  | j :: w => if j.val + 1 < i.val then j :: insertLetter i w else i :: j :: w

private def normal {n : ℕ} : Word n → Word n
  | [] => []
  | j :: w => insertLetter j (normal w)

private def weightAt {n : ℕ} (i : Fin n) (w : Word n) : ℤ :=
  letter n i - (w.map (entry · i)).sum

private def raised {n : ℕ} (i : Fin n) : Word n → List (ℤ × Word n)
  | [] => []
  | j :: w => (if i = j then [(weightAt i w, w)] else []) ++
    (raised i w).map (fun (c,t) => (c, j :: t))

private structure Term (n : ℕ) where
  c : ℤ
  left : Word n
  right : Word n
  deriving DecidableEq, Repr

private abbrev Poly (n : ℕ) := List (Term n)

private def addTerm {n : ℕ} (t : Term n) : Poly n → Poly n
  | [] => [t]
  | s :: p => if t.left = s.left ∧ t.right = s.right then
      ⟨t.c + s.c, s.left, s.right⟩ :: p
    else s :: addTerm t p

private def reduce {n : ℕ} : Poly n → Poly n
  | [] => []
  | t :: p => if dead t.left || dead t.right then reduce p
    else addTerm ⟨t.c, normal t.left, normal t.right⟩ (reduce p)

private def clean {n : ℕ} (p : Poly n) := (reduce p).filter (fun t => t.c != 0)

private def leftRaise {n : ℕ} (i : Fin n) (p : Poly n) : Poly n :=
  p.flatMap (fun t => (raised i t.left).map (fun (c,w) => ⟨t.c * c,w,t.right⟩))

private def rightRaise {n : ℕ} (i : Fin n) (p : Poly n) : Poly n :=
  p.flatMap (fun t => (raised i t.right).map (fun (c,w) => ⟨t.c * c,t.left,w⟩))

private def flip {n : ℕ} (p : Poly n) : Poly n := p.map fun t => ⟨t.c,t.right,t.left⟩

private def negate {n : ℕ} (p : Poly n) : Poly n := p.map fun t => ⟨-t.c,t.left,t.right⟩

set_option linter.unusedSectionVars false

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  {n : ℕ}

private def value (f : Fin n → L) (v : M) : Word n → M
  | [] => v
  | i :: w => ⁅f i, value f v w⁆

private def vector (f : Fin n → L) (v : M) (p : Poly n) : M ⊗[ℂ] M :=
  (p.map fun t => (t.c : ℂ) • (value f v t.left ⊗ₜ[ℂ] value f v t.right)).sum

private theorem vector_cons (f : Fin n → L) (v : M) (t : Term n) (p : Poly n) :
    vector f v (t :: p) = (t.c : ℂ) • (value f v t.left ⊗ₜ[ℂ] value f v t.right) +
      vector f v p := rfl

private theorem vector_append (f : Fin n → L) (v : M) (p q : Poly n) :
    vector f v (p ++ q) = vector f v p + vector f v q := by simp [vector]

private theorem commute_word (f : Fin n → L) (v : M)
    (hc : ∀ i j, far i j = true → ⁅f i,f j⁆ = 0) (i : Fin n) (w : Word n)
    (hw : w.all (far i)) : ⁅f i,value f v w⁆ = value f (⁅f i,v⁆) w := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    obtain ⟨hj,hw⟩ := hw
    rw [value, leibniz_lie, hc i j hj, zero_lie, zero_add, ih hw, value]

private theorem value_zero (f : Fin n → L) (w : Word n) : value f (0 : M) w = 0 := by
  induction w with
  | nil => rfl
  | cons j w ih => simp [value, ih]

private theorem value_dead (f : Fin n → L) (v : M)
    (hc : ∀ i j, far i j = true → ⁅f i,f j⁆ = 0)
    (hz : ∀ i, letter n i = 0 → ⁅f i,v⁆ = 0) (w : Word n) (hw : dead w = true) :
    value f v w = 0 := by
  induction w with
  | nil => contradiction
  | cons j w ih =>
    simp only [dead, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hw
    rcases hw with ⟨hj,hw⟩ | hw
    · rw [value, commute_word f v hc j w hw, hz j hj, value_zero]
    · rw [value, ih hw, lie_zero]

private theorem value_insert (f : Fin n → L) (v : M)
    (hc : ∀ i j, far i j = true → ⁅f i,f j⁆ = 0) (i : Fin n) (w : Word n) :
    value f v (insertLetter i w) = ⁅f i,value f v w⁆ := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    simp only [insertLetter]
    split_ifs with h
    · rw [value, ih, value, leibniz_lie (f i), hc i j (by simp [far,h]), zero_lie, zero_add]
    · rfl

private theorem value_normal (f : Fin n → L) (v : M)
    (hc : ∀ i j, far i j = true → ⁅f i,f j⁆ = 0) (w : Word n) :
    value f v (normal w) = value f v w := by
  induction w with
  | nil => rfl
  | cons j w ih => rw [normal, value_insert f v hc, ih, value]

private theorem vector_addTerm (f : Fin n → L) (v : M) (t : Term n) (p : Poly n) :
    vector f v (addTerm t p) = vector f v [t] + vector f v p := by
  induction p with
  | nil => simp [addTerm,vector]
  | cons s p ih =>
    simp only [addTerm]
    split_ifs with h
    · simp [vector, h.1, h.2, add_smul, add_assoc]
    · simp only [vector_cons, ih]
      abel

private theorem vector_reduce (f : Fin n → L) (v : M)
    (hc : ∀ i j, far i j = true → ⁅f i,f j⁆ = 0)
    (hz : ∀ i, letter n i = 0 → ⁅f i,v⁆ = 0) (p : Poly n) :
    vector f v (reduce p) = vector f v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [reduce]
    split_ifs with h
    · rw [ih, vector_cons]
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [value_dead f v hc hz _ h, TensorProduct.zero_tmul, smul_zero, zero_add]
      · rw [value_dead f v hc hz _ h, TensorProduct.tmul_zero, smul_zero, zero_add]
    · rw [vector_addTerm, ih, vector_cons]
      simp [vector, value_normal f v hc]

private theorem vector_clean (f : Fin n → L) (v : M)
    (hc : ∀ i j, far i j = true → ⁅f i,f j⁆ = 0)
    (hz : ∀ i, letter n i = 0 → ⁅f i,v⁆ = 0) (p : Poly n) :
    vector f v (clean p) = vector f v p := by
  rw [← vector_reduce f v hc hz p]
  unfold clean
  induction reduce p with
  | nil => rfl
  | cons t p ih =>
    by_cases ht : t.c = 0
    · simp [ht, vector_cons, ih]
    · simp [ht, vector_cons, ih]

private theorem word_weight (f : Fin n → L) (v : M) (x : L) (μ : ℂ) (α : Fin n → ℂ)
    (hv : ⁅x,v⁆ = μ • v) (hf : ∀ i, ⁅x,f i⁆ = -(α i • f i)) (w : Word n) :
    ⁅x,value f v w⁆ = (μ - (w.map α).sum) • value f v w := by
  induction w with
  | nil => simpa [value] using hv
  | cons j w ih =>
    simp only [value, leibniz_lie x, hf, neg_lie, smul_lie, ih, lie_smul, List.map_cons, List.sum_cons]
    module

private def wordSum (f : Fin n → L) (v : M) (p : List (ℤ × Word n)) : M :=
  (p.map fun (c,w) => (c : ℂ) • value f v w).sum

private theorem word_raised (f e h : Fin n → L) (v : M)
    (hef : ∀ i j, ⁅e i,f j⁆ = if i = j then h i else 0)
    (hhf : ∀ i j, ⁅h i,f j⁆ = -((entry j i : ℂ) • f j))
    (hev : ∀ i, ⁅e i,v⁆ = 0) (hhv : ∀ i, ⁅h i,v⁆ = (letter n i : ℂ) • v)
    (i : Fin n) (w : Word n) : ⁅e i,value f v w⁆ = wordSum f v (raised i w) := by
  have pref (j : Fin n) (s : List (ℤ × Word n)) :
      ⁅f j,wordSum f v s⁆ = wordSum f v (s.map (fun (c,t) => (c,j :: t))) := by
    induction s with
    | nil => simp [wordSum]
    | cons t s ih =>
      simp only [wordSum, List.map_cons, List.sum_cons, lie_add, lie_smul, value] at ih ⊢
      rw [ih]
  have hw (u : Word n) : ⁅h i,value f v u⁆ = (weightAt i u : ℂ) • value f v u := by
    rw [word_weight f v (h i) (letter n i) (fun j => (entry j i : ℂ)) (hhv i) (hhf i)]
    simp [weightAt, List.map_map, Function.comp_def]
  induction w with
  | nil => simp [value, raised, hev, wordSum]
  | cons j w ih =>
    rw [value, leibniz_lie, hef, ih, pref]
    by_cases he : i = j
    · subst j
      simp [raised, wordSum, hw]
    · simp [he, raised, wordSum]

private theorem vector_leftRaise (f e h : Fin n → L) (v : M)
    (hef : ∀ i j, ⁅e i,f j⁆ = if i = j then h i else 0)
    (hhf : ∀ i j, ⁅h i,f j⁆ = -((entry j i : ℂ) • f j))
    (hev : ∀ i, ⁅e i,v⁆ = 0) (hhv : ∀ i, ⁅h i,v⁆ = (letter n i : ℂ) • v)
    (i : Fin n) (p : Poly n) : vector f v (leftRaise i p) =
      (toEnd ℂ L M (e i)).rTensor M (vector f v p) := by
  have terms (c : ℤ) (u : Word n) (q : List (ℤ × Word n)) :
      vector f v (q.map fun (a,w) => ⟨c*a,w,u⟩) =
        (c : ℂ) • (wordSum f v q ⊗ₜ[ℂ] value f v u) := by
    induction q with
    | nil => simp [vector,wordSum]
    | cons t q ih =>
      simp only [List.map_cons, vector_cons, Int.cast_mul, wordSum, List.sum_cons,
        TensorProduct.add_tmul, ← TensorProduct.smul_tmul', smul_add, smul_smul] at ih ⊢
      rw [ih]
  induction p with
  | nil => simp [leftRaise,vector]
  | cons t p ih =>
    rw [leftRaise, List.flatMap_cons, vector_append, vector_cons, map_add, map_smul, terms,
      LinearMap.rTensor_tmul, toEnd_apply_apply, word_raised f e h v hef hhf hev hhv]
    exact congrArg (_ + ·) ih

private theorem vector_rightRaise (f e h : Fin n → L) (v : M)
    (hef : ∀ i j, ⁅e i,f j⁆ = if i = j then h i else 0)
    (hhf : ∀ i j, ⁅h i,f j⁆ = -((entry j i : ℂ) • f j))
    (hev : ∀ i, ⁅e i,v⁆ = 0) (hhv : ∀ i, ⁅h i,v⁆ = (letter n i : ℂ) • v)
    (i : Fin n) (p : Poly n) : vector f v (rightRaise i p) =
      (toEnd ℂ L M (e i)).lTensor M (vector f v p) := by
  have terms (c : ℤ) (u : Word n) (q : List (ℤ × Word n)) :
      vector f v (q.map fun (a,w) => ⟨c*a,u,w⟩) =
        (c : ℂ) • (value f v u ⊗ₜ[ℂ] wordSum f v q) := by
    induction q with
    | nil => simp [vector,wordSum]
    | cons t q ih =>
      simp only [List.map_cons, vector_cons, Int.cast_mul, wordSum, List.sum_cons,
        TensorProduct.tmul_add, TensorProduct.tmul_smul, smul_add, smul_smul] at ih ⊢
      rw [ih]
  induction p with
  | nil => simp [rightRaise,vector]
  | cons t p ih =>
    rw [rightRaise, List.flatMap_cons, vector_append, vector_cons, map_add, map_smul, terms,
      LinearMap.lTensor_tmul, toEnd_apply_apply, word_raised f e h v hef hhf hev hhv]
    exact congrArg (_ + ·) ih

private theorem vector_flip (f : Fin n → L) (v : M) (p : Poly n) :
    vector f v (flip p) = TensorProduct.comm ℂ M M (vector f v p) := by
  induction p with
  | nil => simp [vector, flip]
  | cons t p ih => simp only [flip, List.map_cons, vector_cons, map_add, map_smul,
      TensorProduct.comm_tmul] at ih ⊢; rw [ih]

private theorem vector_negate (f : Fin n → L) (v : M) (p : Poly n) :
    vector f v (negate p) = -vector f v p := by
  induction p with
  | nil => simp [vector, negate]
  | cons t p ih => simp only [negate, List.map_cons, vector_cons, Int.cast_neg, neg_smul,
      neg_add] at ih ⊢; rw [ih]

private def commWord {n : ℕ} (i : Fin n) (s : List (ℤ × Word n)) : List (ℤ × Word n) :=
  s.map (fun (c,t) => (c,i :: t)) ++ s.map (fun (c,t) => (-c,t ++ [i]))

private def pathTerms (n : ℕ) : Poly n :=
  let nodes := List.finRange n
  let c := match nodes with
    | [] => []
    | i :: is => is.foldl (fun s j => commWord j s) [(1,[i])]
  let cuts := nodes.dropLast.map fun i =>
    ⟨if (n-1+i.val)%2 = 0 then 1 else -1,
      (nodes.take (i.val+1)).reverse, nodes.drop (i.val+1)⟩
  (c.map fun (a,w) => ⟨a,w,[]⟩) ++ cuts

private def pathWitness (n : ℕ) : Poly n := pathTerms n ++ negate (flip (pathTerms n))

private def detect (n : ℕ) (p : Poly n) : Poly n :=
  match List.finRange n with
  | [] => p
  | j :: js => js.foldl (fun s i => clean (rightRaise i s)) (clean (leftRaise j p))

private def sign (n : ℕ) : ℤ := if n%2 = 1 then 1 else -1

private abbrev Checked (n : ℕ) : Prop :=
  (∀ t ∈ pathWitness n, (t.left ++ t.right).Perm (List.finRange n)) ∧
  (∀ j : Fin n, clean (leftRaise j (pathWitness n) ++ rightRaise j (pathWitness n)) = []) ∧
  detect n (pathWitness n) = [⟨sign n,[],[]⟩]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem checked_paths {n : ℕ} (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) : Checked n := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide

private theorem vector_weight (f : Fin n → L) (v : M) (x : L) (μ : ℂ) (α : Fin n → ℂ)
    (hv : ⁅x,v⁆ = μ • v) (hf : ∀ i, ⁅x,f i⁆ = -(α i • f i)) (p : Poly n)
    (hp : ∀ t ∈ p, (t.left ++ t.right).Perm (List.finRange n)) :
    ⁅x,vector f v p⁆ = (2 * μ - ((List.finRange n).map α).sum) • vector f v p := by
  induction p with
  | nil => simp [vector]
  | cons t p ih =>
    have ht := ((hp t (.head _)).map α).sum_eq
    simp only [List.map_append, List.sum_append] at ht
    rw [vector_cons, lie_add, ih (fun t ht => hp t (.tail _ ht)), smul_add, lie_smul,
      TensorProduct.LieModule.lie_tmul_right, word_weight f v x μ α hv hf,
      word_weight f v x μ α hv hf, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← ht]
    module

private theorem vector_other (f : Fin n → L) (v : M) (x : L) (hx : ⁅x,v⁆ = 0)
    (hf : ∀ i, ⁅x,f i⁆ = 0) (p : Poly n) : ⁅x,vector f v p⁆ = 0 := by
  have kill (w : Word n) : ⁅x,value f v w⁆ = 0 := by
    induction w with
    | nil => exact hx
    | cons i w ih => rw [value, leibniz_lie,hf,zero_lie,ih,lie_zero,add_zero]
  induction p with
  | nil => simp [vector]
  | cons t p ih => simp [vector_cons, lie_smul, kill, ih]

private theorem checked_vector (f e h : Fin n → L) (v : M) (hv : v ≠ 0) (hchecked : Checked n)
    (hef : ∀ i j, ⁅e i,f j⁆ = if i = j then h i else 0)
    (hhf : ∀ i j, ⁅h i,f j⁆ = -((entry j i : ℂ) • f j))
    (hev : ∀ i, ⁅e i,v⁆ = 0) (hhv : ∀ i, ⁅h i,v⁆ = (letter n i : ℂ) • v)
    (hc : ∀ i j, far i j = true → ⁅f i,f j⁆ = 0)
    (hz : ∀ i, letter n i = 0 → ⁅f i,v⁆ = 0) :
    let z := vector f v (pathWitness n)
    z ≠ 0 ∧ TensorProduct.comm ℂ M M z = -z ∧ (∀ i, ⁅e i,z⁆ = 0) ∧
      (∀ (x : L) (μ : ℂ) (α : Fin n → ℂ), ⁅x,v⁆ = μ • v → (∀ i, ⁅x,f i⁆ = -(α i • f i)) →
        ⁅x,z⁆ = (2 * μ - ((List.finRange n).map α).sum) • z) ∧
      ∀ x : L, ⁅x,v⁆ = 0 → (∀ i, ⁅x,f i⁆ = 0) → ⁅x,z⁆ = 0 := by
  dsimp only
  have cl := vector_clean f v hc hz
  have ll := vector_leftRaise f e h v hef hhf hev hhv
  have rr := vector_rightRaise f e h v hef hhf hev hhv
  refine ⟨?_, ?_, ?_, (fun x μ α ha hb => vector_weight f v x μ α ha hb _ hchecked.1),
    (fun x ha hb => vector_other f v x ha hb _)⟩
  · intro hzero
    have rightSeq (w : Word n) (p : Poly n) (hp : vector f v p = 0) :
        vector f v (w.foldl (fun s i => clean (rightRaise i s)) p) = 0 := by
      induction w generalizing p with
      | nil => exact hp
      | cons j w ih =>
        apply ih
        rw [cl, rr, hp, map_zero]
    have he : vector f v (detect n (pathWitness n)) = 0 := by
      unfold detect
      split
      · exact hzero
      · apply rightSeq
        rw [cl,ll,hzero,map_zero]
    rw [hchecked.2.2] at he
    have hn := (ClassicalConstituents.symmetric_square_highest_vector (K := ℂ) (L := L) v hv).1
    simp [sign, vector, value, apply_ite] at he
    split_ifs at he <;> simp [hn] at he
  · have invol (u : M ⊗[ℂ] M) : TensorProduct.comm ℂ M M (TensorProduct.comm ℂ M M u) = u :=
      (TensorProduct.comm ℂ M M).symm_apply_apply u
    simp only [pathWitness, vector_append, vector_negate, vector_flip, map_add, map_neg,
      invol, neg_add]
    abel
  · intro i
    have h := congrArg (vector f v) (hchecked.2.1 i)
    rw [cl, vector_append, ll, rr] at h
    exact h

open IsKilling ClassicalConstituentWeights

variable [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    [FiniteDimensional ℂ M]

/-- Let a straight path of two to five simple roots in the ambient root
system have highest labels one at its ends and zero in its interior.
The full orthogonal algebra then has highest weight twice the original
weight minus the sum of the path roots. -/
theorem orthogonal_path_weight
    (β : LinearMap.BilinForm ℂ M) (hβ : β.Nondegenerate) (hInv : β.lieInvariant L)
    (hsym : β.IsSymm) (χ : H → ℂ) (v : M) (hv : v ≠ 0)
    (hw : ∀ x : H, ⁅(x : L), v⁆ = χ x • v)
    (hp : ∀ α : H.root, b.IsPos α → ∀ x ∈ rootSpace H α.val, ⁅x, v⁆ = 0)
    (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) (s : Fin n ↪ b.support)
    (hA : ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.A n i j)
    (hl : ∀ i, χ (coroot (s i).val.val) = if i.val = 0 ∨ i.val + 1 = n then 1 else 0) :
    HasSkewHighestWeight H b β (fun x => 2 * χ x - ((List.finRange n).map (fun i => (s i).val.val x)).sum) := by
  classical
  obtain ⟨e,f,ht,he,hf,hcross,_⟩ := ChevalleySimpleTriples.exists_simple_root_triples H b
  have lower (j : Fin n) (x : H) : ⁅(x : L), f (s j)⁆ = -((s j).val.val x • f (s j)) := by
    simpa only [Pi.neg_apply,neg_smul] using lie_eq_smul_of_mem_rootSpace (hf (s j)) x
  have hhf (i j : Fin n) : ⁅(coroot (s i).val.val : L),f (s j)⁆ = -((entry j i : ℂ) • f (s j)) := by
    rw [lower]
    have hh := b.algebraMap_cartanMatrixIn_apply ℤ (s j) (s i)
    change (b.cartanMatrix (s j) (s i) : ℂ) = (s j).val.val (coroot (s i).val.val) at hh
    rw [← hh,hA]
    rfl
  have eZero (i : b.support) : ⁅e i,v⁆ = 0 := hp _ (b.isPos_of_mem_support i.property) _ (he i)
  have cor (i : Fin n) : ⁅(coroot (s i).val.val : L),v⁆ = (letter n i : ℂ) • v := by
    rw [hw, hl]
    simp only [letter, apply_ite,Int.cast_one,Int.cast_zero]
  have farComm (i j : Fin n) (hd : far i j) : ⁅f (s i),f (s j)⁆ = 0 := by
    have hj : i.val+1 < j.val ∨ j.val+1 < i.val := by simpa [far] using hd
    have hne : i ≠ j := by rintro rfl; omega
    have hz : entry j i = 0 := by
      simp only [entry, if_neg hne.symm]
      split_ifs <;> omega
    have P : (ht (s i)).HasPrimitiveVectorWith (f (s j)) (0 : ℂ) :=
      ⟨(ht _).f_ne_zero, by rw [hhf,hz]; simp, hcross _ _ (fun h => hne (s.injective h))⟩
    simpa using P.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by simp)
  have fZero (i : Fin n) (hi : letter n i = 0) : ⁅f (s i),v⁆ = 0 := by
    have P : (ht (s i)).HasPrimitiveVectorWith v (0 : ℂ) :=
      ⟨hv, by rw [cor,hi,Int.cast_zero], eZero _⟩
    simpa using P.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by simp)
  have cross (i j : Fin n) : ⁅e (s i), f (s j)⁆ = if i = j then (coroot (s i).val.val : L) else 0 := by
    split_ifs with hij
    · subst j; exact (ht _).lie_e_f
    · exact hcross _ _ (fun h => hij (s.injective h))
  obtain ⟨hz,hflip,hraise,hweight,hother⟩ := checked_vector (f ∘ s) (e ∘ s)
    (fun i => (coroot (s i).val.val : L)) v hv (checked_paths hn) cross hhf
    (fun i => eZero (s i)) cor farComm fZero
  apply transport_skew_highest H b β hβ hInv 1 one_ne_zero
    (fun u w => by simpa using hsym.eq u w) _ _ hz (by simpa using hflip)
    (fun x => hweight x _ _ (hw x) (fun i => lower i x))
  intro j x hx
  obtain ⟨c,rfl⟩ := scalar_of_root H (he j) (ht j).e_ne_zero hx
  rw [smul_lie]
  suffices ⁅e j,vector (f ∘ s) v (pathWitness n)⁆ = 0 by rw [this,smul_zero]
  by_cases hj : j ∈ Set.range s
  · obtain ⟨k,rfl⟩ := hj
    exact hraise k
  · exact hother _ (eZero j) (fun i => hcross j _ (fun h => hj ⟨i,h.symm⟩))

end CubicAnomaly.Classification.ClassicalConstituentPath
