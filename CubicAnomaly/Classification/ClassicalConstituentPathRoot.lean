import CubicAnomaly.Classification.ClassicalConstituentPath

/-!
# The root and coroot of a straight simple path

For a simply laced Cartan matrix the two root pairings agree on all
roots. A straight path of simple roots has both root and coroot given
by the corresponding sums. These facts test whether the shifted
orthogonal highest weight can be adjoint.
-/

namespace CubicAnomaly.Classification.ClassicalConstituentPathRoot

open LieAlgebra LieModule Module LieAlgebra.IsKilling

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

/-- Symmetry on the simple roots extends to all root-coroot pairings. -/
theorem pairing_symmetric_of_cartan_symmetric
    (hs : ∀ i j, b.cartanMatrix i j = b.cartanMatrix j i) (u v : H.root) :
    (rootSystem H).pairing u v = (rootSystem H).pairing v u := by
  let P := rootSystem H
  have symm (i j : b.support) : P.pairing i j = P.pairing j i := by
    have hi := b.algebraMap_cartanMatrixIn_apply ℤ i j
    have hj := b.algebraMap_cartanMatrixIn_apply ℤ j i
    change ((b.cartanMatrix i j : ℤ) : ℂ) = P.pairing i j at hi
    change ((b.cartanMatrix j i : ℤ) : ℂ) = P.pairing j i at hj
    rw [← hi,← hj,hs]
  have refl (i j k : H.root) : P.pairing (P.reflectionPerm j i) k =
      P.pairing i k - P.pairing i j * P.pairing j k := by
    simp only [← P.root_coroot_eq_pairing, P.root_reflectionPerm, P.reflection_apply_root,
      map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have refl' (i j k : H.root) : P.pairing k (P.reflectionPerm j i) =
      P.pairing k i - P.pairing j i * P.pairing k j := by
    simp only [← P.root_coroot_eq_pairing, P.coroot_reflectionPerm, P.coreflection_apply_coroot,
      map_sub,map_smul,smul_eq_mul]
  have one (i : H.root) : ∀ k : b.support, P.pairing i k = P.pairing k i := by
    apply b.induction_reflect i
    · intro j hj k
      rw [P.pairing_reflectionPerm_self_left,P.pairing_reflectionPerm_self_right,hj]
    · intro j hj k; exact symm ⟨j,hj⟩ k
    · intro j l hj hl k
      rw [refl,refl',hj k,hj ⟨l,hl⟩,symm ⟨l,hl⟩ k]
  apply b.induction_reflect v (p := fun v => P.pairing u v = P.pairing v u)
  · intro j hj
    rw [P.pairing_reflectionPerm_self_left,P.pairing_reflectionPerm_self_right,hj]
  · intro j hj; exact one u ⟨j,hj⟩
  · intro j l hj hl
    rw [refl,refl',hj,one u ⟨l,hl⟩,one j ⟨l,hl⟩]

private def adjacentSteps {n : ℕ} (part : List (Fin n)) : List (Fin n) → Bool
  | [] => true
  | j :: w => ((part.map (CartanMatrix.A n · j)).sum == -1) && adjacentSteps (part ++ [j]) w

private def pathCheck (n : ℕ) := match List.finRange n with
  | [] => false
  | i :: is => adjacentSteps [i] is

private theorem path_checked {n : ℕ} (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) :
    pathCheck n = true := by rcases hn with rfl | rfl | rfl | rfl <;> decide

/-- On a straight path the sum of the simple roots is a root. Its coroot
is the equal-coefficient sum of the corresponding simple coroots. -/
theorem straight_path_root {n : ℕ} (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5)
    (s : Fin n ↪ b.support) (hA : ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.A n i j) :
    ∃ r : H.root,
      (rootSystem H).root r = ((List.finRange n).map fun i => (rootSystem H).root (s i)).sum ∧
      (rootSystem H).coroot r = ((List.finRange n).map fun i => (rootSystem H).coroot (s i)).sum := by
  let P := rootSystem H
  let rt := fun i => P.root (s i)
  let co := fun i => P.coroot (s i)
  have ent (i j : Fin n) : P.pairing (s i) (s j) = (CartanMatrix.A n i j : ℂ) := by
    rw [← hA]
    exact (b.algebraMap_cartanMatrixIn_apply ℤ (s i) (s j)).symm
  have ent' (i j : Fin n) : P.pairing (s j) (s i) = (CartanMatrix.A n i j : ℂ) := by
    rw [ent, (CartanMatrix.A_isSymm n).apply i j]
  have step (w : List (Fin n)) (p : List (Fin n)) (r : H.root)
      (hr : P.root r = (p.map rt).sum) (hc : P.coroot r = (p.map co).sum)
      (h : adjacentSteps p w = true) :
      ∃ t : H.root, P.root t = ((p ++ w).map rt).sum ∧ P.coroot t = ((p ++ w).map co).sum := by
    induction w generalizing p r with
    | nil => exact ⟨r,by simpa using hr,by simpa using hc⟩
    | cons j w ih =>
      simp only [adjacentSteps,Bool.and_eq_true,beq_iff_eq] at h
      have pair (t : List (Fin n)) :
          P.toLinearMap.flip (co j) (t.map rt).sum = ((t.map (CartanMatrix.A n · j)).sum : ℤ) := by
        induction t with
        | nil => simp
        | cons i t ih =>
          simp only [List.map_cons,List.sum_cons,map_add,Int.cast_add,ih]
          exact congrArg (· + _) (ent i j)
      have copair (t : List (Fin n)) :
          P.toLinearMap (rt j) (t.map co).sum = ((t.map (CartanMatrix.A n · j)).sum : ℤ) := by
        induction t with
        | nil => simp
        | cons i t ih =>
          simp only [List.map_cons,List.sum_cons,map_add,Int.cast_add,ih]
          exact congrArg (· + _) (ent' i j)
      have hp : P.pairing r (s j) = -1 := by
        change P.toLinearMap.flip (co j) (P.root r) = -1
        rw [hr,pair,h.1]; norm_num
      have hp' : P.pairing (s j) r = -1 := by
        change P.toLinearMap (rt j) (P.coroot r) = -1
        rw [hc,copair,h.1]; norm_num
      have nr : P.root (P.reflectionPerm (s j) r) = ((p ++ [j]).map rt).sum := by
        rw [P.root_reflectionPerm,P.reflection_apply_root,hp,hr]
        simp [rt]
      have nc : P.coroot (P.reflectionPerm (s j) r) = ((p ++ [j]).map co).sum := by
        rw [P.coroot_reflectionPerm,P.coreflection_apply_coroot,hp',hc]
        simp [co]
      simpa [List.append_assoc] using ih (p ++ [j]) _ nr nc h.2
  have h := path_checked hn
  cases he : List.finRange n with
  | nil => simp [pathCheck,he] at h
  | cons j w =>
    exact step w [j] (s j) (by simp [rt]) (by simp [co]) (by simpa [pathCheck,he] using h)

private theorem path_label_sum {n : ℕ} (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) :
    ((List.finRange n).map (fun i => if i.val = 0 ∨ i.val + 1 = n then (1 : ℤ) else 0)).sum = 2 := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide

/-- In a simply laced diagram, if the shifted path weight is a root,
then the module's highest weight itself equals the path root. -/
theorem shifted_root_forces_path_weight {n : ℕ} (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5)
    (s : Fin n ↪ b.support) (hA : ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.A n i j)
    (hs : ∀ i j, b.cartanMatrix i j = b.cartanMatrix j i) (χ : H → ℂ)
    (hl : ∀ i, χ (coroot (s i).val.val) = if i.val = 0 ∨ i.val + 1 = n then 1 else 0)
    (γ : H.root) (hγ : ∀ x, γ.val x = 2 * χ x - ((List.finRange n).map (fun i => (s i).val.val x)).sum) :
    ∀ x, χ x = ((List.finRange n).map (fun i => (s i).val.val x)).sum := by
  let P := rootSystem H
  obtain ⟨r,hr,hc⟩ := straight_path_root H b hn s hA
  have value (x : H) (t : List (Fin n)) :
      ((t.map (fun i => P.root (s i))).sum) x = (t.map (fun i => (s i).val.val x)).sum := by
    induction t with
    | nil => rfl
    | cons i t ih => simp only [List.map_cons,List.sum_cons,LinearMap.add_apply,ih]; rfl
  have rr (x : H) : r.val x = ((List.finRange n).map (fun i => (s i).val.val x)).sum :=
    (LinearMap.congr_fun hr x).trans (value _ _)
  let g := P.root γ + P.root r
  have hg (x : H) : g x = 2 * χ x := by
    change γ.val x + r.val x = _
    rw [hγ,rr]; ring
  let label := fun i : Fin n => if i.val = 0 ∨ i.val+1 = n then (1 : ℤ) else 0
  have tot (t : List (Fin n)) :
      g (t.map (fun i => P.coroot (s i))).sum = 2 * ((t.map label).sum : ℤ) := by
    induction t with
    | nil => simp
    | cons i t ih =>
      simp only [List.map_cons,List.sum_cons,map_add,ih,Int.cast_add,mul_add]
      rw [hg,show P.coroot (s i) = coroot (s i).val.val from rfl,hl]
      simp only [label,apply_ite,Int.cast_one,Int.cast_zero]
  have eqpair : P.pairing γ r = 2 := by
    have h := tot (List.finRange n)
    rw [← hc,show ((List.finRange n).map label).sum = 2 from path_label_sum hn] at h
    change P.pairing γ r + P.pairing r r = _ at h
    rw [P.pairing_same] at h
    push_cast at h
    linear_combination h
  have eqroot := (P.pairing_two_two_iff γ r).mp
    ⟨eqpair, (pairing_symmetric_of_cartan_symmetric H b hs r γ).trans eqpair⟩
  subst γ
  intro x
  have h := hγ x
  rw [rr] at h
  linear_combination -h/2

/-- An outside node adjacent to a proper path has a negative label on
the path root. Consequently a dominant highest weight supported at the
ends of that path cannot produce an adjoint shifted weight. -/
theorem proper_path_shift_not_root {n : ℕ} (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5)
    (s : Fin n ↪ b.support) (hA : ∀ i j, b.cartanMatrix (s i) (s j) = CartanMatrix.A n i j)
    (hs : ∀ i j, b.cartanMatrix i j = b.cartanMatrix j i) (χ : H → ℂ)
    (hl : ∀ i, χ (coroot (s i).val.val) = if i.val = 0 ∨ i.val + 1 = n then 1 else 0)
    (k : b.support) (a : ℕ) (hk : χ (coroot k.val.val) = (a : ℂ))
    (hadj : ((List.finRange n).map (fun i => b.cartanMatrix (s i) k)).sum < 0) :
    ¬ ∃ γ : H.root, ∀ x, γ.val x = 2 * χ x - ((List.finRange n).map (fun i => (s i).val.val x)).sum := by
  rintro ⟨γ,hγ⟩
  have h := shifted_root_forces_path_weight H b hn s hA hs χ hl γ hγ (coroot k.val.val)
  have val (t : List (Fin n)) :
      (t.map fun i => (s i).val.val (coroot k.val.val)).sum = ((t.map fun i => b.cartanMatrix (s i) k).sum : ℤ) := by
    induction t with
    | nil => simp
    | cons i t ih =>
      simp only [List.map_cons,List.sum_cons,Int.cast_add,ih]
      exact congrArg (· + _) (b.algebraMap_cartanMatrixIn_apply ℤ (s i) k).symm
  rw [hk,val] at h
  have h' : (a : ℤ) = ((List.finRange n).map (fun i => b.cartanMatrix (s i) k)).sum := by exact_mod_cast h
  omega

/-- A first-lowering weight which is a root must coincide with every
other supported node. This uses the root pairing bound in a simply
laced diagram. -/
theorem first_shift_root_eq_other {χ : H → ℂ} {γ : H.root} (i j : b.support)
    (hs : ∀ i j, b.cartanMatrix i j = b.cartanMatrix j i) (hij : i ≠ j)
    (a : ℕ) (ha : 1 ≤ a) (hj : χ (coroot j.val.val) = (a : ℂ))
    (hγ : ∀ x, γ.val x = 2 * χ x - i.val.val x) : γ = j.val := by
  let P := rootSystem H
  have fr (i j : H.root) : ((P.pairingIn ℤ i j : ℤ) : ℂ) = P.pairing i j :=
    P.algebraMap_pairingIn ℤ i j
  have hs' := pairing_symmetric_of_cartan_symmetric H b hs γ j
  have ss : P.pairingIn ℤ γ j = P.pairingIn ℤ j γ :=
    (Int.cast_injective (α := ℂ)) ((fr _ _).trans (hs'.trans (fr _ _).symm))
  have hc := b.algebraMap_cartanMatrixIn_apply ℤ i j
  change (b.cartanMatrix i j : ℂ) = i.val.val (coroot j.val.val) at hc
  have he := hγ (coroot j.val.val)
  rw [hj,← hc] at he
  have hcast : ((P.pairingIn ℤ γ j : ℤ) : ℂ) = 2 * (a : ℂ) - (b.cartanMatrix i j : ℂ) :=
    (fr γ j).trans he
  have hz : P.pairingIn ℤ γ j = 2 * (a : ℤ) - b.cartanMatrix i j := by exact_mod_cast hcast
  have hb := P.coxeterWeightIn_le_four ℤ γ j
  change P.pairingIn ℤ γ j * P.pairingIn ℤ j γ ≤ 4 at hb
  rw [← ss] at hb
  have hle := b.cartanMatrix_le_zero_of_ne i j hij
  have htwo : P.pairingIn ℤ γ j = 2 := by nlinarith
  exact (P.pairingIn_two_two_iff ℤ γ j).mp ⟨htwo,ss ▸ htwo⟩

/-- If a third simple coroot pairs negatively with the sum of two
supported simple roots, the first lowering at either supported node
cannot be a root. -/
theorem first_shift_not_root_of_neighbor {χ : H → ℂ} (i j k : b.support)
    (hs : ∀ i j, b.cartanMatrix i j = b.cartanMatrix j i) (hij : i ≠ j)
    (a d : ℕ) (ha : 1 ≤ a) (hj : χ (coroot j.val.val) = (a : ℂ))
    (hk : χ (coroot k.val.val) = (d : ℂ))
    (hadj : b.cartanMatrix i k + b.cartanMatrix j k < 0) :
    ¬ ∃ γ : H.root, ∀ x, γ.val x = 2 * χ x - i.val.val x := by
  rintro ⟨γ,hγ⟩
  have he := first_shift_root_eq_other H b i j hs hij a ha hj hγ
  subst γ
  have hc (l : b.support) : (b.cartanMatrix l k : ℂ) = l.val.val (coroot k.val.val) :=
    b.algebraMap_cartanMatrixIn_apply ℤ l k
  have hh := hγ (coroot k.val.val)
  rw [hk,← hc, ← hc] at hh
  have hd : b.cartanMatrix j k = 2 * (d : ℤ) - b.cartanMatrix i k := by exact_mod_cast hh
  omega

end CubicAnomaly.Classification.ClassicalConstituentPathRoot
