import CubicAnomaly.Classification.RootClassificationDynkin

/-!
# Explicit Weyl words acting by negation

For G2, F4, E7, E8 and the indicated classical Cartan matrices of rank at
most eight, half the Coxeter number of repetitions of the simple-root
list acts by negation. The finite calculation uses integral coordinates
of the simple coroots. Its interpretation on an actual splitting Cartan
is proved by the coreflection formula and linearity.
-/

namespace CubicAnomaly.Classification.WeylDualityObstruction

open LieAlgebra LieAlgebra.IsKilling LieModule Module

private def unit {n : ℕ} (i : Fin n) : Vector ℤ n :=
  Vector.ofFn (Pi.single i 1)

private def step {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (z : Vector ℤ n) (i : Fin n) : Vector ℤ n :=
  let d := ∑ j, C i j * z[j]
  Vector.ofFn fun j => z[j] - if i = j then d else 0

/-- An explicit simple reflection word sends each simple coroot to the
negative of the indexed simple coroot. -/
def SignedCorootWord {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (w : List (Fin n))
    (p : Fin n → Fin n) : Prop :=
  ∀ i, w.foldl (step C) (unit i) = Vector.ofFn fun j => -(unit (p i)).get j

instance {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (w : List (Fin n))
    (p : Fin n → Fin n) : Decidable (SignedCorootWord C w p) := by
  unfold SignedCorootWord
  infer_instance

/-- A Coxeter word in ascending order of the numbered simple roots. -/
def coxeterWord (n k : ℕ) : List (Fin n) := (List.replicate k (List.finRange n)).flatten

/-- The word sends each coordinate coroot to its negative. -/
def NegatesCoroots {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Prop :=
  ∀ i : Fin n, (coxeterWord n k).foldl (step C) (unit i) =
    Vector.ofFn fun j => -(unit i).get j

instance {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Decidable (NegatesCoroots C k) := by
  unfold NegatesCoroots
  infer_instance

/-- Orders 6, 12, 18 and 30 for the exceptional Coxeter elements. -/
theorem exceptional_coxeter_negation :
    NegatesCoroots CartanMatrix.G₂ 3 ∧ NegatesCoroots CartanMatrix.F₄ 6 ∧
    NegatesCoroots CartanMatrix.E₇ 9 ∧ NegatesCoroots CartanMatrix.E₈ 15 := by
  native_decide

/-- Every classical type with central opposition in the exceptional rank range. -/
theorem classical_coxeter_negation :
    NegatesCoroots (CartanMatrix.A 1) 1 ∧
    (∀ n : Fin 9, NegatesCoroots (CartanMatrix.B n) n) ∧
    (∀ n : Fin 9, NegatesCoroots (CartanMatrix.C n) n) ∧
    (∀ n : Fin 9, Even n.val → NegatesCoroots (CartanMatrix.D n) (n-1 : ℕ)) := by
  native_decide

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base) {n : ℕ} (s : Fin n → b.support)

private noncomputable def corootSum (v : Vector ℤ n) : H :=
  ∑ j, (v.get j : K) • b.toCoweightBasis (s j)

private theorem step_corootSum {C : Matrix (Fin n) (Fin n) ℤ}
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = C i j) (v : Vector ℤ n) (i : Fin n) :
    corootSum H b s (step C v i) = (rootSystem H).coreflection (s i) (corootSum H b s v) := by
  have hp (j : Fin n) : (rootSystem H).pairing (s i) (s j) = (C i j : K) := by
    have hh := b.algebraMap_cartanMatrixIn_apply ℤ (s i) (s j)
    change ((b.cartanMatrix (s i) (s j) : ℤ) : K) = _ at hh
    rw [h] at hh
    exact hh.symm
  have hv : (rootSystem H).root' (s i) (corootSum H b s v) = (∑ j, C i j * v[j] : ℤ) := by
    simp only [corootSum, map_sum, map_smul, b.toCoweightBasis_apply,
      RootPairing.root'_coroot_eq_pairing, hp, Int.cast_sum, Int.cast_mul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [RootPairing.coreflection_apply, hv]
  have hs (j : Fin n) : ((step C v i).get j : K) =
      (v.get j : K) - if i = j then ((∑ k, C i k * v[k] : ℤ) : K) else (0 : K) := by
    by_cases hij : i = j <;> simp [step, Vector.get, hij]
  simp only [corootSum, hs, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, b.toCoweightBasis_apply]

/-- The actual action of the listed root reflections on the Cartan subalgebra. -/
noncomputable def applyWord (w : List H.root) : H ≃ₗ[K] H :=
  match w with
  | [] => .refl _ _
  | i :: v => ((rootSystem H).coreflection i).trans (applyWord v)

private theorem fold_corootSum {C : Matrix (Fin n) (Fin n) ℤ}
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = C i j) (w : List (Fin n)) (v : Vector ℤ n) :
    corootSum H b s (w.foldl (step C) v) =
      applyWord H (w.map fun i => (s i).val) (corootSum H b s v) := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih =>
    change corootSum H b s (w.foldl _ _) = applyWord H _ ((rootSystem H).coreflection (s i) _)
    rw [ih, step_corootSum H b s h]

/-- Integer signed-permutation certificates determine the action on the
coroots of an actual Cartan block. -/
theorem signed_word_indexed_coroots {C : Matrix (Fin n) (Fin n) ℤ}
    (w : List (Fin n)) (p : Fin n → Fin n)
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = C i j) (hc : SignedCorootWord C w p) (i : Fin n) :
    applyWord H (w.map fun j => (s j).val) (b.toCoweightBasis (s i)) =
      -b.toCoweightBasis (s (p i)) := by
  have hu (k : Fin n) : corootSum H b s (unit k) = b.toCoweightBasis (s k) := by
    simp [corootSum, unit, Vector.get, Pi.single_apply, ite_smul]
  have hh := fold_corootSum H b s h w (unit i)
  rw [hc i, hu] at hh
  refine hh.symm.trans ?_
  rw [← hu]
  simp [corootSum, Vector.get]

/-- The same Coxeter word negates each indexed basis coroot, including when
the displayed matrix is only one connected component. -/
theorem coxeter_negates_indexed_coroots {C : Matrix (Fin n) (Fin n) ℤ} (k : ℕ)
    (h : ∀ i j, b.cartanMatrix (s i) (s j) = C i j) (hc : NegatesCoroots C k) (i : Fin n) :
    applyWord H ((coxeterWord n k).map fun j => (s j).val) (b.toCoweightBasis (s i)) =
      -b.toCoweightBasis (s i) := by
  have hu : corootSum H b s (unit i) = b.toCoweightBasis (s i) := by
    simp [corootSum, unit, Vector.get, Pi.single_apply, ite_smul]
  have hh := fold_corootSum H b s h (coxeterWord n k) (unit i)
  rw [hc i, hu] at hh
  refine hh.symm.trans ?_
  rw [← hu]
  simp [corootSum, Vector.get]

/-- Matrix certificates imply negation on every element of the actual Cartan. -/
theorem actual_weyl_negation_of_coxeter (e : Fin n ≃ b.support) {C : Matrix (Fin n) (Fin n) ℤ} (k : ℕ)
    (h : ∀ i j, b.cartanMatrix (e i) (e j) = C i j) (hc : NegatesCoroots C k) :
    ∃ w : List H.root, ∀ z : H, applyWord H w z = -z := by
  let w := (coxeterWord n k).map fun i => (e i).val
  refine ⟨w, fun z => ?_⟩
  have hb (j : b.support) : applyWord H w (b.toCoweightBasis j) = -b.toCoweightBasis j := by
    obtain ⟨i, rfl⟩ := e.surjective j
    exact coxeter_negates_indexed_coroots H b e k h hc i
  rw [← b.toCoweightBasis.sum_repr z]
  simp only [map_sum, map_smul, hb, smul_neg, Finset.sum_neg_distrib]

/-- The three Dynkin families admitting non-self-dual representations. -/
def NoncentralType {ι : Type*} (C : Matrix ι ι ℤ) : Prop :=
  (∃ (m : ℕ) (e : ι ≃ Fin m), 2 ≤ m ∧ C.reindex e e = CartanMatrix.A m) ∨
  (∃ (m : ℕ) (e : ι ≃ Fin m), Odd m ∧ C.reindex e e = CartanMatrix.D m) ∨
  (∃ e : ι ≃ Fin 6, C.reindex e e = CartanMatrix.E₆)

/-- Classification of the opposition alternatives for each connected block. -/
theorem small_cartan_opposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : C.IsFiniteCartan) (hi : C.IsIndecomposable)
    (hrank : Fintype.card ι ≤ 8) :
    NoncentralType C ∨ ∃ (m : ℕ) (e : ι ≃ Fin m) (k : ℕ), NegatesCoroots (C.reindex e e) k := by
  have bound {m : ℕ} (e : ι ≃ Fin m) : m < 9 := by
    have hh := Fintype.card_congr e
    rw [Fintype.card_fin] at hh
    omega
  rcases hC.exists_A_or_B_or_C_or_D_or_E_or_F_or_G hi with
    ⟨m,e,he⟩ | ⟨m,e,he⟩ | ⟨m,e,he⟩ | ⟨m,e,he⟩ | ⟨e,he⟩ | ⟨e,he⟩ | ⟨e,he⟩ | ⟨e,he⟩ | ⟨e,he⟩
  · by_cases hm : 2 ≤ m
    · exact Or.inl (Or.inl ⟨m,e,hm,he⟩)
    · have hh : ∀ r : Fin 2, NegatesCoroots (CartanMatrix.A r) 1 := by native_decide
      exact Or.inr ⟨_,e,1, he ▸ hh ⟨m,by omega⟩⟩
  · exact Or.inr ⟨_,e,_, he ▸ classical_coxeter_negation.2.1 ⟨m,bound e⟩⟩
  · exact Or.inr ⟨_,e,_, he ▸ classical_coxeter_negation.2.2.1 ⟨m,bound e⟩⟩
  · rcases Nat.even_or_odd m with hm | hm
    · exact Or.inr ⟨_,e,_, he ▸ classical_coxeter_negation.2.2.2 ⟨m,bound e⟩ hm⟩
    · exact Or.inl (Or.inr (Or.inl ⟨m,e,hm,he⟩))
  · exact Or.inl (Or.inr (Or.inr ⟨e, he.trans (by decide)⟩))
  · exact Or.inr ⟨_,e,9,(he.trans (show CartanMatrix.E 7 = CartanMatrix.E₇ by decide)) ▸
      exceptional_coxeter_negation.2.2.1⟩
  · exact Or.inr ⟨_,e,15,(he.trans (show CartanMatrix.E 8 = CartanMatrix.E₈ by decide)) ▸
      exceptional_coxeter_negation.2.2.2⟩
  · exact Or.inr ⟨_,e,6,he ▸ exceptional_coxeter_negation.2.1⟩
  · exact Or.inr ⟨_,e,3,he ▸ exceptional_coxeter_negation.1⟩

/-- The possible Cartan matrices of a simple algebra of rank at most eight
whose Weyl group does not contain negation. -/
theorem cartan_types_of_no_negation [IsAlgClosed K] [LieAlgebra.IsSimple K L]
    (hrank : finrank K H ≤ 8) (hn : ¬ ∃ w : List H.root, ∀ z : H, applyWord H w z = -z) :
    NoncentralType b.cartanMatrix := by
  classical
  obtain ⟨hC, hi⟩ := DynkinClassification.actual_finite_indecomposable_cartan b
  rw [finrank_eq_card_basis b.toCoweightBasis] at hrank
  rcases small_cartan_opposition hC hi hrank with ht | ⟨m,e,k,hk⟩
  · exact ht
  · exact (hn (actual_weyl_negation_of_coxeter H b e.symm k (fun _ _ => rfl) hk)).elim

end CubicAnomaly.Classification.WeylDualityObstruction
