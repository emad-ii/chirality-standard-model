import CubicAnomaly.Classification.ExceptionalSieve
import CubicAnomaly.Classification.ExceptionalSieveFactorTypes
import CubicAnomaly.Classification.ExceptionalSieveFactorProduct
import CubicAnomaly.Classification.ExceptionalSieveStringOpposition
import CubicAnomaly.Classification.ExceptionalSieveStringProducts
import CubicAnomaly.Classification.ExceptionalSieveFaithful
import CubicAnomaly.Classification.ExceptionalSieveFactorDual
import CubicAnomaly.Classification.ExceptionalSieveE6Singleton
import CubicAnomaly.Classification.ExceptionalSieveA2Index

/-!
# Assembly of the exceptional factor sieve

The finite numerical search takes the actual dimension and highest weight
of each isotropy constituent, with the dimension product obtained from
the commuting matrix algebras. Its rank and algebra dimensions use the
Cartan inherited by each ideal from the common isotropy Cartan.
-/

namespace CubicAnomaly.Classification.ExceptionalSieveAssembly

open LieAlgebra LieModule Module LieAlgebra.IsKilling
open Exceptional RootClassificationExceptional ExceptionalSieveCatalog ExceptionalSieveProducts
open ExceptionalSieve ExceptionalSieveFactorTypes ExceptionalSieveNormalization ExceptionalSieveFactorProduct
open ExceptionalSieveStringProducts ExceptionalSieveStringCatalog ExceptionalSieveWeights
open ExceptionalSieveStringOpposition ExceptionalSieveFaithful ExceptionalSieveFactorDual
open CompactGeometry Structural HermitianRealization Complexification CompactCartan AllRankComplex
open scoped TensorProduct

private abbrev key (f : LabelledFactor) : Key := (f.1,List.ofFn f.2)
private def edge : Key → Prop := fun k => k = (.a 1,[0,3]) ∨ k = (.a 1,[3,0])

private theorem selection (G : Ambient) (n : ℕ) (fs : List LabelledFactor)
    (hm : keys (fs.map fun f => stringRow f.1 f.2) ∈ remaining G n)
    (he : ∀ f ∈ fs, edge (key f) → 10 ∣ n) :
    G = .e6 ∧ n = 35 ∧ (fs.map fun f => f.1.rank).sum = 2 := by
  change List.map _ (List.map _ fs) ∈ _ at hm
  rw [List.map_map] at hm
  change fs.map key ∈ remaining G n at hm
  have hn (k : Key) (hk : k ∈ fs.map key) (hh : edge k) : 10 ∣ n := by
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hk
    exact he f hf hh
  have hr : (fs.map fun f => f.1.rank).sum = ((fs.map key).map fun k => k.1.rank).sum := by
    rw [List.map_map]
    rfl
  unfold remaining at hm
  split_ifs at hm with h₄ h₆ h₇
  · obtain ⟨rfl,rfl⟩ := h₄
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm <;> rw [hm] at hn
    · exact False.elim ((by decide : ¬10 ∣ 22) (hn _ (List.mem_cons_self ..) (Or.inl rfl)))
    · exact False.elim ((by decide : ¬10 ∣ 22) (hn _ (List.mem_cons_self ..) (Or.inr rfl)))
  · obtain ⟨rfl,rfl⟩ := h₆
    refine ⟨rfl,rfl,?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm <;> rw [hr,hm] <;> decide
  · obtain ⟨rfl,rfl⟩ := h₇
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm | hm <;> rw [hm] at hn
    · exact False.elim ((by decide : ¬10 ∣ 52) (hn _ (List.mem_cons_self ..) (Or.inl rfl)))
    · exact False.elim ((by decide : ¬10 ∣ 52) (hn _ (List.mem_cons_self ..) (Or.inr rfl)))
    · exact False.elim ((by decide : ¬10 ∣ 52) (hn _ (by simp) (Or.inl rfl)))
    · exact False.elim ((by decide : ¬10 ∣ 52) (hn _ (by simp) (Or.inr rfl)))
  · simp at hm

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [LieAlgebra.IsKilling ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M] [FiniteDimensional ℂ M]
  [IsIrreducible ℂ L M]

private theorem edge_dimension (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (b : (rootSystem H).Base) (t : Factor) (s : Index t.datum ≃ b.support)
    (hC : ∀ i j, b.cartanMatrix (s i) (s j) = RootClassificationExceptional.matrix t.datum i j)
    (a : t.Label) (χ : H → ℂ) (v : M) (hv : v ≠ 0) (hw : ∀ z : H, ⁅z,v⁆ = χ z • v)
    (hl : ∀ i, χ (coroot (s i).val.val) = (a (nodes t i) : ℂ))
    (hp : ∀ α : H.root, b.IsPos α → ∀ z ∈ rootSpace H α.val, ⁅z,v⁆ = 0)
    (he : edge (t,List.ofFn a)) : finrank ℂ M = 10 := by
  obtain rfl : t = .a 1 := he.elim (congrArg Prod.fst) (congrArg Prod.fst)
  have ha : a = ![0,3] ∨ a = ![3,0] := by
    rcases he with h | h
    · exact Or.inl (List.ofFn_injective (congrArg Prod.snd h))
    · exact Or.inr (List.ofFn_injective (congrArg Prod.snd h))
  apply ExceptionalSieveA2Index.a2_edge_three_dimension H b s
    ((hC (0 : Fin 2) (1 : Fin 2)).trans (by decide)) ((hC (1 : Fin 2) (0 : Fin 2)).trans (by decide)) v hv χ hw _
    (fun j => hp j (b.isPos_of_mem_support j.property))
  rcases ha with rfl | rfl
  · exact Or.inr ⟨(hl (0 : Fin 2)).trans (by change ((0 : ℕ) : ℂ) = 0; norm_num),
      (hl (1 : Fin 2)).trans (by change ((3 : ℕ) : ℂ) = 3; norm_num)⟩
  · exact Or.inl ⟨(hl (0 : Fin 2)).trans (by change ((3 : ℕ) : ℂ) = 3; norm_num),
      (hl (1 : Fin 2)).trans (by change ((0 : ℕ) : ℂ) = 0; norm_num)⟩

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]

private theorem ambient_dimension {T : Type*} [LieRing T] [LieAlgebra ℂ T]
    [FiniteDimensional ℂ T] [LieAlgebra.IsKilling ℂ T]
    (H : LieSubalgebra ℂ T) [H.IsCartanSubalgebra]
    (G : Ambient) (b : (rootSystem H).Base) (s : Index (ambientDatum G) ≃ b.support)
    (hm : ∀ i j, b.cartanMatrix (s i) (s j) = RootClassificationExceptional.matrix (ambientDatum G) i j) :
    finrank ℂ T = G.dimension := by
  obtain ⟨E,-⟩ := exists_census_root_equiv b s (ambient_certified G).1 hm
  rw [KillingDimension.killing_finrank_eq_cartan_add_roots H,
    KillingDimension.actual_root_count_eq_card H, ← Fintype.card_congr E,
    finrank_eq_card_basis (b.toCoweightBasis.reindex s.symm)]
  have h : ∀ G : Ambient, (ambientDatum G).cartan.size + (table (ambientDatum G)).card = G.dimension := by
    native_decide
  simpa using h G

set_option maxHeartbeats 2200000 in
/-- Every atom supplies an actual constituent and a catalog entry with
its dimensions, string and index bounds, and opposition properties. -/
private theorem atom_witness
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)] [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)]
    (A : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
    [A.IsCartanSubalgebra] [H.IsCartanSubalgebra]
    (hn : ∀ x : A, complexifiedLieHom h.incl x ∈ H)
    (G : Ambient) (bg : (rootSystem H).Base) (sg : Index (ambientDatum G) ≃ bg.support)
    (hg : ∀ i j, bg.cartanMatrix (sg i) (sg j) = RootClassificationExceptional.matrix (ambientDatum G) i j)
    (i : Atom (ℂ ⊗[ℝ] h)) (hr : finrank ℂ (A.comap i.val.toLieSubalgebra.incl) ≤ 7) :
    let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
    ∃ (S : LieSubmodule ℂ i.val V) (f : LabelledFactor),
      IsAtom S ∧ f.1.rank = finrank ℂ (A.comap i.val.toLieSubalgebra.incl) ∧
      f.1.algebraDim = finrank ℂ i.val ∧ Compatible G (finrank ℂ V) (row f.1 f.2) ∧
      f.2 ≠ 0 ∧ lower f.1 f.2 ≤ finrank ℂ S ∧ (∀ j, f.2 j < finrank ℂ S) ∧
      (dualLabels (key f) = (key f).2 → Nonempty (S ≃ₗ⁅ℂ,i.val⁆ Dual ℂ S)) ∧
      (edge (key f) → finrank ℂ S = 10) := by
  classical
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  let C : LieSubalgebra ℂ i.val := A.comap i.val.toLieSubalgebra.incl
  letI := atomic_ideal_isKilling i.val i.property
  letI := ideal_intersection_isCartan A i.val
  letI := IsSemisimple.isSimple_of_isAtom i.val i.property
  letI := nontrivial_of_isIrreducible ℂ i.val i.val
  obtain ⟨b⟩ := RootPairing.nonempty_base (rootSystem C)
  obtain ⟨t,s,hm⟩ := simple_factor_matches_catalog C b hr
  obtain ⟨S,a,χ,v,hS,hir,hv,hw,hpos,ha,hi⟩ :=
    nested_exceptional_factor_index B h hp e A H hn G bg sg hg i.val i.property b t s hm
  letI := hir
  letI := nontrivial_of_isIrreducible ℂ i.val S
  letI : IsIrreducible ℂ (ℂ ⊗[ℝ] h) V := (ComplexDuality.compact_complement_complex_type_decomposition B h hp e).2.1
  letI : LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] h) V := compact_half_faithful B h heff hp e
  letI : LieModule.IsFaithful ℂ i.val V := inferInstanceAs (LieModule.IsFaithful ℂ i.val.toLieSubalgebra V)
  letI : LieModule.IsFaithful ℂ i.val S := TensorEvaluation.lieHomEvaluation_left_faithful
    (TensorEvaluation.commutingIdeal_lieHomEvaluation_surjective i.val i.valᶜ disjoint_compl_right sup_compl_eq_top
      ⟨S.incl, fun hz => hS.ne_bot ((LieSubmodule.eq_bot_iff _).mpr fun y hy => LieModuleHom.congr_fun hz ⟨y,hy⟩)⟩)
  let u := (nodes t).symm.trans s
  have hu (j k) : b.cartanMatrix (u j) (u k) = ExceptionalSieveStringCatalog.matrix t j k :=
    hm ((nodes t).symm j) ((nodes t).symm k)
  have hl (j) : χ (coroot (u j).val.val) = (a j : ℂ) := by simpa [u] using ha ((nodes t).symm j)
  have hk (j : b.support) := hpos j (b.isPos_of_mem_support j.property)
  have hd := matched_factor_dimensions C b t s hm
  refine ⟨S,⟨t,a⟩,hS,hd.1.symm,hd.2.symm,hi,?_,?_,?_,?_,?_⟩
  · exact faithful_highest_label_ne_zero C b u a v hv
      (fun j => (hw (coroot (u j).val.val)).trans (by rw [hl])) hk
  · exact lower_le_finrank C b t u hu a (χ.toLinear ℂ C S) v hv hw hl (fun j => hk (u j))
  · intro j
    obtain ⟨k,hk,_,hk'⟩ := weight_coroot_mem_integer_interval C χ (u j).val
    rw [hl] at hk
    have hk'' : (a j : ℤ) = k := by exact_mod_cast hk
    change a j < finrank ℂ S
    omega
  · exact factor_self_dual_of_fixed_label C b t u hu a (χ.toLinear ℂ C S) v ⟨hv,hw,hpos⟩ hl
  · exact edge_dimension C b t s hm a χ v hv hw ha hpos

set_option maxHeartbeats 2200000 in
/-- In each exceptional ambient branch, the actual isotropy Cartan attains
the ambient rank, given only the original hypotheses and the numbering of
the prescribed nested ambient Cartan. -/
theorem compact_pair_exceptional_rank_bound
    (B : CompactForm g) (h : LieSubalgebra ℝ g) (heff : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (hR : (hermitianHalfOfCommutant B h e).cubicRadical ≠ ⊥)
    [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] g)] [LieAlgebra.IsKilling ℂ (ℂ ⊗[ℝ] h)]
    (A : LieSubalgebra ℂ (ℂ ⊗[ℝ] h)) (H : LieSubalgebra ℂ (ℂ ⊗[ℝ] g))
    [A.IsCartanSubalgebra] [H.IsCartanSubalgebra]
    (hn : ∀ x : A, complexifiedLieHom h.incl x ∈ H)
    (G : Ambient) (bg : (rootSystem H).Base) (sg : Index (ambientDatum G) ≃ bg.support)
    (hg : ∀ i j, bg.cartanMatrix (sg i) (sg j) = RootClassificationExceptional.matrix (ambientDatum G) i j) :
    G.rank ≤ finrank ℂ A := by
  classical
  by_contra! hr
  let L := ℂ ⊗[ℝ] h
  let V := invariantEigenspace (complexifiedEnd (commutantComplexStructure e)) Complex.I
  letI := atomFintype L
  have hdec := ComplexDuality.compact_complement_complex_type_decomposition B h hp e
  letI : IsIrreducible ℂ L V := hdec.2.1
  have hnons : ¬Nonempty (V ≃ₗ⁅ℂ,L⁆ Dual ℂ V) :=
    fun ⟨f⟩ => hdec.2.2.2.2 ⟨f.trans hdec.2.2.2.1.some.symm⟩
  obtain ⟨hdim,hrank⟩ := atomic_dimension_and_rank_sums A
  have hrs (i : Atom L) : finrank ℂ (A.comap i.val.toLieSubalgebra.incl) ≤ 7 := by
    have hle := Finset.single_le_sum (f := fun i : Atom L => finrank ℂ (A.comap i.val.toLieSubalgebra.incl))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hb : G.rank ≤ 8 := by cases G <;> decide
    have hle' : finrank ℂ (A.comap i.val.toLieSubalgebra.incl) ≤ finrank ℂ A := by
      rw [hrank]
      exact hle
    omega
  choose S f hS hfr hfd hi hne hlo hcoord hfixed hedge using
    fun i : Atom L => atom_witness B h heff hp e A H hn G bg sg hg i (hrs i)
  have ht := all_atomic_constituent_dimension_product S hS
  let order := (Fintype.equivFin (Atom L)).symm
  let fs := List.ofFn (fun j => f (order j))
  have hsums (F : LabelledFactor → ℕ) : (fs.map F).sum = ∑ i : Atom L, F (f i) := by
    rw [List.map_ofFn, Fin.sum_ofFn]
    exact order.sum_comp (fun i => F (f i))
  have hprod (F : LabelledFactor → ℕ) : (fs.map F).prod = ∏ i : Atom L, F (f i) := by
    rw [List.map_ofFn, Fin.prod_ofFn]
    exact order.prod_comp (fun i => F (f i))
  have hmem (u : LabelledFactor) : u ∈ fs ↔ ∃ i : Atom L, f i = u := by
    rw [List.mem_ofFn]
    exact ⟨fun ⟨j,hj⟩ => ⟨order j,hj⟩, fun ⟨i,hi⟩ => ⟨order.symm i, by simpa using hi⟩⟩
  have hrr : (fs.map fun u => u.1.rank).sum = finrank ℂ A := by rw [hsums, hrank]; exact Finset.sum_congr rfl fun i _ => hfr i
  have hdd : (fs.map fun u => u.1.algebraDim).sum = finrank ℝ h := by
    rw [hsums, ← Module.finrank_baseChange (S := ℝ) (R := ℂ) (M' := h), hdim]
    exact Finset.sum_congr rfl fun i _ => hfd i
  have hG : finrank ℝ g = G.dimension := by simpa only [Module.finrank_baseChange] using ambient_dimension H G bg sg hg
  have htotal := QuadraticRestriction.compact_pair_dimension_equation B h hp e
  change finrank ℝ g = finrank ℝ h + 2 * finrank ℂ V at htotal
  have hN : finrank ℂ V ≤ 121 := by
    have hb := SieveBounds.all_rank_exceptional_size_half_bounds B h heff hp e hR
    change (finrank ℝ g = 52 → finrank ℂ V ≤ 23) ∧ (finrank ℝ g = 78 → finrank ℂ V ≤ 36) ∧
      (finrank ℝ g = 133 → finrank ℂ V ≤ 65) ∧ (finrank ℝ g = 248 → finrank ℂ V ≤ 121) at hb
    cases G <;> simp only [Ambient.dimension] at hG <;> omega
  have hsmall (i : Atom L) : finrank ℂ (S i) ≤ finrank ℂ V := Submodule.finrank_le (S i).toSubmodule
  have hdual : ∃ i : Atom L, dualLabels (key (f i)) ≠ (key (f i)).2 := by
    by_contra! hall
    exact hnons (self_dual_of_atomic_constituents S hS fun i => hfixed i (hall i))
  have hm := compatible_string_products G (finrank ℂ V) fs
    (fun u hu => by
      obtain ⟨i,rfl⟩ := (hmem _).mp hu
      exact ⟨hne i, lower_pos _ _, (hlo i).trans (hsmall i),
        fun j => (hcoord i j).le.trans ((hsmall i).trans hN)⟩) hN
    (by rw [hrr]; exact hr) (by rw [hdd, ← hG]; exact htotal)
    (by rw [hprod, ht]; exact Finset.prod_le_prod' fun i _ => hlo i)
    (fun u hu => by obtain ⟨i,rfl⟩ := (hmem _).mp hu; exact hi i)
    (by
      obtain ⟨i,hh⟩ := hdual
      exact ⟨_,List.mem_map_of_mem (List.mem_map_of_mem ((hmem _).mpr ⟨i,rfl⟩)), hh⟩)
  obtain ⟨rfl,-,htwo⟩ := selection G (finrank ℂ V) fs hm (fun u hu hed => by
    obtain ⟨i,rfl⟩ := (hmem _).mp hu
    rw [ht, ← hedge i hed]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact ExceptionalSieveE6Singleton.compact_pair_e6_singleton_excluded
    B h heff hp e hR A H hn (hrr.symm.trans htwo) bg sg hg

end CubicAnomaly.Classification.ExceptionalSieveAssembly
