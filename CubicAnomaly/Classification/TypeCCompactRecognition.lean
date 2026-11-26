import CubicAnomaly.Classification.TypeCMatrixRecognition
import CubicAnomaly.Classification.TypeCRootOrbit
import CubicAnomaly.Classification.TypeCPositiveRootCount
import CubicAnomaly.Classification.SymplecticMatrixDimension
import CubicAnomaly.Classification.KillingDimension
import CubicAnomaly.Classification.SymplecticCompactModel
import CubicAnomaly.Classification.ClassicalModelTransport

/-! The compact simple algebra of type Cₙ is the compact quaternionic
algebra in its 2n-dimensional complex defining representation. -/

namespace CubicAnomaly.Classification.TypeCCompactRecognition

open LieAlgebra LieAlgebra.IsKilling LieModule Module CompactGeometry Structural HermitianRealization
open TypeCCartanCoordinates TypeCRootOrbit SymplecticMatrixGenerators
open CompactChevalleyConjugation CompactChevalleyDescent ChevalleyRootGeneration
open SymplecticGeometry SymplecticCompactModel
open scoped TensorProduct Matrix

variable {n : ℕ} {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [IsKilling ℂ L]

/-- The full set of signed symplectic roots gives a lower bound on the
dimension of the original complex algebra. -/
theorem source_dimension (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (b : (rootSystem H).Base)
    (s : b.support ≃ Fin (n+1)) (hm : b.cartanMatrix.reindex s s = CartanMatrix.C (n+1)) :
    (n+1) * (2*(n+1)+1) ≤ finrank ℂ L := by
  let T := coordinates H b s
  let u (i : Fin (n+1)) := T.symm (Pi.single i 1)
  have hv (i j : Fin (n+1)) : epsilon H b s i (u j) = if i = j then 1 else 0 := by
    change T (T.symm (Pi.single j 1)) i = _
    simp [Pi.single_apply]
  have hc := TypeCPositiveRootCount.card_le (fun a : H.root => (rootSystem H).root a)
    (epsilon H b s) u hv (difference_root H b s hm) (sum_root H b s hm)
    (fun i j => negative_root H (sum_root H b s hm i j))
  rw [KillingDimension.killing_finrank_eq_cartan_add_roots H, KillingDimension.actual_root_count_eq_card H,
    finrank_eq_card_basis (b.toCoweightBasis.reindex s), Fintype.card_fin]
  nlinarith

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g] [Module.Finite ℝ g]
  [IsKilling ℂ (ℂ ⊗[ℝ] g)]

/-- A compact simple real algebra of type C is isomorphic over the reals
to the compact symplectic algebra in its standard quaternionic model. -/
theorem exists_symplectic_equiv [LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g)]
    (B : CompactForm g) (A : LieSubalgebra ℝ g) [(complexifiedSubalgebra A).IsCartanSubalgebra]
    (b : (rootSystem (complexifiedSubalgebra A)).Base) (s : b.support ≃ Fin n)
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.C n) :
    Nonempty (g ≃ₗ⁅ℝ⁆ symplecticAlgebra (quaternionicStructure (Fin n))) := by
  classical
  let H := complexifiedSubalgebra A
  cases n with
  | zero =>
    letI : Nontrivial H := RootPairing.IsIrreducible.nontrivial' (rootSystem H)
    obtain ⟨i⟩ := b.toCoweightBasis.index_nonempty
    exact (s i).elim0
  | succ m =>
    choose e f ht he hf hconj using fun i : b.support => exists_compact_normalized_root_triple A B i.val
    have hdim := (SymplecticMatrixDimension.finrank_le (m+1)).trans (source_dimension H b s hm)
    obtain ⟨Φ, _, hΦe, hΦf⟩ := TypeCMatrixRecognition.exists_matrix_equiv_of_dim H b s hm hdim e f ht he hf
    let F := matrixEquiv (Fin (m+1))
    let Ψ := Φ.trans F.symm
    have hc' (i : Fin (m+1)) : scalarConjugation (F.symm (raising i)) = -F.symm (lowering i) := by
      apply F.injective
      apply Subtype.ext
      change (F (scalarConjugation (F.symm (raising i)))).val = (F (-F.symm (lowering i))).val
      have hn : F (-F.symm (lowering i)) = -lowering i := by
        change F.toLinearEquiv (-F.symm (lowering i)) = _
        exact (_root_.map_neg F.toLinearMap (F.symm (lowering i))).trans (congrArg Neg.neg (F.apply_symm_apply _))
      rw [symplectic_matrix_scalar_conjugation, F.apply_symm_apply, hn, raising_adjoint]
      rfl
    have hc := intertwines_conjugation_of_normalized_generators Ψ e f
      (fun i => F.symm (raising (s i))) (fun i => F.symm (lowering (s i)))
      (lieSpan_simple_root_vectors_eq_top H b e f he (fun i => (ht i).e_ne_zero) hf
        (fun i => (ht i).f_ne_zero)) hconj (fun i => hc' (s i))
      (fun i => congrArg F.symm (hΦe i)) (fun i => congrArg F.symm (hΦf i))
    obtain ⟨ψ, _⟩ := exists_real_equiv_of_conjugation Ψ hc
    exact ⟨ψ⟩

/-- The full mixed cubic radical vanishes for every original effective compact
pair with type-C ambient Cartan matrix, at any isotropy rank. -/
theorem type_C_cubic_radical_eq_bot (B : CompactForm g) (h : LieSubalgebra ℝ g)
    (ha : Effective h) (hp : h ≠ ⊤)
    (e : lieCommutant (L := h) (M := orthogonalComplement B h) ≃ₐ[ℝ] ℂ)
    (A : LieSubalgebra ℝ g) [(complexifiedSubalgebra A).IsCartanSubalgebra]
    (b : (rootSystem (complexifiedSubalgebra A)).Base) (s : b.support ≃ Fin n)
    (hm : b.cartanMatrix.reindex s s = CartanMatrix.C n) :
    (hermitianHalfOfCommutant B h e).cubicRadical = ⊥ := by
  letI : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] g) :=
    AbsoluteSimplicity.compact_pair_complexification_simple B h ha hp e
  obtain ⟨f⟩ := exists_symplectic_equiv B A b s hm
  exact ClassicalModelTransport.symplectic_model_radical_eq_bot B h ha hp e _ f

end CubicAnomaly.Classification.TypeCCompactRecognition
