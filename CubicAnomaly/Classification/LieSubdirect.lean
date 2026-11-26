import CubicAnomaly.Fixed.TensorAnomaly
import Mathlib.Algebra.Lie.Semisimple.Basic

/-! # Subdirect products of simple Lie algebras

A Lie subalgebra that projects onto both simple factors is the full product
or the graph of an isomorphism. The proof applies to arbitrary dimension.
-/

namespace CubicAnomaly.Classification.LieSubdirect

open CubicAnomaly.Fixed.TensorAnomaly

variable {R L K : Type*} [CommRing R] [LieRing L] [LieRing K]
  [LieAlgebra R L] [LieAlgebra R K]

private def fstHom (S : LieSubalgebra R (ProductLie L K)) : S →ₗ⁅R⁆ L where
  toFun x := x.val.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

private def sndHom (S : LieSubalgebra R (ProductLie L K)) : S →ₗ⁅R⁆ K where
  toFun x := x.val.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

private def vertical (S : LieSubalgebra R (ProductLie L K))
    (h : Function.Surjective (sndHom S)) : LieIdeal R K where
  toSubmodule := S.toSubmodule.comap (LinearMap.inr R L K)
  lie_mem := by
    intro x y hy
    obtain ⟨z, rfl⟩ := h x
    change ((0, ⁅z.val.2, y⁆) : ProductLie L K) ∈ S
    have hw := S.lie_mem z.property (show ((0, y) : ProductLie L K) ∈ S from hy)
    change (⁅z.val.1, (0 : L)⁆, ⁅z.val.2, y⁆) ∈ S at hw
    simpa only [lie_zero] using hw

/-- Goursat's dichotomy, with the graph isomorphism oriented from the first
factor to the second. Surjectivity then makes this graph the whole relation. -/
theorem full_or_graph [LieAlgebra.IsSimple R L] [LieAlgebra.IsSimple R K]
    (S : LieSubalgebra R (ProductLie L K))
    (hf : Function.Surjective fun x : S => x.val.1)
    (hg : Function.Surjective fun x : S => x.val.2) :
    S = ⊤ ∨ ∃ e : L ≃ₗ⁅R⁆ K, ∀ x : S, e x.val.1 = x.val.2 := by
  classical
  let J := vertical S hg
  obtain hJ | hJ := LieAlgebra.IsSimple.eq_bot_or_eq_top J
  · have hf' : Function.Injective (fstHom S) := by
      apply (fstHom S).ker_eq_bot.mp
      apply eq_bot_iff.mpr
      intro x hx
      have hfst : x.val.1 = 0 := hx
      have hmem : x.val.2 ∈ J := by
        change ((0, x.val.2) : ProductLie L K) ∈ S
        rw [← hfst]
        exact x.property
      rw [hJ] at hmem
      exact Subtype.ext (Prod.ext hfst (show x.val.2 = 0 from hmem))
    let ef := LieEquiv.ofBijective (fstHom S) ⟨hf', hf⟩
    let g := (sndHom S).comp ef.symm.toLieHom
    have hg' : Function.Surjective g := (show Function.Surjective (sndHom S) from hg).comp
      ef.symm.surjective
    obtain hk | hk := LieAlgebra.IsSimple.eq_bot_or_eq_top g.ker
    · refine Or.inr ⟨LieEquiv.ofBijective g ⟨g.ker_eq_bot.mp hk, hg'⟩, fun x => ?_⟩
      change sndHom S (ef.symm (ef x)) = _
      rw [ef.symm_apply_apply]
      rfl
    · have hab : IsLieAbelian K := ⟨fun x y => by
        obtain ⟨z, rfl⟩ := hg' x
        have hz : z ∈ g.ker := hk ▸ LieSubmodule.mem_top z
        rw [show g z = 0 from hz, zero_lie]⟩
      exact (LieAlgebra.IsSimple.non_abelian R hab).elim
  · left
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := hf x.1
    have hmem : x.2 - y.val.2 ∈ J := hJ ▸ LieSubmodule.mem_top _
    have hz := S.add_mem y.property (show ((0, x.2 - y.val.2) : ProductLie L K) ∈ S from hmem)
    convert hz using 1
    apply Prod.ext
    · exact (hy.symm.trans (add_zero _).symm)
    · change x.2 = y.val.2 + (x.2 - y.val.2)
      abel

end CubicAnomaly.Classification.LieSubdirect
