import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

/-!
# The full cubic radical and the central scalar obstruction

The radical used here fixes the first input and quantifies over **both** other
inputs. Invariance makes it a Lie ideal. For Hermitian matrix generators, a
nonzero scalar generator forces this radical to vanish: inserting it between
two copies of a radical element gives a nonzero multiple of `trace (A * A)`,
and a Hermitian matrix with zero trace square is zero.

These results do not assume a rank bound or a classification of Lie algebras.
-/

namespace CubicAnomaly.Classification.CubicRadical

section Invariant

variable {R L S : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup S] [Module R S]

/-- A trilinear form, with a possibly different scalar-valued target. -/
abbrev TrilinearForm := L →ₗ[R] L →ₗ[R] L →ₗ[R] S

/-- Infinitesimal invariance under the adjoint action in all three slots. -/
def IsInvariant (c : TrilinearForm (R := R) (L := L) (S := S)) : Prop :=
  ∀ a x y z : L, c ⁅a, x⁆ y z + c x ⁅a, y⁆ z + c x y ⁅a, z⁆ = 0

/-- The full first-slot radical of an invariant trilinear form is a Lie ideal. -/
def radical (c : TrilinearForm (R := R) (L := L) (S := S))
    (hc : IsInvariant c) : LieIdeal R L where
  __ := LinearMap.ker c
  lie_mem := by
    intro a x hx
    change c x = 0 at hx
    change c ⁅a, x⁆ = 0
    ext y z
    simpa only [hx, LinearMap.zero_apply, add_zero] using hc a x y z

/-- Membership tests all mixed insertions, not just the diagonal cubic. -/
theorem mem_radical_iff
    (c : TrilinearForm (R := R) (L := L) (S := S)) (hc : IsInvariant c) (x : L) :
    x ∈ radical c hc ↔ ∀ y z, c x y z = 0 := by
  change c x = 0 ↔ _
  constructor
  · intro hx y z
    rw [hx]
    rfl
  · intro hx
    ext y z
    exact hx y z

/-- Vanishing of the radical is precisely nondegeneracy in the first slot. -/
theorem radical_eq_bot_iff
    (c : TrilinearForm (R := R) (L := L) (S := S)) (hc : IsInvariant c) :
    radical c hc = ⊥ ↔ ∀ x, (∀ y z, c x y z = 0) → x = 0 := by
  constructor
  · intro h x hx
    have : x ∈ radical c hc := (mem_radical_iff c hc x).2 hx
    simpa [h] using this
  · intro h
    apply le_antisymm _ bot_le
    intro x hx
    exact (LieSubmodule.mem_bot _).2 (h x ((mem_radical_iff c hc x).1 hx))

end Invariant

section Irreducibility

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]
  [LieModule.IsIrreducible ℝ L M]

/-- An equivariant real endomorphism with a real eigenvector is scalar on an
irreducible real Lie module. This is the kernel proof of the needed Schur step. -/
theorem equivariant_scalar_of_real_eigenvector (f : M →ₗ⁅ℝ,L⁆ M)
    (t : ℝ) (v : M) (hv : v ≠ 0) (heigen : f v = t • v) :
    f = t • LieModuleHom.id := by
  let g : M →ₗ⁅ℝ,L⁆ M := f - t • LieModuleHom.id
  have hvker : v ∈ g.ker := by
    change f v - t • v = 0
    exact sub_eq_zero.mpr heigen
  have hker : g.ker ≠ ⊥ := by
    intro h
    exact hv (by simpa [h] using hvker)
  have htop : g.ker = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top g.ker).resolve_left hker
  have hg : g = 0 := by
    ext x
    apply LieModuleHom.mem_ker.mp
    rw [htop]
    exact LieSubmodule.mem_top x
  exact sub_eq_zero.mp hg

end Irreducibility

section Matrices

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/--
The Hermitian-generator commutator law follows from compatibility with an
actual Lie module action. It is not an additional representation hypothesis.
-/
theorem scaled_commutator_of_action
    {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]
    (v : M ≃ₗ[ℝ] (n → ℂ)) (T : L →ₗ[ℝ] Matrix n n ℂ)
    (haction : ∀ (a : L) (m : M), v ⁅a, m⁆ = Complex.I • ((T a) *ᵥ v m))
    (a b : L) : T ⁅a, b⁆ = Complex.I • (T a * T b - T b * T a) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  have h := congrArg v (lie_lie (x := a) (y := b) (m := v.symm w))
  have h' := congrArg (fun u : n → ℂ => (-Complex.I) • u) h
  simpa only [map_sub, haction, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec, v.apply_symm_apply, smul_sub, smul_smul,
    Complex.I_mul_I, neg_mul, mul_neg, mul_one, neg_neg, one_smul,
    neg_one_smul, smul_neg, neg_smul] using h'

/-- The symmetrized trace cubic, with the manuscript's factor of one half. -/
noncomputable def matrixTraceCubic (A B C : Matrix n n ℂ) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace (A * (B * C + C * B))

/-- The trace cubic pulled back along real-linear matrix generators. -/
noncomputable def traceCubicForm
    {L : Type*} [AddCommGroup L] [Module ℝ L] (T : L →ₗ[ℝ] Matrix n n ℂ) :
    L →ₗ[ℝ] L →ₗ[ℝ] L →ₗ[ℝ] ℂ where
  toFun x := {
    toFun := fun y => {
      toFun := fun z => matrixTraceCubic (T x) (T y) (T z)
      map_add' := by
        intro z w
        simp [matrixTraceCubic, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
        ring
      map_smul' := by
        intro t z
        simp [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add,
          Matrix.trace_smul, Complex.real_smul]
        ring }
    map_add' := by
      intro y z
      ext w
      simp [matrixTraceCubic, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
      ring
    map_smul' := by
      intro t y
      ext z
      simp [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add,
        Matrix.trace_smul, Complex.real_smul]
      ring }
  map_add' := by
    intro x y
    ext z w
    simp [matrixTraceCubic, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    ring
  map_smul' := by
    intro t x
    ext y z
    simp [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add,
      Matrix.trace_smul, Complex.real_smul]
    ring

omit [DecidableEq n] in
/-- The matrix cubic is invariant under simultaneous commutators. -/
theorem matrix_trace_cubic_invariant (D A B C : Matrix n n ℂ) :
    matrixTraceCubic (D * A - A * D) B C +
      matrixTraceCubic A (D * B - B * D) C +
      matrixTraceCubic A B (D * C - C * D) = 0 := by
  have h : (D * A - A * D) * (B * C + C * B) +
      A * ((D * B - B * D) * C + C * (D * B - B * D)) +
      A * (B * (D * C - C * D) + (D * C - C * D) * B) =
      D * (A * (B * C + C * B)) - (A * (B * C + C * B)) * D := by
    noncomm_ring
  simp only [matrixTraceCubic, ← mul_add, ← Matrix.trace_add, h,
    Matrix.trace_sub, Matrix.trace_mul_comm D (A * (B * C + C * B)), sub_self, mul_zero]

private theorem matrixTraceCubic_smul_first (t : ℂ) (A B C : Matrix n n ℂ) :
    matrixTraceCubic (t • A) B C = t * matrixTraceCubic A B C := by
  simp [matrixTraceCubic, Matrix.trace_smul, smul_eq_mul]
  ring

private theorem matrixTraceCubic_smul_second (t : ℂ) (A B C : Matrix n n ℂ) :
    matrixTraceCubic A (t • B) C = t * matrixTraceCubic A B C := by
  simp [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

private theorem matrixTraceCubic_smul_third (t : ℂ) (A B C : Matrix n n ℂ) :
    matrixTraceCubic A B (t • C) = t * matrixTraceCubic A B C := by
  simp [matrixTraceCubic, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

/--
The Hermitian-generator convention has `κ = I`: its bracket is `I` times the
matrix commutator. The same invariance proof works for any fixed coefficient.
-/
theorem trace_cubic_form_invariant_of_scaled_commutator
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (T : L →ₗ[ℝ] Matrix n n ℂ) (κ : ℂ)
    (hbracket : ∀ a x, T ⁅a, x⁆ = κ • (T a * T x - T x * T a)) :
    IsInvariant (traceCubicForm T) := by
  intro a x y z
  change matrixTraceCubic (T ⁅a, x⁆) (T y) (T z) +
    matrixTraceCubic (T x) (T ⁅a, y⁆) (T z) +
    matrixTraceCubic (T x) (T y) (T ⁅a, z⁆) = 0
  rw [hbracket, hbracket, hbracket, matrixTraceCubic_smul_first,
    matrixTraceCubic_smul_second, matrixTraceCubic_smul_third,
    ← mul_add, ← mul_add, matrix_trace_cubic_invariant, mul_zero]

/-- The full radical as a Lie ideal for the Hermitian-generator convention. -/
noncomputable def generatorRadical
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (T : L →ₗ[ℝ] Matrix n n ℂ) (κ : ℂ)
    (hbracket : ∀ a x, T ⁅a, x⁆ = κ • (T a * T x - T x * T a)) :
    LieIdeal ℝ L :=
  radical (traceCubicForm T) (trace_cubic_form_invariant_of_scaled_commutator T κ hbracket)

/-- A Lie representation gives an invariant trilinear trace cubic. -/
theorem trace_cubic_form_invariant
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] (ρ : L →ₗ⁅ℝ⁆ Matrix n n ℂ) :
    IsInvariant (traceCubicForm ρ.toLinearMap) := by
  intro a x y z
  change matrixTraceCubic (ρ ⁅a, x⁆) (ρ y) (ρ z) +
    matrixTraceCubic (ρ x) (ρ ⁅a, y⁆) (ρ z) +
    matrixTraceCubic (ρ x) (ρ y) (ρ ⁅a, z⁆) = 0
  simp only [LieHom.map_lie, Ring.lie_def]
  exact matrix_trace_cubic_invariant (ρ a) (ρ x) (ρ y) (ρ z)

/-- The full trace-cubic radical of an actual matrix representation. -/
noncomputable def representationRadical
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] (ρ : L →ₗ⁅ℝ⁆ Matrix n n ℂ) :
    LieIdeal ℝ L :=
  radical (traceCubicForm ρ.toLinearMap) (trace_cubic_form_invariant ρ)

/-- Inserting a scalar matrix gives the trace-square test. -/
theorem matrix_trace_cubic_scalar (A : Matrix n n ℂ) (t : ℂ) :
    matrixTraceCubic A (t • (1 : Matrix n n ℂ)) A = t * Matrix.trace (A * A) := by
  simp only [matrixTraceCubic, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

omit [DecidableEq n] in
/-- A Hermitian matrix has zero trace square exactly when it is zero. -/
theorem hermitian_trace_square_eq_zero_iff (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    Matrix.trace (A * A) = 0 ↔ A = 0 := by
  simpa only [hA.eq] using
    (Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := A))

/--
For faithful Hermitian generators, one nonzero scalar generator makes the
full trace-cubic radical trivial. Only the mixed insertion `(x,z,x)` is needed.
-/
theorem matrix_cubic_radical_trivial_of_scalar
    {L : Type*} [Zero L] (T : L → Matrix n n ℂ)
    (hfaithful : ∀ x, T x = 0 → x = 0)
    (hhermitian : ∀ x, (T x).IsHermitian)
    (z : L) (t : ℂ) (ht : t ≠ 0) (hscalar : T z = t • (1 : Matrix n n ℂ))
    (x : L) (hx : ∀ y w, matrixTraceCubic (T x) (T y) (T w) = 0) : x = 0 := by
  have h := hx z x
  rw [hscalar, matrix_trace_cubic_scalar] at h
  exact hfaithful x ((hermitian_trace_square_eq_zero_iff (T x) (hhermitian x)).1
    ((mul_eq_zero.mp h).resolve_left ht))

/-- The preceding trace test identifies the actual generator radical with zero. -/
theorem generator_radical_eq_bot_of_scalar
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (T : L →ₗ[ℝ] Matrix n n ℂ) (κ : ℂ)
    (hbracket : ∀ a x, T ⁅a, x⁆ = κ • (T a * T x - T x * T a))
    (hfaithful : Function.Injective T) (hhermitian : ∀ x, (T x).IsHermitian)
    (z : L) (t : ℂ) (ht : t ≠ 0) (hscalar : T z = t • (1 : Matrix n n ℂ)) :
    generatorRadical T κ hbracket = ⊥ := by
  apply (radical_eq_bot_iff _ _).2
  intro x hx
  apply matrix_cubic_radical_trivial_of_scalar T _ hhermitian z t ht hscalar x hx
  intro y hy
  apply hfaithful
  simpa using hy

/--
Contrapositive form used to remove the centre: a nonzero radical element
excludes every nonzero scalar generator in a faithful Hermitian realization.
-/
theorem no_nonzero_scalar_of_nonzero_matrix_cubic_radical
    {L : Type*} [Zero L] (T : L → Matrix n n ℂ)
    (hfaithful : ∀ x, T x = 0 → x = 0)
    (hhermitian : ∀ x, (T x).IsHermitian)
    (hradical : ∃ x, x ≠ 0 ∧ ∀ y w, matrixTraceCubic (T x) (T y) (T w) = 0)
    (z : L) (t : ℂ) (hscalar : T z = t • (1 : Matrix n n ℂ)) : t = 0 := by
  by_contra ht
  obtain ⟨x, hx, hcx⟩ := hradical
  exact hx (matrix_cubic_radical_trivial_of_scalar T hfaithful hhermitian z t ht hscalar x hcx)

/--
Schur's scalar-centre conclusion and a nonzero full cubic radical force the
centre to be zero. The scalar-centre hypothesis is stated explicitly here;
it is separate from the trace argument and from irreducibility.
-/
theorem center_eq_bot_of_scalar_center_and_nonzero_cubic_radical
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (T : L →ₗ[ℝ] Matrix n n ℂ) (hfaithful : Function.Injective T)
    (hhermitian : ∀ x, (T x).IsHermitian)
    (hscalar : ∀ z, z ∈ LieAlgebra.center ℝ L →
      ∃ t : ℂ, T z = t • (1 : Matrix n n ℂ))
    (hradical : ∃ x, x ≠ 0 ∧ ∀ y w, matrixTraceCubic (T x) (T y) (T w) = 0) :
    LieAlgebra.center ℝ L = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨t, ht⟩ := hscalar z hz
  have hfaith : ∀ x, T x = 0 → x = 0 := by
    intro x hx
    apply hfaithful
    simpa using hx
  have ht0 := no_nonzero_scalar_of_nonzero_matrix_cubic_radical
    T hfaith hhermitian hradical z t ht
  have htz : T z = 0 := by simpa [ht0] using ht
  exact (LieSubmodule.mem_bot _).2 (hfaith z htz)

/--
The spectral theorem supplies a real eigenvalue of a Hermitian matrix.
Pulling its eigenspace back to an irreducible real Lie module forces the
matrix to be a real scalar. Equivariance is stated in the chosen realization.
-/
theorem hermitian_scalar_of_irreducible_realization
    {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]
    [LieModule.IsIrreducible ℝ L M]
    (v : M ≃ₗ[ℝ] (n → ℂ)) (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hequivariant : ∀ (a : L) (m : M), A *ᵥ v ⁅a, m⁆ =
      v ⁅a, v.symm (A *ᵥ v m)⁆) :
    ∃ t : ℝ, A = (t : ℂ) • (1 : Matrix n n ℂ) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hempty =>
      letI := hempty
      exact ⟨0, Subsingleton.elim _ _⟩
  | inr hnonempty =>
      letI := hnonempty
      let i : n := Classical.choice hnonempty
      let w : n → ℂ := ⇑(hA.eigenvectorBasis i)
      let t : ℝ := hA.eigenvalues i
      let f : M →ₗ⁅ℝ,L⁆ M := {
        __ := v.symm.toLinearMap.comp
          ((A.mulVecLin.restrictScalars ℝ).comp v.toLinearMap)
        map_lie' := by
          intro a m
          apply v.injective
          simpa using hequivariant a m }
      have hw : w ≠ 0 := by
        intro hw0
        apply (hA.eigenvectorBasis.toBasis.ne_zero i)
        ext j
        exact congrFun hw0 j
      have hwm : v.symm w ≠ 0 := by
        intro h
        exact hw (by simpa using congrArg v h)
      have heigen : f (v.symm w) = t • v.symm w := by
        change v.symm (A *ᵥ v (v.symm w)) = t • v.symm w
        rw [v.apply_symm_apply]
        exact (congrArg v.symm (hA.mulVec_eigenvectorBasis i)).trans (v.symm.map_smul t w)
      have hf := equivariant_scalar_of_real_eigenvector f t (v.symm w) hwm heigen
      refine ⟨t, Matrix.ext_iff_mulVec.mpr ?_⟩
      intro w'
      have h := congrArg (fun g : M →ₗ⁅ℝ,L⁆ M => v (g (v.symm w'))) hf
      change v (v.symm (A *ᵥ v (v.symm w'))) = v (t • v.symm w') at h
      simp only [v.apply_symm_apply, map_smul] at h
      simpa only [Matrix.smul_mulVec, Matrix.one_mulVec,
        RCLike.real_smul_eq_coe_smul (K := ℂ)] using h

/--
A central Hermitian generator is a real scalar in an irreducible real
realization. Scalar central action is proved from irreducibility here.
-/
theorem central_generator_scalar_of_irreducible
    {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]
    [LieModule.IsIrreducible ℝ L M]
    (v : M ≃ₗ[ℝ] (n → ℂ)) (T : L →ₗ[ℝ] Matrix n n ℂ)
    (haction : ∀ (a : L) (m : M), v ⁅a, m⁆ = Complex.I • ((T a) *ᵥ v m))
    (hhermitian : ∀ a, (T a).IsHermitian)
    (z : L) (hz : z ∈ LieAlgebra.center ℝ L) :
    ∃ t : ℝ, T z = (t : ℂ) • (1 : Matrix n n ℂ) := by
  have hz' : ∀ a : L, ⁅a, z⁆ = 0 := hz
  have hcomm (a : L) : T a * T z = T z * T a := by
    apply Matrix.ext_iff_mulVec.mpr
    intro w
    have hLie : ⁅a, ⁅z, v.symm w⁆⁆ = ⁅z, ⁅a, v.symm w⁆⁆ := by
      rw [leibniz_lie, hz' a, zero_lie, zero_add]
    have h := congrArg v hLie
    simpa only [haction, Matrix.mulVec_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul, neg_inj, v.apply_symm_apply, Matrix.mulVec_mulVec] using h
  apply hermitian_scalar_of_irreducible_realization (L := L) v (T z) (hhermitian z)
  intro a m
  simp only [haction, v.apply_symm_apply, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, hcomm]

/--
The centre elimination step of the structural reduction, with Schur's
conclusion derived from the irreducible module and its Hermitian realization.
There is no scalar-centre assumption and no rank restriction.
-/
theorem center_eq_bot_of_irreducible_hermitian_realization
    {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M]
    [LieModule.IsIrreducible ℝ L M]
    (v : M ≃ₗ[ℝ] (n → ℂ)) (T : L →ₗ[ℝ] Matrix n n ℂ)
    (haction : ∀ (a : L) (m : M), v ⁅a, m⁆ = Complex.I • ((T a) *ᵥ v m))
    (hfaithful : Function.Injective T) (hhermitian : ∀ a, (T a).IsHermitian)
    (hradical : ∃ x, x ≠ 0 ∧ ∀ y w, matrixTraceCubic (T x) (T y) (T w) = 0) :
    LieAlgebra.center ℝ L = ⊥ := by
  apply center_eq_bot_of_scalar_center_and_nonzero_cubic_radical
    T hfaithful hhermitian _ hradical
  intro z hz
  obtain ⟨t, ht⟩ := central_generator_scalar_of_irreducible v T haction hhermitian z hz
  exact ⟨(t : ℂ), ht⟩

end Matrices

end CubicAnomaly.Classification.CubicRadical
