# Detailed notes: the chirality theorem, Lisi's E8, and what the scripts check

This is the long companion to `README.md`. It states each result, how it is checked, and
where its limits are. Every claim marked **[checked]** is asserted by a script in this directory
(`python3 lisi/run_all.py`); every claim marked **[not checked]** is background or interpretation.

## 0. Conventions

* E8 roots are stored in doubled integer coordinates: 112 roots of shape (±2, ±2, 0⁶) and 128 of shape
  (±1)⁸ with an even number of minus signs. The true inner product is `dot / 4`; true roots have norm 2.
  The 8 Cartan directions are not roots, so 240 roots + 8 = 248 = dim E8.
* "Root level" means: the statement concerns the complex Lie algebra through its root system. It does
  not see a real form (a signature such as (11,3)), and it is not a check of a theorem about real forms.
* Provenance. Some papers were readable only as abstracts or in part (see §11). Where a formula was relayed by a
  summary rather than read, the script says so and the model is checked for internal consistency only.

## 1. Two threefold structures in one root system

Both of the following live in E8 and meet in a common refinement.

| | Chirality theorem (this repo) | Lisi |
| :--- | :--- | :--- |
| Subalgebra | E6 × SU(3)_M | D4 × D4 |
| Decomposition | 240 = 72 + 6 + 6·27 | 240 = 24 + 24 + 3·64 |
| Where the 3 comes from | weights of the 3 of SU(3)_M (horizontal) | triality permuting (8v,8v), (8s,8s), (8c,8c) |
| Script | `check_e6_su3_bridge.py` | `check_triality_d4d4.py` |

**[checked]** The 27 repeats over the three weights of the 3, 27bar = −27, and the E6 cubic invariant has
45 zero-sum triples. **[checked]** An order-3 map applied to both D4 factors permutes the 240 roots and
cycles the three 64 blocks.

**Common refinement** (`check_common_refinement.py`). With A2 inside the first D4, the second D4 lies in
E6, E6 roots = 24 + 3·16, and each 27 = 8v + 8s + 8c + 1 + 1 + 1.

## 2. The Standard Model inside the 27

`sm_charges.py` (sympy). Under E6 ⊃ SO(10) × U(1), 27 = 1 + 16 + 10 with ⟨w, w0⟩ = 4/3, 1/3, −2/3
(U(1) charges 4 : 1 : −2). The 40 SO(10) roots are the E6 roots orthogonal to w0. Colour, weak isospin,
hypercharge Y and charge Q are read off root inner products. **[checked]** the 16 reproduces
Q_L, u^c, d^c, L, e^c, ν^c; and Σ Y = Σ Y³ = Σ Q = Σ Q³ = 0 over the 16 (the anomaly-type sums), with the
exact multiset of (colour, su(2), Y) values asserted. **[checked]** the mixed sums SU(2)² Y and SU(3)² Y over the
16 also vanish; the 10 is vector-like (its Y sums cancel termwise); the electric charges Q = T3 + Y of the 16
are 0, ±1/3, ±2/3, ±1; and Y takes the SU(5) pattern on the 40 SO(10) roots (8 at 0, 12 at ±5/6, 12 at ±1/6,
6 at ±2/3, 2 at ±1), the standard hypercharge and not a flipped one.

*Provenance.* `sm_charges.py` was missing from the repository and was rewritten from this section and from
`report/sm_charges.tex`, which the original generated. The vectors w0, a, b, g and Y are the ones printed in that
report: w0 = (−2/3, −2/3, −2/3, 0, 0, 0, 0, 0), the SU(3)_c roots a = (0,0,0,1,1,0,0,0) and
b = (0,0,0,−1,0,1,0,0), the SU(2)_L root g = (0,0,0,0,0,0,1,1) and Y = (0,0,0,1/3,−1/3,1/3,1/2,−1/2). They are
*chosen*, not derived: the rewrite asserts that they are SO(10) roots forming A2 × A1 with Y orthogonal to all of
them and to w0 and the horizontal SU(3)_M, and reads every weight off by inner products. Two things support the
rewrite: `make_report.py` regenerates `report/sm_charges.tex` byte for byte from it, and the five scripts that import
it (`match_e8_spin113.py` and, through it, `match_e8_d7.py`, `check_triality_su4.py`, `check_distler_garibaldi.py`
and `check_lisi_theta.py`) all pass against it. Neither shows that it is the original file, and no claim is made here that the choice
of (a, b, g, Y) is the only one that gives the Standard Model content.

## 3. Spin(11,3) and the Majorana–Weyl 64

`spin113.py` builds Cl(11,3) ≅ M(128, R) independently: a Jordan–Wigner real set with signature (7,7)
in which four negative gammas are multiplied by ε = N0N1N2N3 to obtain (11,3). Labels 1–4 are spacetime
(+,−,−,−); 5–14 span spin(10).

* **[checked]** spin(11,3) = 91 = 6 spin(1,3) + 45 spin(10) + 40 frame-Higgs.
* **[checked]** the chirality element Ω squares to +1, so the 128 splits 64 + 64 with a Majorana–Weyl 64.
* **[checked]** Pati–Salam is 21 generators and the Standard Model 12.
* The complex structure I = Γ1Γ2Γ3Γ4 selects the left-handed subspace W (γ5 = −1). **[checked]** the signed
  (colour, weak, Y) content on W is exactly one left-handed generation ×2 spin, but only for
  (κ = −1/3 with T3_R from the L triple) or (κ = +1/3 with T3_R from the R triple). The two are conjugate
  under U = Γ6Γ8Γ10Γ11, which reverses the colour orientation. So su(2)_L is fixed relative to that
  orientation and no orientation-independent statement of "which su(2) is left" is made.
* Eq. 3.1 of Lisi 2010 was garbled by the reading tool and is not transcribed; because Cl(11,3) is simple,
  any real 128 × 128 Clifford set is conjugate to the paper's, so the dimension counts, closure and
  spectra are convention independent.

## 4. The isometry between the Clifford weights and E8

`match_e8_spin113.py`. **[checked]** There are exactly 12 isometries e_i → f_i from the Clifford Cartan
frame onto the span of the 40 SO(10) roots that carry the 16 Clifford weights to the 16 weights of the 27
and send SU(3), SU(2)_L and Y across. They form S3 (the three colour planes) × Z2 (the Weyl reflection of
su(2)_L): the identification is canonical up to Weyl symmetries. The 16 weights of the 27 must first be
projected: `so10_part(w) = w − w0⟨w,w0⟩/⟨w0,w0⟩`.

## 5. E8 ⊃ D7 × U(1): frame-Higgs and the 10

`check_frame_higgs.py`, `match_e8_d7.py`. Roots 240 = 84 + 2·64 + 2·14, i.e.

    248 = 91 + 1 + 64 + 64bar + 14 + 14,        so(14) = so(4) + so(10) + (4, 10).

* **[checked]** the 40 frame-Higgs generators are exactly 4 ⊗ 10 under spin(1,3) ⊕ spin(10); the 10 contains
  (3,1) + (3bar,1) and two Higgs doublets; the boost generator equals −I times the rotation.
* **[checked]** the 10 of the 27 has SO(10) weights exactly ±f_i; the Clifford complex 64 equals an E8 64.
* **[checked]** every placement of su(2) × su(2) (spin(1,3)_C) in the SU(4) that centralizes SO(10) shares
  exactly one su(2) with SU(3)_M. Consequently, of the three 16's in (27,3) at most two lie in the
  physical Majorana–Weyl 64 (family count 2 of 3 or 1 of 3 depending on which su(2) is inside SU(3)_M),
  the rest lie in the 64bar. This is a complex root statement; it is consistent with, but not a check of,
  the Distler–Garibaldi no-go theorem.

## 6. Triality placed against SU(4)

`check_triality_su4.py`. Singling out one f_i gives D4b (SO(10) roots orthogonal to f_i) and D4a (E8 roots
orthogonal to D4b), with 240 = 24 + 24 + 3·64. The centralizer SU(4) of SO(10) and SU(3)_M both lie in D4a.

1. Each (8,8) block is a full product 8X × 8X of weight classes **[checked]**, so triality acts on the two D4's
   independently and can be chosen to fix SU(3)_M pointwise. The explicit triality of
   `check_triality_d4d4.py` moves this A2 **[checked]**; another member of the family, T', fixes it.
2. The six A2-singlet weights of D4a form a hexagon in the plane orthogonal to SU(3)_M, one opposite pair in
   each of 8v, 8s, 8c; D4a = A3 ∪ A3' ∪ A3'': three SU(4)'s pairwise meeting exactly in SU(3)_M **[checked]**.
3. T' is a 120° rotation of the hexagon plane plus a triality of D4b. It permutes the 240 roots, fixes
   SU(3)_M pointwise, cycles the three 64's and the three SU(4)'s **[checked]**.
4. In W(E8): det(x − T') = (x−1)⁴(x²+x+1)² (class A2 × A2); the family Coxeter element c = s_a s_b has
   det(x − c) = (x−1)⁶(x²+x+1) (class A2); they commute, and T'c has order 3 and det = (x−1)²(x²+x+1)³
   **[checked]**. So the two 3's are independent, commuting order-3 elements.
5. Inside each 27, T' cycles 8v → 8c → 8s and the three SO(8) singlets, so it does not preserve
   1 + 16 + 10 (16 = 8 + 8, 10 = 8 + 1 + 1 under SO(8)); T'(16) shares 8 of 16 weights with the 16 **[checked]**.
6. For the Lorentz roots: each A3 root pair shares one su(2) with SU(3)_M; T' fixes it and moves the other
   su(2) into the other two SU(4)'s; the three images are the three su(2)'s of the A1³ centralizing the
   shared su(2) in D4a **[checked]**.

**Conclusion (root level).** The family 3 (horizontal SU(3)_M) and the triality 3 are different, commuting
symmetries; triality moves SM states within a family module and permutes three SU(4)–SO(10) pairs that share
SU(3)_M. Whether the triality 3 has any physical role once the family 3 is present is **[not checked]**.

## 7. Triality algebras, the magic square, and the Z3 grading

`check_magic_square.py`. These are topics of Lisi, arXiv:2609.12112; the script uses the standard
definitions, not the paper's text, and agrees with its Section 3 (tri(C) = u(1)+u(1), tri(H) = su(2)³,
tri(O) = so(8)) and its compound triality decompositions (7.1), (8.1), (9.1), which have the same dimension
counts (e6 = 2 + 28 + 48, e7 = 9 + 28 + 96, e8 = 28 + 28 + 192).

* Cayley–Dickson doubling gives R, C, H, O (O non-associative) **[checked]**.
* The triality algebra tri(A) = {(a,b,c) ∈ so(A)³ : a(xy) = b(x)y + x c(y)} is computed as an exact
  nullspace: dim tri(R, C, H, O) = 0, 2, 9, 28 **[checked]**.
* The magic square dimension L(A,B) = tri(A) + tri(B) + 3 dim A dim B gives the Freudenthal–Tits table
  3, 8, 21, 52 / 8, 16, 35, 78 / 21, 35, 66, 133 / 52, 78, 133, 248 **[checked]**. For A = B = O:
  248 = 28 + 28 + 3·64, the D4 × D4 count of §1; tri(O) = so(8) is the D4 with 24 roots + 4 Cartan **[checked]**.
* The class (l1 + 2 l2) mod 3 of the SU(3)_M weights is a Z3 grading of E8 with eigenspaces
  86 + 81 + 81 = (E6 + SU(3)) + (27,3) + (27bar,3bar), additive on root sums **[checked]**. This is the
  Vinberg-type Z3 grading (theta group of order 3); E8/(E6 × SU(3)) is a 3-symmetric space of dimension 162.
  It is the Z3 reading of the chirality theorem: the chiral 27 is the degree-1 piece.
* This grading is **not** Lisi's Θ. His triality eigenspaces for e8 have fixed algebra so(14) + u(1)
  (dimensions 92 + 78 + 78), while this one has fixed algebra e6 + su(3) (86 + 81 + 81). They are
  compared in §9.

## 8. Distler–Garibaldi, reproduced at the root level

`check_distler_garibaldi.py`. The paper (arXiv:0905.2658v3, 17 pages, all read) proves that no subgroup
SL(2,C)·G of the complex E8 or of a real form of E8 satisfies (ToE1) G compact connected and centralizing SL(2,C),
(ToE2) V_{m,n} = 0 for m + n > 4, and (ToE3) V_{2,1} is a complex representation of G. The argument has a
root-system part, reproduced here with the paper's Bourbaki numbering, and a real-form part (Killing-form
signatures, transfers R(E8,C), Galois descent, maximal compact subgroups), which is **[not checked]**.

**[checked]** against the paper's numbers:

* (5.5) the Dynkin index of the sl2 with defining vector ω_i is 2 4 7 15 10 6 3 1 for i = 1..8; Prop. 5.4:
  only ω_1 (index 2) and ω_8 (index 1) give weights in {0, ±1, ±2}.
* The two order-2 inner automorphisms of E8 have −1 eigenspaces of dimension 128 and 112, so the
  dimension no-go of §3 of the paper holds: three generations need 2·2·45 = 180 > 128 linearly independent
  weight vectors.
* Example 5.3: θ + θ′ = ω_1 (the diagonal of the two index-1 sl2's of the highest roots of E8 and of its E7).
* Lemma 6.1 and (6.4): the index 2 sl2 has centralizer so13 (dimension 78), e8 = 1·78 + 2·64 + 3·(1 + 13).
* (6.3): the pair of index 1 sl2's has centralizer so12 and e8 = (3,1) + (1,3) + (1,1)·66 + (2,1)·32 +
  (1,2)·32 + (2,2)·12.
* (6.6), (6.7): the two index 2 pairs; case (a) has all m + n even, case (b) has multiplicity table
  20 20 6 / 20 16 4 / 6 4 0 (centralizer sp4 × sp4).
* (9.4): index 1 × index 2 has table 39 18 1 / 32 16 0 / 10 2 0 (centralizer A1 × B4).
* The criterion behind (ToE3): the weights of the 32 of Spin(11) are closed under negation (−1 ∈ W(B5)),
  while negation exchanges the 16 and 16bar of Spin(10): a generation in S+ comes with an anti-generation.

One transcription was not used: the coroot table (6.2) did not commute with the sl2 as we read it from
the PDF image, so the defining vectors of (6.6) were tested directly (orthogonal to α_8 and to the D7 highest root).

**Link to this directory's frame [checked].** Each of the three orthogonal root pairs of the SU(4) that
centralizes SO(10) (the spin(1,3)_C candidates of `match_e8_d7.py`) is a pair of index 1 sl2's: the decomposition
(6.3) holds, the centralizer D6 = so12 contains SO(10), and V_{2,1} = 32 restricts to 16 + 16bar, with the
Standard Model 16 of `match_e8_spin113.py` one half. This is Remark 8.2 of the paper in our coordinates.

**What this does and does not say.** The dimension count assumes the fermion weight vectors of the
generations are linearly independent. Lisi's 2026 paper states (end of §10) that in his model the three generations
"are not linearly independent", and that the compact e8 assignment needs Euclidean rather than Lorentzian
signature (§9). Whether that escapes the chirality argument (ToE3) is **[not checked]**; nothing here decides it.

## 9. Lisi's triality eigenspaces against the family grading

`check_lisi_theta.py`. Lisi's Θ is an order-3 automorphism with eigenspaces g_0 + g_{+1} + g_{−1}; the Vinberg
Θ-algebra is g_0 + g_{+1}. At the root level, Θ = exp(−4πi w/3) on the U(1) charge w:

* **[checked]** (6.1) for e8: dimensions 92 + 78 + 78, g_0 = so(14) + u(1)_w (84 roots + 8 Cartan, Cartan
  matrix of α_2..α_8 is D7), g_{+1} = 14_{+1} + 64_{−1/2}; (6.2): the five-grading has 14 + 64 + 84 + 64 + 14 roots.
* **[checked]** (6.1) for e6: g_0 = so(8) + u(1)² (24 roots + 6 Cartan, fixed pointwise), g_{+1} = 8 + 8 + 8.
* **[checked]** Θ and the family grading χ (fixed algebra e6 + su(3)) commute and give a Z3 × Z3 grading of E8
  with joint dimensions (rows χ = 0,1,2; columns k = 0,1,2), the same for the three Lorentz root pairs up to k → −k:

        χ=0:  50   18   18
        χ=1:  21   42   18
        χ=2:  21   18   42

* **[checked]** Θ does not fix SU(3)_M. Two of its six roots (the su(2) shared with spin(1,3)_C) have k = 0 and
  two each have k = ±1, so Θ acts on SU(3)_M as an inner element of order 3 with fixed algebra su(2) + u(1). By
  contrast the Weyl-type triality T′ of §6 fixes SU(3)_M pointwise, and the family grading χ is trivial on it.
* **[checked, as a dimension count only]** the Weyl-type triality T of `check_triality_d4d4.py` has 12 fixed
  roots and 76 three-cycles; if its lift acts with trivial phase on the 12 fixed root vectors, its eigenspaces
  have dimensions 92 + 78 + 78, those of Θ. That is consistent with T and Θ being conjugate; it is not a proof.

**Interpretation.** The chirality theorem's Z3 (E6 × SU(3), the 27 repeated over a 3) and Lisi's Θ (D7 × U(1),
vector plus spinor) are two different order-3 gradings of E8. The family 3 and the triality 3 of §6 commute as Weyl
elements; Lisi's Θ and the family χ commute as torus elements and give the table above. Lisi's generations are
the 120° rotation of the 64 with its mirror (§9 of his paper, Ψ^I, Ψ^II, Ψ^III); that is a statement about
vectors in the representation space and is **[not checked]** by roots. Eq. (5.1) of the paper (the triality
matrix) was not transcribed; the T used here is a member of the same family of trialities.

## 10. Open items

1. The real form: whether the Lorentz signature selects su(2)_a, and the real-form half of Distler–Garibaldi
   (Killing-form signatures, G_max, transfers), which a root computation cannot see.
2. Whether the triality 3 can carry any physical structure once the family 3 is present, and whether Lisi's
   linearly dependent generations evade (ToE3).
3. The unread parts of arXiv:2609.12112: its §4 (su(3), sp(3), f4 in detail, paper pp. 12–24) and the §11–§12
   material on g2 and the discussion (pp. 45–50), and the particle tables 9 and 10 (not transcribed).

## 11. References and reading status

| Reference | Status here |
| :--- | :--- |
| A. G. Lisi, *An Exceptionally Simple Theory of Everything*, arXiv:0711.0770 | used as background; not re-derived |
| A. G. Lisi, *An Explicit Embedding of Gravity and the Standard Model in E8*, arXiv:1006.4908 | only abstracts / partial text readable; Eq. 3.1 garbled and not transcribed |
| J. Distler, S. Garibaldi, *There is no "Theory of Everything" inside E8*, arXiv:0905.2658v3 (also the abstract page https://arxiv.org/abs/0905.2658) | PDF read in full (17 pages); its root-system computations are reproduced by `check_distler_garibaldi.py` (§8); its real-form arguments are not checked |
| A. G. Lisi, *Division Algebras, Triality, and Exceptional Magic*, arXiv:2609.12112v1 (Adv. Appl. Clifford Algebras 36, 45, 2026) | PDF read for pages 1–11 and 25–44 (Clifford algebras from division algebras, generalized reflections and triality, the triality Lie algebras, the magic square, §6 triality eigenspaces and Vinberg Θ-groups, e6, e7, e8, §10 Exceptional Unification); pages 12–24 and 45–50 not read. Checked in `check_magic_square.py` (§7) and `check_lisi_theta.py` (§9) |
| INSPIRE record https://inspirehep.net/literature/820775 | **not read** (the page is a JavaScript shell and the API is not reachable here); the record was not identified. The user supplied arXiv:0905.2658 in the same message, which may be the intended paper, but that is a guess |
| *Trialities and Exceptional Lie Algebras: Deconstructing the Magic Square*, arXiv:0910.1828 | seen only as a search hit; not read |
