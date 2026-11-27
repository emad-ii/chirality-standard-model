# Lisi bridge: two ways to see three families inside E8

This directory connects the chirality theorem of this repository to the E8
programme of A. Garrett Lisi ("An Exceptionally Simple Theory of Everything",
arXiv:0711.0770; "An Explicit Embedding of Gravity and the Standard Model in
E8", arXiv:1006.4908). The root-system scripts use exact integer or rational
arithmetic. The Clifford scripts use exact integer matrices for the algebra
relations and floating-point eigen-decompositions (numpy) for spectra, always
rounded to exact rationals and asserted.

```sh
python3 lisi/run_all.py
```

`run_all.py` runs all fourteen scripts below in a fresh process each and takes a few minutes
(the longest are the sympy and root-search scripts); `python3 lisi/sm_charges.py` alone takes
a second.

| Script | What it checks |
| :--- | :--- |
| `e8.py` | Exact 240-root E8 system (doubled integer coordinates), closure, E7 = 126 orthogonal roots |
| `check_e6_su3_bridge.py` | E8 ⊃ E6 × SU(3): 240 = 72 + 6 + 6·27; the 27 repeats over the 3; 27bar = −27; 45 zero-sum triples (the E6 cubic invariant) |
| `check_triality_d4d4.py` | E8 ⊃ D4 × D4: 240 = 24 + 24 + 3·64; an order-3 automorphism cycles (8v,8v) → (8s,8s) → (8c,8c) |
| `check_common_refinement.py` | A2 ⊂ first D4, so E6 ⊃ second D4: E6 roots = 24 + 3·16; each 27 = 8v + 8s + 8c + 3 singlets |
| `sm_charges.py` | sympy: 27 = 1 + 16 + 10 under SO(10) × U(1); SM content of the 16 and 10; hypercharge from roots; exact Σ Y = Σ Y³ = Σ Q = Σ Q³ = 0 and the mixed SU(2)² Y, SU(3)² Y sums; the SU(5) pattern of Y on the 40 SO(10) roots. Its `build()` is what `match_e8_spin113.py`, `make_report.py` and four further scripts import (see *Provenance* in `THEORY.md` §2) |
| `check_dirac_weyl.py` | sympy: Section 2 of Lisi 2010 — Pauli identity, su(2) bracket, Weyl-representation gammas, P_L / P_R, spin(1,3) = sl(2,C), one-generation hypercharge |
| `spin113.py` | numpy: real Cl(11,3) with 14 gammas of size 128, spin(11,3) = 91 = 6 + 45 + 40, Majorana-Weyl 64, Pati-Salam (21) and Standard Model (12) generators; the left-handed subspace W (γ5 = −1) carries exactly one signed left-handed Standard Model generation, which correlates su(2)_L with the orientation of the colour complex structure |
| `match_e8_spin113.py` | sympy + numpy: exact isometry from the Clifford Cartan weights of W onto the E8 weights of the 16 ⊂ 27, carrying SU(3), SU(2)_L and Y across; the 12 solutions are exactly S3 × Z2 (Weyl symmetries) |
| `check_frame_higgs.py` | numpy: the 40 frame-Higgs generators are exactly 4 × 10 under spin(1,3) ⊕ spin(10); the 10 = (3,1) + (3bar,1) + two Higgs doublets; boost = −I · rotation; 64 weights (±½)^7 over the seven planes of so(14) |
| `match_e8_d7.py` | E8 ⊃ D7 × U(1): 240 = 84 + 2·64 + 2·14; the 40 are the roots (10,(2,2)); the 10 of the 27 is the SO(10) vector; the Clifford 64 equals an E8 64; spin(1,3) against SU(3)_M and where the three 16's sit |
| `check_triality_su4.py` | sympy: places the D4 × D4 triality against SU(4) = centralizer of SO(10): D4a = three SU(4)'s meeting in SU(3)_M; an explicit triality T' fixing SU(3)_M pointwise, commuting with the family cycle, acting inside each 27; what it does to the SO(10)'s and to the spin(1,3) root pairs |
| `check_magic_square.py` | sympy: Cayley–Dickson R, C, H, O; triality algebras tri(A) of dimension 0, 2, 9, 28; the magic-square table; the Z3 grading E8 = (E6 + SU(3)) + (27,3) + (27bar,3bar). Built from standard definitions of the topics in arXiv:2609.12112, not from its text |
| `check_distler_garibaldi.py` | sympy: reproduces the root-system computations of Distler–Garibaldi (arXiv:0905.2658): sl2 Dynkin indices, the 128-vs-180 dimension bound, the decompositions (6.3), (6.4), (6.7), (9.4), and V_{2,1} = 16 + 16bar for each Lorentz root pair of this directory's frame. The real-form arguments are not checked |
| `check_lisi_theta.py` | sympy: Lisi's triality eigenspaces (arXiv:2609.12112 §6, eq. 6.1, 6.2) for e6 and e8 at the root level, and the Z3 × Z3 grading they form with the family grading of the chirality theorem |
| `make_report.py` | Builds `report/sm_charges.tex` from the sympy model and compiles `report/sm_charges.pdf` with pdflatex |

A longer write-up with every result, its status and the reference list is in
[`THEORY.md`](THEORY.md).

`e8.py` and the first three `check_*` scripts need only the standard library;
`sm_charges.py`, `check_dirac_weyl.py` and `make_report.py` need sympy;
`spin113.py` and `check_frame_higgs.py` need numpy; `match_e8_spin113.py` and
`match_e8_d7.py` need both: `pip install -r lisi/requirements.txt`
(and a TeX installation with `pdflatex` for the report).

## The two mechanisms

* **This repository (chirality theorem).** Families come from the *horizontal*
  SU(3)_M in E8 ⊃ E6 × SU(3)_M, giving V = 27 ⊠ 3. E6 is chiral yet has no
  cubic anomaly.
* **Lisi.** Families come from *triality* of D4 in E8 ⊃ D4 × D4, which permutes
  three 64-dimensional blocks.

Both live in the same root system. They meet in the common refinement
SU(3)_M × D4 ⊂ E6 × SU(3)_M: with SU(3)_M inside the first D4, the E6
centralizer contains the second D4, and every 27 decomposes as
8v + 8s + 8c + 1 + 1 + 1. The triality triple Lisi uses for generations
therefore sits inside each chirality-theorem family module, while SU(3)_M
supplies the horizontal 3. Whether these two threefold structures are
physically the same is not established here.

## Spin(1,3) against SU(3)_M

Lisi's spin(11,3) puts the complexified Lorentz algebra spin(1,3)_C = su(2) × su(2)
and the Higgs/frame multiplets next to SO(10) in E8 ⊃ Spin(14) × U(1):

    248 = 91 + 1 + 64 + 64bar + 14 + 14,     so(14) = so(4) + so(10) + (4, 10).

`match_e8_d7.py` verifies these root counts and the matching: the 40 frame-Higgs
generators are the roots (10, (2,2)), each 14 is (1,10) + (4,1), the 10 is the same
vector 10 that sits beside the 16 in the 27 (same isometry as for the 16), and the
Clifford complex 64 equals an E8 64.

The chirality theorem's SU(3)_M and Lisi's spin(1,3)_C both live in the SU(4) that
centralizes SO(10). The roots show that **every** placement of su(2) × su(2) in that
SU(4) shares exactly one su(2) with SU(3)_M, and the other factor lies outside it.
Consequently the three 16's of (27, 3) are not all in the physical Majorana–Weyl 64:

| su(2) inside SU(3)_M | families in the physical 64 | the 16 in the E6 adjoint |
| :--- | :---: | :---: |
| su(2)_a (acts on the physical Weyl spinor) | 2 of 3 | in the 64bar |
| su(2)_b (the other factor) | 1 of 3 | in the physical 64 |

The rest lie in the 64bar. This is a statement about the complex root system; it does
not see the real form (the Lorentz signature) and is not a proof of, or a check on, the
Distler–Garibaldi theorem. It does say, concretely, how the horizontal 3 of the
chirality theorem and the spin doublet of Spin(1,3) overlap.

## Triality against SU(4)

Fix one `f_i` of the SO(10) frame. The SO(10) roots orthogonal to it form a D4b, the E8 roots
orthogonal to D4b form a D4a, and E8 ⊃ D4a × D4b with 240 = 24 + 24 + 3·64. The SU(4) = A3
centralizing SO(10) and the horizontal SU(3)_M both lie in D4a (`check_triality_su4.py`, for each of the
five choices of `i`).

* Each (8,8) block is a full product 8X × 8X of weight classes, so triality acts on the two D4's
  **independently** and can be chosen to fix SU(3)_M pointwise. The explicit triality of
  `check_triality_d4d4.py` does not (it moves this A2), but another member of the same family, T', does.
* D4a = A3 ∪ A3' ∪ A3'': **three SU(4)'s pairwise meeting exactly in SU(3)_M**. The six A2-singlet
  weights of D4a form a hexagon in the plane orthogonal to SU(3)_M, one opposite pair in each of
  8v, 8s, 8c; T' is the 120° rotation of that plane (together with a triality of D4b) and permutes the three
  SU(4)'s cyclically. Hence T' carries (SO(10), SU(4)) to two other pairs; the three SO(10)'s meet exactly in D4b.
* **The two 3's are independent.** T' fixes the family labels (it acts inside each 27) and commutes with the
  family Coxeter element c = s_a s_b: T' has class A2 × A2, c has class A2, and T'c has order 3 and
  class 3 × A2. Inside each 27, T' cycles 8v → 8c → 8s and the three SO(8) singlets, so it does not
  preserve the split 1 + 16 + 10 (16 = 8 + 8, 10 = 8 + 1 + 1 under SO(8)); T'(16) shares 8 of 16 weights with
  the 16.
* **Spin(1,3).** Each A3 root pair shares one su(2) with SU(3)_M. T' fixes that su(2) and moves the other
  su(2) into the other two SU(4)'s; the three images are exactly the three su(2)'s of the A1³ that centralizes
  the shared su(2) in D4a.

Answer to the triality question, at the root level: Lisi's triality 3 and the chirality theorem's family 3
are **not** the same 3. They are commuting order-3 symmetries. The family 3 is the horizontal SU(3)_M weight
and survives; the triality 3 permutes the three SU(4)–SO(10) pairs that share it and mixes the
SM states inside one family module (for `f_4`, `f_5` the singlets are the SO(10) singlet and two Higgs-doublet
components of the 10; for `f_1`–`f_3` they are the singlet and the colour triplet and anti-triplet of the 10).
Whether a physical generation structure can use the triality 3 as well is not decided here.

## Scope and honesty

* `spin113.py` builds Cl(11,3) independently. It does **not** transcribe the
  paper's explicit matrices (Eq. 3.1): the tool used to read the paper returned
  that equation garbled. Because Cl(11,3) ≅ M(128, R) is simple, every real
  128 × 128 Clifford set is conjugate to the paper's, so the checked statements
  (dimensions, closure, the 6 + 45 + 40 split, Majorana-Weyl 64, Pati-Salam and
  Standard Model content) are convention independent. Index orderings, signs and
  the paper's fermion basis (Eq. 2.5, 2.8) are not reproduced.
* Chirality: on the real 64, the complex structure I = Γ1Γ2Γ3Γ4 selects the
  left-handed space W (γ5 = iΓ1Γ2Γ3Γ4 = −1, the convention of
  `check_dirac_weyl.py`). The *signed* hypercharge on W reproduces the
  left-handed Standard Model only for (κ = −1/3, T3_R from the L triple) or
  (κ = +1/3, T3_R from the R triple). These two are conjugate under
  U = Γ6Γ8Γ10Γ11 ∈ Spin(10), which reverses the orientation of the colour
  complex structure (3 ↔ 3bar) and swaps the triples. So su(2)_L is fixed
  *relative to that orientation*; there is no orientation-independent statement
  of which su(2) is "left", and none is claimed.
* The 10 and the singlet of the 27 are not in the 64 (they are not fermions of one
  spin(11,3) generation). The 10 appears instead as the Higgs part of the 14 and in
  the 40 frame-Higgs roots (`match_e8_d7.py`); the singlet has no SO(10) weight.
* The D7 × U(1) structure is a statement about the complex root system. Which
  su(2) factor of spin(1,3)_C acts on the physical Weyl spinor (su(2)_a) is a
  naming choice at the root level; both choices occur and are reported.
* `check_dirac_weyl.py` uses the standard Weyl representation. The hypercharge
  formula was relayed by a summary of the paper, not read verbatim; reproducing
  the Standard Model hypercharges from it is a consistency check on that.
* The root-system scripts verify finite facts only. `check_distler_garibaldi.py`
  reproduces the root-system computations of the Distler–Garibaldi no-go theorem
  (arXiv:0905.2658: Dynkin indices, the 128 < 180 dimension count, the decompositions
  (6.3), (6.4), (6.7), (9.4)) with the paper's own numbers. Its real-form arguments
  (Killing-form signatures, maximal compact subgroups, transfers) are not checked, so
  the theorem itself is not re-proved. The family count above is a different,
  complex-algebra statement. Lisi's 2026 model claims linearly dependent generations
  (triality-related) and a Euclidean compact e8; whether that evades the theorem's
  chirality condition is not examined here.
* `check_lisi_theta.py`: Lisi's Θ (fixed algebra D7 × U(1)) is a different order-3
  grading from the chirality theorem's (E6 × SU(3)). They commute and form a
  Z3 × Z3 grading of E8; Θ breaks SU(3)_M to SU(2) × U(1). Details in `THEORY.md` §9.

## Next steps

1. (done) Spin(11,3) / Pati–Salam matrices and Clifford relations
   (`spin113.py`, `check_dirac_weyl.py`); su(2)_L correlated with chirality;
   64 matched to the E8 weights of the 16 ⊂ 27 (`match_e8_spin113.py`);
   frame-Higgs 40, the 10 and the E8 ⊃ D7 × U(1) structure
   (`check_frame_higgs.py`, `match_e8_d7.py`).
2. (done) Triality 3 of D4 × D4 placed against SU(4), SU(3)_M and spin(1,3)
   (`check_triality_su4.py`): commuting, independent 3's.
   Still open: the real form (does the Lorentz signature select su(2)_a?), and whether the
   triality 3 plays any physical role for generations once the family 3 is present.
3. (done) Standard Model quantum numbers of the 27 under SO(10) × U(1)
   (`sm_charges.py`, `report/sm_charges.pdf`). `sm_charges.py` was rewritten after it was found
   missing from the repository (six of the fourteen checks import it); `make_report.py`
   regenerates `report/sm_charges.tex` identically from the rewrite.
