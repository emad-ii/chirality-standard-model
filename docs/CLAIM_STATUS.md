# Claim and Evidence Register

This register is the quickest way to see what the manuscript proves, what Lean
checks, what exact programs reproduce, and which statements are declared
physical interpretations. The labels are complementary evidence types, each
identifying the authority that carries the claim. “Lean checked” means a
concrete proposition in one of
[`CubicAnomaly/Classification/Exceptional.lean`](../CubicAnomaly/Classification/Exceptional.lean),
[`CubicAnomaly/E6/Claims.lean`](../CubicAnomaly/E6/Claims.lean).

## Status vocabulary

| Status | Meaning |
| --- | --- |
| **P — proved in manuscript** | The paper carries the stated proof |
| **L — Lean checked** | Lean 4 accepts the stated finite proposition through `native_decide` under the disclosed compiler/interpreter and upstream-distribution trust boundary; generated-data freshness and the exact axiom receipt are CI-gated |
| **C2 — independently reproduced** | Two exact implementations agree on the stated result. In the paired $E_6$ implementations, the coordinate realizations and Weyl actions are independently coded. Their closed-subsystem censuses use the same positive-simple-system enumeration strategy, so that census is independently reproduced at the coordinate-realization and Weyl-action levels while the enumeration strategy is shared |
| **C1 — exactly computed** | One exact integer/rational implementation and deterministic output are checked |
| **I — interpretive** | A stated physical interpretation or modelling assumption with its premise made explicit |

## Finite $E_6$ incidence claims

| ID | Claim | Status | Evidence |
| --- | --- | --- | --- |
| E6-01 | The generated reflection orbit has 72 roots of squared length 2, and $(1,2,2,3,2,1)$ is its greatest positive root in the simple-root order | **L, C1** | `e6_root_table_valid` (including `highestRootValid`) and the primary Cartan-coordinate implementation; the independent $\mathbb R^8$ route separately confirms the 72-root orbit |
| E6-02 | The three subsystem orbits have sizes 27, 36, and 40 and consist of closed systems with component signatures $(40,5)$, $(30,5)+(2,1)$, and $(6,2)^3$; standard simply-laced classification identifies $D_5$, $A_5+A_1$, and $A_2^3$ | **L, C1** | `subsystem_orbit_types_and_sizes_valid` and the primary exact implementation; both coordinate routes independently confirm the orbit sizes, while Lean checks closedness and component rank signatures |
| E6-03 | Their Cartesian product contains exactly 38,880 distinct triples | **L, C2** | `triple_space_has_38880_distinct_elements` |
| E6-04 | Six simultaneous-reflection orbits partition the full triple space and are classified by the six committed cell keys | **L, C1** | `six_weyl_orbits_partition_triple_space`; `six_cell_orbits_classified_valid`; primary exact implementation |
| E6-05 | The six cell counts are 12,960; 3,240; 3,240; 2,160; 12,960; and 4,320 in the committed key order | **L, C1** | `six_cell_distribution_valid`; primary exact implementation |
| E6-06 | Pairwise intersections are bounded by $(20,10,14)$ and exactly 4,320 triples attain all three bounds | **L, C2** | `extrema_counts_and_bounds_valid` |
| E6-07 | The largest common intersection has 10 roots and is attained by 2,160 triples | **L, C2** | `extrema_counts_and_bounds_valid` |
| E6-08 | A closed irreducible six-root, rank-two common component occurs exactly in the pairwise-maximal and common-maximal cells; the simply-laced rank-two classification identifies it as $A_2$ | **L, C2** | `a2_occurs_exactly_on_two_extremal_cells` |
| E6-09 | Pairwise maxima yield 720 common subsystems with multiplicity 6; common maxima yield 1,080 with multiplicity 2 | **L, C1** | `pairwise_common_multiplicity_valid`; `common_maximal_multiplicity_valid`; primary Python certificate computation |
| E6-10 | There are 1,080 $(D,\Theta)$ contexts, each with four pairwise and two common maximizers | **L, C1** | `context_counts_valid`; context-symmetry program |
| E6-11 | Pairing those choices produces 8,640 labelled proper-containment incidences and 2,160 distinct subsystem inclusions | **L, C1** | `labelled_containments_valid`; primary exact implementation |

Python computes the precise common root-system label in each of the six cells; the five occurring types are $A_1$, $A_1^2$, $A_1^3$, $A_2+A_1$, and $A_2+A_1^2$. Lean checks closedness and exact root-count/rank component signatures for the three maximal-subsystem orbits and detects an $A_2$ only as a six-root, rank-two irreducible component, not from the presence of an adjacent root pair.

## Other executable claims

| ID | Claim family | Status | Evidence |
| --- | --- | --- | --- |
| EX-01 | All 5,079 closed $E_6$ subsystems and 103 maximal proper subsystems | **C2** | Cartan-coordinate and $\mathbb R^8$ coordinate implementations agree; their root realizations and Weyl actions are independently coded, while both use the same positive-simple-system enumeration strategy |
| EX-02 | $E_6$ context stabilizers, exchange coset, and actual-chain orbit | **C1** | `check_e6_context_symmetry.py`; distinguishes 8,640 labelled pairings in two Weyl orbits from 4,320 chains in one orbit, retaining their Cartan spans |
| EX-03 | Weyl orbit/stabilizer, global $\mathbb Z_6/\mathbb Z_2$ kernels, and the $\mathbb Z_3$ kernel of the LR-to-PS covering-product map | **C1** | `check_proof_and_kernels.py` |
| EX-04 | Pair-first $d_\chi$ table | **P + C1** | Manuscript minuscule-restriction argument; `check_e6_pair_orderings.py` validates the character/domain before opposite-weight cancellation and rejects nonminuscule counterexamples |
| EX-05 | Classical cubic-surface data: 27 lines, 36 double-sixes, 45 tritangents, 40 triads | **C1** | primary Cartan-coordinate $E_6$ implementation |
| EX-06 | Full-rank inner-toral order-two/order-three exceptional grading census | **L, C2** | `exceptional_toral_census`; `exceptional_order_two_odd_graphs_connected`; two exact Python grading checks |
| EX-07 | Exceptional rank-deficient finite sieve | **C1** | deterministic audit JSON + verifier |
| EX-08 | Arithmetic used by the classical rank-deficient proof | **C1** | bounded Cartan/cubic regressions, exact $E_6$ dimensions, and symbolic all-rank odd $D$ inequalities; the manuscript carries the all-rank proof |
| EX-09 | Among the six full-rank rows, the grade-one Cartan trace cubic vanishes on exactly the rank-six, 72-root factor of the row conventionally labelled $E_8\supset E_6+A_2$ | **P + L + C2** | `cartan_cubic_selector` and an independent root-derived Python contraction prove the numerical statement; standard root-system classification supplies the $A_2+E_6$ labels |

## Classification proofs and physical interpretation

| ID | Claim family | Status | Evidence allocation |
| --- | --- | --- | --- |
| MP-01 | Structural normal form: simplicity of $\mathfrak g$, semisimplicity/maximality of $\mathfrak h$, irreducible complex complement | **P** | Manuscript compact-Lie and representation-theoretic proof |
| MP-02 | Exhaustiveness of the six full-rank homogeneous candidates | **P + L + C2** | Manuscript reduction from the homogeneous hypotheses; Lean and exact Python discharge the exhaustive exceptional inner-toral census |
| MP-03 | Exceptional rank-deficient no-go | **P + C1** | Manuscript necessity and completeness argument; exact finite arithmetic sieve discharges the bounded leaf |
| MP-04 | Uniform classical rank-deficient no-go | **P + C1** | The manuscript gives the infinite-family highest-weight proof; a separate executable audit checks its arithmetic |
| MP-05 | Cubic-invariant/radical argument selecting $E_8\supset E_6+A_2$ | **P + L + C2** | Manuscript invariant-theory bridge; Lean and Python discharge the finite Cartan trace-cubic selector from Cartan data |
| MP-06 | Integration to faithful global subgroups and the Standard Model / left–right chain | **P + C1** | Manuscript global Lie-group topology and branching proof; exact kernel arithmetic audit |
| PH-01 | Net chiral index is $\pm3$ for the two orientations | **P** | The branching and chiral-index calculation are proved in the manuscript |
| PH-02 | Under complete-matter interpretation (M), family multiplicity is three | **I** | Explicit physical interpretation conditional on complete matter |

## Recommended description

**“The project gives a computer-assisted classification and uniqueness theorem over the stated compact homogeneous domain. The manuscript proves the compact-Lie, completeness, invariant-theory, and representation-theoretic bridges; Lean checks the finite exceptional inner-toral census, Cartan trace-cubic selector, and bounded $E_6$ incidence propositions; and exact Python discharges and independently reconstructs the finite searches. The complete-matter interpretation (M) turns the resulting chiral index into a family count.”**
