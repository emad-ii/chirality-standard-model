# Release Audit

**Status:** `v0.1.0` release; every hosted release gate passed on the tagged commit on 5 September 2026.

## Audited release state

1. **Full-rank dependency.** Condition (3), the nonzero cubic radical, is used in Lemma 2.2 to prove that the isotropy algebra is semisimple. The direct toral census is therefore stated under Conditions (1) and (3), yields six necessary structural possibilities, and is followed by the cubic-coefficient calculation that eliminates five. Dropping Condition (3) at this stage would admit $SU(3)/S(U(2)\times U(1))\cong\mathbb{CP}^2$, so the regression suite explicitly preserves this dependency.
2. **Equation numbering.** The intermediate formulas are tagged (6c)–(6f), leaving (7)–(11) unique and sequential for the branching/chirality section.
3. **Verification entry point.** The paper names `make verify`, which executes every distributed check, including the standalone order-three audit.
4. **Formal scope.** The paper appendix describes the finite Lean checker and assigns the analytic bridges to the manuscript proof.
5. **Independent finite layer.** Lean regenerates all five exceptional root systems, exhausts the full-rank inner-toral order-two/order-three census, and derives the Cartan trace-cubic selector directly from Cartan data. A separate exact Python implementation reaches the same selector. The manuscript carries the compact-Lie reduction and the invariant-theory promotion from Cartan restriction to the ideal-valued radical.
6. **Exact subsystem semantics.** The certificate-fed Lean checker now proves root negation/addition closure and computes the root count and lattice rank of every irreducible component. Standard simply-laced classification identifies the resulting signatures with $D_5$, $A_5+A_1$, $A_2^3$, and the common $A_2$; none rests on mask sizes or adjacent-root pairs alone.
7. **Optimization-independent verification.** Every release-critical Python invariant uses an explicit runtime check. The gate statically rejects Python `assert` statements and is repeated with interpreter optimizations enabled.
8. **Global-form map.** The covering-product map from the displayed left–right product to the Pati–Salam product is correctly shown with kernel $\langle k_{\mathrm{LR}}^2\rangle\cong\mathbb Z_3$; only the induced faithful quotient map is injective.
9. **Counting and scope.** The paper distinguishes 8,640 labelled containment incidences from 2,160 distinct inclusions and distinguishes bounded classical arithmetic regressions from the symbolic all-rank step and manuscript proof.
10. **Proof exposition.** The classical involution and block-stabilizer equality cases are explicit, and the text distinguishes commuting toral automorphisms from their generally noncommuting fixed groups.
11. **Formula domains and character semantics.** The classical cubic formula chooses the smaller dual node; the SU(n) census distinguishes an inner automorphism from its lift; cubic-index normalization excludes SU(2); and the two-factor proof uses disjoint self-dual blocks with the vanishing-block case treated separately. The chiral-dimension checker validates its minuscule-character domain and rejects the SU(3) and E6 symmetric-cube counterexamples. The one-family parent criterion is explicitly evaluated before further restriction. These repairs preserve every numerical table and the classification statements; source mutations and exact boundary regressions guard their scope.

12. **Extraction scope and conventions.** The discussion names the subgroup-extraction criteria separately from the homogeneous hypotheses. The E6 census row and later branchings use one SU(3) conjugation convention. Exceptional sieve counts explicitly retain both B2 and C2 labels, with their representation/index equivalence checked. The context regression distinguishes 8,640 labelled pairings in two Weyl orbits from 4,320 actual chains in one orbit, including their Cartan spans; this is an exact Python check, not an added Lean theorem.

## Release results

GitHub Actions runs the four content lanes for pull requests, pushes to `main`,
`release-v*`, and `v*` tags, and manual `workflow_dispatch` runs. Outside pull
requests, only `main`, `v0.1.0`, and `release-v0.1.0` can pass the release-
identity job.
The release was accepted only after the exact tagged commit passed every lane
and the three-way identity job matched `main`, the annotated tag, and the
release launcher to that commit.

| Gate | Result |
| --- | --- |
| Python verification | **Pass** — 16 release checks passed at both normal and optimized interpreter settings, including two regenerated JSON artifacts, all 12 exact output fixtures, fail-closed semantic-certificate and adversarial paper/documentation mutations, and a static ban on removable assertions |
| Master notebook top-to-bottom | **Pass** — the canonical source-only notebook matches its builder; CI executed all 10 code cells, separately validated its release-input digest, execution commit, and canonical tag commit against the three-way identity job, and published the executed notebook as a run artifact |
| Lean / Mathlib build | **Pass** — Lean 4.28.0 and Mathlib source revisions were fixed; the build ran under the disclosed upstream compiler/cache trust boundary, and all `native_decide` propositions passed in the clean CI environment |
| Lean generated-data freshness | **Pass** — byte-for-byte match to certificate `1744359c…aab98cb` |
| Lean proof-hygiene / axiom receipt | **Pass** — all 18 exported theorems are covered and the exact disclosed `native_decide` trust receipt is enforced |
| Paper build | **Pass** — 35-page warning-free manuscript, two byte-identical fixed-metadata builds, exact 288-dpi RGB equivalence with the committed PDF, page-local searchable prose/number fingerprints, stable metadata, embedded fonts, and no active content |
| PDF visual inspection | **Pass** — representative pages across the title, proof, appendix, code listing, references, and AI disclosure were rendered from the hosted artifact and inspected |

## Release artifact hashes

| Artifact | SHA-256 |
| --- | --- |
| `verification/certificates/e6_extrema_certificate.json` | `1744359c67f009daa67c43a0989502026b69a3e10597a57706833cff0aab98cb` |
| `paper/paper.tex` | `9997a4dc571ae0e886c983da8a4538d73ee688c1c37d474aa7f60ad4c03b5258` |
| `paper/paper.pdf` | `9ba8b62354153e029b77941234e308e060831023e680743409d6696894bd635c` |
| `Cubic_Anomaly_Master_Verification.ipynb` | `51512404e91d52c9464aedcc4aed88d13867b3d1e21d19d5c608b77e68b9f46b` |

## Formal audit summary

- No project-specific axioms.
- No proof placeholders.
- No unsafe or partial public declarations.
- The certificate-free Lean census regenerates the 12, 48, 72, 126, and 240 exceptional roots from five Cartan matrices.
- Lean exhausts the full-rank inner-toral order-three rows and recovers exactly the six numerical component signatures used by the paper.
- Lean derives the Cartan trace-cubic null factor only in the numerical row
  with component signatures $(6,2)+(72,6)$; exact Python independently
  reproduces it, and standard root-system classification supplies the
  conventional $A_2+E_6$ labels.
- Six simple-reflection permutations are checked against the fixed Cartan formula.
- Every selected subsystem mask is checked for root negation/addition closure; Lean computes paired component root-count/rank signatures, and standard simply-laced classification supplies the conventional subsystem type names.
- The common $A_2$ theorem recognizes a closed six-root, rank-two irreducible component rather than merely an adjacent root pair; standard simply-laced classification identifies it as $A_2$.
- Expected finite counts are stated outside generated certificate data.
- The finite checker covers the full 38,880-triple incidence surface, not only six representatives.
- The manuscript carries the bridge from homogeneous pairs to the finite exceptional census, the invariant-theory promotion from Cartan restriction to a radical ideal, and the broader rank-deficient classification; exact Python carries the complete 5,079-subsystem census, Weyl-group order 51,840, and exact common root-system labels.

See [`CLAIM_STATUS.md`](CLAIM_STATUS.md) for claim-level status and [`FORMALIZATION_BOUNDARY.md`](FORMALIZATION_BOUNDARY.md) for the trust model.
