# From Chirality to the Standard Model

## A visual investigation

The film follows one question: **could the conditions that constrain chiral matter also determine its structure?** The viewer should see why the question is worth asking, understand what is assumed, and follow the two classifications to their result.

This is an original film about the paper dated 6 September 2026, using the manuscript in this repository. Richard Behiel is a requested quality reference, not a collaborator or an endorsement. We have identified his public mathematics/physics channel; no particular reference film has been supplied or frame-by-frame analysed. We will not reuse his footage, narration, branding or voice.

Working format: a 12-minute, 16:9 narrated film for people who enjoy physics but do not know representation theory. The script allows roughly 1,300–1,450 spoken words, plus deliberate visual holds. A later extended edition can unpack the all-rank proof. The current 78-second silent pilot tests the central elimination sequence; it is not the completed main film.

## Story and timing

| Time | What the viewer sees and learns | Concrete animation | Evidence / hand-off |
|---|---|---|---|
| 0:00–0:45 | A mirror need not preserve the rules of the weak interaction. | A stylised cobalt-60 experiment. Nuclear spin stays an axial vector under parity; electron momentum reverses. The asymmetry, not the artist's hand shape, is the observation. | Lee–Yang 1956; Wu and collaborators 1957. Illustration labelled schematic, not measured event data. |
| 0:45–1:35 | Symmetry is a set of allowed transformations. A Lie algebra records infinitesimal ones. | Rotate an asymmetric object around two axes in opposite orders. Keep the endpoints visible. Shrink both angles; reveal the commutator as their leading difference. | Viewer can explain why two small rotations need not commute. Then distinguish spatial illustration from internal symmetry. |
| 1:35–2:25 | A representation tells us how the symmetry acts on a field. | A common phase dial drives charge-one and charge-two arrows at different rates. Then a two-component column mixes under an SU(2) transformation. Labels remain attached throughout. | Charge and dimension are different concepts. Irreducibility means no smaller nonzero subspace is preserved by every transformation. |
| 2:25–3:15 | Left and right have different weak representations; that difference constrains masses. | The left electron shares a weak-doublet bracket with its neutrino; the right electron sits in a singlet. An attempted mass coupling fails the gauge transformation test; inserting the Higgs restores it. | Show the electron example, not a claim that all mass comes from chirality. Define handedness of fields rather than showing classical spinning balls. |
| 3:15–4:00 | Quantum consistency constrains the representations. | A diagrammatic fermion loop with three labelled gauge insertions resolves into a cubic tensor. Introduce one anomaly channel at a time. | A local gauge anomaly obstructs the gauge symmetry; do not animate spacetime exploding. |
| 4:00–4:45 | What is ordinarily chosen, and what question is being reversed? | SU(5)'s 10 plus conjugate 5 fits inside a frame; Spin(10)'s 16 shows that unification need not assemble separate irreducibles. The multiplicity control remains separate. A short heterotic branch shows topology supplying an index. | Input/output comparison, not a story that previous physicists missed an obvious trick. |
| 4:45–5:40 | The embedding supplies a canonical representation. | A sphere and stabiliser give a low-dimensional illustration of G/H and its tangent plane. Replace the illustration with an abstract algebra decomposition. Isolate q, then its conjugate halves. | The sphere illustrates an isotropy representation only; it is not a candidate for the main theorem. State the effective compact inclusion and entire adjoint complement here; homogeneity is the geometric realization. |
| 5:40–6:25 | The radical finds an ideal rather than testing an arbitrarily chosen subgroup. | A tensor with three input sockets. X is constrained to a candidate ideal while Y and Z independently explore the whole isotropy algebra. All such outputs must vanish. | Say “for every pair of other inputs”. A few animated probes illustrate the definition, not its proof. |
| 6:25–7:30 | The classification covers the domain, then the last finite test leaves one pair. | An infinite-rank symbolic tree splits into equal-rank and lower-rank branches. Analytic branch labels remain visible; no invented numerical count of the whole domain. The full-rank branch becomes six labelled pairs. Each receives its own coefficient ports. Five dim only after their tests are displayed. | Main theorem, structural reduction using both invariant conditions, all-rank exclusions, Table 1. Last six are pairs, not six individual Lie algebras. |
| 7:30–8:15 | Why E₆, and why a factor of three? | The survivor's two ports separate: E₆ has coefficient 0; SU(3) has coefficient 27. An 81-dimensional representation rearranges into three 27-dimensional blocks under restriction. | Radical = E₆, commuting multiplicity space = 3. Do not confuse the nonzero cubic on the 27 with a cubic invariant on the E₆ Lie algebra. |
| 8:15–9:40 | The Standard Model step is another classification inside E₆. | Start from the certificate's 72 roots, explicitly labelled as a projection. Highlight D₅, A₅+A₁ and A₂³. Form 27×36×40 triples; collect them into six Weyl orbits. Compare the two distinct extremal cells and track the largest pair-first derived group. | The finite incidence data and faithful group reconstruction. Colour persists through restrictions. Root count and group dimension get different counters. |
| 9:40–10:40 | Recover the charge pattern and count the chiral content. | The group chain unfolds; a charge ruler constructs Y = T³_R + (B−L)/2. One 27 splits into 15 chiral components, 10 in a conjugate pair, and 2 singlets. Repeat the same block three times. | Pair-first construction; branching; chiral class. Conjugate pairs remain visibly present even when they cancel in the index. |
| 10:40–11:30 | What has been established, and how can a viewer inspect it? | The theorem hypotheses reappear as a compact frame around the result. The proof, finite computation and actual Lean declarations connect to the relevant notebook cells. | Never depict a green Lean badge as a proof of the entire analytic classification. Derive the net chiral class by restriction, keeping the full branching visible. |
| 11:30–12:00 | Return to the observation and the person asking the question. | The weak-doublet drawing from the opening now sits beside the recovered charge pattern. Hold the result quietly; finish on the paper and repository address. | “For my son Noah, on his eighteenth birthday.” Date 6 September 2026. No claim that this measures masses or establishes the physical model experimentally. |

## Visual direction

The setting is an illuminated mathematical workbench: near-black blue, warm ivory type, soft blue for a representation, copper for its dual, and restrained gold for a surviving ideal. Use colour plus position and labels, never colour alone. Avoid the visual vocabulary of a pitch deck: boxed slogans, persistent status badges, floating decorative formulae and generic space footage.

The camera stays still while an equation is being read. It moves when a relationship changes: a space becomes a tangent plane, one representation restricts to a subgroup, or the landscape of cases contracts. A transformation should preserve the viewer's object of attention. No dissolving a diagram into an unrelated diagram merely because both look attractive.

Typeset equations exactly with KaTeX/SVG or Manim. Introduce the object in words, show its behaviour, then reveal its notation. Start with physical pictures; gradually replace them with algebra the viewer can now read. A root projection must always be identified as a lower-dimensional image of mathematical data, not a literal object in physical space.

Target master: 3840×2160 at 30 fps after the 1920×1080 edit is approved. The pilot is 1080p. Main labels should generally be at least 42 px at 1080p; supporting labels at least 26 px. Leave a lower safe band for optional captions. Equation landings get 3–5 seconds without new material. No flashes or aggressive zooms. All motion is finite and seekable.

## Tool choice

**Hyperframes + GSAP:** master edit, chapter timing, camera transforms, labels, captions and reproducible frame capture. Local rendering does not require a HeyGen account or credits. Use its code-based composition tools, not an avatar-led template.

**Exact SVG and numerical data:** phase arrows, rotation matrices, anomaly ports, branching diagrams and certificate-derived incidence illustrations. Original mathematical visuals are deterministic, not generated images of plausible equations.

Two bridges are indispensable in the final edit. Before testing individual coefficients, explain why mixed cubics vanish between distinct simple factors in the semisimple shortlist. At the survivor, keep both coefficient ports visible and state that SU(3)ₘ is a background global symmetry whose anomaly remains. A nonzero radical is not vanishing of the entire cubic tensor.

Teach the F₄ coefficient row at enlarged scale before returning to all six rows. For the second classification, use one worked triple before the complete census: form the pairwise derived groups, compare their dimensions, select the largest, and intersect with the third regular group. Do not compare the unreduced groups and only take a derived group afterward. The pairwise-maximal orbit gives the Standard Model output; the common-maximal orbit gives the left–right output. Explain that precisely these two common intersections contain an irreducible A₂ component.

**Manim:** reserve for longer symbol-preserving derivations or genuine formula transformations. Reuse the existing renderer where it helps, but do not turn every chapter into a succession of equation cards.

**Three.js, when justified:** root projections, cutaway geometry and camera-controlled 3D. Its clock must be driven by the film playhead; a free-running animation loop will not produce reliable rendered frames. Start from simple tested geometry, not an ornamental particle swarm.

**Illustration generation:** only if the historical scenes need commissioned-style original art. Keep scientific apparatus, axes and exact labels under deterministic control. No fake archive photographs or quotation cards.

**Narration:** user recording or a licensed synthetic voice after the voice choice. Never clone Behiel or imply he presents the film. No paid voice or cloud rendering is required for the current pilot. Keep captions and pronunciation notes editable. Pronounce the algebra names before relying on their symbols.

## Production sequence and gates

1. **Evidence and story lock.** Every scientific beat gets a paper section or primary external source. An independent physics reviewer checks the transitions, not just isolated sentences.
2. **Narration read-through.** Record a temporary read at a conversational pace. Time actual audio, then revise the shot durations. Word-count estimates are not final timing.
3. **Hardest-scene pilot.** Render the six-to-one sequence and the representation split. Inspect entry, motion and end frames and test arbitrary seeking. Confirm whether the viewer can explain why the other five rows fail.
4. **Grey-box animatic.** Make the whole narrative with simple shapes and scratch narration. Resolve pacing and missing prerequisites before polishing history and 3D.
5. **Final visual production.** Build chapters in independently renderable scenes. Preserve source data and stable identities through every transition.
6. **Adversarial review.** A physicist checks claims and visual implications. A novice reviewer answers the five questions below without the script. A motion/accessibility review checks reading time, captions and legibility at phone size.
7. **Master and delivery.** Render chapter by chapter, then the 4K master. Deliver MP4, caption files, transcript, sources and editable project. Check file duration, stream properties, audio loudness, black frames, missing assets and transition continuity. Publish only the finished, reviewed cut, not this work-in-progress pilot.

No aggregate rating can hide a factual error. “Looks impressive” is not an acceptance test for a missing inference.

## Five viewer tests

After a viewing, a nonexpert should be able to explain:

1. What a representation tells us that a group name alone does not.
2. Why the electron's left/right weak charges obstruct its bare Dirac mass.
3. What the radical tests, including the other two inputs.
4. Why six-to-one is the final stage of a larger classification, not a search through six favourite groups.
5. Why three copies of a 27 give three net chiral families while additional states remain in the full representation.

Failure on any question means revise that transition. Real novice testing remains a production gate; agent review cannot substitute for it.

## Sources

- [Paper and verification repository](https://github.com/emad-ii/chirality-standard-model/tree/main).
- [Lee and Yang, Question of Parity Conservation in Weak Interactions (1956)](https://doi.org/10.1103/PhysRev.104.254).
- [Wu et al., Experimental Test of Parity Conservation in Beta Decay (1957)](https://doi.org/10.1103/PhysRev.105.1413).
- [NIST historical account by experiment collaborator Ralph P. Hudson](https://nvlpubs.nist.gov/nistpubs/sp958-lide/html/111-115.html), including the National Bureau of Standards team's role.
- [CERN: the Standard Model](https://home.cern/science/physics/standard-model).
- [Georgi and Glashow, Unity of All Elementary-Particle Forces (1974)](https://doi.org/10.1103/PhysRevLett.32.438).
- Historical GUT, heterotic and classification references are in the paper's introduction and bibliography; final on-screen citations must be checked against the corresponding originals during chapter production.
- [Richard Behiel's public channel](https://www.youtube.com/@RichBehiel), quality reference only.
- [Hyperframes quickstart](https://hyperframes.heygen.com/quickstart), [animation contract](https://hyperframes.heygen.com/guides/gsap-animation), [rendering](https://hyperframes.heygen.com/packages/cli), [deterministic frames](https://hyperframes.heygen.com/concepts/determinism).

## Scope of this production project

The manuscript, existing website, published notebook and old film are unchanged. This project is local and separate. The pilot visualises a sourced table and representation arithmetic; its tests do not re-prove the paper. Full narration, all chapters, sound design, human learner testing and 4K mastering remain subsequent production work.
