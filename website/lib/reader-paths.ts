export const chapterInfo = {
  question: {
    title: 'The mirror and the language of symmetry',
    summary:
      'Wu’s mirror experiment and the origins of the mathematical language of symmetry.',
  },
  foundations: {
    title: 'Lie algebras and representations',
    summary:
      'Learn what a generator does, how a representation acts, and why dimensions and families are different counts.',
  },
  frontiers: {
    title: 'How physicists built the pattern',
    summary:
      'Follow electroweak discoveries, then compare SU(5), Spin(10), E₆, heterotic compactification and the paper.',
  },
  physics: {
    title: 'The Standard Model, from fields to experiments',
    summary:
      'Read electron and quark charges, connect the mathematics to measurements, then explore mass and anomaly cancellation.',
  },
  selection: {
    title: 'From a broad domain to one pair',
    summary:
      'Follow the reduction to six candidates, then one nonzero cubic radical.',
  },
  argument: {
    title: 'The assumptions and the cubic test',
    summary:
      'Define the compact embedding, its adjoint complement and cubic radical, then inspect the six candidates.',
  },
  geometry: {
    title: 'Inside the surviving E₆',
    summary:
      'Explore 38,880 triples, six orbits, and two extremal configurations.',
  },
  families: {
    title: 'Read the matter content',
    summary:
      'See the familiar charge pattern reappear when the 27 branches, then count the three net families.',
  },
  implications: {
    title: 'Return to the physical question',
    summary:
      'What the common geometric origin fixes about the pattern of matter.',
  },
  verify: {
    title: 'Read the proof and run the checks',
    summary:
      'The manuscript, independent searches and finite Lean checks, with their source snapshot.',
  },
} as const;
export type ChapterId = keyof typeof chapterInfo;
export type PathId = 'curious' | 'physics' | 'mathematics' | 'review';
export type ReaderPath = {
  id: PathId;
  label: string;
  depth: string;
  description: string;
  title: string;
  introduction: string;
  chapters: ChapterId[];
  stops: { id: ChapterId; label: string }[];
  bridges: Partial<Record<ChapterId, string>>;
};
export const readerPaths: ReaderPath[] = [
  {
    id: 'curious',
    label: 'I’m curious',
    depth: 'story',
    description:
      'Begin with an experiment. Build the idea without assuming the mathematics.',
    title: 'Begin with a world that distinguishes left from right.',
    introduction:
      'Start with Wu’s experiment. Learn what symmetries and representations mean, see how they describe the particles we measure, then follow the paper’s search for a common origin. The equations open when you want them.',
    chapters: [
      'question',
      'foundations',
      'physics',
      'frontiers',
      'selection',
      'argument',
      'geometry',
      'families',
      'implications',
      'verify',
    ],
    stops: [
      { id: 'question', label: 'The mirror' },
      { id: 'physics', label: 'The particles' },
      { id: 'selection', label: 'What survives' },
      { id: 'families', label: 'Three families' },
    ],
    bridges: {
      foundations:
        'The experiment establishes an asymmetry in nature. To describe it precisely, we need to know how a symmetry acts on a field. Begin with a transformation you can move yourself.',
      physics:
        'We have the language: an algebra gives transformation rules, a representation tells us how a field follows them. Now meet the Standard Model and work out the charges of an electron and its quark neighbours.',
      frontiers:
        'The particle pattern and its consistency tests were built from experiment and theory. How much does an ordinary unification scheme determine, and which choices does it leave open?',
      selection:
        'Handedness and anomaly cancellation constrain matter. The paper asks for one more connection: let the larger symmetry supply the representation itself. Which compact algebra embeddings can do that?',
      argument:
        'One pair remains in the animation. The reason is a theorem with stated assumptions. Here they are, with the calculation behind the last elimination.',
      geometry:
        'Finding E₆ is only part of the route. Its smaller symmetry patterns determine which overlaps can carry the familiar colour and weak factors.',
      families:
        'We have found the smaller symmetry inside E₆. Read the selected representation under that symmetry, and compare its pieces with the electron and quark labels we started with.',
      implications:
        'The calculation has returned to a familiar charge pattern, repeated three times in the net chiral class. Here is how the mathematical route fits together.',
      verify:
        'Follow the same argument at greater depth in the paper, or run the finite calculations yourself.',
    },
  },
  {
    id: 'physics',
    label: 'I know some physics',
    depth: 'explore',
    description:
      'Start with chirality and anomalies, then follow the geometric construction.',
    title: 'From the known constraints to a common origin.',
    introduction:
      'The Standard Model assigns chiral charges and cancels their anomalies. The paper turns that motivation into an algebraic question: which compact embeddings have an irreducible complex-type adjoint complement and a nonzero cubic radical?',
    chapters: [
      'physics',
      'frontiers',
      'argument',
      'selection',
      'geometry',
      'families',
      'implications',
      'verify',
    ],
    stops: [
      { id: 'physics', label: 'Physical constraints' },
      { id: 'argument', label: 'Algebraic input' },
      { id: 'geometry', label: 'Subgroups' },
      { id: 'families', label: 'Matter content' },
    ],
    bridges: {
      frontiers:
        'Chirality and anomaly cancellation have guided many constructions. Compare their inputs before asking what changes when the embedding itself supplies the matter representation.',
      argument:
        'Anomaly cancellation alone permits many spectra and any number of repeated complete families. Here the representation is the entire adjoint complement of an embedding. Complex type and a nonzero cubic radical are imposed together.',
      selection:
        'With the hypotheses defined, follow how the all-rank reduction reaches the six explicit cubic tests.',
      geometry:
        'The radical selects E₆, while the su(3) factor supplies multiplicity. The next step is internal to E₆: determine the subgroup geometry before restricting the matter module.',
      families:
        'The faithful subgroup chain fixes the setting for restriction. The branching then separates net chiral content from vector-like pairs and singlets.',
    },
  },
  {
    id: 'mathematics',
    label: 'Show me the mathematics',
    depth: 'math',
    description:
      'Begin with the exact domain. Follow reduction, radical, incidence and restriction.',
    title: 'A classification problem with a finite geometric continuation.',
    introduction:
      'Take an effective proper inclusion h ⊂ g of finite-dimensional compact real Lie algebras. Set q = g/h, require Endₕ(q) ≅ ℂ and a nonzero cubic radical. The proof derives a homogeneous realization after the structural reduction; it is not an extra hypothesis about spacetime.',
    chapters: ['argument', 'selection', 'geometry', 'families', 'verify'],
    stops: [
      { id: 'argument', label: 'Hypotheses & tensor' },
      { id: 'selection', label: 'Exhaust the domain' },
      { id: 'geometry', label: 'Incidence' },
      { id: 'verify', label: 'Proof & certificates' },
    ],
    bridges: {
      selection:
        'The coefficient table is the final step of the classification, not its starting domain. This is the reduction that justifies reaching that finite list.',
      geometry:
        'Having selected (e₈, e₆ ⊕ su(3)), pass to the E₆ root system. The incidence calculation classifies triples of maximal closed subsystems under the Weyl action.',
      families:
        'Restriction of the selected complex half gives a representation-ring calculation. Taking its chiral class removes conjugate pairs and neutral singlets.',
      verify:
        'The structural proofs and the finite assertions use different methods. These are the exact artefacts and the boundary of the Lean layer.',
    },
  },
  {
    id: 'review',
    label: 'I’m here to check it',
    depth: 'math',
    description:
      'Open the evidence first. Trace each conclusion back to its inputs.',
    title: 'Start with the sources. Then challenge each transition.',
    introduction:
      'Download the paper and its matching computational snapshot. Examine the domain reduction, the cubic selector, the E₆ incidence calculation and the passage from chiral index to family count. Each claim stays attached to the method that supports it.',
    chapters: ['verify', 'argument', 'selection', 'geometry', 'families'],
    stops: [
      { id: 'verify', label: 'Source & checks' },
      { id: 'argument', label: 'Inputs' },
      { id: 'geometry', label: 'Finite claims' },
      { id: 'families', label: 'Chiral class' },
    ],
    bridges: {
      argument:
        'Check the quantifiers first: effective compact inclusions, the entire adjoint complement, complex type and a nonzero radical. The radical condition is already used to eliminate the centre in the structural reduction.',
      selection:
        'Audit how the proof excludes rank-deficient cases and reaches the six full-rank rows. Exhausting those rows does not replace that reduction.',
      geometry:
        'Check the next transition independently: the 72-root certificate, all labelled triples, six Weyl orbits, extremal cells and the intrinsic largest parent.',
      families:
        'Check the restriction directly: the selected complex half has three copies of the Standard Model family class, plus conjugate pairs and singlets of zero net chiral class. Duality reverses its sign.',
    },
  },
];
export function resolvePath(id: string | null): ReaderPath {
  return readerPaths.find((p) => p.id === id) ?? readerPaths[0];
}
export function omittedChapters(id: PathId): ChapterId[] {
  const included = resolvePath(id).chapters;
  return (Object.keys(chapterInfo) as ChapterId[]).filter(
    (chapter) => !included.includes(chapter),
  );
}
export const nestedChapters: Record<string, ChapterId> = {
  particles: 'physics',
  'standard-model': 'physics',
  'math-and-measurement': 'physics',
  'charge-key': 'physics',
  'lie-algebra': 'foundations',
  'algebra-dictionary': 'foundations',
  representations: 'foundations',
  mass: 'physics',
  anomalies: 'physics',
  'cubic-test': 'argument',
  'equation-film': 'argument',
  'collapse-step-0': 'selection',
  'collapse-step-1': 'selection',
  'collapse-step-2': 'selection',
  'collapse-step-3': 'selection',
};
export function chapterForAnchor(id: string): ChapterId | undefined {
  return Object.hasOwn(chapterInfo, id)
    ? (id as ChapterId)
    : Object.hasOwn(nestedChapters, id)
      ? nestedChapters[id]
      : undefined;
}
export function decodeAnchor(hash: string): string {
  try {
    return decodeURIComponent(hash.replace(/^#/, ''));
  } catch {
    return '';
  }
}
