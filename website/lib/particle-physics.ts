export type Particle = {
  id: string;
  name: string;
  symbol: string;
  kind: 'quark' | 'lepton' | 'neutrino' | 'boson' | 'higgs';
  generation: number;
  charge: string;
  spin: string;
  left: string;
  right: string;
  description: string;
};
const families = [
  ['up', 'down', 'electron', 'electron neutrino', 'u', 'd', 'e', 'νₑ'],
  ['charm', 'strange', 'muon', 'muon neutrino', 'c', 's', 'μ', 'νμ'],
  ['top', 'bottom', 'tau', 'tau neutrino', 't', 'b', 'τ', 'ντ'],
];
export const particles: Particle[] = families
  .flatMap((f, generation) =>
    f.slice(0, 4).map((name, i) => ({
      id: name.replaceAll(' ', '-'),
      name,
      symbol: f[i + 4],
      generation,
      kind: (i < 2
        ? 'quark'
        : i === 2
          ? 'lepton'
          : 'neutrino') as Particle['kind'],
      charge: ['+⅔', '−⅓', '−1', '0'][i],
      spin: '½',
      left: i < 2 ? '(3, 2)₁/₆' : '(1, 2)₋₁/₂',
      right: [
        '(3, 1)₂/₃',
        '(3, 1)₋₁/₃',
        '(1, 1)₋₁',
        'Absent in the minimal Standard Model',
      ][i],
      description:
        i < 2
          ? 'A quark has three colour components. Its left-chiral field belongs to a weak doublet; its right-chiral field is a weak singlet.'
          : i === 2
            ? 'The left-chiral charged lepton shares a weak doublet with its neutrino. The right-chiral field is a weak singlet. Their electric charges agree; their electroweak representations do not.'
            : 'The minimal Standard Model contains a left-chiral neutrino field and its antiparticle, but no independent right-chiral neutrino field. Observed neutrino masses require an extension of that minimal description.',
    })),
  )
  .concat([
    {
      id: 'photon',
      name: 'photon',
      symbol: 'γ',
      kind: 'boson',
      generation: 3,
      charge: '0',
      spin: '1',
      left: '',
      right: '',
      description:
        'The photon carries the electromagnetic interaction. Its two physical helicities are not left/right Weyl matter fields. The unbroken electromagnetic gauge symmetry leaves it massless.',
    },
    {
      id: 'gluon',
      name: 'gluon',
      symbol: 'g',
      kind: 'boson',
      generation: 3,
      charge: '0',
      spin: '1',
      left: '',
      right: '',
      description:
        'The eight gluon fields carry the strong interaction and transform in the adjoint of colour SU(3). Quark colour is a gauge charge, not a visible colour. Isolated gluons are confined.',
    },
    {
      id: 'w',
      name: 'W bosons',
      symbol: 'W±',
      kind: 'boson',
      generation: 3,
      charge: '±1',
      spin: '1',
      left: '',
      right: '',
      description:
        'The charged weak current couples the left-chiral quark and lepton doublets. W bosons acquire a mass through electroweak symmetry breaking.',
    },
    {
      id: 'z',
      name: 'Z boson',
      symbol: 'Z',
      kind: 'boson',
      generation: 3,
      charge: '0',
      spin: '1',
      left: '',
      right: '',
      description:
        'The neutral weak interaction couples to both left- and right-chiral charged fermions, with different strengths. The Z acquires a mass through electroweak symmetry breaking.',
    },
    {
      id: 'higgs',
      name: 'Higgs boson',
      symbol: 'H',
      kind: 'higgs',
      generation: 3,
      charge: '0',
      spin: '0',
      left: '',
      right: '',
      description:
        'The observed Higgs boson is the scalar excitation around the Higgs field’s vacuum value. A scalar has no left/right Weyl chirality. Gauge-invariant Yukawa interactions connect charged fermions to that field.',
    },
  ]);

// All LEFT-handed Weyl convention: uᶜ, dᶜ and eᶜ are conjugate fields.
// q = 6Y makes the displayed anomaly arithmetic integral.
export const multiplets = [
  {
    id: 'Q',
    label: 'Q',
    name: 'quark doublet',
    rep: '(3, 2)₁/₆',
    colour: 3,
    weak: 2,
    q: 1,
    sign: 1,
  },
  {
    id: 'uc',
    label: 'uᶜ',
    name: 'up antiquark',
    rep: '(3̄, 1)₋₂/₃',
    colour: 3,
    weak: 1,
    q: -4,
    sign: -1,
  },
  {
    id: 'dc',
    label: 'dᶜ',
    name: 'down antiquark',
    rep: '(3̄, 1)₁/₃',
    colour: 3,
    weak: 1,
    q: 2,
    sign: -1,
  },
  {
    id: 'L',
    label: 'L',
    name: 'lepton doublet',
    rep: '(1, 2)₋₁/₂',
    colour: 1,
    weak: 2,
    q: -3,
    sign: 0,
  },
  {
    id: 'ec',
    label: 'eᶜ',
    name: 'charged antilepton',
    rep: '(1, 1)₁',
    colour: 1,
    weak: 1,
    q: 6,
    sign: 0,
  },
];
export const anomalyLabels = [
  'SU(3)³',
  'SU(3)²Y',
  'SU(2)²Y',
  'Y³',
  'gravity²Y',
];
export function anomalyContributions(i: number) {
  const p = multiplets[i];
  if (!p) throw new RangeError('Unknown matter multiplet.');
  return [
    p.sign * p.weak,
    p.colour === 3 ? p.weak * p.q : 0,
    p.weak === 2 ? p.colour * p.q : 0,
    p.colour * p.weak * p.q ** 3,
    p.colour * p.weak * p.q,
  ];
}
export function anomalyTotals(included: boolean[]) {
  if (included.length !== 5 || included.some((x) => typeof x !== 'boolean'))
    throw new TypeError('Choose all five multiplet switches.');
  return anomalyLabels.map((_, j) =>
    included.reduce(
      (sum, keep, i) => sum + (keep ? anomalyContributions(i)[j] : 0),
      0,
    ),
  );
}
export function weakDoublets(included: boolean[]) {
  return multiplets.reduce(
    (sum, p, i) => sum + (included[i] && p.weak === 2 ? p.colour : 0),
    0,
  );
}
export function massFraction(higgsPercent: number) {
  if (!Number.isFinite(higgsPercent) || higgsPercent < 0 || higgsPercent > 100)
    throw new RangeError('Higgs background must be between 0 and 100%.');
  return higgsPercent / 100;
}
