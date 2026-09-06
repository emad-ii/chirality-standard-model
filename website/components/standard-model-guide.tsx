'use client';

import { useRef, useState } from 'react';
import { ArrowUpRight } from 'lucide-react';
import { DemoControl, useGentleDemo } from '@/components/exhibit-motion';
import { ToggleGroup, ToggleGroupItem } from '@/components/ui/toggle-group';

export function StandardModelGuide() {
  return (
    <div className="standard-model-guide" id="standard-model">
      <div className="guide-opening">
        <span className="eyebrow">START WITH AN ATOM</span>
        <h3>A few fields. An extraordinary amount of the world.</h3>
        <p>
          Electrons surround an atom’s nucleus. Inside it, protons and neutrons
          contain up and down quarks, bound by the strong interaction. Light is
          made of photons. The Standard Model brings these ingredients into one
          quantum field theory, together with their heavier relatives, neutrinos
          and the fields responsible for the weak interaction and the Higgs
          mechanism.
        </p>
        <p>
          A <strong>field</strong> has a value at every point in spacetime. A
          particle is a quantum excitation of a field: an electron belongs to
          the electron field, a photon to the electromagnetic field. To describe
          their interactions, we need rules for how those fields transform.
        </p>
        <p>
          Quarks and leptons are fermions. Fermion fields can transform in two
          chiral ways under spacetime symmetry, called left- and right-handed.
          The weak interaction treats them differently. The three internal
          symmetries below describe the charge rules.
        </p>
      </div>
      <div
        className="symmetry-map"
        aria-label="The Standard Model gauge symmetries"
      >
        <article>
          <span className="guide-symbol">
            SU(3)<sub>c</sub>
          </span>
          <h4>Colour</h4>
          <p>
            Each quark has three colour components. Eight gluon fields couple to
            this charge and to one another, producing the strong interaction.
            “Colour” names an internal charge, unrelated to visible colour.
          </p>
        </article>
        <article>
          <span className="guide-symbol">
            SU(2)<sub>L</sub>
          </span>
          <h4>Weak isospin</h4>
          <p>
            Left-chiral quarks and leptons come in pairs, such as the electron
            and its neutrino. The W interaction connects the two components. The
            right-chiral electron is a singlet instead. This difference is the
            chiral structure of the weak interaction.
          </p>
        </article>
        <article>
          <span className="guide-symbol">
            U(1)<sub>Y</sub>
          </span>
          <h4>Hypercharge</h4>
          <p>
            Each field also carries a hypercharge, Y. After electroweak symmetry
            breaking, the hypercharge field and neutral weak field mix to give
            the photon and Z. Electric charge combines hypercharge with weak
            isospin: Q = T₃ + Y.
          </p>
        </article>
      </div>
      <p className="guide-bridge">
        The numbers in SU(3) and SU(2) refer to their defining representations.
        They count internal components, not families. The observed matter
        pattern repeats across <strong>three generations</strong>, a different
        kind of three. We will keep those counts separate as the argument
        unfolds.
      </p>
      <details className="inline-depth">
        <summary>
          What makes a symmetry a gauge symmetry? <span>+</span>
        </summary>
        <p>
          U(N) is the group of unitary transformations: matrices that preserve
          the squared norm of N complex components. SU(N) adds the requirement
          that the determinant is one. U(1) is a phase rotation, like the
          turning complex amplitude in the representation exhibit.
        </p>
        <p>
          We can choose the internal basis used to describe a field separately
          at each spacetime point. A gauge transformation changes that
          description while leaving physical observations unchanged. Gauge
          fields let us compare the descriptions at neighbouring points;
          requiring this local freedom constrains how the fields interact.
        </p>
        <p>
          The familiar product SU(3) × SU(2) × U(1) specifies the local symmetry
          structure. Groups with different global identifications can share the
          same Lie algebra. The paper checks that its particular embedded
          Standard Model subgroup has the quotient by ℤ₆.{' '}
          <a
            href="https://arxiv.org/abs/1705.01853"
            target="_blank"
            rel="noreferrer"
          >
            Read about the global forms ↗
          </a>
        </p>
      </details>
    </div>
  );
}

const evidence = [
  {
    id: 'weak',
    label: 'W and Z',
    date: '1983',
    title: 'A theory tells an experiment what to look for.',
    rule: 'The electroweak theory joins weak isospin and hypercharge. Its Higgs field gives masses to the W and Z while leaving the photon massless.',
    calculation:
      'With parameters constrained by earlier measurements, the theory predicted massive W and Z bosons and their interactions. Their decays gave experiments identifiable combinations of charged leptons and missing momentum.',
    observation:
      'UA1 and UA2 found the W and Z at CERN in 1983. The comparison involved masses, event rates and decay patterns, not just the appearance of a new particle.',
    equation: 'At leading order: mW = gv/2; mZ = v√(g² + g′²)/2',
    detail:
      'Here g and g′ are interaction strengths and v is the Higgs vacuum scale. Their values come from measurements; the theory supplies the relationships. Precision comparisons include quantum corrections.',
    source: 'CERN: finding the W and Z',
    url: 'https://cern-courier.web.cern.ch/a/finding-the-w-and-z/',
  },
  {
    id: 'colour',
    label: 'Quarks and gluons',
    date: 'JET MEASUREMENTS',
    title: 'The algebra leaves a trace in particle collisions.',
    rule: 'Quarks transform as colour triplets; gluons carry the eight-dimensional adjoint representation. Because the colour transformations do not commute, gluons interact with one another.',
    calculation:
      'The representation matrices give definite colour factors: CF = 4/3 for a quark and CA = 3 for a gluon. These factors enter predictions for radiation and the angles between jets of particles.',
    observation:
      'Experiments measure hadronic jets rather than isolated quarks and gluons. Their angular distributions test these colour factors and the non-commuting structure of QCD, the theory of the strong interaction.',
    equation: 'For SU(N): CF = (N² − 1)/(2N); CA = N. Set N = 3.',
    detail:
      'These are quadratic Casimir values with the standard generator normalisation. Jet predictions also include the strong coupling, collision energy and the formation of hadrons. Three jets do not mean three colours.',
    source: 'Particle Data Group: QCD and its experimental tests',
    url: 'https://pdg.lbl.gov/2025/reviews/rpp2025-rev-qcd.pdf',
  },
  {
    id: 'higgs',
    label: 'The Higgs',
    date: '2012 →',
    title: 'Finding the particle begins the next test.',
    rule: 'The Higgs mechanism links particle masses to interactions with the Higgs field. For a charged fermion, its mass and its Higgs coupling depend on the same Yukawa parameter.',
    calculation:
      'Once masses and other inputs are measured, the Standard Model predicts Higgs production rates and decay probabilities. Different final states test different parts of that interaction pattern.',
    observation:
      'ATLAS and CMS discovered the Higgs boson in 2012. Subsequent ATLAS measurements of its interactions with W and Z bosons, top and bottom quarks, and tau leptons agree with Standard Model expectations within uncertainties.',
    equation: 'For a charged fermion at leading order: mf = yf v/√2',
    detail:
      'The Yukawa parameter yf sets the mass; the coupling of the physical Higgs excitation to that fermion is mf/v at this order. The observed Higgs mass is an input to these tests, not a number determined by the symmetry alone.',
    source: 'ATLAS: a detailed map of Higgs boson interactions',
    url: 'https://arxiv.org/abs/2207.00092',
  },
] as const;

export function MathematicsAndMeasurement() {
  const [selected, setSelected] = useState(0);
  const ref = useRef<HTMLDivElement>(null);
  const demo = useGentleDemo(
    ref,
    () => setSelected((i) => (i + 1) % evidence.length),
    48000,
  );
  const example = evidence[selected];
  return (
    <div
      className="measurement-guide"
      id="math-and-measurement"
      ref={ref}
      {...demo.handlers}
    >
      <DemoControl {...demo} />
      <div className="guide-opening">
        <span className="eyebrow">FROM A RULE TO A MEASUREMENT</span>
        <h3>How does the mathematics meet reality?</h3>
        <p>
          A detector records energy, momentum and particle tracks. The theory
          predicts the probabilities of different outcomes. Physicists specify
          the fields and their interactions, measure the parameters, then use
          the same theory to calculate other processes. Agreement across those
          tests is what gives the Standard Model its force.
        </p>
      </div>
      <ToggleGroup
        className="lab-tabs"
        aria-label="Experimental example"
        value={[example.id]}
        onValueChange={(values) => {
          const index = evidence.findIndex((item) => item.id === values[0]);
          if (index !== -1) setSelected(index);
        }}
      >
        {evidence.map((item) => (
          <ToggleGroupItem key={item.id} value={item.id}>
            {item.label}
          </ToggleGroupItem>
        ))}
      </ToggleGroup>
      <div
        className="measurement-example"
        key={example.id}
        aria-live={demo.automatic ? 'off' : 'polite'}
      >
        <span className="eyebrow">{example.date}</span>
        <h4>{example.title}</h4>
        <ol className="measurement-chain">
          {[
            ['The structure', example.rule],
            ['The calculation', example.calculation],
            ['The observation', example.observation],
          ].map(([label, text], i) => (
            <li key={label}>
              <span className="chain-step">0{i + 1}</span>
              <h5>{label}</h5>
              <p>{text}</p>
            </li>
          ))}
        </ol>
        <details className="inline-depth">
          <summary>
            One equation behind the example <span>+</span>
          </summary>
          <p className="guide-equation">{example.equation}</p>
          <p>{example.detail}</p>
        </details>
        <a
          className="source-link"
          href={example.url}
          target="_blank"
          rel="noreferrer"
        >
          {example.source} <ArrowUpRight size={14} />
        </a>
      </div>
      <p className="guide-bridge">
        The charge pattern is one of the inputs to this experimentally tested
        theory. The paper asks why that pattern, and its threefold chiral
        repetition, might arise from a single algebraic construction. To reach
        that question, first examine two constraints the pattern already meets:
        chirality and anomaly cancellation.
      </p>
    </div>
  );
}
