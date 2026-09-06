'use client';

import { ChargeKey } from '@/components/symmetry-workbench';
import {
  StandardModelGuide,
  MathematicsAndMeasurement,
} from '@/components/standard-model-guide';
import { lazy, Suspense, useEffect, useRef, useState } from 'react';
import { ArrowDown, ArrowUpRight, CheckCircle2, RotateCcw } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Slider } from '@/components/ui/slider';
import { Switch } from '@/components/ui/switch';
import { ToggleGroup, ToggleGroupItem } from '@/components/ui/toggle-group';
import { Term } from '@/components/learning-exhibits';
import {
  AmbientExhibit,
  DemoControl,
  useGentleDemo,
} from '@/components/exhibit-motion';
import {
  particles,
  multiplets,
  anomalyContributions,
  anomalyLabels,
  anomalyTotals,
  massFraction,
  weakDoublets,
} from '@/lib/particle-physics';
import type { Particle } from '@/lib/particle-physics';
import { nextHiggsFrame } from '@/lib/motion-policy';
const Scene = lazy(() => import('@/components/particle-scene'));

function FieldView(props: {
  particle: Particle;
  coupling?: number;
  vectorlike?: boolean;
  massless?: boolean;
}) {
  const host = useRef<HTMLDivElement>(null);
  const [ready, setReady] = useState(false);
  useEffect(() => {
    const observer = new IntersectionObserver(
      ([e]) => {
        if (e.isIntersecting) {
          setReady(true);
          observer.disconnect();
        }
      },
      { rootMargin: '150px' },
    );
    if (host.current) observer.observe(host.current);
    return () => observer.disconnect();
  }, []);
  return (
    <div className="field-view" ref={host}>
      {ready ? (
        <Suspense
          fallback={
            <div className="field-loading">Preparing the field view…</div>
          }
        >
          <Scene {...props} />
        </Suspense>
      ) : (
        <div className="field-loading">
          A closer look at {props.particle.name}
        </div>
      )}
    </div>
  );
}

function ParticleGallery() {
  const [family, setFamily] = useState(0);
  const [selected, setSelected] = useState('electron');
  const [massless, setMassless] = useState(false);
  const particle = particles.find((p) => p.id === selected)!;
  const demoRef = useRef<HTMLDivElement>(null);
  const demo = useGentleDemo(
    demoRef,
    () => {
      const familyParticles = particles.filter((p) => p.generation === family);
      setSelected(
        familyParticles[
          (familyParticles.findIndex((p) => p.id === selected) + 1) %
            familyParticles.length
        ].id,
      );
    },
    16000,
  );
  const chooseFamily = (value: string[]) => {
    if (!value[0]) return;
    const index = Number(value[0]);
    setFamily(index);
    setSelected(
      particles.find(
        (p) => p.generation === index && (index === 3 || p.kind === 'lepton'),
      )!.id,
    );
  };
  return (
    <div
      className="particle-gallery"
      id="particles"
      ref={demoRef}
      {...demo.handlers}
    >
      <DemoControl {...demo} />
      <div className="lab-heading">
        <span className="eyebrow">THE PARTICLES WE KNOW</span>
        <h3>
          The same charges.
          <br />
          Three families.
        </h3>
        <p>
          The electron in an atom has two heavier relatives, the muon and tau.
          Quarks repeat too. Choose a family, then a particle: the masses change
          across families, while the gauge-charge pattern repeats.
        </p>
      </div>
      <ToggleGroup
        value={[String(family)]}
        onValueChange={chooseFamily}
        aria-label="Particle family"
        className="lab-tabs"
      >
        {[
          'First family',
          'Second family',
          'Third family',
          'Force & Higgs fields',
        ].map((label, i) => (
          <ToggleGroupItem value={String(i)} key={label}>
            {label}
          </ToggleGroupItem>
        ))}
      </ToggleGroup>
      {family !== 3 && (
        <label className="massless-toggle" htmlFor="massless-view">
          <Switch
            id="massless-view"
            checked={massless}
            onCheckedChange={setMassless}
          />{' '}
          Show the massless spin/momentum limit
        </label>
      )}
      <div className="particle-layout">
        <div className="particle-picker" aria-label="Choose a particle">
          {particles
            .filter((p) => p.generation === family)
            .map((p) => (
              <Button
                key={p.id}
                variant="ghost"
                aria-pressed={p.id === selected}
                className={'particle-choice kind-' + p.kind}
                onClick={() => setSelected(p.id)}
              >
                <strong>{p.symbol}</strong>
                <span>{p.name}</span>
                <small>Q = {p.charge}</small>
              </Button>
            ))}
        </div>
        <FieldView particle={particle} massless={massless && family !== 3} />
        <div
          className="particle-inspector"
          key={particle.id}
          aria-live={demo.automatic ? 'off' : 'polite'}
        >
          <span className="eyebrow">
            {particle.kind === 'boson'
              ? 'GAUGE FIELD'
              : particle.kind === 'higgs'
                ? 'SCALAR FIELD'
                : 'MATTER FIELD'}
          </span>
          <h4>{particle.name}</h4>
          <div className="particle-facts">
            <span>
              Electric charge <strong>{particle.charge}</strong>
            </span>
            <span>
              Spin <strong>{particle.spin}</strong>
            </span>
          </div>
          <p>{particle.description}</p>
          {particle.left && (
            <dl className="chiral-charges">
              <div>
                <dt>Left-chiral field</dt>
                <dd>{particle.left}</dd>
              </div>
              <div>
                <dt>Right-chiral field</dt>
                <dd>{particle.right}</dd>
              </div>
            </dl>
          )}
          <small>
            Charges use SU(3) × SU(2) with hypercharge Y; Q = T₃ + Y.
            Antiparticles are implicit. W± and the eight gluon fields are
            grouped in the gallery.
          </small>
        </div>
      </div>
      <details className="inline-depth">
        <summary>
          Is chirality the direction a particle spins? <span>+</span>
        </summary>
        <p>
          Chirality labels the two kinds of Weyl spinor under spacetime
          symmetry. Helicity compares spin with the direction of motion. They
          agree for massless particles with the usual particle convention; for a
          massive particle they are different concepts. The L and R glyphs here
          label field components, not classical rotation.
        </p>
      </details>
    </div>
  );
}

function HiggsExhibit() {
  const [mode, setMode] = useState('higgs');
  const [background, setBackground] = useState(0);
  const [bareMass, setBareMass] = useState(50);
  const vectorlike = mode === 'vectorlike';
  const value = vectorlike ? bareMass : background;
  const fraction = massFraction(value);
  const electron = particles.find((p) => p.id === 'electron')!;
  const direction = useRef(1);
  const demoRef = useRef<HTMLDivElement>(null);
  const demo = useGentleDemo(
    demoRef,
    () => {
      if (vectorlike) return;
      setBackground((v) => {
        const next = nextHiggsFrame(v, direction.current);
        direction.current = next.direction;
        return next.value;
      });
    },
    1600,
  );
  return (
    <div className="mass-exhibit" id="mass" ref={demoRef} {...demo.handlers}>
      <DemoControl {...demo} />
      <div className="lab-heading">
        <span className="eyebrow">WHY THE LEFT/RIGHT DISTINCTION MATTERS</span>
        <h3>
          A mass term needs
          <br />
          the charges to fit.
        </h3>
        <p>
          An electron’s left- and right-chiral fields carry different
          electroweak charges. A bare Dirac mass cannot join them while
          respecting that symmetry. The Higgs field supplies a gauge-invariant
          interaction; its vacuum value turns that interaction into a mass term.
        </p>
      </div>
      <ToggleGroup
        className="lab-tabs"
        value={[mode]}
        onValueChange={(values) => {
          if (values[0]) setMode(values[0]);
        }}
        aria-label="Mass-generation comparison"
      >
        <ToggleGroupItem value="higgs">
          Chiral electroweak theory
        </ToggleGroupItem>
        <ToggleGroupItem value="vectorlike">
          Vector-like comparison
        </ToggleGroupItem>
      </ToggleGroup>
      <div className="mass-layout">
        <FieldView
          particle={electron}
          coupling={fraction}
          vectorlike={vectorlike}
        />
        <div className="mass-control">
          <div key={mode} className="mass-introduction">
            <span className="eyebrow">
              {vectorlike
                ? 'SAME GAUGE REPRESENTATION'
                : 'DIFFERENT ELECTROWEAK REPRESENTATIONS'}
            </span>
            <h4>
              {vectorlike
                ? 'Gauge symmetry allows a bare mass.'
                : background === 0
                  ? 'No Higgs background. No Yukawa mass.'
                  : 'The background connects the two fields.'}
            </h4>
            <p>
              {vectorlike
                ? 'For a vector-like example such as QED, left and right carry the same gauge charge. A Dirac mass is allowed as a parameter. Its value is not forced to be large: chiral symmetry can protect a small fermion mass.'
                : 'Keep the electron’s Yukawa coupling fixed and vary the Higgs background. The bridge shows the strength of the resulting tree-level mass term.'}
            </p>
          </div>
          <label className="mass-slider-label" id="higgs-slider-label">
            {vectorlike
              ? 'Choose a bare mass (arbitrary units)'
              : 'Higgs background, relative to its vacuum value'}
            <strong>{value}%</strong>
          </label>
          <Slider
            value={[value]}
            min={0}
            max={100}
            step={1}
            onValueChange={(v) => {
              const n = Array.isArray(v) ? v[0] : v;
              if (vectorlike) setBareMass(n);
              else setBackground(n);
            }}
            aria-labelledby="higgs-slider-label"
          />
          <div className="mass-slider-ends">
            <span>0</span>
            <span>{vectorlike ? '1 reference unit' : 'v = 246 GeV'}</span>
          </div>
          <div
            className="mass-equation"
            aria-live={demo.automatic ? 'off' : 'polite'}
          >
            {vectorlike ? (
              <>
                <span>m is an allowed parameter</span>
                <strong>m / mᵣₑ𝒻 = {fraction.toFixed(2)}</strong>
              </>
            ) : (
              <>
                <span>mₑ = yₑ v / √2</span>
                <strong>mₑ(v) / mₑ(v₀) = {fraction.toFixed(2)}</strong>
              </>
            )}
          </div>
          <p className="lab-note">
            {vectorlike
              ? '“Allowed” does not mean compulsory, heavy or Planck-scale.'
              : 'This varies a background field, not collision energy or temperature. It shows a Lagrangian mass term, not the full behaviour of particles in a hot plasma.'}
          </p>
        </div>
      </div>
      <details className="inline-depth">
        <summary>
          What does the Higgs actually supply? <span>+</span>
        </summary>
        <p>
          The electroweak-invariant interaction is −yₑ L̄ H eR + h.c. The
          hypercharges add as +½ + ½ − 1 = 0, and the weak-doublet indices
          contract. With ⟨H⟩ = (0, v/√2), it gives mₑ = yₑv/√2. The same Yukawa
          interaction exists before symmetry breaking, but its mass contribution
          vanishes when the background is zero. The value of yₑ remains an
          input.
        </p>
        <p>
          This example concerns Dirac masses. A gauge-singlet Weyl fermion can
          instead admit a Majorana mass. With Standard Model fields, the
          dimension-five operator schematically written (LH)(LH)/Λ is also
          gauge-invariant; after symmetry breaking it can generate a Majorana
          neutrino mass proportional to v²/Λ. The field content and permitted
          operators decide which possibilities exist. Including this
          dimension-five operator extends the minimal renormalizable Standard
          Model.{' '}
          <a
            href="https://www2.physik.uni-muenchen.de/lehre/vorlesungen/wise_21_22/Neutrino-Mass-and-Grand-Unification/Material/Weinberg_baryon.pdf"
            target="_blank"
            rel="noreferrer"
          >
            Weinberg, 1979 ↗
          </a>
        </p>
      </details>
    </div>
  );
}

function AnomalyExhibit() {
  const [included, setIncluded] = useState([true, true, true, true, true]);
  const [channel, setChannel] = useState(3);
  const demoRef = useRef<HTMLDivElement>(null);
  const demo = useGentleDemo(
    demoRef,
    () => setChannel((c) => (c + 1) % anomalyLabels.length),
    12000,
  );
  const totals = anomalyTotals(included);
  const doublets = weakDoublets(included),
    nonempty = included.some(Boolean);
  const passed = totals.every((x) => x === 0) && doublets % 2 === 0;
  const values = multiplets.map((_, i) => anomalyContributions(i)[channel]);
  const extent = Math.max(1, ...values.map(Math.abs));
  return (
    <div
      className="anomaly-exhibit"
      id="anomalies"
      ref={demoRef}
      {...demo.handlers}
    >
      <DemoControl {...demo} />
      <div className="lab-heading">
        <span className="eyebrow">A QUANTUM CONSISTENCY TEST</span>
        <h3>
          Every piece
          <br />
          has to balance.
        </h3>
        <p>
          Quantum loops can spoil a gauge symmetry that works in the classical
          equations. A consistent gauge theory needs these anomaly contributions
          to cancel. In one Standard Model family, the quarks and leptons
          balance each other. Try leaving one out.
        </p>
        <p className="lab-note">
          For this calculation, every field is written left-handed. The symbols
          uᶜ, dᶜ and eᶜ are the conjugates of the right-chiral fields above;
          their gauge charges reverse. Q and L are the quark and lepton
          doublets.
        </p>
      </div>
      <div className="anomaly-layout">
        <div className="multiplet-switches">
          <span className="eyebrow">
            ONE FAMILY · ALL-LEFT-HANDED CONVENTION
          </span>
          {multiplets.map((m, i) => (
            <label
              key={m.id}
              htmlFor={'multiplet-' + m.id}
              className={included[i] ? 'included' : ''}
            >
              <Switch
                id={'multiplet-' + m.id}
                checked={included[i]}
                onCheckedChange={(checked) =>
                  setIncluded((previous) =>
                    previous.map((x, j) => (j === i ? checked : x)),
                  )
                }
              />
              <strong>{m.label}</strong>
              <span>
                {m.name}
                <small>{m.rep}</small>
              </span>
            </label>
          ))}
          <Button
            variant="outline"
            onClick={() => setIncluded([true, true, true, true, true])}
          >
            <RotateCcw size={14} /> Restore the full family
          </Button>
        </div>
        <div className="anomaly-instrument">
          <ToggleGroup
            className="lab-tabs"
            value={[String(channel)]}
            onValueChange={(values) => {
              if (values[0]) setChannel(Number(values[0]));
            }}
            aria-label="Anomaly channel"
          >
            {anomalyLabels.map((name, i) => (
              <ToggleGroupItem key={name} value={String(i)}>
                {name}
              </ToggleGroupItem>
            ))}
          </ToggleGroup>
          <AmbientExhibit className="balance-motion">
            <svg
              viewBox="0 0 580 255"
              aria-label={
                anomalyLabels[channel] +
                ' anomaly contributions; sum ' +
                totals[channel]
              }
            >
              <title>
                Signed contributions of the selected left-handed matter fields.
              </title>
              <line
                x1="285"
                x2="285"
                y1="25"
                y2="240"
                className="balance-axis"
              />
              <text x="105" y="18" className="balance-sign">
                NEGATIVE
              </text>
              <text x="370" y="18" className="balance-sign">
                POSITIVE
              </text>
              {multiplets.map((m, i) => {
                const value = included[i] ? values[i] : 0;
                const width = (Math.abs(value) / extent) * 175;
                return (
                  <g key={m.id}>
                    <text x="12" y={53 + i * 44} className="balance-label">
                      {m.label}
                    </text>
                    <rect
                      x={value < 0 ? 285 - width : 285}
                      y={33 + i * 44}
                      width={width}
                      height="28"
                      rx="3"
                      className={value < 0 ? 'negative' : 'positive'}
                    />
                    <text x="535" y={53 + i * 44} className="balance-value">
                      {value > 0 ? '+' : ''}
                      {value}
                    </text>
                  </g>
                );
              })}
            </svg>
          </AmbientExhibit>
          <div
            className={
              'anomaly-total ' +
              (totals[channel] === 0 ? 'balanced' : 'unbalanced')
            }
            aria-live={demo.automatic ? 'off' : 'polite'}
          >
            <span>{anomalyLabels[channel]} SUM</span>
            <strong>
              {totals[channel] > 0 ? '+' : ''}
              {totals[channel]}
            </strong>
            <span>{totals[channel] === 0 ? 'CANCELS' : 'DOES NOT CANCEL'}</span>
          </div>
          <div className="anomaly-summary">
            {totals.map((n, i) => (
              <span
                key={anomalyLabels[i]}
                className={n === 0 ? 'balanced' : 'unbalanced'}
              >
                {anomalyLabels[i]}
                <strong>{n}</strong>
              </span>
            ))}
          </div>
        </div>
      </div>
      <div
        className={'anomaly-verdict ' + (passed ? 'balanced' : 'unbalanced')}
        aria-live={demo.automatic ? 'off' : 'polite'}
      >
        {passed ? (
          <CheckCircle2 size={22} />
        ) : (
          <span className="anomaly-cross">×</span>
        )}
        <p>
          {!nonempty
            ? 'An empty spectrum cancels trivially, but contains no matter.'
            : passed
              ? 'The displayed local anomalies cancel. The number of weak doublets is even, so the usual SU(2) global-anomaly test also passes.'
              : 'This proposed spectrum fails a gauge-consistency test. It does not describe a quantum gauge theory on its own; adding a mass does not repair the missing cancellation.'}
        </p>
        <span>{doublets} weak doublets</span>
      </div>
      <p className="lab-note">
        The bars use integer-rescaled coefficients, with q = 6Y. A failed sum
        represents an inconsistency in the proposed theory, not an explosion or
        collapse of physical matter. Repeating a complete family preserves
        cancellation, so this test alone does not select three generations.
      </p>
      <details className="inline-depth">
        <summary>
          Follow the exact arithmetic <span>+</span>
        </summary>
        <p>
          For Y³, sum dcolour × dweak × q³. A full family gives 6 − 192 + 24 −
          54 + 216 = 0. For the mixed gravitational anomaly, use q rather than
          q³. For SU(3)²Y and SU(2)²Y, the displayed coefficients absorb the
          common fundamental Dynkin index. The SU(3)³ channel assigns opposite
          signs to a fundamental and its conjugate. The SU(2) global check
          counts colour copies of weak doublets. uᶜ, dᶜ and eᶜ denote
          left-handed conjugates of the right-chiral particle fields shown
          above.
        </p>
      </details>
    </div>
  );
}

export function PhysicsLaboratory() {
  return (
    <section className="physics-laboratory" id="physics">
      <div className="section">
        <div className="section-number">
          <span aria-hidden="true" />
          <span className="label-rule" />
          THE PHYSICS BEHIND THE QUESTION
        </div>
        <div className="section-heading">
          <h2>
            The Standard Model.
            <br />
            A pattern in the <em>world.</em>
          </h2>
          <p className="section-lead">
            The matter in an atom, the light it emits, and the weak processes
            that change one kind of particle into another are described by a
            remarkably small set of fields and interaction rules. Those rules
            carry a mathematical pattern we can learn to read.
          </p>
        </div>
        <nav className="lab-contents" aria-label="Physics exhibits">
          <a href="#standard-model">
            Understand the model <ArrowDown size={14} />
          </a>
          <a href="#particles">
            Meet the particles <ArrowDown size={14} />
          </a>
          <a href="#math-and-measurement">
            Test it against nature <ArrowDown size={14} />
          </a>
          <a href="#mass">
            Connect left and right <ArrowDown size={14} />
          </a>
          <a href="#anomalies">
            Balance the anomalies <ArrowDown size={14} />
          </a>
        </nav>
        <StandardModelGuide />
        <p className="particle-language-key">
          The gallery uses L and R for left- and right-chiral fields. Its
          animated pictures are symbolic; the representation labels give the
          actual charges. For a refresher on those labels,{' '}
          <a href="#representations">explore how a representation works ↗</a>
        </p>
        <ChargeKey />
        <ParticleGallery />
        <MathematicsAndMeasurement />
        <HiggsExhibit />
        <AnomalyExhibit />
        <div className="physics-to-paper">
          <span className="eyebrow">NOW REVERSE THE USUAL QUESTION</span>
          <h3>
            What if the matter and its symmetry
            <br />
            came from the same structure?
          </h3>
          <p>
            In the Standard Model, we specify the symmetry, assign the matter
            representations and repeat the family pattern three times. The paper
            ties those choices together: place one compact algebra inside
            another, and use all the remaining directions as a representation of
            the smaller one. This adjoint complement must be irreducible and of{' '}
            <Term meaning="For this real isotropy module, Endₕ(q) ≅ ℂ. Its complexification splits into two inequivalent conjugate irreducible halves.">
              complex type
            </Term>
            . Requiring a nonzero cubic-anomaly radical as well leaves one pair.
            We can now follow the conditions that make that uniqueness possible.
          </p>
        </div>
        <p className="source-note">
          Physics background:{' '}
          <a
            href="https://pdg.lbl.gov/2025/reviews/rpp2025-rev-standard-model.pdf"
            target="_blank"
            rel="noreferrer"
          >
            Particle Data Group: electroweak theory <ArrowUpRight size={12} />
          </a>{' '}
          ·{' '}
          <a
            href="https://www.damtp.cam.ac.uk/user/tong/sm/standardmodel.pdf"
            target="_blank"
            rel="noreferrer"
          >
            David Tong: anomalies, Yukawa couplings and neutrinos{' '}
            <ArrowUpRight size={12} />
          </a>
          . The illustrations explain these established mechanisms; they are
          separate from the paper’s classification calculation.
        </p>
      </div>
    </section>
  );
}
