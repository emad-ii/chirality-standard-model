'use client';
import { asset } from '@/lib/assets';
import { useRef, useState } from 'react';
import Image from 'next/image';
import { ArrowRight, ArrowUpRight, ChevronRight } from 'lucide-react';
import { ToggleGroup, ToggleGroupItem } from '@/components/ui/toggle-group';
import {
  AmbientExhibit,
  DemoControl,
  useGentleDemo,
} from '@/components/exhibit-motion';
import { repository, snapshot } from '@/lib/e6';

const approaches = [
  {
    id: 'su5',
    label: 'SU(5)',
    title: 'Place one family in two representations.',
    input:
      'Choose SU(5), an embedding of the Standard Model group, and left-handed matter 10 ⊕ 5̄.',
    result:
      'Quarks and leptons share unified multiplets; their cubic SU(5) anomalies cancel.',
    open: 'The number of copies, scalar sector, symmetry-breaking vacuum and Yukawa couplings still need specification.',
    equation: '10 ⊕ 5̄ → Q ⊕ uᶜ ⊕ eᶜ ⊕ dᶜ ⊕ L',
    explanation:
      'The 10 contains Q, uᶜ and eᶜ. The 5̄ contains dᶜ and L. A single family is already anomaly-free; repeating it leaves cancellation intact. This is a real reduction in independent charge assignments, even though it does not fix why there are three families.',
    source: 'https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.32.438',
    credit: 'Georgi & Glashow, 1974',
  },
  {
    id: 'spin10',
    label: 'Spin(10)',
    title: 'Place a family and a neutral state in one 16.',
    input:
      'Choose Spin(10) and a chiral spinor representation for each family.',
    result:
      'The Standard Model family and a Standard Model-singlet neutrino state fit in one irreducible representation.',
    open: 'Family repetition and the symmetry-breaking and mass-generating sectors are not specified by choosing the 16.',
    equation: '16 → 10 ⊕ 5̄ ⊕ 1',
    explanation:
      'The 16 brings a whole family and a neutral state into one irreducible representation. Many separate charge assignments become one representation choice. The present paper asks whether the larger algebra, its subalgebra and the representation supplied by their complement can be classified together.',
    source: 'https://doi.org/10.1016/0003-4916(75)90211-0',
    credit: 'Fritzsch & Minkowski, 1975',
  },
  {
    id: 'e6',
    label: 'E₆',
    title: 'A 27 contains a family and additional matter.',
    input: 'Choose E₆ and its complex 27 as the matter representation.',
    result: 'Under Spin(10), the 27 contains a 16, a 10 and a singlet.',
    open: 'Its extra states need a physical role. Their masses, vacuum and the number of repeated 27s require further input.',
    equation: '27 → 16 ⊕ 10 ⊕ 1',
    explanation:
      'Under the familiar Standard Model subgroup, one 27 has 15 components in a net chiral family, ten in a conjugate pair and two neutral singlets. The absence of a cubic invariant on the Lie algebra e₆ means the pure E₆ cubic gauge anomaly vanishes. This does not determine the spectrum’s masses.',
    source: 'https://doi.org/10.1016/0370-2693(76)90417-2',
    credit: 'Gürsey, Ramond & Sikivie, 1976',
  },
  {
    id: 'heterotic',
    label: 'Heterotic strings',
    title: 'Let compactification determine the light modes.',
    input:
      'Start with the E₈ × E₈ heterotic theory and a Calabi–Yau threefold X; in the standard embedding, identify an SU(3) gauge connection with the tangent connection.',
    result:
      'One E₈ leaves an E₆ gauge sector. Four-dimensional chiral matter is counted by internal zero modes.',
    open: 'The compactification and bundle data matter. The 3 in (27, 3) is not automatically three four-dimensional families.',
    equation: '|N₂₇ − N₂₇̄| = |χ(X)| / 2',
    explanation:
      'For this standard embedding, the net generation count is an index related to the Euler characteristic of X. This is a different use of geometry from a finite-dimensional multiplicity space. Ten-dimensional anomaly cancellation also uses the Green–Schwarz mechanism, not just the four-dimensional cubic trace test on this page.',
    source:
      'https://ooguri.caltech.edu/documents/31340/Candelas_Horowitz_Strominger_Witten.pdf',
    credit: 'Candelas, Horowitz, Strominger & Witten, 1985',
  },
  {
    id: 'paper',
    label: 'This paper',
    title: 'Let the pair supply its own matter representation.',
    input:
      'Vary effective proper inclusions h ⊂ g of compact real Lie algebras. Require the entire adjoint complement to have complex type and a nonzero cubic radical.',
    result:
      'One Lie-algebra pair survives: (e₈, e₆ ⊕ su(3)). Its complex half is 27 ⊗ 3.',
    open: 'The specified domain and the two invariant conditions are the inputs. The theorem classifies the pair and its representation; restriction computes the net chiral class.',
    equation: '(27 ⊗ 3)|E₆ = 27 ⊕ 27 ⊕ 27',
    explanation:
      'The multiplicity three follows by restricting a finite-dimensional representation. The E₆ incidence problem identifies the extremal subgroup constructions. The uniqueness and no-go theorem quantifies over effective compact Lie-algebra inclusions with the two stated conditions; homogeneous geometry realizes the qualifying pair.',
    source: repository + '/blob/' + snapshot + '/paper/paper.tex',
    credit: 'Manuscript, §§1–5',
  },
] as const;

const milestones = [
  {
    year: '1967',
    name: 'A theory links light and weak decay.',
    text: 'Weinberg’s electroweak model combined the weak and electromagnetic interactions with symmetry breaking. Together with the work of Glashow and Salam, it gave a framework whose predictions could be tested.',
    source: 'https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.19.1264',
  },
  {
    year: '1973',
    name: 'Neutral currents become evidence.',
    text: 'Gargamelle at CERN observed weak interactions that transfer no electric charge. The electroweak theory was making experimentally distinctive predictions.',
    source: 'https://home.cern/50-years-giant-electroweak-discoveries/',
  },
  {
    year: '1983',
    name: 'The W and Z are found.',
    text: 'The discovery of the weak-force carriers at CERN tested the theory’s particle content directly.',
    source: 'https://home.cern/50-years-giant-electroweak-discoveries/',
  },
  {
    year: '2012',
    name: 'A Higgs boson is discovered.',
    text: 'ATLAS and CMS independently observed a new boson compatible with the Standard Model Higgs, opening direct experimental study of the Higgs sector.',
    source: 'https://arxiv.org/abs/1207.7214',
  },
] as const;

export function ModelLandscape() {
  const [approach, setApproach] = useState('su5');
  const [year, setYear] = useState(0);
  const discoveryRef = useRef<HTMLDivElement>(null);
  const comparisonRef = useRef<HTMLDivElement>(null);
  const discoveryDemo = useGentleDemo(
    discoveryRef,
    () => setYear((y) => (y + 1) % milestones.length),
    18000,
  );
  const comparisonDemo = useGentleDemo(
    comparisonRef,
    () =>
      setApproach(
        (current) =>
          approaches[
            (approaches.findIndex((item) => item.id === current) + 1) %
              approaches.length
          ].id,
      ),
    22000,
  );
  const model = approaches.find((m) => m.id === approach)!;
  const event = milestones[year];
  return (
    <section className="section model-landscape" id="frontiers">
      <div className="section-number">
        <span aria-hidden="true" />
        <span className="label-rule" />
        HOW THE PATTERN WAS BUILT
      </div>
      <div className="section-heading">
        <h2>
          Knowing the pattern.
          <br />
          Asking <em>why this one.</em>
        </h2>
        <p className="section-lead">
          The Standard Model was built through a conversation between experiment
          and theory. It describes a remarkable amount with a small set of
          symmetry rules. Explaining why those rules and those matter
          representations occur is a further question.
        </p>
      </div>
      <div className="discovery-layout">
        <figure>
          <Image
            unoptimized
            src={asset('electroweak-illustration.webp')}
            width={1774}
            height={887}
            alt="Illustrated later-life portraits of Glashow, Weinberg and Salam"
            loading="lazy"
          />
          <figcaption>
            Glashow · Weinberg · Salam. Illustrated later-life portraits, not a
            scene from the 1960s.
          </figcaption>
        </figure>
        <div
          className="discovery-story"
          ref={discoveryRef}
          {...discoveryDemo.handlers}
        >
          <DemoControl {...discoveryDemo} />
          <span className="eyebrow">THE ELECTROWEAK THREAD</span>
          <ToggleGroup
            className="lab-tabs"
            value={[String(year)]}
            onValueChange={(v) => {
              if (v[0]) setYear(Number(v[0]));
            }}
            aria-label="Electroweak discovery"
          >
            {milestones.map((m, i) => (
              <ToggleGroupItem value={String(i)} key={m.year}>
                {m.year}
              </ToggleGroupItem>
            ))}
          </ToggleGroup>
          <div className="discovery-event" key={event.year}>
            <h3>{event.name}</h3>
            <p>{event.text}</p>
            <a
              className="source-link"
              href={event.source}
              target="_blank"
              rel="noreferrer"
            >
              Read the source <ArrowUpRight size={14} />
            </a>
            {event.year === '2012' && (
              <a
                className="source-link"
                href="https://arxiv.org/abs/1207.7235"
                target="_blank"
                rel="noreferrer"
              >
                CMS discovery paper <ArrowUpRight size={14} />
              </a>
            )}
          </div>
        </div>
      </div>
      <p className="landscape-bridge">
        The strong interaction adds SU(3) colour; electroweak theory uses SU(2)
        × U(1). Together these organise the known matter and interactions. A
        grand unified theory, or GUT, asks whether they fit inside a larger
        gauge symmetry.
      </p>
      <div className="model-choices-heading">
        <span className="eyebrow">
          COMPARE THE INPUTS, NOT JUST THE GROUP NAMES
        </span>
        <h3>
          What do you choose?
          <br />
          What follows from that choice?
        </h3>
        <p>
          “Put in by hand” means specified as part of a model. Those choices are
          constrained by data, consistency and representation theory. They are
          not arbitrary in the sense of unconstrained guesswork.
        </p>
      </div>
      <p className="model-notation-key">
        Numbers such as 10 and 27 label representations by their component
        counts. An overbar marks the conjugate representation; ⊕ combines
        independent pieces. The arrow shows how one representation separates
        into smaller pieces when we keep only a subgroup’s transformations.
      </p>
      <div
        className="model-demo"
        ref={comparisonRef}
        {...comparisonDemo.handlers}
      >
        <DemoControl {...comparisonDemo} />
        <ToggleGroup
          className="lab-tabs model-tabs"
          value={[approach]}
          onValueChange={(v) => {
            if (v[0]) setApproach(v[0]);
          }}
          aria-label="Unification approach"
        >
          {approaches.map((m) => (
            <ToggleGroupItem value={m.id} key={m.id}>
              {m.label}
            </ToggleGroupItem>
          ))}
        </ToggleGroup>
        <AmbientExhibit className="model-comparison">
          <h3>{model.title}</h3>
          <div className="model-flow" key={model.id}>
            <article>
              <span>SPECIFIED</span>
              <p>{model.input}</p>
            </article>
            <ArrowRight className="model-arrow" aria-hidden="true" />
            <article>
              <span>DETERMINED</span>
              <p>{model.result}</p>
            </article>
            <ArrowRight className="model-arrow" aria-hidden="true" />
            <article>
              <span>FURTHER INPUT</span>
              <p>{model.open}</p>
            </article>
          </div>
          <div className="model-equation">{model.equation}</div>
          {model.id === 'heterotic' && (
            <p className="model-notation-key">
              Here χ(X) is the Euler characteristic of the compactification
              space, and N counts four-dimensional matter multiplets. Later,
              χ(V) denotes a chiral representation class: a different
              construction.
            </p>
          )}
          <details className="inline-depth" key={model.id + '-detail'}>
            <summary>
              Follow this construction more closely <span>+</span>
            </summary>
            {model.id === 'su5' && (
              <figure className="unification-portrait">
                <Image
                  unoptimized
                  src={asset('unification-illustration.webp')}
                  width={1685}
                  height={933}
                  alt="Illustrated later-life portraits of Howard Georgi and Sheldon Glashow"
                  loading="lazy"
                />
                <figcaption>
                  Georgi · Glashow. Illustrated later-life portraits, not a
                  scene from 1974.
                </figcaption>
              </figure>
            )}
            <p>{model.explanation}</p>
            {model.id === 'heterotic' && (
              <a
                className="source-link"
                href="https://www.sciencedirect.com/science/article/pii/037026938491565X"
                target="_blank"
                rel="noreferrer"
              >
                Green & Schwarz, 1984 <ArrowUpRight size={14} />
              </a>
            )}
          </details>
          <a
            className="source-link"
            href={model.source}
            target="_blank"
            rel="noreferrer"
          >
            {model.credit} <ArrowUpRight size={14} />
          </a>
        </AmbientExhibit>
      </div>
      <div className="landscape-context">
        <h3>Geometry has a history here.</h3>
        <p>
          Coset-space reduction, exceptional family unification and string
          compactification already connect matter to geometry. There are also
          exhaustive algorithms that start with a supplied gauge algebra and
          fermion spectrum, then find anomaly-free semisimple completions
          without adding fermions.{' '}
          <a
            href="https://arxiv.org/abs/2306.16439"
            target="_blank"
            rel="noreferrer"
          >
            Gomes, Ruhdorfer & Tooby-Smith ↗
          </a>
        </p>
        <p>
          This paper changes the input to a classification problem: vary both
          the pair and its canonical quotient representation. Within that
          domain, the geometric and cubic conditions have one survivor. The
          diagrams that follow show how the alternatives are excluded.
        </p>
        <details className="inline-depth">
          <summary>
            Same E₈ branching, different generation counts <span>+</span>
          </summary>
          <p>
            The branching 248 = (78,1) ⊕ (1,8) ⊕ (27,3) ⊕ (27̄,3̄) is shared
            algebra. Its interpretation depends on the construction. In
            heterotic compactification the four-dimensional spectrum depends on
            internal zero modes; here the chosen module itself contains three E₆
            copies. Equal branching notation does not make the two physical
            mechanisms equivalent.
          </p>
          <p>
            For the classic standard embedding, see the{' '}
            <a href={approaches[3].source} target="_blank" rel="noreferrer">
              1985 construction
            </a>
            . The manuscript’s introduction places the algebraic classification
            alongside earlier coset and family-unification work.
          </p>
        </details>
      </div>
      <div className="question-band">
        <span className="eyebrow">THE INVERSE QUESTION</span>
        <h3>
          What was chosen separately
          <br />
          can the geometry fix <em>together?</em>
        </h3>
        <div className="comparison">
          <div>
            <span>A COMMON STARTING POINT</span>
            <p>
              Choose a gauge symmetry <ChevronRight size={14} /> choose matter
              representations <ChevronRight size={14} /> impose anomaly
              cancellation.
            </p>
          </div>
          <div>
            <span>THIS PAPER’S CONSTRUCTION</span>
            <p>
              Vary compact algebra embeddings <ChevronRight size={14} /> impose
              complex type and a nonzero radical <ChevronRight size={14} />
              classify the pair and its representation together.
            </p>
          </div>
        </div>
        <p className="band-note">
          Repeating a complete anomaly-free family leaves cancellation intact.
          To constrain that repetition, the paper supplies additional geometric
          and mixed-anomaly conditions. The next chapters follow what these
          conditions select.
        </p>
      </div>
    </section>
  );
}
