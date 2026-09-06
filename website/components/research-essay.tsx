'use client';
import { asset } from '@/lib/assets';

import { lazy, Suspense, useEffect, useMemo, useRef, useState } from 'react';
import { flushSync } from 'react-dom';
import Image from 'next/image';
import {
  ArrowDown,
  ArrowUpRight,
  Check,
  CheckCircle2,
  Code2,
  Download,
  FileText,
  Layers3,
  Pause,
  Play,
  RotateCcw,
  ShieldCheck,
} from 'lucide-react';
import { Button } from '@/components/ui/button';
import { ExhibitBoundary } from '@/components/exhibit-boundary';
import { Tabs, TabsContent, TabsList, TabsTrigger } from '@/components/ui/tabs';
import { Tabs as TabsPrimitive } from '@base-ui/react/tabs';
import { Switch } from '@/components/ui/switch';
import { ToggleGroup, ToggleGroupItem } from '@/components/ui/toggle-group';
import { ReaderPaths, PathFlow, PathChapter } from '@/components/reader-paths';
import {
  resolvePath,
  chapterInfo,
  type ChapterId,
  type PathId,
} from '@/lib/reader-paths';
import {
  AmbientExhibit,
  DemoControl,
  MotionProvider,
  MotionControl,
  useGentleDemo,
  useMotion,
} from '@/components/exhibit-motion';
import { PhysicsLaboratory } from '@/components/physics-laboratory';
import { SymmetryWorkbench } from '@/components/symmetry-workbench';
import { ModelLandscape } from '@/components/model-landscape';
import {
  ScrollClassification,
  WuExperiment,
  SymmetryPrelude,
  EquationFilm,
  Term,
} from '@/components/learning-exhibits';
const Roots3D = lazy(() => import('@/components/roots-3d'));
import {
  candidates,
  cells,
  checkCertificate,
  edges,
  inspectCell,
  points,
  reflections,
  repository,
  roots,
  snapshot,
} from '@/lib/e6';

const pointMultiplicityIndex = points.map(
  ([x, y], i) =>
    points
      .slice(0, i)
      .filter(([a, b]) => Math.abs(x - a) < 1e-6 && Math.abs(y - b) < 1e-6)
      .length,
);
const fmt = (n: number) => n.toLocaleString('en-US');
const paper = asset('paper.pdf');
const source = (path: string) => repository + '/blob/' + snapshot + '/' + path;
const palette = ['#8bbcff', '#f1a17d', '#91c9b5'];

function SectionLabel({ children }: { n: string; children: React.ReactNode }) {
  return (
    <div className="section-number">
      <span aria-hidden="true" />
      <span className="label-rule" />
      {children}
    </div>
  );
}
function RootDiagram({
  groups,
  common = [],
  show = [true, true, true],
  hero = false,
  spinning = false,
}: {
  groups?: number[][];
  common?: number[];
  show?: boolean[];
  hero?: boolean;
  spinning?: boolean;
}) {
  const color = (i: number) => {
    if (!groups) return i % 7 === 0 ? '#eec49b' : '#94bdf4';
    if (common.includes(i)) return '#f4d592';
    const found = groups.findIndex((g, j) => show[j] && g.includes(i));
    return found < 0 ? '#334050' : palette[found];
  };
  const visible = (i: number) =>
    !groups ||
    common.includes(i) ||
    groups.some((g, j) => show[j] && g.includes(i));
  return (
    <svg
      viewBox="0 0 560 560"
      className={'root-diagram ' + (spinning ? 'spinning' : '')}
      aria-label={
        hero
          ? 'The 72 roots of E6 projected onto a Coxeter plane'
          : 'E6 roots, with selected subsystem roots coloured and their common intersection in gold'
      }
    >
      <title>
        E6 roots projected onto a Coxeter plane; concentric rings distinguish
        coincident projections.
      </title>
      <circle cx="280" cy="280" r="252" className="root-guide" />
      <circle cx="280" cy="280" r="164" className="root-guide" />
      <circle cx="280" cy="280" r="73" className="root-guide" />
      <path d="M280 13V547 M13 280H547" className="root-axis" />
      <g className="root-network">
        {edges.map(([i, j]) => (
          <line
            key={i + '-' + j}
            x1={points[i][0]}
            y1={points[i][1]}
            x2={points[j][0]}
            y2={points[j][1]}
            stroke={
              common.includes(i) && common.includes(j) ? '#f4d592' : '#6e99d4'
            }
            strokeWidth={common.includes(i) && common.includes(j) ? 1.6 : 0.65}
            opacity={
              hero
                ? 0.2
                : common.includes(i) && common.includes(j)
                  ? 0.9
                  : visible(i) && visible(j)
                    ? 0.14
                    : 0.025
            }
          />
        ))}
      </g>
      {points.map(([x, y], i) => (
        <g key={i}>
          <circle
            cx={x}
            cy={y}
            r={common.includes(i) ? 8 : hero ? 5 : 4.5}
            fill={color(i)}
            opacity={visible(i) ? 0.12 : 0.03}
          />
          <circle
            cx={x}
            cy={y}
            r={
              (common.includes(i) ? 3.8 : hero ? 2.4 : 2.8) +
              2.7 * pointMultiplicityIndex[i]
            }
            fill={pointMultiplicityIndex[i] ? 'none' : color(i)}
            stroke={pointMultiplicityIndex[i] ? color(i) : 'none'}
            strokeWidth={1.2}
            opacity={visible(i) ? 1 : 0.35}
          >
            <title>
              {'Root ' +
                (i + 1) +
                ': (' +
                roots[i].join(', ') +
                ')' +
                (common.includes(i) ? ' — common intersection' : '')}
            </title>
          </circle>
        </g>
      ))}
    </svg>
  );
}

const steps = [
  {
    title: 'Start with a compact algebra embedding',
    short: 'The domain',
    formula: <>q = g / h</>,
    text: 'Take a finite-dimensional compact real Lie algebra g and a proper subalgebra h. Require effectiveness: h contains no nonzero ideal of g. The entire adjoint complement q ≅ h⊥ carries the action of h.',
    note: 'The search begins with compact Lie-algebra inclusions, allowing centres, products and every rank. Neither E₈ nor a family number is specified.',
  },
  {
    title: 'Require one complex-type module',
    short: 'Chirality',
    formula: (
      <>
        End<sub>h</sub>(q) ≅ ℂ
      </>
    ),
    text: 'The adjoint complement is real-irreducible of complex type. Its complexification splits as qℂ = V ⊕ V*, with inequivalent irreducible halves. A Weyl field valued in V has a complex gauge representation.',
    note: 'This is a condition on the entire complement, not permission to select a convenient subrepresentation. It is imposed alongside the nonzero radical condition.',
  },
  {
    title: 'Let the anomaly identify the gauge ideal',
    short: 'The radical',
    formula: (
      <>
        c<sub>V</sub>(k, h, h) = 0
      </>
    ),
    text: 'The cubic trace tensor records the perturbative cubic anomaly. Its radical is the largest ideal k of h for which the tensor vanishes whenever one input lies in k. Demand a nonzero radical.',
    note: 'Mixed inputs from all of h matter while a centre is allowed. Once h is semisimple, cross-factor cubic terms vanish: for an ideal, the pure and mixed tests agree.',
  },
  {
    title: 'Exhaust the domain',
    short: 'Classification',
    formula: <>g simple · h semisimple</>,
    text: 'Both conditions drive the structural reduction to simple g and maximal semisimple h. The proof then excludes rank-deficient cases and reaches six full-rank complex-type candidates for explicit cubic evaluation.',
    note: 'The six rows are the end of a reduction, not an assumption that only six Lie-algebra embeddings exist.',
  },
];

export default function ResearchEssay({
  initialPath = 'curious',
}: {
  initialPath?: PathId;
}) {
  return (
    <MotionProvider>
      <EssayContent initialPath={initialPath} />
    </MotionProvider>
  );
}

function EssayContent({ initialPath }: { initialPath: PathId }) {
  const { enabled: motionEnabled } = useMotion();
  const [pathId, setPathId] = useState<PathId>(initialPath);
  const currentPath = useRef(initialPath);
  const path = resolvePath(pathId);
  const [depth, setDepth] = useState(resolvePath(initialPath).depth);
  const [view, setView] = useState('3d');
  const flatViewControl = useRef<HTMLButtonElement>(null);
  const [activeSection, setActiveSection] = useState('question');
  const [spin, setSpin] = useState(true);
  const [heroVisible, setHeroVisible] = useState(true);
  const heroRef = useRef<HTMLDivElement>(null);
  const [step, setStep] = useState('0');
  const [candidate, setCandidate] = useState('5');
  const [cell, setCell] = useState(5);
  const [permutation, setPermutation] = useState(roots.map((_, i) => i));
  const [reflectionCount, setReflectionCount] = useState(0);
  const [show, setShow] = useState([true, true, true]);
  const [spectrum, setSpectrum] = useState('full');
  const [conjugate, setConjugate] = useState(false);
  const [report, setReport] = useState<ReturnType<
    typeof checkCertificate
  > | null>(null);
  const [copied, setCopied] = useState(false);
  const [copyError, setCopyError] = useState(false);
  const geometry = useMemo(
    () => inspectCell(cell, permutation),
    [cell, permutation],
  );

  const selectCell = (index: number) => {
    setCell(index);
    setPermutation(roots.map((_, i) => i));
    setReflectionCount(0);
  };
  const reflect = () => {
    const p = reflections[reflectionCount % 6];
    setPermutation((previous) => previous.map((i) => p[i]));
    setReflectionCount((n) => n + 1);
  };

  const stepDemoRef = useRef<HTMLDivElement>(null);
  const stepDemo = useGentleDemo(
    stepDemoRef,
    () => setStep((s) => String((Number(s) + 1) % steps.length)),
    18000,
    pathId,
  );
  const candidateDemoRef = useRef<HTMLDivElement>(null);
  const candidateDemo = useGentleDemo(
    candidateDemoRef,
    () => setCandidate((c) => String((Number(c) + 1) % candidates.length)),
    14000,
    pathId,
  );
  const geometryDemoRef = useRef<HTMLDivElement>(null);
  const geometryDemo = useGentleDemo(
    geometryDemoRef,
    () => selectCell((cell + 1) % cells.length),
    18000,
    pathId,
  );
  const spectrumDemoRef = useRef<HTMLDivElement>(null);
  const spectrumDemo = useGentleDemo(
    spectrumDemoRef,
    () => setSpectrum((s) => (s === 'full' ? 'net' : 'full')),
    12000,
    pathId,
  );

  const choosePath = (id: PathId) => {
    const next = resolvePath(id);
    const apply = () => {
      currentPath.current = next.id;
      setPathId(next.id);
      setDepth(next.depth);
      setActiveSection(next.chapters[0]);
    };
    const transition = (
      document as Document & {
        startViewTransition?: (callback: () => void) => unknown;
      }
    ).startViewTransition;
    if (transition && motionEnabled)
      transition.call(document, () => flushSync(apply));
    else apply();
    const url = new URL(location.href);
    url.searchParams.set('path', next.id);
    url.hash = 'reader-paths';
    history.replaceState(history.state, '', url);
  };
  useEffect(() => {
    const restore = () => {
      const next = resolvePath(new URL(location.href).searchParams.get('path'));
      if (next.id === currentPath.current) return;
      currentPath.current = next.id;
      setPathId(next.id);
      setDepth(next.depth);
      setActiveSection(next.chapters[0]);
    };
    restore();
    window.addEventListener('popstate', restore);
    return () => window.removeEventListener('popstate', restore);
  }, []);

  useEffect(() => {
    const observer = new IntersectionObserver(
      (entries) =>
        entries.forEach((entry) => {
          if (entry.isIntersecting) setActiveSection(entry.target.id);
        }),
      { rootMargin: '-15% 0px -65% 0px' },
    );
    const observed = new Map<string, HTMLElement>();
    const watchChapters = () => {
      Object.keys(chapterInfo).forEach((id) => {
        const element = document.getElementById(id);
        const previous = observed.get(id);
        if (element === previous) return;
        if (previous) observer.unobserve(previous);
        if (element) {
          observed.set(id, element);
          observer.observe(element);
        } else observed.delete(id);
      });
    };
    watchChapters();
    const chapterChanges = new MutationObserver(watchChapters);
    const flow = document.querySelector('.path-flow');
    if (flow) chapterChanges.observe(flow, { childList: true, subtree: true });
    const heroObserver = new IntersectionObserver(([entry]) =>
      setHeroVisible(entry.isIntersecting),
    );
    if (heroRef.current) heroObserver.observe(heroRef.current);
    return () => {
      observer.disconnect();
      chapterChanges.disconnect();
      heroObserver.disconnect();
    };
  }, [path]);

  useEffect(() => {
    type Tool = {
      name: string;
      title: string;
      description: string;
      inputSchema: object;
      annotations: { readOnlyHint: boolean; untrustedContentHint: boolean };
      execute: (input: unknown) => unknown;
    };
    const context = (
      document as Document & {
        modelContext?: {
          registerTool: (
            tool: Tool,
            options: { signal: AbortSignal },
          ) => void | Promise<void>;
        };
      }
    ).modelContext;
    if (!context?.registerTool) return;
    const lifecycle = new AbortController();
    const register = (tool: Tool) => {
      try {
        void Promise.resolve(
          context.registerTool(tool, { signal: lifecycle.signal }),
        ).catch(() => {});
      } catch {
        /* The essay works without this optional browser API. */
      }
    };
    register({
      name: 'select_e6_cell',
      title: 'Explore an E6 configuration',
      description:
        'Select one of the six verified E6 incidence cells and update the visible explorer. Returns its representative intersection counts.',
      inputSchema: {
        type: 'object',
        properties: { cell: { type: 'integer', minimum: 1, maximum: 6 } },
        required: ['cell'],
        additionalProperties: false,
      },
      annotations: { readOnlyHint: false, untrustedContentHint: false },
      execute: (input) => {
        if (
          !input ||
          typeof input !== 'object' ||
          Object.keys(input).length !== 1 ||
          !('cell' in input) ||
          !Number.isInteger(input.cell) ||
          Number(input.cell) < 1 ||
          Number(input.cell) > 6
        )
          throw new Error('cell must be an integer from 1 to 6.');
        const index = Number(input.cell) - 1;
        flushSync(() => selectCell(index));
        document
          .getElementById('geometry')
          ?.scrollIntoView({ behavior: 'instant' });
        return {
          cell: index + 1,
          profile: inspectCell(index).profile,
          commonRoots: cells[index].common_root_count,
          labelledTriples: cells[index].cell_count,
        };
      },
    });
    register({
      name: 'run_local_certificate_checks',
      title: 'Check the displayed E6 data',
      description:
        'Run the same six local checks as the visible verification button and display the results. Does not run the full Python census or Lean.',
      inputSchema: {
        type: 'object',
        properties: {},
        additionalProperties: false,
      },
      annotations: { readOnlyHint: false, untrustedContentHint: false },
      execute: (input) => {
        if (
          !input ||
          typeof input !== 'object' ||
          Array.isArray(input) ||
          Object.keys(input).length
        )
          throw new Error('Expected an empty object.');
        const result = checkCertificate();
        flushSync(() => setReport(result));
        return result;
      },
    });
    return () => lifecycle.abort();
  }, []);

  const reviewPrompt =
    'Independently examine From Chirality to the Standard Model by Emad Mostaque at ' +
    repository +
    '. Read the complete paper and inspect the executable verification. Start with effective compact Lie-algebra inclusions and the entire adjoint complement. Audit how complex type and a nonzero cubic radical jointly drive structural reduction; then check all-rank completeness, the six cubic tests, E6 incidence and the threefold net chiral class. Seek counterexamples, omitted cases and unjustified implications. Cite exact locations and record the revision and checks actually run. Distinguish manuscript proofs, exact computations and the finite Lean trust model. If sources are inaccessible, request the PDF and repository ZIP.';

  return (
    <main data-depth={depth} data-path={pathId}>
      <a href={'#' + path.chapters[0]} className="skip-link">
        Skip to the research essay
      </a>
      <header className="masthead">
        <a className="wordmark" href="#beginning">
          CHIRALITY<span> / </span>STANDARD MODEL
        </a>
        <nav>
          <MotionControl />
          <a href="#reader-paths">Your path</a>
          <a
            className="repository-link"
            href={repository}
            target="_blank"
            rel="noreferrer"
          >
            Repository <ArrowUpRight size={14} />
          </a>
          <a
            href={paper}
            target="_blank"
            rel="noreferrer"
            className="paper-link"
          >
            Read the paper <ArrowUpRight size={15} />
          </a>
        </nav>
      </header>
      <section className="hero" id="beginning" tabIndex={-1}>
        <div className="hero-kicker">
          <span className="live-dot" /> AN INTERACTIVE RESEARCH ESSAY{' '}
          <span className="edition">EMAD MOSTAQUE · 2026</span>
        </div>
        <div className="hero-content">
          <div className="hero-copy">
            <p className="eyebrow">FROM CHIRALITY TO THE STANDARD MODEL</p>
            <h1>
              What if handedness
              <br />
              fixed the structure
              <br />
              of <em>matter?</em>
            </h1>
            <p className="hero-deck">
              The electron in an atom belongs to a pattern that repeats across
              three families of matter. The weak interaction treats left and
              right differently. This is a journey from those discoveries to a
              mathematical question: could a common origin fix the pattern?
            </p>
            <a className="primary-link" href="#reader-paths">
              Find your way into the argument <ArrowDown size={18} />
            </a>
          </div>
          <div className="hero-art" ref={heroRef}>
            <div className="hero-halo" />
            <AmbientExhibit>
              <RootDiagram
                hero
                spinning={spin && heroVisible && motionEnabled}
              />
            </AmbientExhibit>
            <div className="root-overlay">
              <span>
                E<sub>6</sub>
              </span>
              <small>
                <span>72 ROOTS</span>
                <span>6 DIMENSIONS</span>
              </small>
            </div>
            <div className="art-caption">
              <span>COXETER-PLANE PROJECTION</span>
              <Button
                variant="ghost"
                size="sm"
                disabled={!motionEnabled}
                aria-label={
                  !motionEnabled
                    ? 'Root animation paused by motion settings'
                    : spin
                      ? 'Pause root rotation'
                      : 'Rotate root projection'
                }
                onClick={() => setSpin(!spin)}
              >
                {spin && motionEnabled ? (
                  <Pause size={13} />
                ) : (
                  <Play size={13} />
                )}
                <span>
                  {!motionEnabled ? 'Motion paused' : spin ? 'Pause' : 'Rotate'}
                </span>
              </Button>
            </div>
          </div>
        </div>
        <div className="hero-footer">
          <span>A UNIQUENESS & NO-GO THEOREM</span>
          <span className="hero-result-chain">
            <span>ONE PAIR</span>
            <span>
              <span className="footer-arrow">→</span> TWO EXTREMAL
              CONFIGURATIONS
            </span>
            <span>
              <span className="footer-arrow">→</span> THREE NET FAMILIES
            </span>
          </span>
        </div>
      </section>

      <ReaderPaths selected={pathId} depth={depth} onChoose={choosePath} />
      <div className="reading-level">
        <div>
          <span className="eyebrow">CHOOSE YOUR DEPTH</span>
          <p>The same argument, with more detail when you want it.</p>
        </div>
        <ToggleGroup
          value={[depth]}
          onValueChange={(values) => {
            if (values[0]) setDepth(values[0]);
          }}
          aria-label="Reading depth"
        >
          <ToggleGroupItem value="story">The story</ToggleGroupItem>
          <ToggleGroupItem value="explore">Explore</ToggleGroupItem>
          <ToggleGroupItem value="math">The mathematics</ToggleGroupItem>
        </ToggleGroup>
      </div>
      <nav className="chapter-nav" aria-label="Essay chapters">
        {activeSection in chapterInfo &&
          !path.chapters.includes(activeSection as ChapterId) && (
            <a
              className="optional-location active"
              href={'#' + activeSection}
              aria-current="location"
            >
              <span>REFRESHER</span>
              {chapterInfo[activeSection as ChapterId].title}
            </a>
          )}
        {path.chapters.map((id, i) => (
          <a
            key={id}
            href={'#' + id}
            className={activeSection === id ? 'active' : ''}
            aria-current={activeSection === id ? 'location' : undefined}
          >
            <span>{String(i + 1).padStart(2, '0')}</span>
            {chapterInfo[id].title}
          </a>
        ))}
        <a
          href={paper}
          target="_blank"
          rel="noreferrer"
          className="chapter-pdf"
        >
          <FileText size={15} /> PDF
        </a>
      </nav>

      <PathFlow selected={pathId} key={pathId}>
        <PathChapter chapter="selection">
          <ScrollClassification showExample={pathId === 'curious'} />
        </PathChapter>
        <PathChapter chapter="question">
          <section className="section" id="question">
            <SectionLabel n="01">A QUESTION WITH A HISTORY</SectionLabel>
            <div className="section-heading">
              <h2>
                Nature distinguishes
                <br />
                left from <em>right.</em>
              </h2>
              <p className="section-lead">
                Put your hands together. They match as mirror images, but you
                cannot turn one into the other. Physicists once expected the
                laws of nature to treat a process and its mirror image alike.
                Wu’s experiment showed that the weak interaction does not.
              </p>
            </div>
            <div className="history-layout">
              <figure className="wu-portrait">
                <Image
                  unoptimized
                  src={asset('wu-illustration.webp')}
                  width="1024"
                  height="1536"
                  alt="Stylised engraved illustration of Chien-Shiung Wu beside laboratory instruments"
                  loading="lazy"
                />
                <div className="portrait-label">
                  <span>CHIEN-SHIUNG WU</span>
                  <span>1912—1997</span>
                </div>
                <figcaption>
                  AI-generated historical interpretation, based on a portrait
                  from the AIP Emilio Segrè Visual Archives, Segrè Collection.{' '}
                  <a
                    href="https://commons.wikimedia.org/wiki/File:Informal_portrait_of_Chien-shiung_Wu.jpg"
                    target="_blank"
                    rel="noreferrer"
                  >
                    Source
                  </a>{' '}
                  ·{' '}
                  <a
                    href="https://creativecommons.org/licenses/by/4.0/"
                    target="_blank"
                    rel="noreferrer"
                  >
                    CC BY 4.0
                  </a>
                  ; stylised and recomposed. The apparatus is illustrative.
                </figcaption>
              </figure>
              <div className="timeline">
                <article>
                  <span className="timeline-year">1956</span>
                  <div>
                    <h3>Ask whether the mirror rule was ever tested</h3>
                    <p>
                      Tsung-Dao Lee and Chen-Ning Yang examined the evidence for
                      parity conservation. For the weak interaction, the
                      decisive experiments were missing. They proposed ways to
                      test what had been treated as a general rule of nature.
                    </p>
                    <a
                      href="https://journals.aps.org/pr/abstract/10.1103/PhysRev.104.254"
                      target="_blank"
                      rel="noreferrer"
                    >
                      Lee & Yang, Question of Parity Conservation{' '}
                      <ArrowUpRight size={13} />
                    </a>
                  </div>
                </article>
                <article>
                  <span className="timeline-year">1957</span>
                  <div>
                    <h3>The mirror breaks</h3>
                    <p>
                      Wu and her National Bureau of Standards collaborators
                      found that electrons from polarised cobalt-60 nuclei
                      preferred one direction relative to the nuclear spin.
                      Their experiment established parity violation in beta
                      decay: the weak interaction distinguishes a process from
                      its mirror image.
                    </p>
                    <a
                      href="https://journals.aps.org/pr/abstract/10.1103/PhysRev.105.1413"
                      target="_blank"
                      rel="noreferrer"
                    >
                      Wu et al., Physical Review <ArrowUpRight size={13} />
                    </a>
                  </div>
                </article>
              </div>
            </div>
            <WuExperiment />
            <SymmetryPrelude />
            <div className="mathematician-gallery">
              {[
                {
                  id: 'lie',
                  name: 'Sophus Lie',
                  date: '1870s',
                  text: 'Continuous transformations become an object of study.',
                  url: 'https://mathshistory.st-andrews.ac.uk/Biographies/Lie/',
                },
                {
                  id: 'killing',
                  name: 'Wilhelm Killing',
                  date: '1888–1890',
                  text: 'The simple algebras, including the exceptional cases, come into view.',
                  url: 'https://eudml.org/doc/157352',
                },
                {
                  id: 'cartan',
                  name: 'Élie Cartan',
                  date: '1894',
                  text: 'The classification is completed and its exceptional structures constructed.',
                  url: 'https://books.google.cat/books?id=JY8LAAAAYAAJ',
                },
              ].map((p) => (
                <a key={p.id} href={p.url} target="_blank" rel="noreferrer">
                  <Image
                    unoptimized
                    src={asset(p.id + '-illustration.webp')}
                    width={1122}
                    height={1402}
                    alt={'Stylised engraved portrait of ' + p.name}
                    loading="lazy"
                  />
                  <div>
                    <span>{p.date}</span>
                    <h4>
                      {p.name} <ArrowUpRight size={14} />
                    </h4>
                    <p>{p.text}</p>
                  </div>
                </a>
              ))}
            </div>
            <p className="source-note">
              Illustrated historical portraits. Dates identify the work
              described, not the age shown in each portrait.
            </p>
            <div className="question-band">
              <span className="eyebrow">
                FROM THE EXPERIMENT TO ITS DESCRIPTION
              </span>
              <h3>
                Left and right follow
                <br />
                different <em>weak-interaction rules.</em>
              </h3>
              <p className="band-note">
                In the Standard Model, left- and right-chiral fermion fields
                transform differently under the weak gauge symmetry. “Chiral”
                describes this handed structure. Lie algebras and their
                representations let us write down exactly how it works.
              </p>
            </div>
          </section>
        </PathChapter>

        <PathChapter chapter="physics">
          <PhysicsLaboratory />
        </PathChapter>
        <PathChapter chapter="foundations">
          <SymmetryWorkbench
            depth={depth}
            returnToCharges={pathId === 'physics'}
          />
        </PathChapter>
        <PathChapter chapter="frontiers">
          <ModelLandscape />
        </PathChapter>
        <PathChapter chapter="argument">
          <section className="section argument-section" id="argument">
            <SectionLabel n="02">THE LOGICAL CHAIN</SectionLabel>
            <div className="section-heading">
              <h2>
                Start broad.
                <br />
                Ask a <em>precise question.</em>
              </h2>
              <p className="section-lead">
                A long list is useful only if you know what to ask of it. The
                paper makes two demands on a compact algebra embedding: its
                remaining directions form one complex-type whole, and its cubic
                anomaly leaves a nonzero gauge ideal. It then follows those
                demands through the domain.
              </p>
            </div>
            <div className="plain-result">
              <p>
                <Term meaning="A theorem that identifies all solutions within stated assumptions. Here one pair survives up to duality, and every other pair in the domain is excluded.">
                  Uniqueness and no-go
                </Term>{' '}
                is a precise claim: one pair meets the conditions, and the
                alternatives in that domain do not. The equations below say
                exactly what the conditions are.
              </p>
            </div>
            <details
              className="unpack-panel"
              open={depth === 'math' ? true : undefined}
            >
              <summary>
                Open the precise assumptions <span>+</span>
              </summary>
              <div className="isotropy-bridge">
                <h3>From an algebra embedding to a homogeneous space</h3>
                <p>
                  The starting object is h ⊂ g. An invariant positive inner
                  product identifies q = g/h with h⊥. The action is the bracket:
                  an element of h moves the remaining directions within q. The
                  quotient need not itself be a Lie algebra.
                </p>
                <p>
                  The two conditions force g to be simple and h semisimple.
                  Integrating the compact semisimple algebra h gives a closed,
                  connected subgroup H of a compact group G. Now G/H realizes
                  the same q as a tangent representation. Homogeneity belongs
                  here: it is a geometric realization of the qualifying pair,
                  not an assumption that physical space is homogeneous.
                </p>
              </div>
              <div ref={stepDemoRef} {...stepDemo.handlers}>
                <DemoControl {...stepDemo} />
                <Tabs
                  value={step}
                  onValueChange={(value) => setStep(String(value))}
                  className="step-tabs"
                >
                  <TabsList className="step-list">
                    {steps.map((s, i) => (
                      <TabsTrigger value={String(i)} key={s.short}>
                        <span>0{i + 1}</span>
                        {s.short}
                      </TabsTrigger>
                    ))}
                  </TabsList>
                  {steps.map((s, i) => (
                    <TabsContent
                      value={String(i)}
                      key={s.short}
                      className="step-panel"
                    >
                      <div>
                        <span className="eyebrow">STEP 0{i + 1}</span>
                        <h3>{s.title}</h3>
                        <p>{s.text}</p>
                        <p className="step-note">{s.note}</p>
                      </div>
                      <div className="formula-card">
                        <div className="formula">{s.formula}</div>
                        <span>
                          {i === 0
                            ? 'ISOTROPY: THE QUOTIENT DIRECTIONS'
                            : i === 1
                              ? 'COMPLEX TYPE: V IS NOT ITS DUAL'
                              : i === 2
                                ? 'A NONZERO IDEAL INSULATED FROM THE CUBIC ANOMALY'
                                : 'STRUCTURAL REDUCTION, THEN EXHAUSTION'}
                        </span>
                      </div>
                    </TabsContent>
                  ))}
                </Tabs>
              </div>
              <details className="inline-depth">
                <summary>
                  Why include the mixed inputs? <span>+</span>
                </summary>
                <p>
                  Consider e₇ ⊃ e₆ ⊕ u(1). The complex half is a charged 27.
                  Three e₆ inputs give zero cubic anomaly, but an e₆–e₆–u(1)
                  insertion does not. The central generator acts as Tz = λI with
                  λ ≠ 0, so cV(X,z,X) = λ Tr(TX²) ≠ 0 for nonzero X. Thus the
                  pure e₆ test passes while the full radical is zero.
                </p>
                <p>
                  This distinction matters before the centre is excluded. Once h
                  is semisimple, mixed cubic terms between simple factors vanish
                  by tracelessness. For a fixed ideal k, testing cV(k,k,k) = 0
                  then agrees with testing cV(k,h,h) = 0.{' '}
                  <a
                    href={source('paper/paper.tex')}
                    target="_blank"
                    rel="noreferrer"
                  >
                    Manuscript, structural reduction ↗
                  </a>
                </p>
              </details>
            </details>
            <div className="candidate-intro">
              <span className="eyebrow">THE CUBIC TEST</span>
              <h3>Six candidates. One nonzero radical.</h3>
              <p>
                Select a row to see why it passes or fails. These are the six
                full-rank candidates left by the structural reduction;
                rank-deficient cases are excluded in the paper.
              </p>
            </div>
            <details
              className="unpack-panel candidate-unpack"
              id="cubic-test"
              open={depth !== 'story' ? true : undefined}
            >
              <summary>
                Inspect each candidate’s cubic anomaly <span>+</span>
              </summary>
              <div ref={candidateDemoRef} {...candidateDemo.handlers}>
                <DemoControl {...candidateDemo} />
                <TabsPrimitive.Root
                  value={candidate}
                  onValueChange={(value) => setCandidate(String(value))}
                  orientation="vertical"
                  data-slot="tabs"
                  className="candidate-layout group/tabs"
                >
                  <TabsList className="candidate-list">
                    {candidates.map((c, i) => (
                      <TabsTrigger
                        value={String(i)}
                        key={c.g + c.h}
                        className={i === 5 ? 'survivor-trigger' : ''}
                      >
                        <span className="candidate-number">0{i + 1}</span>
                        <span className="candidate-pair">
                          {c.g}
                          <span> ⊃ </span>
                          {c.h}
                        </span>
                        <span
                          className={
                            'candidate-result ' + (i === 5 ? 'is-survivor' : '')
                          }
                        >
                          {i === 5 ? (
                            <>
                              <Check size={14} /> E₆
                            </>
                          ) : (
                            'rad = 0'
                          )}
                        </span>
                      </TabsTrigger>
                    ))}
                  </TabsList>
                  {candidates.map((c, i) => (
                    <TabsContent
                      value={String(i)}
                      key={c.g + c.h}
                      className="candidate-detail"
                    >
                      <div className="panel-top">
                        <span>CUBIC COEFFICIENTS</span>
                        <span>{i === 5 ? 'SURVIVES' : 'EXCLUDED'}</span>
                      </div>
                      <div className="coefficient-row">
                        {c.coefficients.map((co, j) => (
                          <div
                            key={j}
                            className={co === 0 ? 'zero-coefficient' : ''}
                          >
                            <span>{c.labels[j]}</span>
                            <strong>
                              {co > 0 ? '+' : ''}
                              {co}
                            </strong>
                            <small>{co === 0 ? 'VANISHES' : 'NONZERO'}</small>
                          </div>
                        ))}
                      </div>
                      <h4>
                        V = {c.module}
                        <span>dim V = {c.dimension}</span>
                      </h4>
                      <p>{c.detail}</p>
                      <div className="radical-line">
                        <span>
                          Rad(c<sub>V</sub>)
                        </span>
                        <strong>{c.radical}</strong>
                      </div>
                    </TabsContent>
                  ))}
                </TabsPrimitive.Root>
              </div>
            </details>
            <p className="source-note">
              Coefficients use the paper’s defining-representation normalization
              and its choice of complex half; conjugation reverses all signs,
              not the radical.{' '}
              <a
                href={source('paper/paper.tex')}
                target="_blank"
                rel="noreferrer"
              >
                Manuscript: the cubic calculation ↗
              </a>
            </p>
            <AmbientExhibit>
              <div className="survivor-banner">
                <span className="eyebrow">
                  THE UNIQUE SURVIVOR, UP TO DUALITY
                </span>
                <div className="survivor-equation">
                  e<sub>8</sub> <span>⊃</span> e<sub>6</sub> <span>⊕</span>{' '}
                  su(3)
                  <sub>M</sub>
                </div>
                <div className="survivor-details">
                  <span>
                    MATTER HALF <strong>27 ⊗ 3</strong>
                  </span>
                  <span>
                    GAUGE IDEAL <strong>E₆</strong>
                  </span>
                  <span>
                    MULTIPLICITY <strong>3</strong>
                  </span>
                </div>
                <p>
                  At Lie-algebra level, the assumptions select (e₈, e₆ ⊕ su(3)).
                  The E₆ ideal is anomaly-safe even with mixed isotropy inputs.
                  The SU(3)
                  <sub>M</sub> factor supplies multiplicity and has a nonzero
                  cubic anomaly of its own.
                </p>
              </div>
            </AmbientExhibit>
            <EquationFilm />
          </section>
        </PathChapter>

        <PathChapter chapter="geometry">
          <section className="geometry-section" id="geometry">
            <div className="section">
              <SectionLabel n="03">EXPLORE THE VERIFIED GEOMETRY</SectionLabel>
              <div className="section-heading">
                <h2>
                  38,880 possibilities.
                  <br />
                  <em>Six configurations.</em>
                </h2>
                <p className="section-lead">
                  A smaller symmetry sits inside E₆ when its generators close
                  under the same bracket. Lay three such patterns over one
                  another and ask which transformations they share. There are 27
                  choices of the first pattern, 36 of the second and 40 of the
                  third. All 38,880 combinations fall into six types under
                  symmetry.
                </p>
              </div>
              <p className="explorer-invitation">
                {depth === 'story'
                  ? 'Open the explorer to see the '
                  : 'The points below are '}
                <Term meaning="Roots are vectors that encode the structure of a Lie algebra. These 72 vectors belong to E6. They are not 72 particles, and their six coordinates are internal mathematical data.">
                  roots
                </Term>
                , a compact way to record that symmetry. Choose a configuration,
                hide a layer, or turn the pattern in 3D. Gold marks the
                directions all three share.
              </p>
              <p className="explorer-task">
                Try configurations 06 and 04. In 06, every pair shares as many
                roots as it can. In 04, more roots belong to all three at once.
                Maximising the pairs and maximising the common part are
                different questions.
              </p>
              <details
                className="geometry-depth"
                open={depth !== 'story' ? true : undefined}
              >
                <summary>
                  Open the six-configuration explorer <span>+</span>
                </summary>
                <p className="root-notation-key">
                  D, A and Θ name the three subsystem families: D₅, A₅ + A₁ and
                  A₂ + A₂ + A₂. Aₙ and Dₙ are root-system types; the subscript
                  is their rank, not their number of roots. Here “+” joins
                  independent components. An overlap of type A₂ + A₁ has 6 + 2 =
                  8 roots.
                </p>
                <div
                  className="explorer-shell"
                  ref={geometryDemoRef}
                  {...geometryDemo.handlers}
                >
                  <div className="explorer-top">
                    <span>
                      <span className="live-dot" /> LIVE CERTIFICATE EXPLORER
                    </span>
                    <DemoControl {...geometryDemo} />
                    <a href={asset('e6-certificate.json')} download>
                      Download data <Download size={13} />
                    </a>
                  </div>
                  <Tabs
                    value={String(cell)}
                    onValueChange={(value) => selectCell(Number(value))}
                    className="cell-tabs"
                  >
                    <TabsList className="cell-selectors">
                      {cells.map((c, i) => (
                        <TabsTrigger value={String(i)} key={i}>
                          <span className="cell-id">0{i + 1}</span>
                          <span className="cell-value">
                            {fmt(c.cell_count)}
                          </span>
                          <span className="cell-kind">
                            {i === 3
                              ? 'Common maximum'
                              : i === 5
                                ? 'Pairwise maximum'
                                : 'Labelled triples'}
                          </span>
                        </TabsTrigger>
                      ))}
                    </TabsList>
                    <TabsContent value={String(cell)}>
                      <div className="explorer-body">
                        <div className="geometry-display">
                          <ToggleGroup
                            className="view-selector"
                            value={[view]}
                            onValueChange={(values) => {
                              if (values[0]) setView(values[0]);
                            }}
                            aria-label="Root projection view"
                          >
                            <ToggleGroupItem value="2d" ref={flatViewControl}>
                              The flat view
                            </ToggleGroupItem>
                            <ToggleGroupItem value="3d">
                              Turn it in 3D
                            </ToggleGroupItem>
                          </ToggleGroup>
                          {view === '3d' ? (
                            <ExhibitBoundary
                              onFlatView={() => setView('2d')}
                              flatViewControl={flatViewControl}
                            >
                              <Suspense
                                fallback={
                                  <div className="three-loading">
                                    Preparing the 3D root projection…
                                  </div>
                                }
                              >
                                <Roots3D
                                  groups={[geometry.D, geometry.A, geometry.T]}
                                  common={geometry.common}
                                  show={show}
                                />
                              </Suspense>
                            </ExhibitBoundary>
                          ) : (
                            <AmbientExhibit>
                              <RootDiagram
                                spinning
                                groups={[geometry.D, geometry.A, geometry.T]}
                                common={geometry.common}
                                show={show}
                              />
                            </AmbientExhibit>
                          )}
                          <div className="plot-caption">
                            <span>
                              72 ROOTS ·{' '}
                              {view === '3d'
                                ? '3D PROJECTION'
                                : 'COXETER PLANE'}
                            </span>
                            <span>GOLD = COMMON ROOTS</span>
                          </div>
                          <div className="legend-controls">
                            {[
                              'D₅ · 40 roots',
                              'A₅ + A₁ · 32 roots',
                              'A₂³ · 18 roots',
                            ].map((label, j) => (
                              <label
                                key={label}
                                htmlFor={'subsystem-' + j}
                                style={{ color: palette[j] }}
                              >
                                <Switch
                                  id={'subsystem-' + j}
                                  size="sm"
                                  checked={show[j]}
                                  onCheckedChange={(checked) =>
                                    setShow((previous) =>
                                      previous.map((s, k) =>
                                        k === j ? checked : s,
                                      ),
                                    )
                                  }
                                  aria-label={'Show ' + label}
                                />
                                {label}
                              </label>
                            ))}
                          </div>
                        </div>
                        <div
                          className="cell-inspector"
                          aria-live={geometryDemo.automatic ? 'off' : 'polite'}
                        >
                          <span className="eyebrow">
                            CONFIGURATION 0{cell + 1}
                          </span>
                          <h3>
                            {cell === 5
                              ? 'The pairwise maximum'
                              : cell === 3
                                ? 'The common maximum'
                                : 'A non-extremal cell'}
                          </h3>
                          <p>
                            {cell === 5
                              ? 'All three pairwise overlaps attain their individual maxima at once. The common semisimple root system is A₂ + A₁.'
                              : cell === 3
                                ? 'The intersection of all three subsystems has the most roots. The common semisimple root system is A₂ + A₁ + A₁.'
                                : 'This cell contains no common A₂ component. The colour-type factor occurs only in the two extremal cells.'}
                          </p>
                          <dl className="intersection-table">
                            <div className="table-label">
                              <dt>INTERSECTION</dt>
                              <dd>
                                ROOTS <span>SS DIM.</span>
                              </dd>
                            </div>
                            {['D ∩ A', 'D ∩ Θ', 'A ∩ Θ'].map((label, j) => (
                              <div
                                key={label}
                                className={j === 0 ? 'dominant-pair' : ''}
                              >
                                <dt>
                                  {label}
                                  {j === 0 && <small>largest parent</small>}
                                </dt>
                                <dd>
                                  {geometry.profile[j]}
                                  <span>{geometry.dimensions[j]}</span>
                                </dd>
                              </div>
                            ))}
                            <div className="common-row">
                              <dt>D ∩ A ∩ Θ</dt>
                              <dd>
                                {geometry.common.length}
                                <span>roots</span>
                              </dd>
                            </div>
                          </dl>
                          <div className="orbit-meter">
                            <span>
                              <strong>{fmt(cells[cell].cell_count)}</strong> of
                              38,880 triples
                            </span>
                            <div>
                              <i
                                style={{
                                  width:
                                    (cells[cell].cell_count / 38880) * 100 +
                                    '%',
                                }}
                              />
                            </div>
                          </div>
                          <div className="reflection-controls">
                            <Button variant="outline" onClick={reflect}>
                              <RotateCcw size={14} /> Rearrange by symmetry
                            </Button>
                            <span>
                              {reflectionCount
                                ? reflectionCount +
                                  ' applied · counts unchanged'
                                : 'A Weyl reflection changes the placement, not the counts.'}
                            </span>
                          </div>
                        </div>
                      </div>
                    </TabsContent>
                  </Tabs>
                </div>
                <p className="source-note">
                  The root positions and intersections come from the repository
                  certificate. Lines join roots with inner product 1; the
                  projection is a view of a six-dimensional root system. Some
                  roots share a projected position; concentric rings distinguish
                  them. Gold roots remain visible when a subsystem layer is
                  hidden. Semisimple dimension = number of roots + rank.
                </p>
              </details>
              <p className="geometry-plain-reading">
                Only two configurations share an A₂ component, the root-system
                type of the colour algebra su(3). One maximises all three
                pairwise overlaps; the other maximises the overlap shared by all
                three. Following their largest parent gives the Standard Model
                and left–right routes described in the paper.
              </p>
              <details
                className="geometry-depth"
                open={depth !== 'story' ? true : undefined}
              >
                <summary>
                  Follow the two extremal subgroup chains <span>+</span>
                </summary>
                <div className="geometry-insights">
                  <div>
                    <span>4,320</span>
                    <h3>Pairwise maximizers</h3>
                    <p>
                      Common roots: A₂ + A₁. The D ∩ A parent has type A₄ and
                      chiral dimension 15.
                    </p>
                  </div>
                  <div>
                    <span>2,160</span>
                    <h3>Common maximizers</h3>
                    <p>
                      Common roots: A₂ + 2A₁. The D ∩ A parent has type A₃ + 2A₁
                      and chiral dimension 16.
                    </p>
                  </div>
                  <div>
                    <span>1</span>
                    <h3>Intrinsic largest pairing</h3>
                    <p>
                      D ∩ A is uniquely largest in semisimple dimension in every
                      cell. The stated greatest-dimension criterion selects this
                      pairing uniquely.
                    </p>
                  </div>
                </div>
                <div className="chain-line">
                  <span className="eyebrow">
                    THE PAPER THEN IDENTIFIES THE CONNECTED GROUPS
                  </span>
                  <p>
                    G<sub>SM</sub> <span>⊂</span> G<sub>LR</sub> <span>⊂</span>{' '}
                    G<sub>PS</sub> <span>⊂</span> Spin(10) <span>⊂</span> E
                    <sub>6</sub>
                  </p>
                  <small>
                    The global kernels and primitive hypercharge are checked
                    separately: G<sub>SM</sub> = (SU(3) × SU(2) × U(1)) / ℤ₆.
                  </small>
                </div>
              </details>
            </div>
          </section>
        </PathChapter>

        <PathChapter chapter="families">
          <section className="section" id="families">
            <SectionLabel n="04">FROM REPRESENTATION TO MATTER</SectionLabel>
            <div className="section-heading">
              <h2>
                One family pattern.
                <br />
                Three <em>net families.</em>
              </h2>
              <p className="section-lead">
                {pathId === 'mathematics' || pathId === 'review'
                  ? 'Restrict V = 27 ⊗ 3 along the identified subgroup chain. The chiral class cancels conjugate pairs and neutral singlets, leaving three copies of the Standard Model family class. Duality reverses the chiral class.'
                  : 'Under the Standard Model subgroup, the selected representation splits into recognisable pieces. One piece carries the charge pattern of a quark and lepton family. A separate three-dimensional multiplicity space repeats every piece three times.'}
              </p>
              <p className="branching-key">
                A representation can be read using only the transformations of a
                smaller subgroup. It may then split into pieces that no longer
                mix with each other. This is called branching. The components
                stay the same; we are identifying how each piece transforms
                under the smaller symmetry.
              </p>
            </div>
            <div ref={spectrumDemoRef} {...spectrumDemo.handlers}>
              <DemoControl {...spectrumDemo} />
              <div className="branching-header">
                <div className="branching-formula">
                  <strong>27</strong>
                  <span>→</span>
                  <strong>
                    16 <span>+</span> 10 <span>+</span> 1
                  </strong>
                  <small>E₆ → Spin(10)</small>
                </div>
                <p className="branching-key">
                  Now restrict further to SU(5): the Spin(10) 16 gives 10 + 5̄ +
                  1, while the Spin(10) 10 gives 5 + 5̄. The two representations
                  called “10” belong to different groups. The cards below then
                  read these pieces under the Standard Model subgroup.
                </p>
                <ToggleGroup
                  value={[spectrum]}
                  onValueChange={(values) => {
                    if (values[0]) setSpectrum(values[0]);
                  }}
                  aria-label="Matter spectrum view"
                >
                  <ToggleGroupItem value="full">All the pieces</ToggleGroupItem>
                  <ToggleGroupItem value="net">
                    What remains chiral
                  </ToggleGroupItem>
                </ToggleGroup>
              </div>
              <div
                className={
                  'spectrum-map ' + (spectrum === 'net' ? 'net-view' : '')
                }
              >
                <div className="spectrum-chiral">
                  <span className="eyebrow">
                    <Term meaning="One Standard Model family has 15 complex components in the all-left-handed convention used here. A right-handed neutrino, when included, is an additional Standard Model singlet.">
                      CHIRAL FAMILY
                    </Term>
                  </span>
                  <div className="rep-expression">
                    10 + <span className="overline">5</span>
                  </div>
                  <div className="particles">
                    {[
                      {
                        n: 'Q',
                        charge: '(3, 2)₁/₆',
                        d: 6,
                        role: 'quark doublet',
                      },
                      {
                        n: 'uᶜ',
                        charge: '(3̄, 1)₋₂/₃',
                        d: 3,
                        role: 'up antiquark',
                      },
                      {
                        n: 'eᶜ',
                        charge: '(1, 1)₁',
                        d: 1,
                        role: 'charged antilepton',
                      },
                      {
                        n: 'dᶜ',
                        charge: '(3̄, 1)₁/₃',
                        d: 3,
                        role: 'down antiquark',
                      },
                      {
                        n: 'L',
                        charge: '(1, 2)₋₁/₂',
                        d: 2,
                        role: 'lepton doublet',
                      },
                    ].map((p) => (
                      <div
                        key={p.n}
                        title={p.role + ' · ' + p.d + ' complex components'}
                      >
                        <strong>{p.n}</strong>
                        <span>{p.charge}</span>
                      </div>
                    ))}
                  </div>
                  <div className="spectrum-foot">
                    <span>15 complex components</span>
                    <strong>χ = one family</strong>
                  </div>
                </div>
                <div className="spectrum-vector">
                  <span className="eyebrow">
                    <Term meaning="A representation together with its conjugate. The two make equal and opposite contributions to the chiral index. That cancellation does not by itself determine their masses.">
                      VECTOR-LIKE PAIR
                    </Term>
                  </span>
                  <div className="rep-expression">
                    5 + <span className="overline">5</span>
                  </div>
                  <p>
                    Conjugate representations contribute opposite chiral
                    classes.
                  </p>
                  <div className="cancellation">
                    <span>+χ(5)</span>
                    <span>−χ(5)</span>
                  </div>
                  <div className="spectrum-foot">
                    <span>10 complex components</span>
                    <strong>χ = 0</strong>
                  </div>
                </div>
                <div className="spectrum-singlets">
                  <span className="eyebrow">
                    <Term meaning="Fields that do not transform under the Standard Model gauge group. They contribute zero to the net chiral class used here.">
                      NEUTRAL SINGLETS
                    </Term>
                  </span>
                  <div className="rep-expression">1 + 1</div>
                  <p>
                    Two Standard Model singlets, including the singlet in the
                    Spin(10) 16.
                  </p>
                  <div className="spectrum-foot">
                    <span>2 complex components</span>
                    <strong>χ = 0</strong>
                  </div>
                </div>
              </div>
              <p className="source-note">
                These are the same charge labels used in the particle explorer.
                Here every field is written as left-handed: uᶜ, dᶜ and eᶜ are
                the charge-conjugates of the right-handed fields, so their
                charges have the opposite sign. “Net” subtracts conjugate
                representation content; it counts chirality rather than deciding
                which particles are light.
              </p>
              <AmbientExhibit>
                <div className="family-result">
                  <div>
                    <span className="eyebrow">
                      NOW INCLUDE THE MULTIPLICITY FACTOR
                    </span>
                    <div className="family-equation" key={String(conjugate)}>
                      χ({conjugate ? 'V*' : 'V'}) ={' '}
                      <em>{conjugate ? '−3' : '3'}</em> χ(F<sub>SM</sub>)
                    </div>
                    <p>
                      {spectrum === 'full'
                        ? '81 complex components = 45 in the three chiral families + 30 in vector-like pairs + 6 singlets.'
                        : 'After conjugate pairs and singlets drop out of the chiral class, exactly three copies remain.'}
                    </p>
                  </div>
                  <div className="family-controls">
                    <div
                      className={
                        'three-families ' + (conjugate ? 'dual-families' : '')
                      }
                      aria-hidden="true"
                    >
                      {[1, 2, 3].map((n) => (
                        <span key={n}>
                          <Layers3 size={24} />
                          <small>F{n}</small>
                        </span>
                      ))}
                    </div>
                    <label htmlFor="conjugate-half">
                      <Switch
                        id="conjugate-half"
                        checked={conjugate}
                        onCheckedChange={setConjugate}
                        aria-label="Show the dual half’s net chiral index"
                      />
                      Show the dual index χ(V*)
                    </label>
                  </div>
                </div>
              </AmbientExhibit>
              <div className="interpretation-note">
                <span>THE NET CHIRAL CLASS</span>
                <p>
                  Restriction gives three Standard Model family classes, three
                  vector-like 5 ⊕ 5̄ pairs and six singlets. Conjugate pairs and
                  singlets vanish in the chiral class, leaving χ(V) = 3χ(FSM).
                  This is a representation-theoretic consequence of the selected
                  pair. Choosing V* reverses the sign, not the multiplicity.
                </p>
              </div>
            </div>
          </section>
        </PathChapter>

        <PathChapter chapter="implications">
          <section className="implications" id="implications">
            <div className="section">
              <SectionLabel n="05">WHY THE RESULT MATTERS</SectionLabel>
              <h2>
                What was chosen separately
                <br />
                is fixed <em>together.</em>
              </h2>
              <div className="implication-grid">
                <article>
                  <span>01</span>
                  <h3>A symmetry and its matter</h3>
                  <p>
                    The gauge ideal E₆ and the module 27 ⊗ 3 emerge from the
                    same compact algebra embedding. They are not independent
                    choices within this construction.
                  </p>
                </article>
                <article>
                  <span>02</span>
                  <h3>A uniqueness and a no-go</h3>
                  <p>
                    One pair satisfies the stated hypotheses, up to duality.
                    Every other effective compact inclusion in the stated domain
                    is excluded by the same classification.
                  </p>
                </article>
                <article>
                  <span>03</span>
                  <h3>A finite, inspectable route</h3>
                  <p>
                    The subsequent E₆ incidence geometry is small enough to
                    enumerate completely. The root data let you check its two
                    extremal configurations and intrinsic parent ordering.
                  </p>
                </article>
              </div>
              <div className="closing-thought">
                We began with the electron in an atom. Its charge, its weak
                partner and the quark charges now reappear in the branching of
                the selected representation. Three copies of their chiral
                pattern come with it.
                <br />
                <em>
                  Within the paper’s domain, those choices belong to one
                  structure.
                </em>
              </div>
            </div>
          </section>
        </PathChapter>

        <PathChapter chapter="verify">
          <section className="section verification-section" id="verify">
            <SectionLabel n="06">READ IT. RUN IT. QUESTION IT.</SectionLabel>
            <div className="section-heading">
              <h2>
                The argument is open
                <br />
                to <em>inspection.</em>
              </h2>
              <p className="section-lead">
                Read the proof, replay the finite search, or check the
                certificate in Lean. The repository keeps these routes connected
                to the same mathematical inputs.
              </p>
            </div>
            <div className="resource-grid">
              <a
                className="resource-card featured"
                href={paper}
                target="_blank"
                rel="noreferrer"
              >
                <FileText size={24} />
                <span className="resource-type">THE MANUSCRIPT</span>
                <h3>
                  From Chirality to
                  <br />
                  the Standard Model
                </h3>
                <p>
                  The exact domain, uniqueness proof, E₆ incidence geometry and
                  restriction to the threefold chiral class.
                </p>
                <span className="resource-action">
                  Read the PDF <ArrowUpRight size={19} />
                </span>
              </a>
              <a
                className="resource-card"
                href={asset('Cubic_Anomaly_Master_Verification.ipynb')}
                download
              >
                <Code2 size={24} />
                <span className="resource-type">THE MASTER NOTEBOOK</span>
                <h3>
                  Reproduce
                  <br />
                  the calculation.
                </h3>
                <p>
                  One guided notebook, the full Python suite and optional pinned
                  Lean 4 / Mathlib checks.
                </p>
                <span className="resource-action">
                  Download notebook <Download size={18} />
                </span>
              </a>
              <a
                className="resource-card"
                href={repository}
                target="_blank"
                rel="noreferrer"
              >
                <Layers3 size={24} />
                <span className="resource-type">THE REPOSITORY</span>
                <h3>
                  Follow every
                  <br />
                  dependency.
                </h3>
                <p>
                  Source, exact certificates, independent implementations and
                  the verification notes.
                </p>
                <span className="resource-action">
                  Explore on GitHub <ArrowUpRight size={19} />
                </span>
              </a>
            </div>
            <div className="download-strip">
              <a href={asset('paper.tex')} download>
                LaTeX source <Download size={14} />
              </a>
              <a href={repository + '/archive/refs/heads/main.zip'}>
                Complete repository ZIP <Download size={14} />
              </a>
              <a
                href="https://colab.research.google.com/github/emad-ii/chirality-standard-model/blob/main/Cubic_Anomaly_Master_Verification.ipynb"
                target="_blank"
                rel="noreferrer"
              >
                Open Google Colab <ArrowUpRight size={14} />
              </a>
            </div>
            <p className="source-note">
              Open Colab and choose Runtime → Run all. Python runs by default;
              switch on Lean for the finite theorem checks. For an offline copy,
              download the repository ZIP and open the notebook in Jupyter.
            </p>
            <div className="proof-layers">
              <div>
                <span className="proof-label">01 / MANUSCRIPT PROOFS</span>
                <h3>The structural mathematics</h3>
                <p>
                  Compact Lie-algebra reduction, the all-rank classification
                  argument, invariant theory and the passage from Lie algebras
                  to faithful connected groups.
                </p>
              </div>
              <div>
                <span className="proof-label">02 / EXACT COMPUTATION</span>
                <h3>The exhaustive finite searches</h3>
                <p>
                  16 verification checks. Two coordinate realizations. Complete
                  orbit and subsystem censuses. Deterministic certificates and
                  corrupted-data tests.
                </p>
              </div>
              <div>
                <span className="proof-label">03 / LEAN 4 + MATHLIB</span>
                <h3>The finite theorem layer</h3>
                <p>
                  25 exported theorems cover finite census, cubic-selector and
                  E₆ certificate claims, with a checked JSON-to-Lean translation
                  and an explicit axiom audit.
                </p>
              </div>
            </div>
            <AmbientExhibit>
              <div className="live-verification">
                <div className="live-check-heading">
                  <div>
                    <span className="eyebrow">TRY A SMALL CHECK HERE</span>
                    <h3>Verify the data behind this page.</h3>
                    <p>
                      Reconstruct reflections and intersections directly in your
                      browser.
                    </p>
                  </div>
                  <Button
                    onClick={() => setReport(checkCertificate())}
                    className="check-button"
                  >
                    <ShieldCheck size={17} />
                    {report ? 'Run checks again' : 'Run local checks'}
                  </Button>
                </div>
                {report && (
                  <div className="check-report" aria-live="polite">
                    <strong
                      className={report.passed ? 'check-pass' : 'check-fail'}
                    >
                      {report.passed
                        ? 'All six local checks passed'
                        : 'A local check failed'}
                    </strong>
                    {report.checks.map((c) => (
                      <div key={c.label}>
                        {c.passed ? <CheckCircle2 size={16} /> : <span>×</span>}
                        <span>{c.label}</span>
                      </div>
                    ))}
                    <p>{report.scope}</p>
                  </div>
                )}
              </div>
            </AmbientExhibit>
            <details
              className="disclosure"
              open={pathId === 'review' ? true : undefined}
            >
              <summary>
                Source snapshot, proof scope & credits <span>+</span>
              </summary>
              <div>
                <p>
                  This interactive edition is built from the repository’s{' '}
                  <a
                    href={repository + '/tree/' + snapshot}
                    target="_blank"
                    rel="noreferrer"
                  >
                    launch source ↗
                  </a>{' '}
                  . Its PDFs, LaTeX sources, notebook, films and root data are
                  copied directly from that checkout and checked byte for byte.
                  The{' '}
                  <a href={asset('source-manifest.json')}>download manifest</a>{' '}
                  records their SHA-256 hashes. The full repository ZIP includes
                  the website and video sources as well as the mathematical
                  checks.
                </p>
                <p>
                  The browser checks recompute the displayed root and
                  representative data; they do not enumerate all 38,880 triples
                  or execute Lean. The notebook provides those full checks. The
                  Lean layer uses native_decide and reports propext, Quot.sound,
                  Lean.ofReduceBool and Lean.trustCompiler in its trust audit.{' '}
                  <a
                    href={source('verification/README.md')}
                    target="_blank"
                    rel="noreferrer"
                  >
                    Read the exact scope and trust model ↗
                  </a>
                </p>
                <p>
                  Historical sources are linked beside their claims. Historical
                  portraits are stylised illustrations, with sources and
                  adaptation credits beside them. The images share an
                  engraved-ink and paper style. Root diagrams are generated from
                  the published coordinates; the Manim film explains the
                  equations.
                </p>
                <p>
                  This paper was created with the aid of the Intelligent
                  Internet Zenith system. The paper was checked with GPT-6 Astra
                  Pro and Fable 5.1 Max. The repository and computational
                  verification were generated by GPT-6 Astra.
                </p>
              </div>
            </details>
            <div className="review-row">
              <div>
                <h3>Bring your own scrutiny.</h3>
                <p>
                  A useful review reconstructs the argument and looks for
                  counterexamples.
                </p>
              </div>
              <Button
                variant="outline"
                onClick={async () => {
                  try {
                    await navigator.clipboard.writeText(reviewPrompt);
                    setCopied(true);
                    setCopyError(false);
                  } catch {
                    setCopyError(true);
                  }
                }}
              >
                {copied ? (
                  <>
                    <Check size={15} /> Review prompt copied
                  </>
                ) : (
                  'Copy independent-review prompt'
                )}
              </Button>
            </div>
            {copyError && (
              <div className="copy-fallback">
                <p>
                  Clipboard access is unavailable. Select and copy the prompt
                  below.
                </p>
                <textarea
                  aria-label="Independent review prompt"
                  readOnly
                  value={reviewPrompt}
                />
              </div>
            )}
          </section>
        </PathChapter>
      </PathFlow>
      <footer className="site-footer">
        <div>
          <a className="wordmark" href="#beginning">
            CHIRALITY<span> / </span>STANDARD MODEL
          </a>
          <p>A mathematical question about the matter of our world.</p>
        </div>
        <div>
          <span>EMAD MOSTAQUE · 2026</span>
          <a href={paper} target="_blank" rel="noreferrer">
            Paper <ArrowUpRight size={14} />
          </a>
          <a href={repository} target="_blank" rel="noreferrer">
            Repository <ArrowUpRight size={14} />
          </a>
          <a href="#beginning">Back to the beginning ↑</a>
        </div>
      </footer>
    </main>
  );
}
