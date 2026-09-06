'use client';
import { asset } from '@/lib/assets';

import { useEffect, useRef, useState } from 'react';
import Image from 'next/image';
import {
  select,
  easeCubicInOut,
  lineRadial,
  curveCardinalClosed,
  range,
} from 'd3';
import { ArrowDown, ArrowRight } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Switch } from '@/components/ui/switch';
import {
  Tooltip,
  TooltipTrigger,
  TooltipContent,
  TooltipProvider,
} from '@/components/ui/tooltip';
import { candidates } from '@/lib/e6';
import {
  AmbientExhibit,
  DemoControl,
  useGentleDemo,
  useInView,
  useMotion,
} from '@/components/exhibit-motion';

export function Term({
  children,
  meaning,
}: {
  children: React.ReactNode;
  meaning: string;
}) {
  const [open, setOpen] = useState(false);
  return (
    <TooltipProvider delay={100}>
      <Tooltip open={open} onOpenChange={setOpen}>
        <TooltipTrigger
          className="glossary-term"
          onClick={() => setOpen(!open)}
        >
          {children}
        </TooltipTrigger>
        <TooltipContent className="glossary-popup">{meaning}</TooltipContent>
      </Tooltip>
    </TooltipProvider>
  );
}

const collapseStages = [
  {
    title: 'Begin with the complete compact catalogue.',
    label: 'THE STARTING DOMAIN',
    text: 'A Lie algebra describes the infinitesimal rules of a continuous symmetry. Start with any finite-dimensional compact algebra g and an effective proper subalgebra h. Keep every remaining direction: together they form the representation q = g/h.',
    detail:
      'Effective means that h contains no nonzero ideal of g. The quotient is a vector space acted on by h, not generally a Lie algebra. No choice of E₈, rank or family number has been made.',
  },
  {
    title: 'Impose the two conditions together.',
    label: 'COMPLEX TYPE + NONZERO RADICAL',
    text: 'The remaining directions must form one irreducible module of complex type. Its two conjugate halves are inequivalent. For either half, require a nonzero ideal invisible to the cubic trace tensor—even when the other inputs range over all of h.',
    detail:
      'Endₕ(q) ≅ ℂ and Rad(cᵥ) ≠ 0 are both inputs. Together they force g to be simple and h to be maximal and semisimple. In particular, the radical condition helps exclude a central u(1).',
  },
  {
    title: 'Follow every branch of the classification.',
    label: 'SIX EXPLICIT CANDIDATES',
    text: 'The proof treats both full-rank and rank-deficient embeddings. After the structural reduction, it excludes the rank-deficient cases and reaches six full-rank, complex-type candidates. Their cubic tensors finish the classification.',
    detail:
      'The earlier labels are a schematic catalogue, not a count of possible pairs. These six rows, by contrast, are the actual final candidates in the paper.',
  },
  {
    title: 'Keep a gauge ideal with no cubic anomaly.',
    label: 'ONE NONZERO RADICAL',
    text: 'A gauge anomaly would make the quantum symmetry inconsistent. The cubic trace tests the local anomaly. Five candidates have no nonzero ideal insulated from that tensor. The remaining pair fixes E₆ and a multiplicity factor of three.',
    detail:
      'The condition is cᵥ(k, h, h) = 0 for a nonzero ideal k. In the survivor, Rad(cᵥ) = e₆, while the su(3) factor has cubic coefficient 27.',
  },
];

type VisualNode = {
  id: string;
  label: string;
  sub: string;
  x: number;
  y: number;
  opacity: number;
  survivor: boolean;
};
export function ScrollClassification({
  showExample = false,
}: {
  showExample?: boolean;
}) {
  const { reduced, paused } = useMotion();
  const host = useRef<HTMLElement>(null);
  const svg = useRef<SVGSVGElement>(null);
  const [stage, setStage] = useState(0);
  const [excluded, setExcluded] = useState(0);

  useEffect(() => {
    let frame = 0;
    const update = () => {
      frame = 0;
      if (!host.current) return;
      const steps = [
        ...host.current.querySelectorAll<HTMLElement>('.collapse-story-step'),
      ];
      let current = 0;
      steps.forEach((el, i) => {
        if (el.getBoundingClientRect().top < window.innerHeight * 0.55)
          current = i;
      });
      setStage(current);
      const last = steps[3].getBoundingClientRect();
      const amount = Math.max(
        0,
        Math.min(
          1,
          (window.innerHeight * 0.55 - last.top) /
            Math.max(250, last.height * 0.58),
        ),
      );
      setExcluded(current === 3 ? Math.min(5, Math.floor(amount * 6)) : 0);
    };
    const onScroll = () => {
      if (!frame) frame = requestAnimationFrame(update);
    };
    window.addEventListener('scroll', onScroll, { passive: true });
    window.addEventListener('resize', onScroll);
    onScroll();
    return () => {
      window.removeEventListener('scroll', onScroll);
      window.removeEventListener('resize', onScroll);
      cancelAnimationFrame(frame);
    };
  }, []);

  useEffect(() => {
    if (!svg.current) return;
    const duration = reduced || paused ? 0 : 850;
    const root = select(svg.current);
    const families = [
      'Aₙ',
      'Bₙ',
      'Cₙ',
      'Dₙ',
      'G₂',
      'F₄',
      'E₆',
      'E₇',
      'E₈',
      'Direct sums',
      'Centre',
    ];
    const data: VisualNode[] =
      stage < 2
        ? families.map((label, i) => ({
            id: label,
            label,
            sub:
              i < 4
                ? 'an infinite series'
                : i < 9
                  ? 'exceptional'
                  : 'compact structures',
            x: 118 + (i % 3) * 170,
            y: 98 + Math.floor(i / 3) * 112,
            opacity: stage === 1 && i > 8 ? 0.09 : 1,
            survivor: false,
          }))
        : candidates.map((c, i) => ({
            id: c.g + c.h,
            label: c.g + ' ⊃ ' + c.h,
            sub:
              stage === 3 && i < excluded
                ? 'radical = 0'
                : i === 5 && excluded === 5
                  ? 'radical = E₆'
                  : 'candidate ' + (i + 1),
            x: 175 + (i % 2) * 250,
            y: 140 + Math.floor(i / 2) * 136,
            opacity: i < excluded ? 0.12 : 1,
            survivor: i === 5 && excluded === 5,
          }));
    const joined = root
      .selectAll<SVGGElement, VisualNode>('g.option')
      .data(data, (d) => d.id);
    joined
      .exit()
      .transition()
      .duration(duration * 0.65)
      .attr('opacity', 0)
      .attr('transform', 'translate(300,275) scale(.1)')
      .remove();
    const enter = joined
      .enter()
      .append('g')
      .attr('class', 'option')
      .attr('transform', 'translate(300,275) scale(.5)')
      .attr('opacity', 0);
    enter.append('rect').attr('rx', 9);
    enter
      .append('text')
      .attr('class', 'option-label')
      .attr('text-anchor', 'middle')
      .attr('dy', -3);
    enter
      .append('text')
      .attr('class', 'option-sub')
      .attr('text-anchor', 'middle')
      .attr('dy', 23);
    const merged = enter.merge(joined);
    merged.select('text.option-label').text((d) => d.label);
    merged.select('text.option-sub').text((d) => d.sub);
    merged
      .select('rect')
      .transition()
      .duration(duration)
      .attr('x', stage < 2 ? -72 : -113)
      .attr('y', -40)
      .attr('width', stage < 2 ? 144 : 226)
      .attr('height', 82)
      .attr('fill', (d) => (d.survivor ? '#183c36' : '#122235'))
      .attr('stroke', (d) => (d.survivor ? '#9acbb9' : '#365271'))
      .attr('stroke-width', (d) => (d.survivor ? 2 : 1));
    merged
      .transition()
      .duration(duration)
      .ease(easeCubicInOut)
      .attr('opacity', (d) => d.opacity)
      .attr(
        'transform',
        (d) =>
          'translate(' +
          d.x +
          ',' +
          d.y +
          ') scale(' +
          (d.survivor ? 1.07 : 1) +
          ')',
      );
    return () => {
      root.selectAll('*').interrupt();
    };
  }, [stage, excluded, reduced, paused]);

  return (
    <section className="scroll-classification" ref={host} id="selection">
      <div className="collapse-sticky">
        <AmbientExhibit className="collapse-instrument">
          <div className="collapse-heading">
            <span>SCROLL TO FOLLOW THE SELECTION</span>
            <span>0{stage + 1} / 04</span>
          </div>
          <svg
            ref={svg}
            viewBox="0 0 600 555"
            aria-label={
              stage < 2
                ? 'Schematic families of compact symmetry structures'
                : 6 -
                  excluded +
                  ' of six explicit candidates remain after the cubic test'
            }
          >
            <title>
              The classification narrows to six candidates and one nonzero cubic
              radical.
            </title>
          </svg>
          <div className="collapse-caption">
            <strong>
              {stage < 2
                ? 'All compact algebra types'
                : excluded === 5
                  ? 'One pair remains'
                  : fmtCount(6 - excluded) + ' candidates'}
            </strong>
            <span>
              {stage < 2
                ? 'Four series, five exceptions, sums and centre.'
                : 'Exact final candidates from the paper.'}
            </span>
          </div>
          <div className="collapse-progress" aria-label="Selection stages">
            {collapseStages.map((s, i) => (
              <button
                type="button"
                key={s.label}
                className={stage === i ? 'active' : ''}
                onClick={() =>
                  document
                    .getElementById('collapse-step-' + i)
                    ?.scrollIntoView({
                      behavior: reduced || paused ? 'instant' : 'smooth',
                      block: 'center',
                    })
                }
                aria-label={s.label}
                aria-current={stage === i ? 'step' : undefined}
              >
                <span />
              </button>
            ))}
          </div>
        </AmbientExhibit>
      </div>
      <div className="collapse-story">
        {collapseStages.map((s, i) => (
          <article
            key={s.label}
            id={'collapse-step-' + i}
            className={
              'collapse-story-step ' + (stage === i ? 'is-current' : '')
            }
          >
            <span className="eyebrow">
              0{i + 1} / {s.label}
            </span>
            <h2>{s.title}</h2>
            {i === 0 && (
              <p>
                The Killing–Cartan classification exhausts the compact simple
                Lie algebras. A direct sum of simple Lie algebras is called
                semisimple. Allow these sums and an abelian centre, whose
                directions commute with everything, and every finite-dimensional
                compact Lie algebra is covered. The infinite series have no
                upper rank cutoff. This is a complete starting catalogue, not a
                shortlist of favoured symmetries.
              </p>
            )}
            {i === 0 && showExample && (
              <p>
                Rotations move a point around a sphere. The rotations fixing
                that point still act on its tangent plane: the possible
                directions of motion from there. This is isotropy: a symmetry
                left at a point acts on a space of directions. The sphere is an
                illustration, not the paper’s eventual survivor.
              </p>
            )}
            <p>{s.text}</p>
            <details className="inline-depth">
              <summary>
                Unpack this step <span>+</span>
              </summary>
              <p>{s.detail}</p>
            </details>
            {i === 0 && (
              <span className="scroll-cue">
                KEEP SCROLLING <ArrowDown size={14} />
              </span>
            )}
          </article>
        ))}
      </div>
    </section>
  );
}
const fmtCount = (n: number) => String(n);

export function WuExperiment() {
  const { reduced, paused } = useMotion();
  const [mirror, setMirror] = useState(false);
  const demoRef = useRef<HTMLDivElement>(null);
  const demo = useGentleDemo(demoRef, () => setMirror((m) => !m), 13000);
  const svg = useRef<SVGSVGElement>(null);
  useEffect(() => {
    if (!svg.current) return;
    const duration = reduced || paused ? 0 : 950;
    const root = select(svg.current);
    const radial = lineRadial<number>()
      .angle((d) => d)
      .radius((d) => 79 * (1 + (mirror ? 0.55 : -0.55) * Math.cos(d)))
      .curve(curveCardinalClosed);
    root
      .select<SVGPathElement>('.emission-shape')
      .transition()
      .duration(duration)
      .ease(easeCubicInOut)
      .attr('d', radial(range(0, Math.PI * 2, Math.PI / 40)))
      .attr('fill', mirror ? '#f1a17d25' : '#8bbcff25')
      .attr('stroke', mirror ? '#f1a17d' : '#8bbcff');
    const dots = range(24).map((i) => {
      const theta = (i * Math.PI * 2) / 24;
      const radius = 79 * (1 + (mirror ? 0.55 : -0.55) * Math.cos(theta));
      return { x: Math.sin(theta) * radius, y: -Math.cos(theta) * radius };
    });
    root
      .select('.emission-dots')
      .selectAll<SVGCircleElement, { x: number; y: number }>('circle')
      .data(dots)
      .join('circle')
      .style('--emission-delay', (_, i) => `${-i * 0.22}s`)
      .attr('r', 2.1)
      .transition()
      .duration(duration)
      .attr('cx', (d) => d.x)
      .attr('cy', (d) => d.y)
      .attr('fill', mirror ? '#f1a17d' : '#8bbcff');
    return () => {
      root.selectAll('*').interrupt();
    };
  }, [mirror, reduced, paused]);
  return (
    <div className="wu-experiment" ref={demoRef} {...demo.handlers}>
      <div>
        <span className="eyebrow">TRY THE MIRROR</span>
        <DemoControl {...demo} />
        <h3>
          The spin stays.
          <br />
          The preference flips.
        </h3>
        <p>
          Wu’s team aligned the nuclear spins and measured where the electrons
          went. More emerged opposite the spin. A spatial inversion reverses the
          electron directions but leaves spin, an axial vector, unchanged. The
          two patterns differ.
        </p>
        <label htmlFor="mirror-experiment">
          <Switch
            id="mirror-experiment"
            checked={mirror}
            onCheckedChange={setMirror}
          />{' '}
          {mirror
            ? 'Spatially inverted pattern'
            : 'Observed direction of preference'}
        </label>
        <small>
          Illustrative angular pattern, not measured data. The shape exaggerates
          the asymmetry to make it visible.
        </small>
      </div>
      <AmbientExhibit className="wu-diagram">
        <svg
          ref={svg}
          viewBox="0 0 380 350"
          aria-label={
            mirror
              ? 'Mirrored pattern: electron preference along unchanged nuclear spin'
              : 'Original pattern: electron preference opposite nuclear spin'
          }
        >
          <title>Parity reverses momentum, not nuclear spin.</title>
          <g transform="translate(190,175)">
            <circle
              r="125"
              fill="none"
              stroke="#35495c"
              strokeDasharray="2 5"
            />
            <circle r="79" fill="none" stroke="#24384d" />
            <line y1="-142" y2="142" stroke="#35495c" strokeDasharray="3 6" />
            <path className="emission-shape" fill="none" strokeWidth="1.5" />
            <g className="emission-dots" />
            <circle r="9" fill="#ede9df" />
            <path
              d="M0 -15V-108M-5 -101L0 -109L5 -101"
              fill="none"
              stroke="#ede9df"
              strokeWidth="2"
            />
            <text x="14" y="-77" fill="#c4cdd7" fontSize="12">
              nuclear spin
            </text>
          </g>
          <text
            x="190"
            y="338"
            textAnchor="middle"
            fill={mirror ? '#f1a17d' : '#8bbcff'}
            fontSize="11"
          >
            {mirror
              ? 'MIRRORED PATTERN'
              : 'ELECTRONS FAVOUR THE OPPOSITE DIRECTION'}
          </text>
        </svg>
      </AmbientExhibit>
    </div>
  );
}

export function SymmetryPrelude() {
  return (
    <section className="symmetry-prelude">
      <div className="symmetry-story">
        <span className="eyebrow">
          BEFORE THE PARTICLES: A LANGUAGE FOR SYMMETRY
        </span>
        <h3>
          A small turn can tell you
          <br />
          about the whole.
        </h3>
        <p>
          Turn a perfect sphere and it still looks the same. You can turn it a
          little, then a little more. Those continuous transformations form a{' '}
          <Term meaning="A collection of smooth, continuous symmetry transformations. Rotations are a familiar example. Here the groups describe internal symmetries, not extra spatial dimensions.">
            Lie group
          </Term>
          , named after the Norwegian mathematician Sophus Lie.
        </p>
        <p>
          In the 1870s, Lie developed a way to study such transformations
          through their infinitesimal changes. A{' '}
          <Term meaning="The local, linear description of a Lie group near the identity. Its bracket records how infinitesimal transformations fail to commute.">
            Lie algebra
          </Term>{' '}
          records those tiny motions and how they combine. For rotations, the
          order matters: turn a book about one axis and then another, and
          reversing the order generally gives a different result.
        </p>
        <p>
          Killing and Cartan’s classification is exhaustive. Every
          finite-dimensional compact simple Lie algebra belongs to one of four
          infinite series, Aₙ, Bₙ, Cₙ and Dₙ, or five exceptional types: G₂, F₄,
          E₆, E₇ and E₈. There is no further compact simple type outside this
          list. Allowing direct sums and commuting central directions extends
          the catalogue to every finite-dimensional compact Lie algebra. A sum
          of simple factors is called semisimple; the abelian centre is the
          additional part that commutes with the whole algebra.
        </p>
        <p>
          That completeness matters here. The paper starts with the full compact
          domain, then studies embeddings and their representations under its
          two conditions. The catalogue supplies every possible building block;
          the paper’s reduction and anomaly test determine what survives.{' '}
          <a
            href="https://math.mit.edu/~etingof/lnlg.pdf"
            target="_blank"
            rel="noreferrer"
          >
            Classification and compact forms, MIT notes §§22–23, 39, 42 ↗
          </a>
        </p>
        <a
          href="https://ocw.mit.edu/courses/18-755-introduction-to-lie-groups-fall-2004/256974d724f956b5d22d18d6d9935c9f_helga_sopmath3_2.pdf"
          target="_blank"
          rel="noreferrer"
        >
          The history of Lie’s work <ArrowRight size={14} />
        </a>
        <details className="inline-depth">
          <summary>
            Why use this language for particles? <span>+</span>
          </summary>
          <p>
            A representation tells us how a symmetry acts on a set of fields.
            The Standard Model’s charges are representation data. In this paper,
            the remaining directions of a larger algebra supply the
            representation, so the symmetry and its proposed matter content are
            tied together from the start.
          </p>
        </details>
      </div>
      <figure className="symmetry-art">
        <AmbientExhibit className="symmetry-motion">
          <Image
            unoptimized
            src={asset('symmetry-illustration.webp')}
            width={1536}
            height={1024}
            alt="Illustrated sphere, rotation paths and an open mathematics notebook"
            loading="lazy"
          />
          <svg
            viewBox="0 0 240 240"
            className="symmetry-orbit"
            aria-hidden="true"
          >
            <ellipse
              cx="120"
              cy="120"
              rx="98"
              ry="32"
              fill="none"
              stroke="currentColor"
              strokeDasharray="3 10"
            />
            <ellipse
              cx="120"
              cy="120"
              rx="32"
              ry="98"
              fill="none"
              stroke="currentColor"
              strokeDasharray="3 10"
            />
          </svg>
        </AmbientExhibit>
        <figcaption>
          Continuous symmetry, illustrated. These are internal mathematical
          directions in the paper, not extra dimensions of space.
        </figcaption>
      </figure>
    </section>
  );
}

export function EquationFilm() {
  const video = useRef<HTMLVideoElement>(null);
  const visible = useInView(video);
  const { enabled } = useMotion();
  const [manual, setManual] = useState(false);
  useEffect(() => {
    const element = video.current;
    if (!element) return;
    if (!visible || !enabled) element.pause();
    else if (!manual) void element.play().catch(() => {});
  }, [visible, enabled, manual]);
  const chapters = [
    { t: 0, label: 'Algebraic starting point' },
    { t: 11 + 1 / 24, label: 'Complex type' },
    { t: 22 + 21 / 24, label: 'Cubic radical' },
    { t: 35 + 23 / 24, label: 'One survivor' },
    { t: 50 + 1 / 24, label: 'The 27 branches' },
    { t: 63 + 22 / 24, label: 'Three net families' },
  ];
  return (
    <section className="equation-film" id="equation-film">
      <div className="film-heading">
        <div>
          <span className="eyebrow">THE EQUATIONS, ONE AT A TIME</span>
          <h3>Watch the argument take shape.</h3>
        </div>
        <p>
          A short Manim film. Each symbol arrives with its meaning. Pause, go
          back, or jump to a particular step.
        </p>
      </div>
      <video
        ref={video}
        controls
        muted
        loop
        playsInline
        onPointerDown={() => setManual(true)}
        onKeyDown={() => setManual(true)}
        preload="none"
        poster={asset('equation-poster.jpg')}
        aria-label="Manim walkthrough of the core equations"
      >
        <source src={asset('equation-story.mp4')} type="video/mp4" />
        <track
          kind="captions"
          src={asset('equation-story.vtt')}
          srcLang="en"
          label="English"
          default
        />
        Your browser does not support embedded video.{' '}
        <a href={asset('equation-story.mp4')} download>
          Download the equation film.
        </a>
      </video>
      <div className="film-chapters">
        {chapters.map((c, i) => (
          <Button
            key={c.label}
            variant="ghost"
            onClick={() => {
              setManual(true);
              if (video.current) {
                video.current.currentTime = c.t;
                void video.current.play().catch(() => {});
              }
            }}
          >
            <span>0{i + 1}</span>
            {c.label}
          </Button>
        ))}
      </div>
      <details className="inline-depth">
        <summary>
          Read the film as text <span>+</span>
        </summary>
        <div className="film-transcript">
          <p>
            <strong>q = g/h.</strong> Begin with an effective proper inclusion
            of compact real Lie algebras h ⊂ g. The entire adjoint complement q
            is the representation to be classified.
          </p>
          <p>
            <strong>Endₕ(q) ≅ ℂ.</strong> Require one irreducible module of
            complex type. Its complexification splits into inequivalent
            conjugate halves V and V*. Either choice determines the cubic
            tensor; duality changes its sign but not its radical.
          </p>
          <p>
            <strong>cᵥ(k, h, h) = 0, k ≠ 0.</strong> Look for a nonzero ideal
            with no cubic anomaly, even when the other inputs come from the full
            algebra h. This condition and complex type are both used in the
            structural reduction, including the exclusion of a centre.
          </p>
          <p>
            <strong>e₈ ⊃ e₆ ⊕ su(3).</strong> The classification and cubic test
            first reduce to simple g and maximal semisimple h, then exhaust the
            ranks and evaluate six candidates. This unique pair survives, up to
            duality. Its radical is e₆.
          </p>
          <p>
            <strong>V = 27 ⊗ 3.</strong> Each 27 branches into a chiral family,
            a vector-like pair and two Standard Model singlets.
          </p>
          <p>
            <strong>χ(V) = 3χ(FSM).</strong> Conjugate pairs and singlets
            contribute zero net chiral class. Restriction therefore gives
            exactly three copies of the Standard Model family class. The dual
            has the opposite chiral class.
          </p>
        </div>
      </details>
      <div className="download-strip">
        <a href={asset('equation-story.mp4')} download>
          Download equation film
        </a>
        <a
          href={asset('one-survivor-pilot.mp4')}
          target="_blank"
          rel="noreferrer"
        >
          Watch the selection pilot · 78 seconds ↗
        </a>
        <a
          href="https://github.com/emad-ii/chirality-standard-model/tree/main/media"
          target="_blank"
          rel="noreferrer"
        >
          Captions and editable sources ↗
        </a>
      </div>
    </section>
  );
}
